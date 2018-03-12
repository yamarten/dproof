open Names
open Pp

module RelDec = Context.Rel.Declaration
module NamedDec = Context.Named.Declaration

(* flags *)
let term = ref false
let file = ref (None : out_channel option)

(* types *)
type env = {env:Environ.env; rename:(Id.t*Id.t) list; avoid:Id.t list}
type prfstep = Vernacexpr.vernac_expr * Constr.t * (Goal.goal list * Evd.evar_map ref)
type prftree =
  | Proof of prfstep * (Constr.existential_key * prftree) list * bool
  | Warn of std_ppcmds * (Constr.existential_key * prftree) list

let warn s v = str "(* " ++ str s ++ str ": " ++ Ppvernac.pr_vernac v ++ str " *)"

let pr_constr env evmap c =
  Ppconstr.default_term_pr.pr_constr_expr (Constrextern.extern_constr false env.env !evmap c)

let pr_type ?typ env evmap c = match typ with
  | None ->
    let t = Typing.e_type_of env.env evmap c in
    (pr_constr env evmap (Reduction.nf_betaiota env.env t))
  | Some t -> pr_constr env evmap t

(* TODO: Anonymous時の処理 *)
let name_to_id = function
  | Name n -> n
  | Anonymous -> Id.of_string "_"

let pr_name n = Id.print (name_to_id n)

let pr_name_opt = function
  | Some n -> pr_name n ++ str ":"
  | None -> mt ()

let named_to_rel = function
  | NamedDec.LocalAssum (n,c) -> RelDec.LocalAssum (Name n,c)
  | NamedDec.LocalDef (n,c,t) -> RelDec.LocalDef (Name n,c,t)

let new_name ?term env =
  let rec f env em t = match Constr.kind t with
    | Ind _ | Const _ | Var _ | Rel _ -> string_of_ppcmds (pr_constr env em t)
    | App (c,_) -> f env em c
    | Prod (n,t,c) -> f env em t ^ f {env with env = Termops.push_rel_assum (n,t) env.env} em c
    | _ -> ""
  in
  let base = match term with
    | Some (t,evmap) ->
      let tname = f env evmap (Typing.e_type_of env.env evmap t) in
      let tname = Str.global_replace (Str.regexp "[^0-9a-zA-Z]") "" tname in
      let tname = if String.length tname > 3 then String.sub tname 0 2 else tname in
      Id.of_string (Id.to_string Namegen.default_prop_ident ^ tname)
    | None -> Namegen.default_prop_ident
  in
  let name = Namegen.next_ident_away_in_goal base env.avoid in
  name, {env with avoid = name::env.avoid}

let push_rel name ?body typ env =
  (* TODO: typがenv中に存在するときの処理 *)
  let push id =
    let open RelDec in
    match body with
    | None -> Environ.push_rel (LocalAssum (Name id,typ)) env.env
    | Some b -> Environ.push_rel (LocalDef (Name id,b,typ)) env.env
  in
  match name with
  | Anonymous ->
    let (newid,newe) = new_name env in
    Name newid, {newe with env=push newid}
  | Name id ->
    let newid = Namegen.next_ident_away_in_goal id env.avoid in
    let newe = push newid in
    let newmap = if id <> newid then (id,newid)::env.rename else env.rename in
    let newa = newid::env.avoid in
    Name newid, {env = newe; rename = newmap; avoid = newa;}

let rec search_evar t =
  let open Constr in
  match kind t with
  | Evar _ -> true
  | Rel _ | Var _ | Meta _ | Sort _ | Const _ | Ind _ | Construct _ -> false
  | _ -> fold (fun b t -> b || search_evar t) false t

let concl env g e =
  let open Term in
  let a = ref env.avoid in
  let rec f x = match kind_of_term x with
    | LetIn (n,b,t,k) ->
      let n = Namegen.next_name_away n !a in
      a := n::!a;
      map_constr f (mkLetIn (Name n,b,t,k))
    | Lambda (n,t,b) ->
      let n = Namegen.next_name_away n !a in
      a := n::!a;
      map_constr f (mkLambda (Name n,t,b))
    | Var n -> begin try mkVar (List.assoc n env.rename) with Not_found -> x end
    | _ -> map_constr f x
  in
  f (Goal.V82.concl e (List.hd g))

let rec diff_term t1 t2 =
  let open Term in
  let f_array l1 l2 = List.concat @@ Array.to_list @@ CArray.map2 diff_term l1 l2 in
  if eq_constr t1 t2 then [] else
  match kind_of_term t1, kind_of_term t2 with
  | Evar e1, Evar e2 -> []
  | Evar _, _ -> [fst (destEvar t1),t2]
  | Cast (c1,_,t1), Cast (c2,_,t2) -> diff_term c1 c2 @ diff_term t1 t2
  | Lambda (n,t1,b1), Lambda (_,t2,b2) -> diff_term t1 t2 @ diff_term b1 b2
  | LetIn (n,b1,t1,k1), LetIn (_,b2,t2,k2) -> diff_term t1 t2 @ diff_term b1 b2 @ diff_term k1 k2
  | App (b1,l1), App (b2,l2) ->
    if not (isEvar b1) then diff_term b1 b2 @ f_array l1 l2 else
    let (l21,l22) = CArray.chop (Array.length l2 - Array.length l1) l2 in
    diff_term b1 (mkApp (b2,l21)) @ f_array l1 l22
  | Proj (_,t1), Proj (_,t2) -> diff_term t1 t2
  | Case (_,p1,b1,bl1), Case (_,p2,b2,bl2) -> diff_term p1 p2 @ diff_term b1 b2 @ f_array bl1 bl2
  | Fix (_,(ns,tl1,bl1)), Fix (_,(_,tl2,bl2))
  | CoFix (_,(ns,tl1,bl1)), Fix (_,(_,tl2,bl2)) -> f_array tl1 tl2 @ f_array bl1 bl2
  | _ -> failwith "proof term changed"

let rec find_evar g t =
  let open Constr in
  match kind t with
  | Evar (e,_) when e = g -> Some t
  | Rel _ | Var _ | Meta _ | Sort _ | Const _ | Ind _ | Construct _ | Evar _ -> None
  | _ -> fold (fun b t -> if Option.has_some b then b else find_evar g t) None t

let diff_proof e p1 p2 =
  let diffs = List.concat @@ CList.map2 diff_term (Proof.partial_proof p1) (Proof.partial_proof p2) in
  if List.length diffs = 0 then
    let (g::_,_,_,_,_) = Proof.proof p2 in
    (e, Option.get (find_evar g (List.hd (Proof.partial_proof p2))))
  else if List.length diffs > 1 || fst (List.hd diffs) <> e then
    failwith "other goals changed"
  else
    List.hd diffs

(* 新変数名は以降で使われないことを仮定 *)
let find_vars env evmap c =
  let rec collect i env vars c =
    let open Term in
    match kind_of_term c with
    | Rel j ->
      if j <= i then vars,[] else
        (pr_name (RelDec.get_name (Environ.lookup_rel j env.env)))::vars,[]
    | Var n -> (Id.print n::vars),[]
    | LetIn (n,c,t,b) ->
      let (v1,e1) = collect i env vars c in
      let env = {env with env=Environ.push_rel (RelDec.LocalDef (n,b,t)) env.env} in
      let (v2,e2) = collect (i+1) env v1 b in
      v2,e1@e2
    | Lambda (n,t,c) | Prod (n,t,c) ->
      let env = {env with env=Termops.push_rel_assum (n,t) env.env} in
      collect (i+1) env vars c
    (* TODO: | Fix _ -> _ *)
    | Case (_,_,c,a) | App (c,a) ->
      let (v,e) = collect i env vars c in
      let f (v,e) c = let (v',e') = collect i env v c in v',e'@e in
      let (v,e) = Array.fold_left f (v,e) a in
      (* 危険かもしれない *)
      if isSort (Typing.e_type_of env.env evmap c) then ([],e) else (v,e)
    | Cast (c,_,_) -> collect i env vars c
    | Evar _ -> vars,[fst (destEvar c),env]
    | _ -> vars,[]
  in
  let (vars,envs) = collect 0 env [] c in
  (List.rev (CList.uniquize vars), envs)

(* TODO:ローカル環境を持ってくる *)
let init_env p =
  let (g,_,_,_,e) = Proof.proof p in
  let env82 = Goal.V82.env e (List.hd g) in
  let f _ d (l,e) =
    let n = NamedDec.get_id d in
    let t = NamedDec.get_type d in
    n::l, Environ.push_rel (RelDec.LocalAssum (Name n,t)) e
  in
  let (l,env) = Environ.fold_named_context f env82 ~init:([],env82) in
  {env = env; rename = []; avoid = l}

(* 部分適用で壊れない？ *)
let arg_filter c a =
  let open Impargs in
  let l = Array.to_list a in try
  (* print_constr に頼るの危なくない？ *)
  if String.get (string_of_ppcmds (Termops.print_constr c)) 0 = '@' then l else
  let glob = Globnames.global_of_constr c in
  let imps = implicits_of_global glob in
  (* なるべく暗黙の引数が少ないものを選ぶ *)
  let (nums,imp) = CList.last (extract_impargs_data imps) in
  let pos = positions_of_implicits (CList.last imps) in
  let ret = CList.filteri (fun i _ -> not (List.mem (i+1) pos)) l in
  let len = List.length ret in
  (* 適用しきった結果が関数の可能性もあるので、上限の確認はしない *)
  match nums with Some (n,_) when len < n -> l | _ -> ret
  with _ -> l