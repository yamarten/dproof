open Names
open Pp

module RelDec = Context.Rel.Declaration
module NamedDec = Context.Named.Declaration

type env = {env:Environ.env; rename:(Id.t*Id.t) list; avoid:Id.t list}
type prfstep = Vernacexpr.vernac_expr * Constr.t * (Goal.goal list * Evd.evar_map ref)
type prftree =
  | Proof of prfstep * (Constr.existential_key * prftree) list * bool
  | Warn of std_ppcmds * (Constr.existential_key * prftree) list

let warn s v = str "(* " ++ str s ++ str ": " ++ Ppvernac.pr_vernac v ++ str " *)"

let pr_constr env evmap c =
  Ppconstr.default_term_pr.pr_constr_expr (Constrextern.extern_constr false env.env !evmap c)

let pr_type env evmap c = let t = Typing.e_type_of env.env evmap c in pr_constr env evmap t

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

(* TODO: Anonymous時の処理 *)
let name_to_id = function
  | Name n -> n
  | Anonymous -> Id.of_string "_"

let pr_name n = Id.print (name_to_id n)

let pr_name_opt = function
  | Some n -> pr_name n ++ str ":"
  | None -> mt ()

(* 新変数名は以降で使われないことを仮定 *)
let find_vars env c =
  let rec collect i env vars c =
    let open Term in
    match kind_of_term c with
    | Rel j ->
      if j <= i then vars,[] else
        (pr_name (RelDec.get_name (Environ.lookup_rel j env.env)))::vars,[]
    | Const (c,_) -> (Constant.print c)::vars,[]
    | Var n -> (Id.print n)::vars,[]
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
      Array.fold_left f (v,e) a
    | Cast (c,_,_) -> collect i env vars c
    | Evar _ -> vars,[fst (destEvar c),env]
    | _ -> vars,[]
  in
  let (vars,envs) = collect 0 env [] c in
  (List.rev (CList.uniquize vars), envs)

let reset_level, is_bullet =
  let n = ref 0 in
  (fun () -> n := 0),
  let open Vernacexpr in
  function
  | VernacBullet _ -> true
  | VernacFocus None | VernacFocus (Some 1)
  | VernacSubproof None | VernacSubproof (Some 1) -> n := !n+1; true
  | VernacUnfocus | VernacEndSubproof when !n > 0 -> n := !n-1; true
  | _ -> false

let prftree stream =
  let s = Stream.of_list stream in
  let rec sublist = function
    | _,[],_ -> true
    | 0,l1,_::l2 | -1,l1,l2 -> l1 = l2
    | n, l1, _::l2 when n > 0 -> sublist (n-1,l1,l2)
    | _,_,_ -> false
  in
  let warn s v p e = [e, Warn (warn s v, p)] in
  let rec f () =
    if Stream.peek s = None then [] else
    let (p1,v,p2) = Stream.next s in
    if is_bullet v then f () else
    let (g1,b1,_,_,e1) = Proof.proof p1 in
    let (g2,b2,_,_,e2) = Proof.proof p2 in
    let n1 = List.length g1 in
    let n2 = List.length g2 in
    if n1 = 0 then [] else
    try
      let (evar,diff) = diff_proof (List.hd g1) p1 p2 in
      let step = (v, diff, (g1,ref e2)) in
      let eq_env e = try Environ.eq_named_context_val (Goal.V82.hyps e1 (List.hd g1)) (Goal.V82.hyps e2 e) with _ -> false in
      if sublist (n2-n1,List.tl g1,g2) then
        let rec fork n = if n>=0 then f () @ fork (n-1) else [] in
        let l = List.rev (fork (n2-n1)) in
        let eq = List.fold_left (fun b e -> eq_env e && b) true (CList.firstn (List.length l) g2) in
        [evar, Proof (step, l, eq)]
      else warn "unsupported tactic" v (f ()) evar
    with Failure s -> warn s v [] (Evar.unsafe_of_int 0)
  in snd (List.hd (f ()))

let replace_name pat str target =
  let open Str in
  let pat = string_of_ppcmds pat in
  let str = string_of_ppcmds str in
  let target = string_of_ppcmds target in
  let code = "\\(^\\|[]\n -/:-@[-^`{-~.()]\\|^\\|$\\)" in
  let pat = global_replace (regexp "^(\\(.*\\))$") "\\1" pat in
  let pat = global_replace (regexp "\\([][$^.*+?\\\\]\\)") "\\\\\\1" pat in
  let pat = code ^ "\\(" ^ global_replace (regexp " \\|\n") "[ \\|\n]" pat ^ "\\)" ^ code in
  let str = ("\\1"^str^"\\3") in
  let reg = (regexp pat) in
  let rec repall s =
    try ignore (search_forward reg s 0); repall (global_replace reg str s)
    with Not_found -> Pp.str s
  in
  repall target

let pr_just tac hyps env =
  let com = Ppvernac.pr_vernac_body tac in
  let com = List.fold_left (fun com (oldn,newn) -> replace_name (Id.print oldn) (Id.print newn) com) com env.rename in
  let hyps = List.map (fun v -> List.fold_left (fun v (oldn,newn) -> replace_name (Id.print oldn) (Id.print newn) v) v env.rename) hyps in
  let hyps = CList.uniquize hyps in
  let by =
    if hyps = [] then mt () else
      str "by " ++ (if List.length hyps > 5 then str "*" else h 0 (prlist_with_sep pr_comma (fun x->x) hyps)) ++ spc ()
  in
  h 0 (spc () ++ by ++ str "using " ++ com)

let pr_instr root leaf =
  match root, leaf with
  | true, true -> str "thus "
  | true, false -> str "hence "
  | false, true -> str "have "
  | false, false -> str "then "

let pr_simple root leaf ?name env tac vars typ =
  hv 2 (pr_instr root leaf ++ pr_name_opt name ++ typ ++ pr_just tac vars env ++ str ".")

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

let wrap_claim root leaf ?name typ body =
  if leaf && not (Option.has_some name) then body root name else
    hv 2 (str "claim " ++ pr_name_opt name ++ typ ++ str "." ++ fnl () ++
          body true None) ++ fnl () ++ str "end claim." ++
    if root then fnl () ++ str "hence thesis." else mt ()

let pr_value env evmap term =
  let ty = Typing.e_type_of env.env evmap term in
  let ty_of_ty = Typing.e_type_of env.env evmap ty in
  let prop = Term.is_Prop ty_of_ty in
  let x = ref None in
  let open Constr in
  let pick _ r n =
    let t = Vars.lift n (RelDec.get_type r) in
    if equal ty t then
      x := Some (RelDec.get_name r);
    n-1
  in
  if prop then ignore (Environ.fold_rel_context pick env.env ~init:(Environ.nb_rel env.env));
  if Option.has_some !x then Some (pr_name (Option.get !x)) else
  let open Constr in
  match kind term with
  | Rel _ | Var _ | Const _ | Construct _ | Ind _ | Sort _ -> Some (pr_constr env evmap term)
  (* | App _ | Lambda _ when n>0 -> *)
  | App _  | Lambda _ | Cast _ | Prod _ -> (* Evarが含まれていると危険 *)
    if (Term.is_Set ty_of_ty || Term.is_Type ty_of_ty) && not (search_evar term)
    then Some (pr_constr env evmap term)
    else None
  | _ -> None

(* TODO:適度な空行 *)
let rec pr_term_body root leaf ?name env evmap rest term =
  let ty_of_ty = Typing.e_type_of env.env evmap (Typing.e_type_of env.env evmap term) in
  if (Term.is_Set ty_of_ty || Term.is_Type ty_of_ty) && not (search_evar term) then
    let (n,env) = match name with Some (Name n) -> (n,env) | _ -> new_name env in
    str "define " ++ Id.print n ++ str " as " ++ pr_constr env evmap term ++ str "."
  else
  let open Term in
  match kind_of_term term with
  | LetIn (n,b,t,c) ->
    let (Name hname,new_env) = push_rel n ~body:b t env in
    let def = pr_term_body false true ~name:(Name hname) {env with avoid=hname::env.avoid} evmap rest b in
    let body = pr_term_body root leaf ?name new_env evmap rest c in
    def ++ fnl () ++ body
  | Lambda _ -> pr_lambda root leaf ?name env evmap rest term
  | Evar _ -> begin try
        let f = List.assoc (fst (destEvar term)) rest in
        f root leaf name env
      with Not_found -> str "(* write your proof *)" end
  | App (f,a) -> pr_app root leaf ?name env rest evmap (f,a)
  | Cast (c,_,t) -> pr_term_body root leaf ?name env evmap rest c
  | Case (ci,t,c,bs) -> pr_case root leaf ?name env evmap rest (ci,t,c,bs)
  | Rel _ | Var _ | Const _ | Construct _ ->
    if not root then mt () else
    let i = match name with
      | None -> str "thus"
      | Some n -> str "have " ++ pr_name_opt name
    in
    i ++ str " thesis by " ++ pr_constr env evmap term ++ str "."
  | Prod _ | Sort _ | Meta _ | Fix _ | CoFix _ | Proj _ | Ind _ -> str "(* not supported *)"

and pr_lambda root leaf ?name env evmap rest term =
  let typ = pr_type env evmap term in
  (* decompose_lam_nにすべき？ *)
  let (args,c) = Term.decompose_lam term in
  let args = List.rev args in
  let iter (s,env) (n,t) =
    let (id,newe) = push_rel n t env in
    let c = if s = mt () then mt () else pr_comma () in
    let d = pr_name id ++ str ":" ++ pr_constr env evmap t in
    (s ++ c ++ d, newe)
  in
  let (decls, new_env) = List.fold_left iter (mt (), env) args in
  let body root name =
    h 2 (str "let " ++ decls ++ str ".") ++ fnl () ++
    pr_term_body root true ?name new_env evmap rest c
  in
  wrap_claim root leaf ?name typ body

and pr_app root leaf ?name env rest evmap (f,a) =
  let args = (f :: Array.to_list a) in
  let args_v = List.map (pr_value env evmap) args in
  let hyps = List.fold_left2 (fun a x y -> if Option.has_some y then a else x::a) [] args args_v in
  let hyps = List.rev hyps in
  let (names,env) = List.fold_left (fun (ns,e) _ ->let (n,e) = new_name ~term:(Term.mkApp (f,a),evmap) e in n::ns,e) ([],env) hyps in
  let names = List.rev names in
  let pr_branch a t n = a ++ pr_term_body false false ~name:(Name n) env evmap rest t ++ fnl () in
  let branches = List.fold_left2 pr_branch (mt ()) hyps names in
  let marge =
    (* TODO:implicitnessをちゃんとする *)
    let args_v = match List.hd (args_v) with
      | Some x when String.get (string_of_ppcmds x) 0 <> '@' -> (Some (str "@" ++ x))::(List.tl args_v)
      | _ -> args_v
    in
    let f (s,i) = function Some x -> x::s,i | None -> Id.print (List.nth names i)::s, i+1 in
    List.rev (fst (List.fold_left f ([],0) args_v))
  in
  let just = str " by (" ++ prlist_with_sep (fun _->str " ") (fun x->x) marge ++ str ")" in
  let typ = pr_type env evmap (Constr.mkApp (f,a)) in
  let body root name = branches ++ hv 2 (pr_instr root (leaf || hyps=[]) ++ pr_name_opt name ++ typ ++ just ++ str ".") in
  if hyps = [] || (List.length hyps = 1 && root) then body root name else wrap_claim root leaf ?name typ body

and pr_case root leaf ?name env evmap rest (ci,t,c,bs) =
  let ind = let (mi,i) = ci.ci_ind in (Environ.lookup_mind mi env.env).mind_packets.(i) in
  let remove_lam n c =
    let rec f n c a e =
      if n=0 then a,e,c else
      match Constr.kind c with
      | Lambda (x,t,c) ->
        let (newx,newe) = push_rel x t e in
        f (n-1) c (newx::a) newe
      | _ -> a,e,c
    in f n c [] env
  in
  let pr_br n c =
    let con = Name ind.mind_consnames.(n) in
    let (args,env,br) = remove_lam ind.mind_consnrealargs.(n) c in
    let args = List.rev args in
    let body = pr_term_body true true env evmap rest br in
    hv 2 (str "suppose it is (" ++
          prlist_with_sep (fun _ -> str " ") pr_name (con::args) ++
          str ")." ++ fnl () ++ body) ++ fnl ()
  in
  let body _ _ =
    str "per cases on " ++ pr_constr env evmap c ++ str "." ++ fnl () ++
    prvecti_with_sep mt pr_br bs ++ str "end cases."
  in
  let typ = pr_type env evmap (Constr.mkCase (ci,t,c,bs)) in
  wrap_claim root leaf ?name typ body

let rec pr_tree root leaf ?name env = function
  | Proof (p,l,false) -> pr_term root leaf ?name env p l
  | Proof (p,l,true) when List.length l <= 1 -> pr_path root leaf ?name env p l
  | Proof (p,l,true) -> pr_branch root ?name leaf env p l
  | Warn (s,l) -> List.fold_left (fun s (_,x) -> s ++ pr_tree root leaf ?name env x) s l

and pr_term root leaf ?name env (v,diff,(_,evmap)) l =
  try pr_ind root leaf ?name env diff evmap l v with _ ->
    let f t root leaf name env = pr_tree root leaf ?name env t in
    let rest = List.map (fun (e,t) -> (e,f t)) l in
    pr_term_body root leaf ?name env evmap rest diff

and pr_term_simpl root leaf ?name env evmap l diff =
  let f t root leaf name env = pr_tree root leaf ?name env t in
  let rest = List.map (fun (e,t) -> (e,f t)) l in
  pr_term_body root leaf ?name env evmap rest diff

and pr_path root leaf ?name env (v,diff,(g,e)) next =
  let (vars,envs) = find_vars env diff in
  let after_env = match next with [e,_] -> List.assoc e envs | _ -> env in
  let next_var = match next with
    | [_,Proof ((_,diff,(_,e)),[],_)] -> pr_value after_env e diff
    | _ -> None
  in
  let open Evd in
  let typ = pr_type env e diff in
  match next_var, next with
  | Some var, _ ->
    pr_simple root true ?name env v (var::vars) typ
  | None, [] ->
    pr_simple root true ?name env v vars typ
  | None, (_,next)::_ ->
    let body root name =
      pr_tree false false after_env next ++ fnl () ++
      pr_simple root false ?name env v vars typ
    in
    wrap_claim root leaf ?name typ body

and pr_branch root leaf ?name env (v,diff,(g,e)) l =
  let (vars,envs) = find_vars env diff in
  let pr_br (s,a,l) (evar,b) =
    match b with
    | Proof ((_,d,(_,em)),_,_) ->
      let env = let e = List.assoc evar envs in {e with avoid = a@e.avoid} in
      let (name,newe) = new_name ~term:(d,em) env in
      let next_var = pr_value newe em d in
      if Option.has_some next_var then s,a,(Option.get next_var)::l else
      let body = s ++ pr_tree false false ~name:(Name name) newe b ++ fnl () in
      body,name::a,(Id.print name)::l
    | _ ->
      let (name,newe) = new_name {env with avoid = a@env.avoid} in
      pr_tree root leaf ~name:(Name name) env b,name::a,l
  in
  let (branches,_,vs) = List.fold_left pr_br (mt (), [], []) l in
  let vars = vars @ (List.rev vs) in
  let typ = pr_type env e diff in
  let body root name =
    branches ++ hv 2 (pr_instr root leaf ++ pr_name_opt name ++ typ ++ pr_just v vars env ++ str ".")
  in
  wrap_claim root leaf ?name typ body

and pr_ind root leaf ?name env diff evmap l v =
  let open Term in
  let open Pcoq in
  let open Str in
  (* TODO:セミコロンでつないでいる場合にも対応すべき？ *)
  let regvar = regexp "^ *(induction +\\(.*\\)) *$" in
  let com = string_of_ppcmds (Ppvernac.pr_vernac_body v) in
  let var = ignore (string_match regvar com 0); matched_group 1 com in
  let (f,args) = destApp diff in
  let (c,_) = destConst f in
  let name = Constant.to_string c in
  let regind = regexp "^\\(.+\\)_\\(ind\\|rec\\|rect\\)$" in
  if string_match regind name 0 = false then failwith "" else
  (* *_indの第1（ではないかもしれない）引数から抜くべき？ *)
  let typ_expr = parse_string Constr.constr (matched_group 1 name) in
  let (_,typ) = Constrintern.interp_open_constr env.env !evmap typ_expr in
  let (_,ind) = Inductive.lookup_mind_specif env.env (fst (destInd typ)) in
  let brs = Array.sub args (1 + ind.mind_nrealargs) (Array.length ind.mind_consnames) in
  (* caseと共通化できるのでは？ *)
  let pr_branch i s b =
    let (args,c) = decompose_lam_n ind.mind_consnrealargs.(i) b in
    let f (l,e) (n,t) = let (newn,newe) = push_rel n t e in newn::l, newe in
    let (args,newe) = List.fold_left f ([],env) args in
    let (hyps,c) = decompose_lam_n ind.mind_consnrealargs.(i) c in
    let f (l,e,s) (n,t) =
      let (newn,newe) = push_rel n t e in
      let h = str " and " ++ pr_name n ++ str ":" ++ pr_constr e evmap t in
      newn::l, newe, h
    in
    let (_,newe,hyps) = List.fold_left f ([],newe,mt ()) hyps in
    s ++ fnl () ++
    hv 2 (str "suppose it is (" ++ Id.print ind.mind_consnames.(i) ++ str " " ++
          prlist_with_sep (fun _ -> str " ") pr_name (List.rev args) ++ str ")" ++
          hyps ++ str "." ++ fnl () ++
          pr_term_simpl true leaf newe evmap [List.nth l i] c)
  in
  str "per induction on " ++ str var ++ str "." ++
  CArray.fold_left_i pr_branch (mt ()) brs ++ fnl () ++
  str "end induction."

(* TODO:ローカル環境を持ってくる *)
let init_env p =
  reset_level ();
  let (g,_,_,_,e) = Proof.proof p in
  let env82 = Goal.V82.env e (List.hd g) in
  let f _ d e =
    let n = NamedDec.get_id d in
    let t = NamedDec.get_type d in
    Environ.push_rel (RelDec.LocalAssum (Name n,t)) e
  in
  let env = Environ.fold_named_context f env82 ~init:env82 in
  {env = env; rename = []; avoid = []}

let header_and_footer p body =
  let (g,_,_,_,sigma) = Proof.proof p in
  let (g,sigma) = Goal.V82.nf_evar sigma (List.hd g) in
  let env = Goal.V82.env sigma g in
  let concl = Printer.pr_goal_concl_style_env env sigma (Goal.V82.concl sigma g) in
  let pr_hyp env decl (hyps, lets) =
    let open Context.Named.Declaration in
    let id = Id.print (get_id decl) in
    let typ = Printer.pr_constr_env env sigma (get_type decl) in
    hyps ++ str "forall " ++ id ++ str ":" ++ typ ++ str ", ",
    lets ++ str "let " ++ id ++ str ":" ++ typ ++ str "." ++ fnl ()
  in
  let (hyps,lets) = Environ.fold_named_context pr_hyp ~init:(mt (), mt ()) env in
  fnl () ++ str "Goal " ++ hyps ++ concl ++ str "." ++ fnl () ++
  hv 2 (str "proof." ++ fnl () ++ lets ++ body) ++ fnl () ++ str "end proof." ++ fnl () ++ str "Qed." ++ fnl ()

let pr_tree p t = header_and_footer p (pr_tree true true (init_env p) t)

let pr_term_all p1 p2 =
  let (g,_,_,_,e) = Proof.proof p1 in
  let (_,diff) = diff_proof (List.hd g) p1 p2 in
  header_and_footer p1 (pr_term_simpl true true (init_env p1) (ref e) [] diff)