open Names
open Pp

module RelDec = Context.Rel.Declaration
module NamedDec = Context.Named.Declaration

type env = {env:Environ.env; rename:(Id.t*Id.t) list; avoid:Id.t list}
type prfstep = Vernacexpr.vernac_expr * (Constr.t * Constr.t) option * (Goal.goal list * Evd.evar_map)
type prftree = End | Path of prfstep * prftree | Branch of prfstep * prftree list | Other of std_ppcmds * prftree
let warn s v = str "(* " ++ str s ++ str ": " ++ Ppvernac.pr_vernac v ++ str " *)"

let pr_constr env evmap c =
  Ppconstr.default_term_pr.pr_constr_expr (Constrextern.extern_constr false env.env evmap c)

let pr_type env evmap c = pr_constr env !evmap (Typing.e_type_of env.env evmap c)

let rec diff_term t1 t2 =
  let open Constr in
  let f_array l1 l2 = List.concat @@ Array.to_list @@ CArray.map2 diff_term l1 l2 in
  if equal t1 t2 then [] else
  match kind t1, kind t2 with
  | Evar e1, Evar e2 -> [None]
  | Evar _, _ -> [ Some (t1,t2) ]
  | Cast (c1,_,t1), Cast (c2,_,t2) -> diff_term c1 c2 @ diff_term t1 t2
  | Lambda (n,t1,b1), Lambda (_,t2,b2) -> diff_term t1 t2 @ diff_term b1 b2
  | LetIn (n,b1,t1,k1), LetIn (_,b2,t2,k2) -> diff_term t1 t2 @ diff_term b1 b2 @ diff_term k1 k2
  | App (b1,l1), App (b2,l2) -> diff_term b1 b2 @ f_array l1 l2
  | Proj (_,t1), Proj (_,t2) -> diff_term t1 t2
  | Case (_,p1,b1,bl1), Case (_,p2,b2,bl2) -> diff_term p1 p2 @ diff_term b1 b2 @ f_array bl1 bl2
  | Fix (_,(ns,tl1,bl1)), Fix (_,(_,tl2,bl2))
  | CoFix (_,(ns,tl1,bl1)), Fix (_,(_,tl2,bl2)) -> f_array tl1 tl2 @ f_array bl1 bl2
  | _ -> failwith "proof term changed"

let diff_proof p1 p2 =
  let evars = List.concat @@ CList.map2 (diff_term) (Proof.partial_proof p1) (Proof.partial_proof p2) in
  let changes = List.filter Option.has_some evars in
  let change_num = List.length changes in
  if change_num = 0 then None else
  if change_num > (if Option.has_some (List.hd evars) then 1 else 0) then failwith "tail of the goals changed" else
    List.hd changes

(* TODO: Anonymous時の処理 *)
let name_to_id = function
  | Name n -> n
  | Anonymous -> Id.of_string "_"

let pr_name n = Id.print (name_to_id n)

let pr_name_opt = function
  | Some n -> pr_name n ++ str ":"
  | None -> mt ()

(* TODO:newsをpr_termのものと合わせる（重複回避する） *)
let find_vars env c =
  let rec collect i temp (vars,news) c =
    let open Constr in
    match kind c with
    | Rel j ->
      if j <= i then vars,news else
      (pr_name (RelDec.get_name (Environ.lookup_rel (j-i) env)))::vars,news
    | Const (c,_) -> (Constant.print c)::vars,news
    | Var n -> (Id.print n)::vars,news
    | LetIn (n,c,t,b) -> collect (i+1) (n::temp) (collect i temp (vars,news) c) b
    | Lambda (n,t,c) | Prod (n,t,c) -> collect (i+1) (n::temp) (vars,news) c
    (* | Fix _ -> _ *)
    | Case (_,_,c,b) -> Array.fold_left (collect i temp) (collect i temp (vars,news) c) b
    | App (c,a) -> Array.fold_left (collect i temp) (collect i temp (vars,news) c) a
    | Cast (c,_,_) -> collect i temp (vars,news) c
    | Evar _ -> vars,(temp@news)
    | _ -> vars,news
  in
  let (vars,news) = collect 0 [] ([],[]) c in
  (CList.uniquize vars, CList.uniquize news)

let prftree stream =
  let s = Stream.of_list stream in
  let rec sublist l1 l2 = if l1=[] || l1=l2 then true else if l2=[] then false else sublist l1 (List.tl l2) in
  let sublist l1 l2 = if l1=[] then true else sublist (List.tl l1) l2 in
  let warn s v p = Other (warn s v, p) in
  let rec f () =
    let (p1,v,p2) = Stream.next s in
    let (g1,b1,_,_,_) = Proof.proof p1 in
    let (g2,b2,_,_,e) = Proof.proof p2 in
    let n1 = List.length g1 in
    let n2 = List.length g2 in
    try(
      let diff = diff_proof p1 p2 in
      if n1 = 0 then warn "no goals" v (f ()) else
      let step = (v, diff, (g1,e)) in
      if n1 < n2 then
        if sublist g1 g2 then
          let rec fork n = if n>=0 then f ()::fork (n-1) else [] in
          Branch (step, List.rev (fork (n2-n1)))
        else warn "subgoals increased" v (f ())
      else
      if List.tl g1 = g2 then Path (step, End) else
      if List.tl g1 = List.tl g2 then Path (step, f ()) else
        warn "unsupported" v (f ()))
    with _ -> warn "something happens" v End
  in f ()

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
    str "by " ++ h 0 (prlist_with_sep pr_comma (fun x->x) hyps) ++ spc ()
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

let push_rel name typ env =
  (* TODO: typがenv中に存在するときの処理 *)
  match name with
  | Anonymous -> name, {env with env=Termops.push_rel_assum (name,typ) env.env }
  | Name id ->
    let newid = Namegen.next_ident_away_in_goal id env.avoid in
    let newe = Termops.push_rel_assum (Name newid,typ) env.env in
    let newmap = if id <> newid then (id,newid)::env.rename else env.rename in
    let newa = newid::env.avoid in
    Name newid, {env = newe; rename = newmap; avoid = newa;}

let new_name env =
  (* TODO:型に応じた名前 *)
  let name = Namegen.next_ident_away_in_goal Namegen.default_prop_ident env.avoid in
  name, {env with avoid = name::env.avoid}

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
  | Rel _ | Var _ | Const _ | Construct _ | Ind _ | Sort _ -> Some (pr_constr env !evmap term)
  (* | App _ | Lambda _ when n>0 -> *)
  | App _  | Lambda _ | Cast _ | Prod _ -> (* Evarが含まれていると危険 *)
    if Term.is_Set ty_of_ty || Term.is_Type ty_of_ty
    then Some (pr_constr env !evmap term)
    else None
  | _ -> None

(* TODO:適度な空行 *)
let pr_term root leaf ?name env diff rest evmap =
  if diff = None then List.fold_left (fun s f -> f root leaf name env) (mt ()) rest else
  let rest = ref rest in
  let (evar,diff) = Option.get diff in
  let evmap = ref evmap in
  let rec pr_term root leaf ?name env term =
    let ty_of_ty = Typing.e_type_of env.env evmap (Typing.e_type_of env.env evmap term) in
    if Term.is_Set ty_of_ty || Term.is_Type ty_of_ty then
      str "define ___ as " ++ pr_constr env !evmap term ++ str "."
    else
    let open Constr in
    match kind term with
    | LetIn (n,b,t,c) ->
      let (hname,new_env) = push_rel n t env in
      let def = pr_term false true ~name:hname env b in
      let body = pr_term root leaf ?name new_env c in
      def ++ fnl () ++ body
    | Lambda _ ->
      let typ = pr_type env evmap term in
      (* decompose_lam_nにすべき？ *)
      let (args,c) = Term.decompose_lam term in
      let args = List.rev args in
      let iter (s,env) (n,t) =
        let (id,newe) = push_rel n t env in
        let c = if s = mt () then mt () else pr_comma () in
        let d = pr_name id ++ str ":" ++ pr_constr env !evmap t in
        (s ++ c ++ d, newe)
      in
      let (decls, new_env) = List.fold_left iter (mt (), env) args in
      let body root name =
        h 2 (str "let " ++ decls ++ str ".") ++ fnl () ++
        pr_term root true ?name new_env c
      in
      wrap_claim root leaf ?name typ body
    | Evar _ ->
      let f = List.hd !rest in
      rest := List.tl !rest;
      f root leaf name env
    | App (f,a) ->
      let args = (f :: Array.to_list a) in
      let args_v = List.map (pr_value env evmap) args in
      let hyps = List.fold_left2 (fun a x y -> if Option.has_some y then a else x::a) [] args args_v in
      let hyps = List.rev hyps in
      let (names,env) = List.fold_left (fun (ns,e) _ ->let (n,e) = new_name e in n::ns,e) ([],env) hyps in
      let names = List.rev names in
      let pr_branch a t n = a ++ pr_term false false ~name:(Name n) env t ++ fnl () in
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
      let typ = pr_type env evmap term in
      branches ++ hv 2 (pr_instr root leaf ++ pr_name_opt name ++ typ ++ just ++ str ".")
    | Cast (c,_,t) -> pr_term root leaf ?name env c
    | Case (ci,t,c,bs) ->
      let ind = let (mi,i) = ci.ci_ind in (Environ.lookup_mind mi env.env).mind_packets.(i) in
      let remove_lam n c =
        let rec f n c a e =
          if n=0 then a,e,c else
          match kind c with
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
        let body = pr_term true true env br in
        hv 2 (str "suppose it is (" ++
              prlist_with_sep (fun _ -> str " ") pr_name (con::args) ++
              str ")." ++ fnl () ++ body) ++ fnl ()
      in
      let body _ _ =
        str "per cases on " ++ pr_constr env !evmap c ++ str "." ++ fnl () ++
        prvecti_with_sep mt pr_br bs ++ str "end cases."
      in
      let typ = pr_type env evmap term in
      wrap_claim root leaf ?name typ body
    | Rel _ | Var _ | Const _ | Construct _ ->
      if root then
        let i = match name with
          | None -> str "thus"
          | Some n -> str "have " ++ pr_name_opt name
        in
        i ++ str " thesis by " ++ pr_constr env !evmap term ++ str "."
      else mt ()
    | Prod _ | Sort _ | Meta _ | Fix _ | CoFix _ | Proj _ | Ind _ -> str "(* not supported *)"
  in pr_term root leaf ?name env diff

let rec pr_tree root leaf ?name env = function
  | Path (p,n) -> pr_path root leaf ?name env p n
  | Branch (p,l) -> pr_branch root ?name leaf env p l
  | End -> mt ()
  | _ -> str "(* todo *)"

and pr_path root leaf ?name env (v,diff,(g,e)) next =
  match diff with
  | None -> warn "nothing happened" v ++ fnl () ++ pr_tree root leaf env next(* TODO:simpl対応 *)
  | Some (evar,diffterm) ->
    let (vars,news) = find_vars env.env diffterm in
    if news <> [] then pr_term root leaf env diff [fun root leaf name env -> pr_tree root leaf ?name env next] e else
    let next_var = match next with
      | Path ((_,Some (_,diff),(g,e)),End) -> pr_value env (ref e) diff
      | _ -> None
    in
    let typ = pr_type env (ref e) diffterm in
    begin match next_var, next=End with
      | Some var, leaf ->
        pr_simple root leaf ?name env v (var::vars) typ
      | None, true ->
        pr_simple root true ?name env v vars typ
      | None, false ->
        let body root name =
          pr_tree false false env next ++ fnl () ++
          pr_simple root false ?name env v vars typ
        in
        wrap_claim root leaf ?name typ body
    end

and pr_branch root leaf ?name env (v,diff,(g,e)) l =
  if diff = None then warn "nothing happened" v ++ fnl () else
  let (evar,diffterm) = Option.get diff in
  let (vars,news) = find_vars env.env diffterm in
  if news <> [] then pr_term root leaf env diff (List.map (fun b root leaf name env -> pr_tree root leaf ?name env b) l) e else
  let pr_br (s,e,l) b =
    let (name,newe) = new_name e in
    let now_avoid = name::env.avoid in
    match b with
    | Path ((_,Some (_,d),(_,em)),_) | Branch ((_,Some (_,d),(_,em)),_) ->
      let next_var = pr_value env (ref em) d in
      if Option.has_some next_var then s,e, (Option.get next_var)::l else
      let body = s ++ pr_tree false false ~name:(Name name) {env with avoid = now_avoid} b ++ fnl () in
      body,newe,(Id.print name)::l
    | _ -> pr_tree root leaf env b,e,l
  in
  let (branches,env,vs) = List.fold_left pr_br (mt (), env, []) l in
  let vars = vars @ (List.rev vs) in
  let typ = pr_type env (ref e) diffterm in
  let body root name =
    branches ++ hv 2 (pr_instr root leaf ++ pr_name_opt name ++ typ ++ pr_just v vars env ++ str ".")
  in
  wrap_claim root leaf ?name typ body

let init_env () = {env = Global.env (); rename = []; avoid = []}

let pr_tree t =
  fnl () ++ v 2 (str "proof." ++ fnl () ++ pr_tree true true (init_env ()) t) ++
  fnl () ++ str "end proof."