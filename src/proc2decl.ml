open Names
open Dutil
open Pp

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
let rec pr_term_body root leaf ?name ?typ env evmap rest term =
  let ty_of_ty = Typing.e_type_of env.env evmap (Typing.e_type_of env.env evmap term) in
  if (Term.is_Set ty_of_ty || Term.is_Type ty_of_ty) && not (search_evar term) then
    let (n,env) = match name with Some (Name n) -> (n,env) | _ -> new_name env in
    let ppterm = pr_constr env evmap term in
    begin if root
    then str "thus thesis by" ++ spc () ++ ppterm ++ str "."
    else str "define " ++ Id.print n ++ str " as" ++ spc () ++ ppterm ++ str "." end
  else
  let open Term in
  match kind_of_term term with
  | LetIn (n,b,t,c) ->
    let (Name hname,new_env) = push_rel n ~body:b t env in
    let def = pr_term_body false true ~name:(Name hname) ~typ:t {env with avoid=hname::env.avoid} evmap rest b in
    let body = pr_term_body root leaf ?name ?typ new_env evmap rest c in
    def ++ fnl () ++ body
  | Lambda _ -> pr_lambda root leaf ?name ?typ env evmap rest term
  | Evar _ -> begin try
    let f = List.assoc (fst (destEvar term)) rest in
    f root leaf name env
    with Not_found -> str "(* write your proof *)" end
  | App _ -> pr_app root leaf ?name ?typ env rest evmap term
  | Cast (c,_,typ) -> pr_term_body root leaf ?name ~typ env evmap rest c
  | Case (ci,t,c,bs) -> pr_case root leaf ?name env evmap rest (ci,t,c,bs)
  | Rel _ | Var _ | Const _ | Construct _ ->
    if not root && name = None then mt () else
    let i = match name with
      | None -> str "thus"
      | Some n -> str "have " ++ pr_name_opt name
    in
    i ++ str " " ++ pr_type ?typ env evmap term ++ str " by " ++ pr_constr env evmap term ++ str "."
  | Prod _ | Sort _ | Meta _ | Fix _ | CoFix _ | Proj _ | Ind _ -> str "(* not supported *)"

and pr_lambda root leaf ?name ?typ env evmap rest term =
  let typ = pr_type ?typ env evmap term in
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

and pr_app root leaf ?name ?typ env rest evmap diff =
  let open Term in
  let open List in
  try pr_ind root leaf ?name ?typ env rest evmap diff with _ ->
  let (f,a) = destApp diff in
  let simpl = Reduction.whd_betaiota env.env diff in
  if not (eq_constr diff simpl) && not (search_evar f) then pr_term_body root leaf ?name ?typ env evmap rest simpl else
  let args = (f :: Array.to_list a) in
  let args_v = map (pr_value env evmap) args in
  let hyps = fold_left2 (fun a x y -> if Option.has_some y then a else x::a) [] args args_v in
  let hyps = rev hyps in
  let (names,env) = fold_left (fun (ns,e) _ ->let (n,e) = new_name ~term:(mkApp (f,a),evmap) e in n::ns,e) ([],env) hyps in
  let names = rev names in
  let pr_branch a t n = a ++ pr_term_body false false ~name:(Name n) env evmap rest t ++ fnl () in
  let branches = fold_left2 pr_branch (mt ()) hyps names in
  let marge =
    (* TODO:implicitnessをちゃんとする *)
    let args_v = match hd (args_v) with
      | Some x when String.get (string_of_ppcmds x) 0 <> '@' -> (Some (str "@" ++ x))::(tl args_v)
      | _ -> args_v
    in
    let f (s,i) = function Some x -> x::s,i | None -> Id.print (nth names i)::s, i+1 in
    rev (fst (fold_left f ([],0) args_v))
  in
  let just = str " by (" ++ prlist_with_sep (fun _->str " ") (fun x->x) marge ++ str ")" in
  let typ = pr_type ?typ env evmap diff in
  let body root name = branches ++ hv 2 (pr_instr root (leaf || hyps=[]) ++ pr_name_opt name ++ typ ++ just ++ str ".") in
  if hyps = [] || (length hyps = 1 && root) then body root name else wrap_claim root leaf ?name typ body

and pr_ind root leaf ?name ?typ env rest evmap diff =
  let open Term in
  let open Pcoq in
  let open Str in
  let (f,args) = destApp diff in
  let (c,_) = destConst f in
  let tname = Constant.to_string c in
  let regind = regexp "^\\(.+\\)_\\(ind\\|rec\\|rect\\)$" in
  if string_match regind tname 0 = false then failwith "not induction" else
  (* *_indの第1（ではないかもしれない）引数から抜くべき？ *)
  let typ_expr = parse_string Constr.constr (matched_group 1 tname) in
  let (_,ttyp) = Constrintern.interp_open_constr env.env !evmap typ_expr in
  let (_,ind) = Inductive.lookup_mind_specif env.env (fst (destInd ttyp)) in
  let arity = Context.Rel.length ind.mind_arity_ctxt in
  if Array.length args <> 2 + arity + Array.length ind.mind_consnames then failwith "too many args" else
  let var = pr_constr env evmap (CArray.last args) in
  let brs = Array.sub args (1 + arity) (Array.length ind.mind_consnames) in
  let pr_branch i s b =
    let (args,c) = decompose_lam_n ind.mind_consnrealargs.(i) b in
    let f (l,e) (n,t) = let (newn,newe) = push_rel n t e in newn::l, newe in
    let (args,newe) = List.fold_left f ([],env) (List.rev args) in
    let countrec =
      let open Rtree in
      let cons = (snd (dest_node ind.mind_recargs)).(i) in
      Array.fold_left (fun i x -> match fst (dest_node x) with Declarations.Norec -> i | _ -> i+1) 0 (snd (dest_node cons))
    in
    let (hyps,c) = decompose_lam_n countrec c in
    let f (l,e,s) (n,t) =
      let (newn,newe) = push_rel n t e in
      let h = str " and " ++ pr_name n ++ str ":" ++ pr_constr e evmap t in
      newn::l, newe, h
    in
    let pat =
      let cons = Id.print ind.mind_consnames.(i) in
      if args = [] then cons else
      str "(" ++ cons ++ str " " ++ prlist_with_sep (fun _ -> str " ") pr_name (List.rev args) ++ str ")"
    in
    let (_,newe,hyps) = List.fold_left f ([],newe,mt ()) (List.rev hyps) in
    s ++ fnl () ++
    hv 2 (str "suppose it is " ++ pat ++ hyps ++ str "." ++ fnl () ++
          pr_term_body true true newe evmap rest c)
  in
  let typ = pr_type ?typ env evmap diff in
  let body _ _ =
    str "per induction on " ++ var ++ str "." ++
    CArray.fold_left_i pr_branch (mt ()) brs ++ fnl () ++
    str "end induction."
  in
  wrap_claim false root ?name typ body

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
  | Proof (p,l,false) -> let (_,d,(g,e)) = p in pr_term root leaf ?name env g e d l
  | Proof (p,l,true) when List.length l <= 1 -> pr_path root leaf ?name env p l
  | Proof (p,l,true) -> pr_branch root ?name leaf env p l
  | Warn (s,l) -> List.fold_left (fun s (_,x) -> s ++ pr_tree root leaf ?name env x) s l

and pr_term root leaf ?name env g evmap diff l =
  let f t root leaf name env = pr_tree root leaf ?name env t in
  let rest = List.map (fun (e,t) -> (e,f t)) l in
  let typ = concl env g !evmap in
  pr_term_body root leaf ?name ~typ env evmap rest diff

and pr_path root leaf ?name env (v,diff,(g,e)) next =
  let (vars,envs) = find_vars env diff in
  let after_env = match next with [e,_] -> List.assoc e envs | _ -> env in
  let next_var = match next with
    | [_,Proof ((_,diff,(_,e)),[],_)] -> pr_value after_env e diff
    | _ -> None
  in
  let open Evd in
  let typ = pr_constr env e (concl env g !e) in
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
    wrap_claim root true ?name typ body

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
  let typ = pr_constr env e (concl env g !e) in
  let body root name =
    branches ++ hv 2 (pr_instr root leaf ++ pr_name_opt name ++ typ ++ pr_just v vars env ++ str ".")
  in
  wrap_claim root leaf ?name typ body

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
  let diff = Reduction.nf_betaiota (Goal.V82.env e (List.hd g)) diff in
  header_and_footer p1 (pr_term true true (init_env p1) g (ref e) diff [])