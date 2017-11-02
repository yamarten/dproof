open Constr
open Names
open Pp

type p_or_w = Proof of Proof.proof * Vernacexpr.vernac_expr * Proof.proof | Warn of std_ppcmds
type prftree = End | Path of p_or_w * prftree | Branch of p_or_w * prftree list | Other of p_or_w
let warn s v = str "(* " ++ str s ++ str ": " ++ Ppvernac.pr_vernac v ++ str " *)"

let pr_constr (env,_,_) evar_map constr =
  Ppconstr.default_term_pr.pr_constr_expr (Constrextern.extern_constr false env evar_map constr)

let rec diff_term env t1 t2 =
  let f_array env l1 l2 = List.concat @@ Array.to_list @@ CArray.map2 (diff_term env) l1 l2 in
  let add e n t = Termops.push_rel_assum (n,t) e in
  if equal t1 t2 then [] else
  match kind t1, kind t2 with
  | Evar _, _ -> [ (t1,t2,env) ]
  | Cast (c1,_,t1), Cast (c2,_,t2) -> diff_term env c1 c2 @ diff_term env t1 t2
  | Prod (n,t1,b1), Prod (_,t2,b2) | Lambda (n,t1,b1), Lambda (_,t2,b2) -> diff_term env t1 t2 @ diff_term (add env n t1) b1 b2
  | LetIn (n,b1,t1,k1), LetIn (_,b2,t2,k2) -> diff_term env t1 t2 @ diff_term env b1 b2 @ diff_term (add env n t1) k1 k2
  | App (b1,l1), App (b2,l2) -> diff_term env b1 b2 @ f_array env l1 l2
  | Proj (_,t1), Proj (_,t2) -> diff_term env t1 t2
  | Case (_,p1,b1,bl1), Case (_,p2,b2,bl2) -> diff_term env p1 p2 @ diff_term env b1 b2 @ f_array env bl1 bl2
  | Fix (_,(ns,tl1,bl1)), Fix (_,(_,tl2,bl2)) | CoFix (_,(ns,tl1,bl1)), Fix (_,(_,tl2,bl2)) ->
    let env' = CArray.fold_left2 add env ns tl1 in
    f_array env tl1 tl2 @ f_array env' bl1 bl2
  | _ -> failwith ""

let diff_proof ?(env=Global.env ()) p1 p2 = List.concat @@ CList.map2 (diff_term env) (Proof.partial_proof p1) (Proof.partial_proof p2)

let find_vars c =
  let collect a c = match kind c with
    | Rel _ -> str "Rel"::a (* todo *)
    | Const (c,_) -> Label.print (Constant.label c)::a
    | _ -> str "else"::a (* todo *)
  in
  let a = List.concat @@ List.map (fun (_,x,_) -> (List.hd (collect [] x)) :: fold collect [] x) c in
  (*if a = [] then mt () else str "by " ++ prlist_with_sep pr_comma (fun x -> x) a ++ spc ()*)
  str "by * "
let rename avoid id =
  let rec f id = if Id.Set.mem id avoid then f (Nameops.lift_subscript id) else id in
  let ret = f id in
  ret, Id.Set.add ret avoid

let collect_id t =
  let rec f s t = match kind t with
    | Var i -> Id.Set.add i s
    | Prod (Name i,_,_) | Lambda (Name i,_,_) | LetIn (Name i,_,_,_) -> Id.Set.add i (fold f s t)
    | Const (c,_) -> Id.Set.add (Label.to_id (Constant.label c)) s
    | Ind ((i,_),_) | Construct (((i,_),_),_) -> Id.Set.add (Label.to_id (MutInd.label i)) s
    | Fix (_,(ns,_,_)) | CoFix (_,(ns,_,_)) -> Array.fold_left (fun s n -> match n with Anonymous->s | Name i -> Id.Set.add i s) (fold f s t) ns
    | _ -> fold f s t
  in
  f Id.Set.empty t

let env = ref []

let prftree s =
  let s = Stream.of_list s in
  let rec sublist l1 l2 = if l1=[] || l1=l2 then true else if l2=[] then false else sublist l1 (List.tl l2) in
  let sublist l1 l2 = if l1=[] then true else sublist (List.tl l1) l2 in
  let focus _ _ = false in (* TODO *)
  let rec setenv = function
    | Proof (_,_,p)::l -> env := Id.Set.elements (List.fold_left (fun s c -> Id.Set.union (collect_id c) s) (Id.Set.of_list !env) (Proof.partial_proof p))
    | _::l -> setenv l
    | _ -> ()
  in
  setenv (List.rev (Stream.npeek (1000) s));

  let rec f () = try(
    match Stream.next s with
    | Proof (p1,v,p2) ->
      let warntree m = Path (Warn (warn m v), f ()) in
      let (g1,b1,_,_,_) = Proof.proof p1 in
      let (g2,b2,_,_,_) = Proof.proof p2 in
      let n1 = List.length g1 in
      let n2 = List.length g2 in
      if focus g1 g2 then warntree "focus" else
      if focus g2 g1 then warntree "unfocus" else
      if n1 < n2 then
        if sublist g1 g2 then
          let rec fork n = if n>=0 then f ()::fork (n-1) else [] in
          Branch (Proof (p1,v,p2), fork (n2-n1))
        else warntree "subgoals increased"
      else
      if n1 = 0 then warntree "no goals" else
      if List.tl g1 = g2 then Path (Proof (p1,v,p2), End) else
      if List.tl g1 = List.tl g2 then Path (Proof (p1,v,p2), f ()) else
        warntree "unsupported"
    | Warn s -> Path (Warn s, f ()))
    with _ -> End
  in f ()

let pr_concl (g,e) (env,_,_) =
  let (g,e) = Goal.V82.nf_evar e (List.hd g)  in
  let concl = Goal.V82.concl e g in
  Printer.pr_goal_concl_style_env env e concl

(* あまりにもひどいので後でなんとかしよう *)
let eq_env (g1,e1) (g2,e2) =
  List.length g1 = 0 || List.length g2 = 0 ||
  Printer.pr_context_of (Goal.V82.env e1 (List.hd g1)) e1 = Printer.pr_context_of (Goal.V82.env e2 (List.hd g2)) e2

let replace_name pat str =
  Feedback.msg_debug (Pp.str (pat^"->"^str));
  let code = "\\(^\\|[]\n -/:-@[-^`{-~]\\)" in
  let pat = Str.global_replace (Str.regexp "^(\\(.*\\))$") "\\1" pat in
  let pat = Str.global_replace (Str.regexp "\\([][$^.*+?\\\\]\\)") "\\\\\\1" pat in
  let pat = code ^ "\\(" ^ Str.global_replace (Str.regexp " \\|\n") "[ \\|\n]" pat ^ "\\)" ^ code in
  let str = ("\\1"^str^"\\3") in
  let reg = (Str.regexp pat) in
  let rec repall s =
    try ignore (Str.search_forward reg s 0); repall (Str.global_replace reg str s)
    with Not_found -> s
  in
  List.map repall

(* (* from detyping.ml*)
   let evar_defs env evmap evk cl = Term.(
   let bound_to_itself_or_letin decl c =
    match decl with
    | Context.Named.Declaration.LocalDef _ -> true
    | Context.Named.Declaration.LocalAssum (id,_) ->
      try
        let rel = Environ.lookup_rel (destRel c) env in
        Context.Rel.Declaration.get_name rel = (Names.Name id)
      with Not_found -> isVarId id c
   in
   try
    let l = Evd.evar_instance_array bound_to_itself_or_letin (Evd.find evmap evk) cl in
    let fvs,rels = List.fold_left (fun (fvs,rels) (_,c) -> match kind_of_term c with Rel n -> (fvs,Int.Set.add n rels) | Var id -> (Id.Set.add id fvs,rels) | _ -> (fvs,rels)) (Id.Set.empty,Int.Set.empty) l in
    let l = Evd.evar_instance_array (fun d c ->(bound_to_itself_or_letin d c && not (isRel c && Int.Set.mem (destRel c) rels || isVar c && (Id.Set.mem (destVar c) fvs)))) (Evd.find evmap evk) cl in
    l
   with Not_found -> CArray.map_to_list (fun c -> (Id.of_string "__",c)) cl)

   let replace_with_evar env evmap (k,a) = function
   | Vernacexpr.VernacExtend (n,args) ->
    let args_str = List.map (fun a -> Pp.string_of_ppcmds (Pptactic.pr_raw_generic env a)) args in
    let rep = evar_defs env evmap k a in
    let new_args = List.fold_left (fun a (id,c) -> replace_name (Names.Id.to_string id) (string_of_ppcmds (pr_constr env evmap c)) a) args_str rep in
    let stream = Stream.of_string (String.concat " " new_args ^ ".") in
    begin match Pcoq.Gram.entry_parse Pcoq.main_entry (Pcoq.Gram.parsable stream) with
      | Some (_,v) -> v
      | None -> failwith "argument replacement faild" end
   | _ -> failwith "invalid command" *)

let pr_simple ?(first=false) env p1 p2 v =
  let (g,_,_,_,e) = Proof.proof p1 in
  let diff = diff_proof p1 p2 in
  let tac = if first then "have" else "then" in
  str tac ++ spc () ++ str "(" ++ pr_concl (g,e) env ++ str ")" ++ spc () ++
  find_vars diff ++
  str "using" ++ spc () ++ Ppvernac.pr_vernac_body v ++ str "." ++ fnl ()

(* TODO: Anonymous時の処理 *)
let pr_name = function
  | Name n -> Id.print n
  | Anonymous -> str "_"

let named_to_rel = Context.(function
  | Named.Declaration.LocalAssum (n,c) -> Rel.Declaration.LocalAssum (Name n,c)
  | Named.Declaration.LocalDef (n,c,t) -> Rel.Declaration.LocalDef (Name n,c,t))

let push_rel id typ (env,avoids,map) =
  (* TODO: typがenv中に存在するときの処理 *)
  let env = Termops.push_rel_assum (id,typ) env in
  let avoids = id::avoids in
  id, (env,avoids,map)

let pr_term env top p1 p2 rest =
  if diff_proof p1 p2 = [] then str "thus thesis." ++ rest env else
  let (e,_,_) = env in
  let (evar,diff,_) = List.hd (diff_proof ~env:e p1 p2) in
  let evmap = let (_,_,_,_,em) = Proof.proof p2 in ref em in
  let rec pr_term top env term names =
    let typ =
      let (e,_,_) = env in
      let t = Typing.e_type_of e evmap term in
      pr_constr env !evmap t
    in
    match kind term with
    | LetIn (n,b,t,c) ->
      let def = pr_term true env b names in
      let (id,new_env) = push_rel n t env in
      let body = pr_term false new_env c names in
      str "claim " ++ pr_name id ++ str ":" ++ typ ++ str "." ++ fnl () ++
      def ++ str "hence thesis." ++ fnl () ++ str "end claim." ++ fnl () ++
      body ++ fnl ()
    | Lambda (n,t,c) ->
      let (id,new_env) = push_rel n t env in
      let body =
        str "let " ++ pr_name id ++ str ":" ++ pr_constr env !evmap t ++ str "." ++ fnl () ++
        pr_term true new_env c names
      in
      if top then body else
        str "claim " ++ typ ++ str "." ++ fnl () ++
        body ++ str "hence thesis." ++ fnl ()++ str "end claim." ++ fnl ()
    | Evar _ ->
      str "claim " ++ typ ++ str "." ++ fnl () ++
      rest env ++ str "hence thesis." ++ fnl () ++ str "end claim." ++ fnl ()
    | App (f,a) ->
      let fs = pr_term top env f names in
      let pr_branch (a,n) t =
        let name = str "new_name" in
        a ++ pr_term top env t names, name::n
      in
      let (args,names) = Array.fold_left pr_branch (mt (), []) a in
      fs ++ args ++ str "have " ++ typ ++ str " by *." ++ fnl ()
    | Cast (c,_,t) -> pr_term top env c names
    | Case (ci,t,c,bs) ->
      let (e,_,_) = env in
      let ind = let (mi,i) = ci.ci_ind in (Environ.lookup_mind mi e).mind_packets.(i) in
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
        let body = pr_term true env br names in
        str "suppose it is (" ++
        prlist_with_sep spc pr_name (con::args) ++
        str ")." ++ fnl () ++ body ++ str "hence thesis." ++ fnl ()
      in
      str "claim " ++ typ ++ str "." ++ fnl () ++
      str "per cases on " ++ pr_constr env !evmap c ++ str "." ++ fnl () ++
      prvecti_with_sep mt pr_br bs ++
      str "end cases." ++ fnl () ++ str "end claim." ++ fnl ()
    | Rel _ | Var _ | Const _ | Construct _ -> mt ()
    | Prod _ | Sort _ | Meta _ | Fix _ | CoFix _ | Proj _ | Ind _ -> str "(* not supported *)"
  in pr_term top env diff []

let rec pr_tree env s = function
  | Path (Proof (p1,v,p2), next) ->
    let (g1,_,_,_,e1) = Proof.proof p1 in
    let (g2,_,_,_,e2) = Proof.proof p2 in
    if not (eq_env (g1,e1) (g2,e2)) then pr_term env (next=End) p1 p2 (fun e->pr_tree e (mt ()) next) ++ s else
    if List.tl g1 = g2 then pr_tree env (pr_simple ~first:true env p1 p2 v ++ s) next else
    if List.tl g1 = List.tl g2 then pr_tree env (pr_simple env p1 p2 v ++ s) next else
      warn "unsupported" v
  | Path (Warn m, next) -> m ++ fnl () ++ pr_tree env s next
  | Branch (p,l) -> pr_branch env p l ++ s
  | End -> s
  | _ -> s ++ str "(* todo *)"

and pr_branch env p l =
  let getp = function
    | Path (Proof (p,_,_), _) | Branch ((Proof (p,_,_)), _) -> let (g,_,_,_,e) = Proof.proof p in pr_concl (g,e) env
    | _ -> str "???"
  in
  let pr b =
    let id = str "new_name" in
    str "claim " ++ id ++ str":(" ++ getp b ++ str ")." ++ fnl () ++ pr_tree env (mt ()) b ++ str "hence thesis." ++ fnl () ++ str "end claim." ++ fnl ()
  in
  let join = match p with
    | Proof (p1,v,p2) ->
      let (g1,_,_,_,e1) = Proof.proof p1 in
      let (g2,_,_,_,e2) = Proof.proof p2 in
      if not (eq_env (g1,e1) (g2,e2)) then pr_term env false p1 p2 (fun _->mt ()) else
      let diff = diff_proof p1 p2 in
      str "have" ++ spc () ++ str "(" ++ pr_concl (g1,e1) env ++ str ")" ++ spc () ++
      find_vars diff ++
      str "using" ++ spc () ++ Ppvernac.pr_vernac_body v ++ str "." ++ fnl ()
    | Warn s -> s
  in
  List.fold_left (fun t b -> pr b ++ t) (mt ()) l ++ join

let init_env () = (Global.env (),[],[])

let pr_tree t = str "proof." ++ fnl () ++ pr_tree (init_env ()) (mt ()) t ++ str "hence thesis." ++fnl () ++ str "end proof."