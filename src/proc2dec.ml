open Constr
open Names
open Pp

type env = {env:Environ.env; rename:(name*name) list; avoid:Id.t list}
type prfstep = Vernacexpr.vernac_expr * (constr * constr) option * (Goal.goal list * Evd.evar_map)
type prftree = End | Path of prfstep * prftree | Branch of prfstep * prftree list | Other of std_ppcmds * prftree
let warn s v = str "(* " ++ str s ++ str ": " ++ Ppvernac.pr_vernac v ++ str " *)"

let pr_constr env evar_map constr =
  Ppconstr.default_term_pr.pr_constr_expr (Constrextern.extern_constr false env.env evar_map constr)

let rec diff_term t1 t2 =
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

let find_vars env =
  let rec collect env (vars,news) c = match kind c with
    | Rel i -> (Context.Rel.Declaration.get_name (Environ.lookup_rel i env))::vars,news
    | Const (c,_) -> (Name (Label.to_id (Constant.label c)))::vars,news
    | Var n -> (Name n)::vars,news
    | LetIn (n,c,t,b) -> collect (Termops.push_rel_assum (n,t) env) (collect env (vars,c::news) c) c
    | Lambda (n,t,c) | Prod (n,t,c) -> collect (Termops.push_rel_assum (n,t) env) (vars,c::news) c
    (* | Fix _ -> _ *)
    | Case (_,_,c,b) -> Array.fold_left (collect env) (collect env (vars,news) c) b
    | App (c,a) -> Array.fold_left (collect env) (collect env (vars,news) c) a
    | Cast (c,_,_) -> collect env (vars,news) c
    | _ -> vars,news
  in
  collect env ([],[])

let rename avoid id =
  let rec f id = if Id.Set.mem id avoid then f (Nameops.lift_subscript id) else id in
  let ret = f id in
  ret, Id.Set.add ret avoid

let pr_concl (g,e) env =
  let (g,e) = Goal.V82.nf_evar e (List.hd g)  in
  let concl = Goal.V82.concl e g in
  Printer.pr_goal_concl_style_env (env.env) e concl

let prftree s =
  let s = Stream.of_list s in
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
          Branch (step, fork (n2-n1))
        else warn "subgoals increased" v (f ())
      else
      if List.tl g1 = g2 then Path (step, End) else
      if List.tl g1 = List.tl g2 then Path (step, f ()) else
        warn "unsupported" v (f ()))
    with _ -> warn "something happens" v End
  in f ()

let replace_name pat str =
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

let pr_simple env v diff concl =
  str "have (" ++ pr_concl concl env ++ str ")" ++ spc () ++
  str "by * using " ++  Ppvernac.pr_vernac_body v ++ str "." ++ fnl ()

(* TODO: Anonymous時の処理 *)
let pr_name = function
  | Name n -> Id.print n
  | Anonymous -> str "_"

let named_to_rel = Context.(function
  | Named.Declaration.LocalAssum (n,c) -> Rel.Declaration.LocalAssum (Name n,c)
  | Named.Declaration.LocalDef (n,c,t) -> Rel.Declaration.LocalDef (Name n,c,t))

let push_rel name typ env =
  (* TODO: typがenv中に存在するときの処理 *)
  let newe = Termops.push_rel_assum (name,typ) env.env in
  match name with
  | Anonymous -> name, {env with env=newe}
  | Name id ->
    let newid = Namegen.next_ident_away_in_goal id env.avoid in
    let newa = newid::env.avoid in
    Name newid, {env with env = newe; avoid = newa}

let new_name env =
  (* TODO:型に応じた名前 *)
  let name = Namegen.next_ident_away_in_goal Namegen.default_prop_ident env.avoid in
  name, {env with avoid = name::env.avoid}

let wrap_claim top typ body =
  if top then body else
    hv 2 (str "claim " ++ typ ++ str "." ++ fnl () ++
          body ++ str "hence thesis.") ++ fnl () ++ str "end claim." ++ fnl ()

(* TODO:適度な空行 *)
let pr_term top env diff rest evmap =
  if diff = None then List.fold_left (fun s f -> f top env) (mt ()) rest else
  let rest = ref rest in
  let Some (evar,diff) = diff in
  let evmap = ref evmap in
  let rec pr_term top env term names =
    let typ =
      let t = Typing.e_type_of env.env evmap term in
      pr_constr env !evmap t
    in
    match kind term with
    | LetIn (n,b,t,c) ->
      let def = pr_term true env b names in
      let (id,new_env) = push_rel n t env in
      let body = pr_term false new_env c names in
      hv 2 (str "claim " ++ pr_name id ++ str ":" ++ pr_constr env !evmap t ++ str "." ++ fnl () ++
            def ++ str "hence thesis.") ++ fnl () ++
      str "end claim." ++ fnl () ++ body
    | Lambda (n,t,c) ->
      let (id,new_env) = push_rel n t env in
      let body =
        h 2 (str "let " ++ pr_name id ++ str ":" ++ pr_constr env !evmap t ++ str ".") ++ fnl () ++
        pr_term true new_env c names
      in
      wrap_claim top typ body
    | Evar _ ->
      let r = (List.hd !rest) top env in rest := List.tl !rest;
      wrap_claim top typ r
    | App (f,a) ->
      (* TODO:色々 *)
      let fs = pr_term top env f names in
      let pr_branch (a,n) t =
        let name = str "new_name" in
        a ++ pr_term top env t names, name::n
      in
      let (args,names) = Array.fold_left pr_branch (mt (), []) a in
      fs ++ args ++ str "have " ++ typ ++ str " by *." ++ fnl ()
    | Cast (c,_,t) -> pr_term top env c names
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
        let body = pr_term true env br names in
        hv 2 (str "suppose it is (" ++
              prlist_with_sep (fun _ -> str " ") pr_name (con::args) ++
              str ")." ++ fnl () ++ body ++ str "hence thesis.") ++ fnl ()
      in
      let body =
        str "per cases on " ++ pr_constr env !evmap c ++ str "." ++ fnl () ++
        prvecti_with_sep mt pr_br bs ++ str "end cases." ++ fnl ()
      in
      wrap_claim top typ body
    | Rel _ | Var _ | Const _ | Construct _ -> mt ()
    | Prod _ | Sort _ | Meta _ | Fix _ | CoFix _ | Proj _ | Ind _ -> str "(* not supported *)"
  in pr_term top env diff []

let rec pr_tree top env = function
  | Path (p,n) -> pr_path top env p n
  | Branch (p,l) -> pr_branch top env p l
  | End -> mt ()
  | _ -> str "(* todo *)"

and pr_path top env (v,diff,(g,e)) next =
  match diff with
  | None -> warn "nothing happened" v ++ fnl () ++ pr_tree top env next(* TODO:simpl対応 *)
  | Some (evar,diffterm) ->
    let (vars,news) = find_vars env.env diffterm in
    if news <> [] then pr_term top env diff [fun top env -> pr_tree top env next] e else
      pr_tree false env next ++ pr_simple env v diff (g,e)

and pr_branch top env (v,diff,(g,e)) l =
  if diff = None then warn "nothing happened" v ++ fnl () else
  let Some (evar,diffterm) = diff in
  let (vars,news) = find_vars env.env diffterm in
  if news <> [] then pr_term false env diff (List.map (fun b top env -> pr_tree top env b) l) e else
  let pr_br (s,e) b =
    (* TODO:証明しなくてよかったときの処理 *)
    let (name,newe) = new_name e in
    let now_avoid = name::env.avoid in
    match b with
    | Path ((_,_,c),_) | Branch ((_,_,c),_) ->
      let body =
        s ++
        hv 2 (str "claim " ++ Id.print name ++ str ":" ++ pr_concl c env ++ str "." ++ fnl () ++
              pr_tree true {env with avoid = now_avoid} b ++ str "hence thesis.") ++
        fnl () ++ str "end claim." ++ fnl ()
      in
      body,newe
    | _ -> pr_tree top env b,e
  in
  let (branches,env) = List.fold_left pr_br (mt (), env) l in
  let join =
    hv 2 (str "have " ++ pr_concl (g,e) env ++ spc () ++ str "by * using " ++ Ppvernac.pr_vernac_body v ++ str ".")
  in
  branches ++ join ++ fnl ()

let init_env () = {env = Global.env (); rename = []; avoid = []}

let pr_tree t =
  fnl () ++ v 2 (str "proof." ++ fnl () ++ pr_tree true (init_env ()) t ++ str "hence thesis.") ++
  fnl () ++ str "end proof."