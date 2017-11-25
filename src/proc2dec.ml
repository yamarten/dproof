open Constr
open Names
open Pp

type env = {env:Environ.env; rename:(Id.t*Id.t) list; avoid:Id.t list}
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

(* TODO: Anonymous時の処理 *)
let name_to_id = function
  | Name n -> n
  | Anonymous -> Id.of_string "_"

let pr_name n = Id.print (name_to_id n)

(* TODO:vars,newsをpr_termのものと合わせる（重複回避する） *)
(* TODO:Nameではなく名前空間を含んだものを返す *)
let find_vars env =
  let rec collect env (vars,news) c = match kind c with
    | Rel i -> (pr_name (Context.Rel.Declaration.get_name (Environ.lookup_rel i env)))::vars,news
    | Const (c,_) -> (Constant.print c)::vars,news
    | Var n -> (Id.print n)::vars,news
    | LetIn (n,c,t,b) -> collect (Termops.push_rel_assum (n,t) env) (collect env (vars,n::news) c) c
    | Lambda (n,t,c) | Prod (n,t,c) -> collect (Termops.push_rel_assum (n,t) env) (vars,n::news) c
    (* | Fix _ -> _ *)
    | Case (_,_,c,b) -> Array.fold_left (collect env) (collect env (vars,news) c) b
    | App (c,a) -> Array.fold_left (collect env) (collect env (vars,news) c) a
    | Cast (c,_,_) -> collect env (vars,news) c
    | _ -> vars,news
  in
  collect env ([],[])

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
          Branch (step, List.rev (fork (n2-n1)))
        else warn "subgoals increased" v (f ())
      else
      if List.tl g1 = g2 then Path (step, End) else
      if List.tl g1 = List.tl g2 then Path (step, f ()) else
        warn "unsupported" v (f ()))
    with _ -> warn "something happens" v End
  in f ()

let replace_name pat str s =
  let pat = string_of_ppcmds pat in
  let str = string_of_ppcmds str in
  let s = string_of_ppcmds s in
  let code = "\\(^\\|[]\n -/:-@[-^`{-~.]\\|^\\|$\\)" in
  let pat = Str.global_replace (Str.regexp "^(\\(.*\\))$") "\\1" pat in
  let pat = Str.global_replace (Str.regexp "\\([][$^.*+?\\\\]\\)") "\\\\\\1" pat in
  let pat = code ^ "\\(" ^ Str.global_replace (Str.regexp " \\|\n") "[ \\|\n]" pat ^ "\\)" ^ code in
  let str = ("\\1"^str^"\\3") in
  let reg = (Str.regexp pat) in
  let rec repall s =
    try ignore (Str.search_forward reg s 0); repall (Str.global_replace reg str s)
    with Not_found -> Pp.str s
  in
  repall s

let pr_just v vars env =
  let com = Ppvernac.pr_vernac_body v in
  let com = List.fold_left (fun com (oldn,newn) -> replace_name (Id.print oldn) (Id.print newn) com) com env.rename in
  let vars = List.map (fun v -> List.fold_left (fun v (oldn,newn) -> replace_name (Id.print oldn) (Id.print newn) v) v env.rename) vars in
  let vars = CList.uniquize vars in
  let by =
    if vars = [] then mt () else
    str "by " ++ h 0 (prlist_with_sep pr_comma (fun x->x) vars) ++ spc ()
  in
  h 0 (spc () ++ by ++ str "using " ++ com)

(* root,top *)
let pr_instr = function
  | true, true -> str "thus "
  | true, false -> str "hence "
  | false, true -> str "have "
  | false, false -> str "then "

let pr_simple root top env v vars typ =
  hv 2 (pr_instr (root,top) ++ typ ++ pr_just v vars env ++ str ".")

let named_to_rel = Context.(function
  | Named.Declaration.LocalAssum (n,c) -> Rel.Declaration.LocalAssum (Name n,c)
  | Named.Declaration.LocalDef (n,c,t) -> Rel.Declaration.LocalDef (Name n,c,t))

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

let wrap_claim root top ?name typ body =
  if top && not (Option.has_some name) then body root else
  let n = match name with Some (Name n) -> Id.print n ++ str ":" | _ -> mt () in
  hv 2 (str "claim " ++ n ++ typ ++ str "." ++ fnl () ++
        body true) ++ fnl () ++ str "end claim." ++
        if root then fnl () ++ str "hence thesis." else mt ()

let pr_value env evmap term =
  let ty = Typing.e_type_of env.env evmap term in
  let ty_of_ty = Typing.e_type_of env.env evmap ty in
  let prop = Term.is_Prop ty_of_ty in
  let x = ref None in
  if prop then ignore (Environ.fold_rel_context (fun _ r t -> if equal t (Context.Rel.Declaration.get_type r) then x := Some (Context.Rel.Declaration.get_name r); Termops.pop t) env.env ~init:ty);
  if Option.has_some !x then Some (pr_name (Option.get !x)) else
  match kind term with
  | Rel _ | Var _ | Const _ | Construct _ | Ind _ | Sort _ -> Some (pr_constr env !evmap term)
  (* | App _ | Lambda _ when n>0 -> *)
  | App _  | Lambda _ | Cast _ | Prod _ -> (* Evarが含まれていると危険 *)
    if Term.is_Set ty_of_ty || Term.is_Type ty_of_ty
    then Some (pr_constr env !evmap term)
    else None
  | _ -> None

(* TODO:適度な空行 *)
let pr_term root top env diff rest evmap =
  if diff = None then List.fold_left (fun s f -> f root top env) (mt ()) rest else
  let rest = ref rest in
  let Some (evar,diff) = diff in
  let evmap = ref evmap in
  let rec pr_term root top ?name env term =
    let ty_of_ty = Typing.e_type_of env.env evmap (Typing.e_type_of env.env evmap term) in
    if Term.is_Set ty_of_ty || Term.is_Type ty_of_ty then
      str "define ___ as " ++ pr_constr env !evmap term ++ str "."
    else
    let typ =
      let t = Typing.e_type_of env.env evmap term in
      pr_constr env !evmap t
    in
    match kind term with
    | LetIn (n,b,t,c) ->
      let def root = pr_term root true env b in
      let (hname,new_env) = push_rel n t env in
      let body = pr_term root top ?name new_env c in
      wrap_claim false false ~name:hname (pr_constr env !evmap t) def ++ fnl () ++ body
    | Lambda (n,t,c) ->
      (* TODO:複数のletをまとめる *)
      let (id,new_env) = push_rel n t env in
      let body root =
        h 2 (str "let " ++ pr_name id ++ str ":" ++ pr_constr env !evmap t ++ str ".") ++ fnl () ++
        pr_term root true new_env c
      in
      wrap_claim root top ?name typ body
    | Evar _ ->
      let f = List.hd !rest in
      let r root = f root true env in
      rest := List.tl !rest;
      wrap_claim root top ?name typ r
    | App (f,a) ->
      let args = (f :: Array.to_list a) in
      let args_v = List.map (pr_value env evmap) args in
      let justs = CList.map_filter (fun x->x) args_v in
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
      branches ++ hv 2 (pr_instr (root,top) ++ (match name with Some n -> pr_name n ++ str ":" | _ -> mt ()) ++ typ ++ just ++ str ".")
    | Cast (c,_,t) -> pr_term root top ?name env c
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
      let body _ =
        str "per cases on " ++ pr_constr env !evmap c ++ str "." ++ fnl () ++
        prvecti_with_sep mt pr_br bs ++ str "end cases."
      in
      wrap_claim root top ?name typ body
    | Rel _ | Var _ | Const _ | Construct _ ->
      if root then str "thus thesis by " ++ pr_constr env !evmap term ++ str "." else mt ()
    | Prod _ | Sort _ | Meta _ | Fix _ | CoFix _ | Proj _ | Ind _ -> str "(* not supported *)"
  in pr_term root top env diff

let rec pr_tree root top env = function
  | Path (p,n) -> pr_path root top env p n
  | Branch (p,l) -> pr_branch root top env p l
  | End -> mt ()
  | _ -> str "(* todo *)"

and pr_path root top env (v,diff,(g,e)) next =
  match diff with
  | None -> warn "nothing happened" v ++ fnl () ++ pr_tree root top env next(* TODO:simpl対応 *)
  | Some (evar,diffterm) ->
    let (vars,news) = find_vars env.env diffterm in
    if news <> [] then pr_term root top env diff [fun root top env -> pr_tree root top env next] e else
    let next_var = match next with
      | Path ((_,Some (_,diff),(g,e)),End) -> pr_value env (ref e) diff
      | _ -> None
    in
    let leaf = next = End in
    begin match next_var with
      | Some var ->
        pr_simple root leaf env v (var::vars) (pr_constr env e (Typing.unsafe_type_of env.env e diffterm))
      | None ->
        pr_tree false false env next ++ fnl () ++ pr_simple root leaf env v vars (pr_constr env e (Typing.unsafe_type_of env.env e diffterm))
    end

and pr_branch root top env (v,diff,(g,e)) l =
  if diff = None then warn "nothing happened" v ++ fnl () else
  let Some (evar,diffterm) = diff in
  let (vars,news) = find_vars env.env diffterm in
  if news <> [] then pr_term root top env diff (List.map (fun b root top env -> pr_tree root top env b) l) e else
  let pr_br (s,e,l) b =
    let (name,newe) = new_name e in
    let now_avoid = name::env.avoid in
    match b with
    | Path ((_,Some (_,d),(_,em)),_) | Branch ((_,Some (_,d),(_,em)),_) ->
      let next_var = pr_value env (ref em) d in
      if Option.has_some next_var then s,e, (Option.get next_var)::l else
      let body =
        s ++
        hv 2 (str "claim " ++ Id.print name ++ str ":" ++ (pr_constr env em (Typing.unsafe_type_of env.env em d)) ++ str "." ++ fnl () ++
              pr_tree true true {env with avoid = now_avoid} b) ++
        fnl () ++ str "end claim." ++ fnl ()
      in
      body,newe,(Id.print name)::l
    | _ -> pr_tree root top env b,e,l
  in
  let (branches,env,vs) = List.fold_left pr_br (mt (), env, []) l in
  let vars = vars @ (List.rev vs) in
  let join =
    hv 2 (str "have " ++ pr_constr env e (Typing.unsafe_type_of env.env e diffterm) ++ pr_just v vars env ++ str ".")
  in
  branches ++ join

let init_env () = {env = Global.env (); rename = []; avoid = []}

let pr_tree t =
  fnl () ++ v 2 (str "proof." ++ fnl () ++ pr_tree true true (init_env ()) t) ++
  fnl () ++ str "end proof."