open Pp
open Constr

let resize_buffer ibuf = let open Bytes in
  let nstr = create (2 * length ibuf.Coqloop.str + 1) in
  blit ibuf.Coqloop.str 0 nstr 0 (length ibuf.Coqloop.str);
  ibuf.Coqloop.str <- nstr

let top_stderr x = msg_with ~pp_tag:Ppstyle.pp_tag !Pp_control.err_ft x

let prompt_char ic ibuf count =
  Coqloop.(let bol = match ibuf.bols with
      | ll::_ -> Int.equal ibuf.len ll
      | [] -> Int.equal ibuf.len 0
     in
     if bol && not !Flags.print_emacs then top_stderr (str (ibuf.prompt()));
     try
       let c = input_char ic in
       if c == '\n' then ibuf.bols <- (ibuf.len+1) :: ibuf.bols;
       if ibuf.len == String.length ibuf.str then resize_buffer ibuf;
       ibuf.str.[ibuf.len] <- c;
       ibuf.len <- ibuf.len + 1;
       Some c
     with End_of_file ->
       None)

let vernaclog = ref []
let reset () = vernaclog := []
let rec_stream () =
  let rec next i =
    try let e = Stream.next (Stream.from (prompt_char stdin Coqloop.top_buffer)) in
      vernaclog := e::!vernaclog; Some e
    with Stream.Failure -> None in
  Stream.from next

let (save,load) =
  let p = ref (Proof_global.freeze `No) in
  let s = ref (States.freeze `Yes) in
  let save () = p := Proof_global.freeze `No; s := States.freeze `Yes in
  let load () = Proof_global.unfreeze !p; States.unfreeze !s in
  save, load
let record () = save (); Coqloop.top_buffer.tokens <- Pcoq.Gram.parsable (rec_stream ())


let get_tokens () =
  Pcoq.Gram.parsable (Stream.of_list (List.rev !vernaclog))

let stop () = Coqloop.top_buffer.tokens <- Pcoq.Gram.parsable (Stream.from (prompt_char stdin Coqloop.top_buffer))

let rec rel2var vs t =
    match Obj.magic t with
    |Rel i              -> begin match (List.nth vs (i-1)) with
        |Names.Name v    -> mkVar v
        |Names.Anonymous -> failwith "Anonymous : not supported"
      end
    |Var v              -> mkVar v
    |Meta v             -> mkMeta v
    |Evar (k,a)         -> mkEvar(k,(Array.map (rel2var vs) a))
    |Sort v             -> mkSort v
    |Cast (v,ck,tp)     -> mkCast(rel2var vs v,ck,rel2var vs tp)
    |Prod (v,t1,t2)     -> mkProd(v,rel2var vs t1, rel2var (v::vs) t2 )
    |Lambda (v,t1,t2)   -> mkLambda(v,rel2var (v::vs) t1, rel2var (v::vs) t2)
    |LetIn (v,t1,tp,t2) -> mkLetIn(v,rel2var vs t1,rel2var vs tp, rel2var (v::vs) t2 )
    |App (c,ca)         -> mkApp(rel2var ((Name (Obj.magic "dummy"))::vs) c,Array.map (rel2var ((Name (Obj.magic "dummy"))::vs)) ca)
    (*リストの長さを調整するためにダミーをひとつ追加しておく*)
    |Const pc           -> t
    |Ind pi             -> t
    |Construct pc       -> t
    |Case (ci,t1,t2,ca) -> mkCase(ci,rel2var vs t1,rel2var vs t2,Array.map (rel2var vs ) ca)
    |Fix (a,(n,tp,t1))  -> failwith "fix:not supported"
    |CoFix (a,(n,tp,t1))-> failwith "cofix:not supported"
    |Proj (p,v)         -> mkProj(p,rel2var vs t)

let rec diff_term t1 t2 =
  let f_array l1 l2 = List.concat @@ Array.to_list @@ CArray.map2 diff_term l1 l2 in
  if equal t1 t2 then [] else
    match kind t1, kind t2 with
    | Evar (e1,l1), Evar (e2,l2) when e1=e2 -> f_array l1 l2
    | Evar _, _ -> [ (t1,t2) ]
    | Cast (c1,_,t1), Cast (c2,_,t2) -> diff_term c1 c2 @ diff_term t1 t2
    | Prod (_,t1,b1), Prod (_,t2,b2) -> diff_term t1 t2 @ diff_term b1 b2
    | Lambda (_,t1,b1), Lambda (_,t2,b2) -> diff_term t1 t2 @ diff_term b1 b2
    | LetIn (_,b1,t1,k1), LetIn (_,b2,t2,k2) -> diff_term t1 t2 @ diff_term b1 b2
    | App (b1,l1), App (b2,l2) -> diff_term b1 b2 @ f_array l1 l2
    | Proj (_,t1), Proj (_,t2) -> diff_term t1 t2
    | Case (_,p1,b1,bl1), Case (_,p2,b2,bl2) -> diff_term p1 p2 @ diff_term b1 b2 @ f_array bl1 bl2
    | Fix (_,(_,tl1,bl1)), Fix (_,(_,tl2,bl2)) -> f_array tl1 tl2 @ f_array bl1 bl2
    | CoFix (_,(_,tl1,bl1)), Fix (_,(_,tl2,bl2)) -> f_array tl1 tl2 @ f_array bl1 bl2
    | _ -> failwith ""
let diff_term t1 t2 = diff_term (rel2var [] t1) (rel2var [] t2)

let diff_proof p1 p2 = List.concat @@ CList.map2 diff_term (Proof.partial_proof p1) (Proof.partial_proof p2)

let find_vars c =
  let collect a c = match kind c with
    | Rel _ -> str "Rel"::a (* todo *)
    | Const (c,_) -> Names.Label.print (Names.Constant.label c)::a
    | _ -> str "else"::a (* todo *)
  in
  let a = List.concat @@ List.map (fun (_,x) -> (List.hd (collect [] x)) :: fold collect [] x) c in
  (*if a = [] then mt () else str "by " ++ prlist_with_sep pr_comma (fun x -> x) a ++ spc ()*)
  str "by * "

type p_or_w = Proof of Proof.proof * Vernacexpr.vernac_expr * Proof.proof | Warn of std_ppcmds
type prftree = End | Path of p_or_w * prftree | Branch of p_or_w * prftree list | Other of p_or_w
let warn s v = str "(* " ++ str s ++ str ": " ++ Ppvernac.pr_vernac v ++ str " *)"

let rename avoid id =
  let rec f id = if Names.Id.Set.mem id avoid then f (Nameops.lift_subscript id) else id in
  let ret = f id in
  ret, Names.Id.Set.add ret avoid

let collect_id t = Names.(
    let f s t = match kind t with
      | Var i | Prod (Name i,_,_) | Lambda (Name i,_,_) | LetIn (Name i,_,_,_) -> Id.Set.add i s
      | Const (c,_) -> Id.Set.add (Label.to_id (Constant.label c)) s
      | Ind ((i,_),_) | Construct (((i,_),_),_) -> Id.Set.add (Label.to_id (MutInd.label i)) s
      | Fix (_,(ns,_,_)) | CoFix (_,(ns,_,_)) -> Array.fold_left (fun s n -> match n with Anonymous->s | Name i -> Id.Set.add i s) s ns
      | _ -> s
    in
    f (fold f Id.Set.empty t)) t

let prftree s =
  let s = Stream.of_list s in
  let rec sublist l1 l2 = if l1=[] || l1=l2 then true else if l2=[] then false else sublist l1 (List.tl l2) in
  let sublist l1 l2 = if l1=[] then true else sublist (List.tl l1) l2 in
  let focus _ _ = false in (* TODO *)

  let rec f () = try
      (match Stream.next s with
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

let pr_concl c (g,e) =
  let (g,e) = Goal.V82.nf_evar e (List.hd g)  in
  let env = Goal.V82.env e g in
  let concl = Goal.V82.concl e g in
  let rec remove_intros c e t =
    if c = 0 then (e,t) else match kind t with
      | Prod (n,typ,t) -> remove_intros (c-1) (Termops.push_rel_assum (n,typ) e) t
      | _ -> print_string "(* error: remove *)"; (e,t)
  in
  let (env,concl) = remove_intros c env concl in
  Printer.pr_goal_concl_style_env env e concl

(* あまりにもひどいので後でなんとかしよう *)
let eq_env (g1,e1) (g2,e2) =
  List.length g1 = 0 || List.length g2 = 0 ||
  Printer.pr_context_of (Goal.V82.env e1 (List.hd g1)) e1 = Printer.pr_context_of (Goal.V82.env e2 (List.hd g2)) e2

(*
[シンプルに変換できる場合]
フォ−カスしているサブゴールのみ変形し、分裂しておらず、環境の変化も無い場合

[頑張って変換する場合]
* 関数適用でサブゴールが増える場合
** 引数にそれぞれ名前をつけ、普通に証明
** 最後にbyして完成
* パターンマッチでサブゴールが増える場合
** case使う
** 分岐直後にセミコロンで繋がっていた場合が厄介
** 証明項全体に対する変換も考えるべきか
* rewiteやintroなど環境を書き換えている場合
** 証明項を見てlet等に置き換えるしかない?

[対応できない場合]
フォーカスしていないサブゴールが変化している場合（典型的にはコロンを伴うもの）
*)

let pr_simple ?(first=false) p1 p2 v =
  let (g,_,_,_,e) = Proof.proof p1 in
  let diff = diff_proof p1 p2 in
  let tac = if first then "have" else "then" in
  str tac ++ spc () ++ pr_concl 0 (g,e) ++ spc () ++
  find_vars diff ++
  str "using" ++ spc () ++ Ppvernac.pr_vernac_body v ++ str "." ++ fnl ()
(*  ++ str "(**" ++ Pp.prlist_with_sep pr_semicolon (fun x -> Printer.pr_constr (snd x)) diff ++ str "*)" ++ fnl () *)

let rec pr_tree s = function
  | Path (Proof (p1,v,p2), next) ->
    let (g1,_,_,_,e1) = Proof.proof p1 in
    let (g2,_,_,_,e2) = Proof.proof p2 in
    if not @@ eq_env (g1,e1) (g2,e2) then warn "environment changed" v ++ fnl () ++ pr_tree s next else
    if List.tl g1 = g2 then pr_tree (pr_simple ~first:true p1 p2 v ++ s) next else
    if List.tl g1 = List.tl g2 then pr_tree (pr_simple p1 p2 v ++ s) next else
      warn "unsupported" v
  | Path (Warn m, next) -> m ++ fnl () ++ pr_tree s next
  | Branch (p,l) -> pr_branch p l ++ s
  | End -> s ++ str "hence thesis." ++ fnl ()
  | _ -> s ++ str "(* todo *)"

and pr_branch p l =
  let pr b = str "claim H:P." ++ fnl () ++ pr_tree (mt ()) b ++ str "end claim." ++ fnl () in
  let join = match p with
    | Proof (p1,v,p2) ->
      let (g,_,_,_,e) = Proof.proof p1 in
      let diff = diff_proof p1 p2 in
      str "have" ++ spc () ++ pr_concl 0 (g,e) ++ spc () ++
      find_vars diff ++
      str "using" ++ spc () ++ Ppvernac.pr_vernac_body v ++ str "." ++ fnl ()
    | Warn s -> s
  in
  List.fold_left (fun t b -> pr b ++ t) (mt ()) l ++ fnl () ++ join ++ fnl () ++ str "hence thesis." ++ fnl ()

let pr_tree t = str "proof." ++ fnl () ++ pr_tree (mt ()) t ++ str "end proof."


let replay tokens =
  let play (l,v) = try begin
    match Vernac_classifier.classify_vernac v with
    | VtProofStep _, _ ->
      let p1 = Proof_global.give_me_the_proof () in
      let p2 = Vernacentries.interp (l,v); Proof_global.give_me_the_proof () in
      Proof (p1, v, p2)
    | _ -> Warn (warn "not tactic" v)
  end with _ -> Warn (warn "error" v)
  in
  let rec f l = match Pcoq.Gram.entry_parse Pcoq.main_entry tokens with
    | Some v -> f (play v::l)
    | None -> l
  in
  List.rev (List.tl (f []))

let start () =
  let p = Proof_global.freeze `No in
  let s = States.freeze `Yes in
  load ();
  Feedback.msg_notice (pr_tree (prftree (replay (get_tokens ()))) ++ fnl ());
  Proof_global.unfreeze p;
  States.unfreeze s

open Constrarg

VERNAC COMMAND EXTEND DProof CLASSIFIED AS QUERY
  | [ "DProof" ]  -> [ record () ]
  | [ "DAbort"] -> [ stop (); reset () ]
  | [ "DEnd" ] -> [ stop (); start (); reset () ]
  | [ "DQed" ] -> [ stop (); start (); reset (); Vernacentries.interp (Loc.dummy_loc, VernacEndProof (Proved (Opaque None,None)))]
END
