open Pp

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

let rec diff_term t1 t2 =
  let f_array l1 l2 = List.concat @@ Array.to_list @@ CArray.map2 diff_term l1 l2 in
  if Constr.equal t1 t2 then [] else
  match Term.kind_of_term t1, Term.kind_of_term t2 with
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
    | Fix (_,(_,tl1,bl1)), Fix (_,(_,tl2,bl2)) -> f_array tl1 tl2 @ f_array bl1 bl2
    | _ -> failwith ""

(* trunk版
let rec diff_term evm1 evm2 t1 t2 =
  let f = diff_term evm1 evm2 in
  let f_array l1 l2 = List.concat @@ Array.to_list @@ Array.map2 f l1 l2 in (* Ocaml4.03以降 *)
  match EConstr.kind evm1 t1, EConstr.kind evm2 t2 with
    | t1, t2 when t1=t2 -> []
    | Evar (e1,l1), Evar (e2,l2) when e1=e2 -> f_array l1 l2
    | Evar _, _ -> [ (t1,t2) ]
    | Cast (c1,_,t1), Cast (c2,_,t2) -> f c1 c2 @ f t1 t2
    | Prod (_,t1,b1), Prod (_,t2,b2) -> f t1 t2 @ f b1 b2
    | Lambda (_,t1,b1), Lambda (_,t2,b2) -> f t1 t2 @ f b1 b2
    | LetIn (_,b1,t1,k1), LetIn (_,b2,t2,k2) -> f t1 t2 @ f b1 b2
    | App (b1,l1), App (b2,l2) -> f b1 b2 @ f_array l1 l2
    | Proj (_,t1), Proj (_,t2) -> f t1 t2
    | Case (_,p1,b1,bl1), Case (_,p2,b2,bl2) -> f p1 p2 @ f b1 b2 @ f_array bl1 bl2
    | Fix (_,(_,tl1,bl1)), Fix (_,(_,tl2,bl2)) -> f_array tl1 tl2 @ f_array bl1 bl2
    | Fix (_,(_,tl1,bl1)), Fix (_,(_,tl2,bl2)) -> f_array tl1 tl2 @ f_array bl1 bl2
    | _ -> failwith "unmatch" *)

let diff_proof p1 p2 = List.concat @@ CList.map2 diff_term (Proof.partial_proof p1) (Proof.partial_proof p2)
(* let diff_proof evm p1 p2 = diff_term (return p1) (return p2) (partial_proof p1) (partial_proof p2) *)

let find_vars c =
  let collect a c = match Constr.kind c with
    | Rel _ -> str "Rel"::a
    | Const (c,_) -> Names.Label.print (Names.Constant.label c)::a
    | _ -> str "else"::a
  in
  let a = List.concat @@ List.map (fun (_,x) -> (List.hd (collect [] x)) :: Constr.fold collect [] x) c in
  if a = [] then mt () else str "by " ++ prlist_with_sep pr_comma (fun x -> x) a ++ spc ()

type p_or_w = Proof of Proof.proof * Vernacexpr.vernac_expr * Proof.proof | Warn of std_ppcmds
let warn s v = str "(* " ++ str s ++ str ": " ++ Ppvernac.pr_vernac v ++ str " *)"

let pr_concl (g,e) =
  let (g,e) = Goal.V82.nf_evar e (List.hd g)  in
  let env = Goal.V82.env e g in
  let concl = Goal.V82.concl e g in
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
  str tac ++ spc () ++ pr_concl (g,e) ++ spc () ++
  find_vars diff ++
  str "using" ++ spc () ++ Ppvernac.pr_vernac_body v ++ str "." ++ fnl ()
  ++ str "(**" ++ Pp.prlist_with_sep pr_semicolon (fun x -> Printer.pr_constr (snd x)) diff ++ str "*)" ++ fnl ()

let pr_dproof ps =
  let rec pr_step n m =
    if n >= m then mt () else
    match ps.(n) with
      | Proof (p1,v,p2) ->
        let (g1,_,_,_,e1) = Proof.proof p1 in
        let (g2,_,_,_,e2) = Proof.proof p2 in
        if not @@ eq_env (g1,e1) (g2,e2) then warn "environment changed" v ++ fnl () ++ pr_step (n+1) m else
        let n1 = List.length g1 in
        let n2 = List.length g2 in
        if n1 < n2 then warn "subgoals increased" v ++ fnl () ++ pr_step (n+1) m else
        if n1 = 0 then warn "no goals" v ++ fnl () ++ pr_step (n+1) m else
        if List.tl g1 = g2 then pr_simple ~first:true p1 p2 v ++ pr_step (n+1) m else
        if List.tl g1 = List.tl g2 then pr_simple p1 p2 v ++ pr_step (n+1) m
        else warn "unsupported" v
      | Warn s -> s ++ fnl () ++ pr_step (n+1) m
  in Feedback.msg_info (fnl () ++ pr_step 1 (Array.length ps))

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
  Array.of_list (f [])

let start () =
  let p = Proof_global.freeze `No in
  let s = States.freeze `Yes in
  load ();
  pr_dproof @@ replay @@ get_tokens ();
  Proof_global.unfreeze p;
  States.unfreeze s


VERNAC COMMAND EXTEND DProof CLASSIFIED AS QUERY
  | [ "DProof" ]  -> [ record () ]
  | [ "DAbort"] -> [ stop (); reset () ]
  | [ "DEnd" ] -> [ stop (); start (); reset () ]
  | [ "DQed" ] -> [ stop (); start (); reset (); Vernacentries.interp (Loc.dummy_loc, VernacEndProof (Proved (Opaque None,None)))]
END
