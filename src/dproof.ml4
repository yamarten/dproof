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

let pr_proofstep v =
  let now_proof () =
    let (g,_,_,_,e) = Proof.proof (Proof_global.give_me_the_proof ()) in
    (g,e)
  in
  let pr_concl (g,e) =
    let (g,e) = Goal.V82.nf_evar e (List.hd g)  in
    let env = Goal.V82.env e g in
    let concl = Goal.V82.concl e g in
    Printer.pr_goal_concl_style_env env e concl
  in
  match Vernac_classifier.classify_vernac (snd v) with
    | VtProofStep _,_ ->
      let p1 = now_proof () in
      let p2 = Vernacentries.interp v; now_proof () in
      (match List.length (fst p1), List.length (fst p2) with
        | n1, n2 when n1 < n2 -> str "(* subgoals increased *)"
        | n1, n2 ->
          pr_concl p1 ++ spc () ++ str "==(" ++ Ppvernac.pr_vernac_body (snd v) ++ str ")==>" ++ spc () ++
          if n1 = n2 then pr_concl p2 else str "(* proved *)")
    | _ -> str "(* not tactic *)"

let start () =
  let p = Proof_global.freeze `No in
  let s = States.freeze `Yes in
  let t = get_tokens () in
  let rec f () =
    match Pcoq.Gram.entry_parse Pcoq.main_entry t with
      | Some v -> Feedback.msg_info (pr_proofstep v); f ()
      | None -> ()
  in
  load (); f (); Proof_global.unfreeze p; States.unfreeze s


VERNAC COMMAND EXTEND DProof CLASSIFIED AS QUERY
  | [ "DProof" ]  -> [ record () ]
  | [ "DAbort"] -> [ stop (); reset () ]
  | [ "DEnd" ] -> [ stop (); start (); reset () ]
  | [ "DQed" ] -> [ stop (); start (); reset (); Vernacentries.interp (Loc.dummy_loc, VernacEndProof (Proved (Opaque None,None)))]
END
