open Pp
open Proc2dec

let resize_buffer ibuf = let open Bytes in
  let nstr = create (2 * length ibuf.Coqloop.str + 1) in
  blit ibuf.Coqloop.str 0 nstr 0 (length ibuf.Coqloop.str);
  ibuf.Coqloop.str <- nstr

let top_stderr x = msg_with ~pp_tag:Ppstyle.pp_tag !Pp_control.err_ft x

let prompt_char ic ibuf count = Coqloop.(
  let bol = match ibuf.bols with
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
  with End_of_file -> None)

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

let replay tokens =
  let play (l,v) =
    match Vernac_classifier.classify_vernac v with
    | VtProofStep _, _ ->
      let p1 = Proof_global.give_me_the_proof () in
      let p2 = Vernacentries.interp (l,v); Proof_global.give_me_the_proof () in
      [(p1, v, p2)]
    | _ -> Feedback.msg_notice (warn "not tactic, ignored" v); []
  in
  let rec f l = match Pcoq.Gram.entry_parse Pcoq.main_entry tokens with
    | Some v -> f (play v::l)
    | None -> l
  in
  List.rev (List.fold_left List.append [] (f []))

let term = ref false
let start () =
  let p2 = Proof_global.give_me_the_proof () in
  let p = Proof_global.freeze `No in
  let s = States.freeze `Yes in
  load ();
  let p1 = Proof_global.give_me_the_proof () in
  begin
    if !term then
      let (_,_,_,_,e) = Proof.proof p1 in
      let body = pr_term true true (init_env ()) (diff_proof p1 p2) [fun _ _ _->mt ()] e in
      Feedback.msg_info (fnl () ++ hv 2 (str "proof." ++ fnl () ++ body) ++ fnl () ++ str "end proof." ++ fnl ())
    else Feedback.msg_info (pr_tree (prftree (replay (get_tokens ()))) ++ fnl ())
  end;
  Proof_global.unfreeze p; States.unfreeze s

