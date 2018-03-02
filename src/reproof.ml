open Pp
open Dutil

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
  in reset_level (); snd (List.hd (f ()))

let start () =
  let p2 = Proof_global.give_me_the_proof () in
  let p = Proof_global.freeze `No in
  let s = States.freeze `Yes in
  load ();
  let p1 = Proof_global.give_me_the_proof () in
  let out = match !file with None -> Feedback.msg_info ?loc:None | Some o -> (fun s -> output_string o (string_of_ppcmds s)) in
  begin
    if !term then out (Proc2decl.pr_term_all p1 p2) else
      out (Proc2decl.pr_tree p1 (prftree (replay (get_tokens ()))) ++ fnl ())
  end;
  Proof_global.unfreeze p; States.unfreeze s