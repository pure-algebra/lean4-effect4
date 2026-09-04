(* Witness 02: a handler that resumes the same continuation twice.
   Transcribes `double_resume` of effects5_capabilities.ml:24-33.
   Machine arms: caml_continuation_use_noexc on a taken handle answers the null stack
   (fiber.c:595-622), and do_resume on a null stack raises
   Continuation_already_resumed (interp.c:1291-1294, amd64.S:947-951). *)
open Effect
open Effect.Deep
type _ Effect.t += Number : int Effect.t
let row s = print_string s; print_newline ()
let () =
  let rejected =
    try_with (fun () ->
      row "perform\tNumber";
      ignore (perform Number);
      row "body";
      0) ()
      { effc = (fun (type a) (e : a Effect.t) ->
          match e with
          | Number -> Some (fun (k : (a, int) continuation) ->
              row "handled\tNumber";
              row "continue\t0";
              ignore (continue k 0);
              row "continue\t1";
              (try ignore (continue k 1); row "no-exn"; 0
               with Continuation_already_resumed ->
                 row "already-resumed"; 1))
          | _ -> None) }
  in
  row (Printf.sprintf "value\t%d" rejected)
