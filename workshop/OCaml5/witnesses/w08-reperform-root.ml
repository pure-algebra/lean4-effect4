(* Witness 08: an effect that reaches the root by `reperform`, not by `perform`.
   The one handler answers None, so `reperform eff k last_fiber` runs on a stack with
   no parent: interp.c:1374-1381 takes the continuation with caml_continuation_use and
   resumes it with a function that raises Unhandled, so the exception surfaces INSIDE
   the performing fiber and the fiber's own try/with catches it. The native route is
   amd64.S label 112, which switches back to the performer stack loaded from the
   continuation before raising. Contrast witness 04, where no continuation is taken. *)
open Effect
open Effect.Deep
type _ Effect.t += Number : int Effect.t
let row s = print_string s; print_newline ()
let () =
  let r =
    match_with (fun () ->
      (try
         row "perform\tNumber";
         ignore (perform Number);
         row "unreachable";
         0
       with Unhandled Number -> row "caught-in-fiber\tUnhandled"; 1)) ()
      { retc = (fun v -> row "retc"; v);
        exnc = (fun e -> row "exnc"; raise e);
        effc = (fun (type a) (_ : a Effect.t) -> row "forward\tNumber"; None) }
  in
  row (Printf.sprintf "value\t%d" r)
