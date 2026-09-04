(* Witness 09: traps survive capture. A try/with is pushed inside the fiber before the
   perform; the handler discontinues; the trap that was captured with the stack catches
   the exception and the fiber returns normally, so retc runs and exnc does not.
   PUSHTRAP pushes on the current stack and trap_sp_off is saved per stack at every
   switch (interp.c:930-938, :1283, :1329, :1369). *)
open Effect
open Effect.Deep
type _ Effect.t += Stop : unit Effect.t
exception Cancelled
let row s = print_string s; print_newline ()
let () =
  let r =
    match_with (fun () ->
      (try
         row "perform\tStop";
         perform Stop;
         row "unreachable";
         0
       with Cancelled -> row "caught-in-fiber\tCancelled"; 1)) ()
      { retc = (fun v -> row "retc"; v);
        exnc = (fun _ -> row "exnc"; 2);
        effc = (fun (type a) (e : a Effect.t) ->
          match e with
          | Stop -> Some (fun (k : (a, int) continuation) ->
              row "handled\tStop";
              row "discontinue\tCancelled";
              discontinue k Cancelled)
          | _ -> None) }
  in
  row (Printf.sprintf "value\t%d" r)
