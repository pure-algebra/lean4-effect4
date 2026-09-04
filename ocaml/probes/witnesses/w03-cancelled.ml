(* Witness 03: discontinue through Fun.protect ~finally, caught by exnc.
   Transcribes `cancelled` of effects5_capabilities.ml:36-49.
   Machine arms: resume with a raising function, the child stack raising past its
   last trap (interp.c:980-1000; amd64.S fiber_exn_handler, :1022-1024), handle_exn
   run on the parent. *)
open Effect
open Effect.Deep
type _ Effect.t += Stop : unit Effect.t
exception Cancelled
let row s = print_string s; print_newline ()
let () =
  let cancelled =
    match_with (fun () ->
      Fun.protect
        ~finally:(fun () -> row "finally\t2")
        (fun () ->
          row "cleanup\t1";
          row "perform\tStop";
          perform Stop;
          row "unreachable";
          99)) ()
      { retc = (fun _ -> row "retc"; 0);
        exnc = (function
          | Cancelled -> row "exnc\tCancelled"; 1
          | e -> raise e);
        effc = (fun (type a) (e : a Effect.t) ->
          match e with
          | Stop -> Some (fun (k : (a, int) continuation) ->
              row "handled\tStop";
              row "discontinue\tCancelled";
              discontinue k Cancelled)
          | _ -> None) }
  in
  row (Printf.sprintf "value\t%d" cancelled)
