(* Witness 12: caml_drop_continuation (fiber.c:659-664) on a parked continuation.
   The Stdlib does not export it, so the external is declared here exactly as the
   runtime spells it. Drop takes the continuation with caml_continuation_use, so a
   later continue raises Continuation_already_resumed, and frees the stack WITHOUT
   running any handler: no finally, no exnc, no retc.
   js_of_ocaml 5.7.1 does not implement this primitive; see the report. *)
open Effect
open Effect.Deep
type _ Effect.t += Stop : unit Effect.t
external drop_continuation : ('a, 'b) continuation -> unit = "caml_drop_continuation"
let row s = print_string s; print_newline ()
let parked : (unit, int) continuation option ref = ref None
let () =
  let status =
    match_with (fun () ->
      Fun.protect ~finally:(fun () -> row "finally") (fun () ->
        row "perform\tStop";
        perform Stop)) ()
      { retc = (fun () -> row "retc"; 0);
        exnc = (fun e -> row "exnc"; raise e);
        effc = (fun (type a) (e : a Effect.t) ->
          match e with
          | Stop -> Some (fun (k : (a, int) continuation) ->
              row "handled\tStop";
              parked := Some k;
              row "parked";
              2)
          | _ -> None) }
  in
  row (Printf.sprintf "status\t%d" status);
  (match !parked with
   | None -> row "missing"
   | Some k -> row "drop"; drop_continuation k);
  let after =
    match !parked with
    | None -> row "missing"; 9
    | Some k ->
      (try row "continue-after-drop"; continue k ()
       with Continuation_already_resumed -> row "already-resumed"; 1)
  in
  row (Printf.sprintf "after\t%d" after)
