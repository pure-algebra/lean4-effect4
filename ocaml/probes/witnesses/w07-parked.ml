(* Witness 07: the handler parks the continuation in a ref and returns a value; the
   fiber is discontinued much later, outside the handler.
   Transcribes `parked`/`after` of effects5_capabilities.ml:71-87.
   Machine arms: a captured stack survives the handler's own return to the parent (the
   value of handle_effect is the value of runstack), and a later resume sets the
   outermost captured stack's parent to whoever resumes (interp.c:1295-1296). *)
open Effect
open Effect.Deep
type _ Effect.t += Stop : unit Effect.t
exception Cancelled
let row s = print_string s; print_newline ()
let parked : (unit, int) continuation option ref = ref None
let () =
  let status =
    match_with (fun () ->
      Fun.protect ~finally:(fun () -> row "finally") (fun () ->
        row "perform\tStop";
        perform Stop)) ()
      { retc = (fun () -> row "retc"; 0);
        exnc = (function
          | Cancelled -> row "exnc\tCancelled"; 1
          | e -> raise e);
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
  let after =
    match !parked with
    | None -> row "missing"; 9
    | Some k -> row "discontinue\tCancelled"; discontinue k Cancelled
  in
  row (Printf.sprintf "after\t%d" after)
