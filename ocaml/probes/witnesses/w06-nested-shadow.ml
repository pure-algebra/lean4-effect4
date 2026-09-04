(* Witness 06: two handlers for the same effect; the innermost wins.
   Transcribes `nested` of effects5_capabilities.ml:66-68.
   Machine arm: perform switches to the immediate parent and runs the performing
   stack's own handle_effect there (interp.c:1352, `Stack_handle_effect(old_stack)`). *)
open Effect
open Effect.Deep
type _ Effect.t += Number : int Effect.t
let row s = print_string s; print_newline ()
let handler tag value main =
  try_with main ()
    { effc = (fun (type a) (e : a Effect.t) ->
        match e with
        | Number -> Some (fun (k : (a, int) continuation) ->
            row (Printf.sprintf "handled\t%s" tag);
            row (Printf.sprintf "continue\t%d" value);
            continue k value)
        | _ -> None) }
let () =
  let r =
    handler "outer" 10 (fun () ->
      let i = handler "inner" 20 (fun () ->
        row "perform\tNumber\tin-inner";
        perform Number) in
      row (Printf.sprintf "got\t%d" i);
      row "perform\tNumber\tin-outer";
      let o = perform Number in
      row (Printf.sprintf "got\t%d" o);
      i + o)
  in
  row (Printf.sprintf "value\t%d" r)
