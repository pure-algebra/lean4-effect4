(* Witness 01: two performs under one deep handler that continues each time.
   Transcribes `repeated` of effects5_capabilities.ml:20-23 (number_handler 21).
   Machine arms exercised: runstack, perform-with-parent, resume, child returns. *)
open Effect
open Effect.Deep
type _ Effect.t += Number : int Effect.t
let row s = print_string s; print_newline ()
let () =
  let r =
    try_with (fun () ->
      row "perform\tNumber";
      let left = perform Number in
      row (Printf.sprintf "got\t%d" left);
      row "perform\tNumber";
      let right = perform Number in
      row (Printf.sprintf "got\t%d" right);
      left + right) ()
      { effc = (fun (type a) (e : a Effect.t) ->
          match e with
          | Number -> Some (fun (k : (a, int) continuation) ->
              row "handled\tNumber";
              row "continue\t21";
              continue k 21)
          | _ -> None) }
  in
  row (Printf.sprintf "value\t%d" r)
