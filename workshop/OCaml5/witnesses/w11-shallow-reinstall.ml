(* Witness 11: Shallow.continue_with re-installing a different handler.
   `caml_continuation_use_and_update_handler_noexc` (fiber.c:632-649) takes the stack and
   overwrites the handler triple of the OUTERMOST captured fiber, then resumes; so the
   second perform of the same fiber is seen by the new triple, and the fiber's eventual
   return runs the new retc. *)
open Effect
open Effect.Shallow
type _ Effect.t += Number : int Effect.t
let row s = print_string s; print_newline ()
let rec h2 : (int, int) handler =
  { retc = (fun v -> row (Printf.sprintf "retc2\t%d" v); v);
    exnc = (fun e -> raise e);
    effc = (fun (type a) (e : a Effect.t) ->
      match e with
      | Number -> Some (fun (k : (a, int) continuation) ->
          row "h2\tNumber";
          row "continue\t22";
          continue_with k 22 h2)
      | _ -> None) }
let h1 : (int, int) handler =
  { retc = (fun v -> row (Printf.sprintf "retc1\t%d" v); v);
    exnc = (fun e -> raise e);
    effc = (fun (type a) (e : a Effect.t) ->
      match e with
      | Number -> Some (fun (k : (a, int) continuation) ->
          row "h1\tNumber";
          row "continue\t20";
          continue_with k 20 h2)
      | _ -> None) }
let () =
  let k0 = fiber (fun () ->
    row "perform\tNumber\tfirst";
    let a = perform Number in
    row (Printf.sprintf "got\t%d" a);
    row "perform\tNumber\tsecond";
    let b = perform Number in
    row (Printf.sprintf "got\t%d" b);
    a + b) in
  let r = continue_with k0 () h1 in
  row (Printf.sprintf "value\t%d" r)
