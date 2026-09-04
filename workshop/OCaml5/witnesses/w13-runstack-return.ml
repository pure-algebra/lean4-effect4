(* Witness 13: the plain return and raise routes. Nothing performs, so the child stack
   completes (or raises past its last trap), is freed, and exactly one of
   handle_value / handle_exn runs on the parent (do_return, interp.c:575-594;
   raise_notrace, :980-1000; frame_runstack and fiber_exn_handler, amd64.S:1003-1024). *)
open Effect
open Effect.Deep
type _ Effect.t += Number : int Effect.t
exception Boom
let row s = print_string s; print_newline ()
let () =
  let a =
    match_with (fun () -> row "body\tvalue"; 7) ()
      { retc = (fun v -> row (Printf.sprintf "retc\t%d" v); v + v);
        exnc = (fun _ -> row "exnc"; 0);
        effc = (fun (type a) (_ : a Effect.t) -> None) } in
  row (Printf.sprintf "a\t%d" a);
  let b =
    match_with (fun () -> row "body\traise"; raise Boom) ()
      { retc = (fun v -> row "unreachable"; v);
        exnc = (function Boom -> row "exnc\tBoom"; 5 | e -> raise e);
        effc = (fun (type a) (_ : a Effect.t) -> None) } in
  row (Printf.sprintf "b\t%d" b);
  row (Printf.sprintf "value\t%d" (a + b))
