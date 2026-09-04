(* P2 harness minimisation of seed 122, depth 3, as OCaml.
   A top-level `try` around a `match_with` whose body raises: the CPS transform wraps the
   top-level call in caml_callback, which resets caml_exn_stack.  Does the outer trap still
   catch?  ocamlrun says 18; this asks node. *)
exception E of int

type _ Effect.t += Ping : int Effect.t

let () =
  let v =
    try
      Effect.Deep.match_with (fun () -> raise (E 103)) ()
        { retc = (fun (x : int) -> x)
        ; exnc = (fun e -> raise e)
        ; effc = (fun (type a) (_ : a Effect.t) -> None) }
    with E _ -> 18
  in
  print_string (string_of_int v); print_newline ()
