(* Same as uc2 but with a reference to `Effect.Unhandled`, which forces `Stdlib__Effect` to be
   linked and its `Callback.register_exception` initialiser to run. *)
type _ Effect.t += Ping : int Effect.t
let () = if false then raise (Effect.Unhandled Ping)
let f () = try 1 + Effect.perform Ping with _ -> 7
let () = print_string (string_of_int (f ())); print_newline ()
