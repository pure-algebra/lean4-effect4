type _ Effect.t += Ping : int Effect.t
let f () = try 1 + Effect.perform Ping with _ -> 7
let () = print_string (string_of_int (f ())); print_newline ()
