exception Boom

type _ Effect.t += E : int -> int Effect.t

let body () =
  try 1 + Effect.perform (E 41) with Boom -> 7

let () =
  let r =
    Effect.Deep.match_with body ()
      { retc = (fun v -> v)
      ; exnc = (fun e -> raise e)
      ; effc = (fun (type a) (eff : a Effect.t) ->
          match eff with
          | E _ -> Some (fun (k : (a, _) Effect.Deep.continuation) ->
                           Effect.Deep.discontinue k Boom)
          | _ -> None) }
  in
  print_string (string_of_int r); print_newline ()
