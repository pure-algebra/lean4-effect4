type _ Effect.t += E : int -> int Effect.t

let body () = 1 + Effect.perform (E 41)

let () =
  let r =
    Effect.Deep.match_with body ()
      { retc = (fun v -> v)
      ; exnc = (fun e -> raise e)
      ; effc = (fun (type a) (eff : a Effect.t) ->
          match eff with
          | E n -> Some (fun (k : (a, _) Effect.Deep.continuation) ->
                           Effect.Deep.continue k n)
          | _ -> None) }
  in
  print_string (string_of_int r); print_newline ()
