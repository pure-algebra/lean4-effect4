type _ Effect.t += E : int -> int Effect.t

let body () = 1 + Effect.perform (E 41)

(* Inner handler forwards E by not handling it; the outer handler handles it. *)
let inner () =
  Effect.Deep.match_with body ()
    { retc = (fun v -> v)
    ; exnc = (fun e -> raise e)
    ; effc = (fun (type a) (_ : a Effect.t) -> None) }

let () =
  let r =
    Effect.Deep.match_with inner ()
      { retc = (fun v -> v * 2)
      ; exnc = (fun e -> raise e)
      ; effc = (fun (type a) (eff : a Effect.t) ->
          match eff with
          | E n -> Some (fun (k : (a, _) Effect.Deep.continuation) ->
                           Effect.Deep.continue k n)
          | _ -> None) }
  in
  print_string (string_of_int r); print_newline ()
