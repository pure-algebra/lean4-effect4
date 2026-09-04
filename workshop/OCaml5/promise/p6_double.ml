(* P6 witness B2: a foreign `then` that calls the fulfilment handler twice.
   Does OCaml's one-shot continuation guard fire across the JS boundary? *)
external log : string -> unit = "p6_log"
external call_twice : (string -> unit) -> string -> unit = "p6_call_twice"
external at_exit_dump : unit -> unit = "p6_at_exit"

type _ Effect.t += AwaitForeign : string Effect.t

let () =
  at_exit_dump ();
  let open Effect.Deep in
  match_with (fun () ->
    log "K:enter";
    let v = Effect.perform AwaitForeign in
    log ("K:resumed " ^ v);
    log "K:done") ()
    { retc = (fun () -> log "K:handler-retc")
    ; exnc = (fun e -> log ("K:handler-exnc " ^ Printexc.to_string e))
    ; effc = (fun (type a) (eff : a Effect.t) ->
        match eff with
        | AwaitForeign ->
            Some (fun (k : (a, unit) continuation) ->
              log "H:register-foreign";
              call_twice (fun v -> log ("H:resume " ^ v); continue k v) "vX";
              log "H:handler-returns")
        | _ -> None) };
  log "S:sync-tail"
