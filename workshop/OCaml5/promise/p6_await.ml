(* P6 witness B: an `Await` effect over JavaScript Promises, handled by a deep handler
   that attaches `.then` and resumes the one-shot continuation from inside the microtask.
   OCaml 5.1.1 + js_of_ocaml 5.7.1 `--enable effects`, run under Node. *)

external log : string -> unit = "p6_log"
external new_promise : unit -> int = "p6_new_promise"
external settle : int -> bool -> string -> unit = "p6_settle"
external resolved : string -> int = "p6_resolved"
external attach : int -> (string -> unit) -> (string -> unit) -> unit = "p6_then"
external js_then : int -> string -> unit = "p6_js_then"
external at_exit_dump : unit -> unit = "p6_at_exit"

type _ Effect.t += Await : int -> string Effect.t
exception Rejected of string

(* The handler is the whole bridge: one reaction registered per Await, resuming the
   captured continuation from the reaction job. Nothing here is a Promise combinator. *)
let run (main : unit -> unit) : unit =
  let open Effect.Deep in
  match_with main ()
    { retc = (fun () -> log "K:handler-retc")
    ; exnc = (fun e -> log ("K:handler-exnc " ^ Printexc.to_string e))
    ; effc = (fun (type a) (eff : a Effect.t) ->
        match eff with
        | Await id ->
            Some (fun (k : (a, unit) continuation) ->
              log ("H:attach-then p" ^ string_of_int id);
              attach id
                (fun v -> log ("H:resume-in-microtask " ^ v); continue k v)
                (fun e -> log ("H:discontinue-in-microtask " ^ e);
                          discontinue k (Rejected e));
              log ("H:handler-returns p" ^ string_of_int id))
        | _ -> None) }

let () =
  at_exit_dump ();
  let gate = new_promise () in
  js_then gate "JS:first-then";
  run (fun () ->
    log "K:enter";
    let v = Effect.perform (Await gate) in
    log ("K:resumed-1 " ^ v);
    let w = Effect.perform (Await (resolved (v ^ "!"))) in
    log ("K:resumed-2 " ^ w);
    (try
       let _ = Effect.perform (Await (let bad = new_promise () in
                                      settle bad false "boom"; bad)) in
       log "K:UNREACHABLE"
     with Rejected e -> log ("K:discontinued " ^ e));
    log "K:done");
  js_then gate "JS:third-then";
  log "S:settling";
  settle gate true "v0";
  log "S:sync-tail"
