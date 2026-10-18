(* E4_host -- a host driver over the engine (hand-written).

   What it is: Lean's `Effect4.Run.driveFrom` (src/Effect4/Run/Basic.lean) over an
   E4_engine.ENGINE. The program is loaded and its root evaluated; then each round answers the
   first host call the machine waits on from a provider, or flushes when there is none. The
   engine's answer is read after every step, and the drive stops when a flush leaves no host
   call, when the machine is stuck or short of fuel, or when the host stops it. A provider is
   the host: a function of the call's row, its request and the host's state, answering a
   completion and the host's next state, as Lean's `Run.Reactor` does. Native interfaces are
   hosts (decisions row 393).
   Depends on: E4_engine, E4_clock, Eff_types, Eff_wire.

   Properties:
   H1  The decisions are Lean's: `evaluate 0`, then per round one `answerAsync` for the first
       host call, or one `flush`, until the drive stops.
                                                      by construction; tested (test_todo T8)
   H2  A reply is applied only when the engine admits it (`E4_engine.admits`, Lean's checked
       replay) and the step that applies it stays inside the host numeric profile (EN3). A
       reply refused either way stops the drive at once, with `Refused` or `Outside_profile`:
       the provider was called once, the engine and the host's state are the ones before the
       call, no call is recorded for it, and the call stays outstanding.
                                                         tested (test_serve S1, S2, S3)
   H3  A provider that declines, a call whose row is not in the table, and the last round each
       stop the drive with their own host stop (`Declined`, `Unknown_row`, `Out_of_rounds`),
       with the engine and the host's state the round began with.          by construction
   H4  The drive takes at most `rounds` rounds (64 by default, as `Run.drive`'s).
                                                                            by construction
   H5  A provider that raises answers nothing: the drive stops with `Raised`, the engine and the
       host's state are the ones before the call, and the call stays outstanding, a live
       frontier, as after a provider that declines. An exception is never turned into a typed
       failure or a defect here; a host that means a failure answers it. `Out_of_memory` and
       `Sys.Break` are no host's answer and are raised again.
                                                       by construction; tested (test_todo T15)
   H6  An answer outside the host numeric profile (EN9, `E4_engine.check_answer`) is not
       applied: the drive stops with `Outside_profile`, the engine and the host's state are the
       ones before the call.                           by construction; tested (test_todo T17)
   H7  A row is found by its position in O(1): the table is read into an array once.
                                                                            by construction
   H8  Loading has its own result. A program that `E.load` refuses at the host numeric profile
       (EN8: a natural literal outside it, or a value its loading computes outside it) is
       `Error (Load_outside_profile why)`: never an escaping exception, never a stop.
                                                                    tested (test_serve S7)
   H9  Every step's answer is read (`E4_engine.answer`): after `evaluate 0`, after each reply
       and after each flush. A step refused at the host numeric profile is not taken: the drive
       stops with `Outside_profile`, and the engine is the one before the step.
                                                                tested (test_serve S1, S8)
   H10 The stop separates what the machine reached (`Machine`) from why the host stopped
       (`Host`). `Finished` is read only off the engine's `Finished`, and `Waiting` only off its
       `Suspended`, each after a flush that leaves no host call. `Stuck` (the engine's
       `Refused`, with its reason) and `Delay` stop the drive after any step, with the engine
       after it. So no stuck, refused, short-of-fuel or out-of-profile machine reads as
       `Finished`. `Waiting` and `Delay` are live frontiers, never errors.
       tested (test_serve S3, S4, S6; S5 over a stand-in engine, as no program reaches `Stuck`)
   H11 The drive stops where `driveFrom` stops, and at three places where it does not, since
       `driveFrom` reads no step's verdict and its naturals are unbounded:
       (a) the host numeric profile (H2, H6, H8, H9) exists only in OCaml;
       (b) at a refused reply `driveFrom` plays the refused rows, each changing nothing
           (`Api.Runner.step`), keeps the reactor's next state, and stops at the next round
           because the bound call is no fresh call; here the drive stops at once with the
           state before the call (H2);
       (c) `driveFrom` plays on past a stuck machine (`HostSession.advance` refuses each row)
           and past a step short of fuel (that row's phase is `frontier`); here the drive
           stops at the first, as `replayEval` does (EN4b).               by construction
   H12 The host's types (`provider`, `outcome`, `host_stop`, `stop`, `load_refusal`, `call`)
       mention no engine, so they are declared once, in `Types`, and every instance of `Make`
       re-exports them with type equalities: two instances' stops and calls are one type.
                                            by construction; tested (test_todo T8 compiles) *)

open Eff_types

type completion = (Val.t, Err.t, Defect.t, int, unit) Eff_types.Completion.t

module Types = struct
  type 'st provider = Row.t -> Val.t -> 'st -> (completion * 'st) option

  type outcome = Finished | Waiting | Delay | Stuck of string

  type host_stop =
    | Declined
    | Raised of exn
    | Refused
    | Outside_profile of E4_clock.refusal
    | Unknown_row
    | Out_of_rounds

  type stop = Machine of outcome | Host of host_stop

  let stop_name = function
    | Machine Finished -> "finished"
    | Machine Waiting -> "waiting"
    | Machine Delay -> "delay: the fuel ran out"
    | Machine (Stuck why) -> "stuck: " ^ why
    | Host Declined -> "declined"
    | Host (Raised e) -> "raised " ^ Printexc.to_string e
    | Host Refused -> "refused"
    | Host (Outside_profile why) -> "outside the profile: " ^ E4_clock.refusal_text why
    | Host Unknown_row -> "unknown row"
    | Host Out_of_rounds -> "out of rounds"

  type load_refusal = Load_outside_profile of E4_clock.refusal

  type call = { row : int; request : Val.t; answer : completion }
end

include Types

module Make (E : E4_engine.ENGINE) = struct
  include Types

  type 'st served = { engine : E.t; state : 'st; calls : call list; stop : stop }

  let serve ?(table = []) ?(rounds = 64) (provider : 'st provider) (program : Eff_wire.program)
      ~(fuel : int) (state : 'st) : ('st served, load_refusal) result =
    match E.load ~table program ~fuel with
    | exception E4_clock.Profile_refusal why -> Error (Load_outside_profile why)
    | loaded ->
      let rows = Array.of_list table in
      let served engine st calls stop = { engine; state = st; calls = List.rev calls; stop } in
      (* One round: answer the first host call, or flush. Every step before it was read, so
         the machine [t] is live and was refused nothing (H9, H10). *)
      let rec round n t st calls =
        if n = 0 then served t st calls (Host Out_of_rounds)
        else
          match E.host_calls t with
          | (fiber, token, row, request) :: _ -> (
            if row < 0 || row >= Array.length rows then served t st calls (Host Unknown_row)
            else
              match provider rows.(row) request st with
              | exception ((Out_of_memory | Sys.Break) as e) -> raise e
              | exception e -> served t st calls (Host (Raised e))
              | None -> served t st calls (Host Declined)
              | Some (answer, st') -> (
                match E.answer_async fiber token answer with
                | exception E4_clock.Profile_refusal why ->
                  served t st calls (Host (Outside_profile why))
                | d ->
                  if not (E.admits t d) then served t st calls (Host Refused)
                  else
                    read (n - 1) (t, st, calls) (E.step t d) st' ({ row; request; answer } :: calls)
                      ~flushed:false))
          | [] -> read (n - 1) (t, st, calls) (E.step t E.flush) st calls ~flushed:true
      (* The answer of the step that took [t] to [t']; [st'] and [calls'] are the host's state
         and the calls once that step is taken. A refusal at the profile boundary keeps [t],
         [st] and [calls] (H2, H9); a stuck machine and one short of fuel are what the machine
         reached (H10); a flush that leaves no host call ends the drive with the machine's
         outcome. *)
      and read n (t, st, calls) t' st' calls' ~flushed =
        match E.answer t' with
        | E4_engine.Outside_profile why -> served t st calls (Host (Outside_profile why))
        | E4_engine.Refused why -> served t' st' calls' (Machine (Stuck why))
        | E4_engine.Delay _ -> served t' st' calls' (Machine Delay)
        | E4_engine.Finished when flushed && List.is_empty (E.host_calls t') ->
          served t' st' calls' (Machine Finished)
        | E4_engine.Suspended _ when flushed && List.is_empty (E.host_calls t') ->
          served t' st' calls' (Machine Waiting)
        | E4_engine.Finished | E4_engine.Suspended _ -> round n t' st' calls'
      in
      Ok (read rounds (loaded, state, []) (E.step loaded (E.evaluate 0)) state [] ~flushed:false)
end
