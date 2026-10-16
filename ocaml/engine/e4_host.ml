(* E4_host -- a host driver over the engine (hand-written).

   What it is: Lean's `Effect4.Run.driveFrom` (src/Effect4/Run/Basic.lean) over an
   E4_engine.ENGINE. The root is evaluated; then each round answers the first host call the
   machine waits on from a provider, or flushes when there is none, and the drive stops when a
   flush leaves no host call. A provider is the host: a function of the call's row, its request
   and the host's state, answering a completion and the host's next state, as Lean's
   `Run.Reactor` does. Native interfaces are hosts (decisions row 393).
   Depends on: E4_engine, E4_clock, Eff_types, Eff_wire.

   Properties:
   H1  The decisions are Lean's: `evaluate 0`, then per round one `answerAsync` for the first
       host call, or one `flush`.                     by construction; tested (test_todo T8)
   H2  A reply is applied only when the engine admits it (`E4_engine.admits`, Lean's checked
       replay); a refused reply stops the drive, which reports `Refused`.   by construction
   H3  A provider that declines, a call whose row is not in the table, and the last round each
       stop the drive with their own report; a flush that leaves no host call is `Settled`.
                                                                            by construction
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
                                                                            by construction *)

open Eff_types

type completion = (val_, err, defect, int, unit) Eff_types.completion

module Make (E : E4_engine.ENGINE) = struct
  type 'st provider = row -> val_ -> 'st -> (completion * 'st) option

  type stop =
    | Settled
    | Declined
    | Raised of exn
    | Refused
    | Outside_profile of string
    | Unknown_row
    | Out_of_rounds

  let stop_name = function
    | Settled -> "settled"
    | Declined -> "declined"
    | Raised e -> "raised " ^ Printexc.to_string e
    | Refused -> "refused"
    | Outside_profile why -> "outside the profile: " ^ why
    | Unknown_row -> "unknown row"
    | Out_of_rounds -> "out of rounds"

  type call = { row : int; request : val_; answer : completion }

  type 'st served = { engine : E.t; state : 'st; calls : call list; stop : stop }

  let serve ?(table = []) ?(rounds = 64) (provider : 'st provider) (program : Eff_wire.program)
      ~(fuel : int) (state : 'st) : 'st served =
    let rows = Array.of_list table in
    let rec go n t st calls =
      let finish stop = { engine = t; state = st; calls = List.rev calls; stop } in
      if n = 0 then finish Out_of_rounds
      else
        match E.host_calls t with
        | (fiber, token, row, request) :: _ -> (
          if row < 0 || row >= Array.length rows then finish Unknown_row
          else
            match provider rows.(row) request st with
            | exception ((Out_of_memory | Sys.Break) as e) -> raise e
            | exception e -> finish (Raised e)
            | None -> finish Declined
            | Some (answer, st') -> (
              match E.answer_async fiber token answer with
              | exception E4_clock.Profile_refusal why -> finish (Outside_profile why)
              | d ->
                if not (E.admits t d) then finish Refused
                else go (n - 1) (E.step t d) st' ({ row; request; answer } :: calls)))
        | [] ->
          let flushed = E.step t E.flush in
          if E.host_calls flushed = [] then
            { engine = flushed; state = st; calls = List.rev calls; stop = Settled }
          else go (n - 1) flushed st calls
    in
    go rounds (E.step (E.load ~table program ~fuel) (E.evaluate 0)) state []
end
