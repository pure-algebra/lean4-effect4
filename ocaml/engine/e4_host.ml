(* E4_host -- a host driver over the engine (hand-written).

   What it is: Lean's `Effect4.Run.driveFrom` (src/Effect4/Run/Basic.lean) over an
   E4_engine.ENGINE. The root is evaluated; then each round answers the first host call the
   machine waits on from a provider, or flushes when there is none, and the drive stops when a
   flush leaves no host call. A provider is the host: a function of the call's row, its request
   and the host's state, answering a completion and the host's next state, as Lean's
   `Run.Reactor` does. Native interfaces are hosts (decisions row 393).
   Depends on: E4_engine, Eff_types, Eff_wire.

   Properties:
   H1  The decisions are Lean's: `evaluate 0`, then per round one `answerAsync` for the first
       host call, or one `flush`.                     by construction; tested (test_todo T8)
   H2  A reply is applied only when the engine admits it (`E4_engine.admits`, Lean's checked
       replay); a refused reply stops the drive, which reports `Refused`.   by construction
   H3  A provider that declines, a call whose row is not in the table, and the last round each
       stop the drive with their own report; a flush that leaves no host call is `Settled`.
                                                                            by construction
   H4  The drive takes at most `rounds` rounds (64 by default, as `Run.drive`'s).
                                                                            by construction *)

open Eff_types

type completion = (val_, err, defect, int, unit) Eff_types.completion

module Make (E : E4_engine.ENGINE) = struct
  type 'st provider = row -> val_ -> 'st -> (completion * 'st) option

  type stop = Settled | Declined | Refused | Unknown_row | Out_of_rounds

  type call = { row : int; request : val_; answer : completion }

  type 'st served = { engine : E.t; state : 'st; calls : call list; stop : stop }

  let serve ?(table = []) ?(rounds = 64) (provider : 'st provider) (program : Eff_wire.program)
      ~(fuel : int) (state : 'st) : 'st served =
    let rec go n t st calls =
      let finish stop = { engine = t; state = st; calls = List.rev calls; stop } in
      if n = 0 then finish Out_of_rounds
      else
        match E.host_calls t with
        | (fiber, token, row, request) :: _ -> (
          match List.nth_opt table row with
          | None -> finish Unknown_row
          | Some r -> (
            match provider r request st with
            | None -> finish Declined
            | Some (answer, st') ->
              let d = E.answer_async fiber token answer in
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
