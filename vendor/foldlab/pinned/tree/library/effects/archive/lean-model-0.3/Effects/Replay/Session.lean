import Effects.Replay.History
import Effects.Replay.Decision

/-!
# The session state

Mode, status, flat history, and cursor. Record mode invokes live adapters
and appends history; replay mode is hermetic and consumes it. The status
carries the terminal abort state structurally: an aborted session absorbs
every input and emits nothing, so nothing appends past a failure and
histories stay truthful prefixes — there is no mutable poisoned flag to
forget.

Well-formedness pins the cursor inside the history, and in record mode
pins it to the history length — the occurrence index of the next append.
The reducer preserves it (the WF-PRESERVE obligation).

`SessionOutcome` lives here beside the state: completion means the
program reached a terminal AND the cursor equals the history length,
uniformly across both terminal kinds; the unconsumed-suffix rejection is
the only rejection that carries the program's terminal so far.
-/

namespace Effects.Replay

/-- Record invokes live adapters and appends; replay is hermetic. -/
inductive Mode where
  | record
  | replay
  deriving DecidableEq

/-- Active, or structurally aborted: an aborted session absorbs every
input and emits nothing. -/
inductive Status where
  | active
  | aborted
  deriving DecidableEq

/-- The session state: mode, status, flat history, cursor, and the
outstanding record-mode delegation. `pending` carries the invocation a
live delegation is currently executing — set by the record-mode invoke,
cleared by the solicited append; record-mode delegation is exclusive, so
`some` refuses further invocations until the outcome arrives. -/
structure SessionState (Op Req Val Err : Type) where
  mode : Mode
  status : Status
  history : List (Entry Op Req Val Err)
  cursor : Nat
  pending : Option (Invocation Op Req)
  deriving DecidableEq

/-- Well-formedness: the cursor sits inside the history, record mode
pins it to the history length, and replay mode carries no outstanding
delegation. -/
def SessionState.WF {Op Req Val Err : Type}
    (s : SessionState Op Req Val Err) : Prop :=
  s.cursor ≤ s.history.length ∧
    (s.mode = .record → s.cursor = s.history.length) ∧
    (s.mode = .replay → s.pending = none)

instance {Op Req Val Err : Type} (s : SessionState Op Req Val Err) :
    Decidable s.WF := by
  unfold SessionState.WF; infer_instance

/-- The tagged session outcome. `rejected` carries the program's terminal
so far ONLY for the unconsumed-suffix case; `violated` is produced by the
runtime tripwires, never by the pure reducer in this slice. -/
inductive SessionOutcome (Val Err : Type) where
  | completed (terminal : Terminal Val Err)
  | rejected (category : MismatchCategory) (pos : Nat)
      (terminalSoFar : Option (Terminal Val Err))
  | violated (service : AmbientService)
  deriving DecidableEq

end Effects.Replay
