import Effect4.Laws.Program.DenoteRows
import Effect4.Laws.Run.Tape
import Effect4.Laws.Auto.Semantics

/-!
# Api.SessionMeaning — the meaning under a run's reply tape is the run's observation (DI-69)

Slice H7 of `docs/research/2026-10-07-packet-host-meaning.md` (decisions row 310). The session's
side of DI-69: a run's reply tape (`appliedExits`), the premise that a host drives it
(`hostDriven`), and the planned goal `denoteRows_eq_session` on the fragment `StraightRows`,
which admits `catchIf` (the owner, row 310). Its proof is the packet's slice H8.
-/

set_option autoImplicit false

namespace Effect4.Run

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote

/-- A decision that a host hands a one-fiber run: the root's evaluation, a flush, or an answer
that holds an exit. An interruption, a clock step and a delayed cell read are not. -/
def hostDecision : Api.Decision → Bool
  | .answerAsync _ _ (.ofExit _) => true
  | decision => decision == Api.evaluate || decision == Api.flush

/-- The reply tape of a decision tape: the exits of its answer decisions, in order. -/
def exitsOf (tape : List Api.Decision) : ReplyTape :=
  tape.filterMap fun
    | .answerAsync _ _ (.ofExit ex) => some ex
    | _ => none

/-- The reply tape of a run: the exits of the replies that the session applied, in order. -/
def appliedExits (s : Run) : ReplyTape := exitsOf (tapeOf s)

/-- A run that a host drives: each decision of its tape is a host's (`hostDecision`). The
premise reads the tape, as both sides of the statement do: a row that the session refuses, and
a reply that it never applies, hand the machine nothing. -/
def hostDriven (s : Run) : Bool := (tapeOf s).all hostDecision

/-- The proposition of `denoteRows_eq_session`, on the fragment `frag`. -/
def DenoteRowsEqSession (frag : RowTable → NativeEff → Bool) : Prop :=
  ∀ (s : Run), Run.Reached s → funded s = true → atRest s = true → hostDriven s = true →
    frag s.built.table s.built.program = true →
    meaningRows s.built.table s.built.program [] Stores.empty (appliedExits s) =
      s.exit.map fun ex => ((ex, s.machine.state), [])

/-- **The meaning under a run's reply tape is the run's observation** (DI-69). For a recorded
run of a program of the fragment, the meaning of the program under the run's reply tape is the
root's exit with the stores, and the reply tape is read to its end. Where the root has no exit,
the meaning is the frontier. Reach: `StraightRows`, one fiber; a run that is funded, at rest and
driven by a host: its controls evaluate the root or flush, and each reply holds an exit. It
does not establish the same for a run with an interruption, a clock step, a delayed cell read
or a handle row: each has a red control. It says nothing of a fiber, a scope or a loop. Concept
`translation-simulation`, claim `rows-denotation-session`, role simulation; requirement R6.
Consumer: a fact of a program's call tree, read on a run. -/
@[semantics "translation-simulation" (requirement := R6)]
proof_goal denoteRows_eq_session : DenoteRowsEqSession StraightRows

end Effect4.Run
