import Test.Api.HostSessionContract
import Effect4.Laws.Program.Typed.Admission

/-!
E4-HOST-CE-008 (seeded 2026-10-03 by Codex, `docs/research/2026-10-03-session-work/t4-audit.lean`;
repaired the same day, decisions row 191): a host failure carrying one of the machine's reserved
defects, `badName` or `notImplemented`, passed executable admission (`admit`, the session's
`preflight`, the oracle path `externalAdmits`) while the typed exit judgment refuses it (`ExitOk`'s
`NoShapeDefect`, decisions row 152). So `admit = none` did not imply the ghost `AnswerOk` on
failures. Admission now refuses such a failure (`Refusal.reservedDefect`) on both paths, and an
ordinary user defect is still admitted at every error column.

These are finite execution controls at one session, beside the universal theorem
`preflight_failure_noShapeDefect`. Nothing here is about the value half of admission (row 97).
-/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

namespace Test.Counterexamples.Machine.Runtime.HostReservedDefect
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Api.HostSession
open Test.Api.HostSessionContract

def reservedReply : Reply :=
  { reply0 with completion := .ofExit (.failure (Cause.die .badName)) }
def unimplementedReply : Reply :=
  { reply0 with completion := .ofExit (.failure (Cause.die .notImplemented)) }
def userReply : Reply :=
  { reply0 with completion := .ofExit (.failure (Cause.die (.user 7))) }

-- The seeded behaviour, now refused on every admission path.
#guard admit table bound0.machine (.answerAsync Api.root 0 reservedReply.completion) =
  some (.reservedDefect Api.root 0)
#guard admit table bound0.machine (.answerAsync Api.root 0 unimplementedReply.completion) =
  some (.reservedDefect Api.root 0)
#guard preflight bound0 reservedReply = .error .envelope
#guard (submit bound0 reservedReply).phase = .refused .envelope
#guard externalAdmits table 0 reservedReply.completion [] = false

-- An ordinary defect stays admitted at every error column (decisions row 152).
#guard admit table bound0.machine (.answerAsync Api.root 0 userReply.completion) = none
#guard preflight bound0 userReply = .ok (.answerAsync Api.root 0 userReply.completion)
#guard externalAdmits table 0 userReply.completion [] = true

/-- The typed judgment refuses what admission now refuses, at every world. -/
example (w : Typed.World) : ¬ Typed.ExitOk w admitted.ty (.failure (Cause.die .badName)) := by
  intro h
  exact (h.2 (.die .badName .empty) (by decide)).1 rfl

/-- The theorem at this session: whatever failing reply preflight accepts is shape-free. -/
example (reply : Reply) (decision : NativeDecision) (c : Machine.CauseV)
    (failed : reply.completion = .ofExit (.failure c))
    (accepted : preflight bound0 reply = .ok decision) :
    Typed.NoShapeDefect admitted.ty (.failure c) :=
  preflight_failure_noShapeDefect bound0 reply decision c failed accepted admitted.ty

/-- info: 'Effect4.Api.HostSession.preflight_failure_noShapeDefect' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms preflight_failure_noShapeDefect

end Test.Counterexamples.Machine.Runtime.HostReservedDefect
