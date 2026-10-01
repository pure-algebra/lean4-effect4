import Effect4.Api.HostSession
import Effect4.Program.Profile
import Effect4.Laws.Program.Typed.Assembly
import Effect4.Laws.Program.Guard.Decision

/-!
# Research.Pass.LiftVerify.Controls — two checks on the seat's controls

1. The seat's C2 shows the frame law's halting case with a hand-made evaluator and reads the
   native case off `Machine/Fibers.lean:1108`. Here the native evaluator itself: a join on a
   fiber that does not exist halts the machine and drops the commands queued behind it
   (finite checks).
2. The seat's C4 states today's capstone by hand. Here the kernel checks that the hand copy is
   the ledger's `typedState_reachable` at that instance.
3. The freshness clause M6 lacks: the native guard's queue invariant (`GuardQueue.keys`, whose
   `ReservedKeys.below` asks every queued resume's token to be below `nextToken`,
   `Guard/Core.lean:1080-1083`) refuses the early queue that M6's `QueueOk` accepts
   (`verify-steppreserves.lean`).
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Research.Pass.LiftVerify.Controls

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed

/-! ## 1. The native halting case of the frame law -/

/-- A host row that answers a fiber handle (the host-answers probe's `fiberRow`). -/
def fiberRow : Program.Row where
  name := "returnFiber"
  spelling := "Host.returnFiber"
  kind := .async
  registration := .external
  request := .unit
  answer := .fiberOf .nat .never
  error := .never
  cite := "verify probe"

def table : RowTable := [fiberRow]

/-- Ask the host for a fiber, then join it. -/
def joinHosted : NativeEff := .bind (.perform (.external 0) (.lit .unit)) (.awaitFiber (.var 0) .joinEffect)

/-- The root parked on the host row. -/
def parkedOnHost : NativeMachine :=
  letI := evaluatorFor joinHosted table
  (driveState (interpOf joinHosted table) 20 (Api.load joinHosted 20 [])
    [Cmd.evaluate Api.root, Cmd.drainDue]).1

/-- The resume a host answer naming fiber 7 (which does not exist) puts in the queue. -/
def ghostCode : NCode := (interpOf joinHosted table).answerCode (.ofExit (.success (Value.fiber 7)))

/-- A marker queued behind the answer's own commands. -/
def queued : List (Cmd EffName EffThunk Val Err Defect FiberId Ann) :=
  [Cmd.resume Api.root 0 ghostCode, Cmd.drainDue, Cmd.exitDone ⟨99⟩]

def ghostRun : NativeMachine × List (Cmd EffName EffThunk Val Err Defect FiberId Ann) :=
  letI := evaluatorFor joinHosted table
  driveState (interpOf joinHosted table) 20 parkedOnHost queued

-- The root is parked at token 0 before the answer.
#guard (parkedOnHost.fiber? Api.root).any (fun f => f.parked == .withGuard 0)
#guard parkedOnHost.stuck.isNone
-- After it the machine halts on the unknown fiber, and nothing is left: the `drainDue` and the
-- marker were dropped by `settle`'s stuck arm (a halted machine otherwise keeps its commands in
-- `driveState`, `Fibers.lean:1977`, so a command still queued at the halt would remain).
#guard (match ghostRun.1.stuck with | some (.unknownFiber id) => id == ⟨7⟩ | _ => false)
#guard ghostRun.2.isEmpty

/-! ## 2. The seat's hand copy of today's capstone is the ledger's statement -/

def sleeper : NativeEff := .perform .sleep (.lit (.nat 1))
def badTape : List Api.Decision :=
  [Api.evaluate, .answerAsync Api.root 0 (.ofExit (.success (.nat 42)))]
def bad : RState := (replayR sleeper 80 badTape).machine

/-- `Controls.lean:111-115`'s statement, verbatim. -/
def SeatCapstone : Prop :=
  Api.typeOf sleeper [] = some (EffTy.pure .unit) →
    ClosedEff (EffTy.pure .unit) →
    RReachable (sleeper : ProgramSource) 80 bad →
    ∃ w, TypedState (sleeper : ProgramSource) (EffTy.pure .unit) w bad

example : ProofGraph.Obligation SeatCapstone :=
  M6Ledger.typedState_reachable (sleeper : ProgramSource) (EffTy.pure .unit) 80 bad

/-! ## 3. The native guard refuses the early queue -/

/-- The early queue of `verify-steppreserves.lean`, at the native machine: a resume for token 0
queued at load, when no token is allocated. The guard's queue invariant is false there, because
its reserved keys must lie below `nextToken` (`ReservedKeys.below`). -/
theorem guard_refuses_early (table : RowTable) (code : NCode) :
    ¬ Guard.GuardQueue sleeper table (Api.load sleeper 80 [])
      [Cmd.evaluate Api.root, Cmd.resume Api.root 0 code, Cmd.drainDue] := fun q =>
  Nat.lt_irrefl 0 (q.keys.below (Api.root, 0) (List.mem_singleton_self _))

/-- M6's queue fact asks nothing of the same resume in any world that does not declare token 0,
and a world typing the loaded machine declares none (`WorldValid.tokenBound`). -/
theorem m6_accepts_early (w : Typed.World) (h : w.Θ Api.root 0 = none) (code : RProgram) :
    QueueOk (sleeper : ProgramSource) w [Cmd.evaluate Api.root, Cmd.resume Api.root 0 code, Cmd.drainDue] := by
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · trivial
  · show Contracts.ResumeOk (TypedProg (sleeper : ProgramSource)) w Api.root 0 code
    intro ty hty
    rw [h] at hty
    cases hty
  · trivial

end Research.Pass.LiftVerify.Controls

#print axioms Research.Pass.LiftVerify.Controls.guard_refuses_early
#print axioms Research.Pass.LiftVerify.Controls.m6_accepts_early
