import Effect4.Laws.Program.Typed.Assembly

/-!
# H1's typed state as merged at `0c534f06`, kept for the historical controls

Decisions row 134 (ruled 2026-10-01) replaced H1's queue-relative saved-code clause (`CodeInert`,
read inside the generated bundle through `statePreds root m commands`) by the split `J`/`I` of
`Laws/Program/Typed/Assembly.lean`, and row 139 put `stuck = none` into `J`, superseding H1's halt
extension of row 133 (plan O4). These are the merged definitions as they stood at `bb269fde`
(`Laws/Program/Typed/Assembly.lean:68-185` there), so the controls that refuted or confirmed them
stay checkable: `E4-TYPED-CE-011`'s cut and probe C's halt facts
(`Test/Counterexamples/Machine/Semantics/StaleCode.lean`), `E4-SCHED-CE-019` and `-020`
(`Test/Counterexamples/Machine/Semantics/M6Capstone.lean`).

`statePreds` overrides only `SavedOk` of the production `preds`, whose other fields are H1's
unchanged; `QueueOk` is the production structure.
-/

set_option autoImplicit false
namespace Test.Counterexamples.Machine.Semantics.H1Shapes
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed
open Effect4.Laws.Effects Contracts
abbrev W := Effect4.Program.Typed.World

/-- A terminal fiber delivers the exit carried by its queued finish, or the exit already
published on that fiber. -/
def TerminalFiber (m : RState) (commands : List RCmd) (id : FiberId) : Prop :=
  (∃ exit, .finish id exit ∈ commands) ∨
    ∃ fiber ∈ m.fibers, fiber.id = id ∧ fiber.exit.isSome = true

/-- The generated saved position retains its identity while its current code becomes inert. -/
def TerminalPosition (m : RState) (commands : List RCmd) : Expect → Prop
  | .root => TerminalFiber m commands Api.root
  | .fiber id => TerminalFiber m commands id
  | .hook _ => False

/-- H1: current code is inert after a machine halt, while its finish is queued, or after its
exit has been published. -/
def CodeInert (m : RState) (commands : List RCmd) (position : Expect) : Prop :=
  m.stuck.isSome = true ∨ TerminalPosition m commands position

/-- H1: only the current-code premise is conditional. -/
def SavedPosition (root : ProgramSource) (w : W) (m : RState) (commands : List RCmd)
    (position : Expect) (final : EffTy) (saved : RSaved) : Prop :=
  ∃ tin, (¬ CodeInert m commands position → TypedProg root w tin saved.current) ∧
    StackAccepts (TypedProg root) ExitOk (frameProtocols root) w tin final saved.stack ∧
    InterruptProvenance saved

/-- H1: the generated bundle with the saved-code clause read at the machine and the queue. -/
def statePreds (root : ProgramSource) (m : RState) (commands : List RCmd) : Preds W :=
  { preds root with
    SavedOk := fun w position saved => ∀ ty, expectOf w position = some ty →
      SavedPosition root w m commands position ty saved }

/-- A fully typed saved frame also satisfies H1's conditional current-code clause. -/
theorem savedPosition_of_saved (root : ProgramSource) (w : W) (m : RState)
    (commands : List RCmd) (position : Expect) (final : EffTy) (saved : RSaved)
    (typed : Contracts.SavedOk (TypedProg root) ExitOk (frameProtocols root) w final saved) :
    SavedPosition root w m commands position final saved := by
  obtain ⟨tin, code, stack, provenance⟩ := typed
  exact ⟨tin, fun _ => code, stack, provenance⟩

/-- H1's typed state: its explicit queue controls the saved current-code clause; the empty queue
is the initialization and completed-run interface. -/
def TypedState (root : ProgramSource) (rootTy : EffTy) (w : W) (m : RState)
    (commands : List RCmd := []) : Prop :=
  WorldValid rootTy w m ∧ RStateOk (statePreds root m commands) w m ∧
    ActiveDelivery root w m ∧ SchedulerState m ∧ ObserverState root w m ∧ RegistrationState root w m

/-- H1's command obligation, at the dispatch premise `m.stuck = none`. -/
def StepPreserves (root : ProgramSource) (rootTy : EffTy) (cmd : RCmd) : Prop :=
  ∀ w m rest, m.stuck = none → TypedState root rootTy w m (cmd :: rest) →
    QueueOk root w m (cmd :: rest) →
    let r := (letI := termEvaluatorFor root.program
              driveStep (interpR root.program) m cmd rest)
    ∃ w', w.leHost w' ∧ TypedState root rootTy w' r.1 r.2 ∧ QueueOk root w' r.1 r.2

end Test.Counterexamples.Machine.Semantics.H1Shapes
