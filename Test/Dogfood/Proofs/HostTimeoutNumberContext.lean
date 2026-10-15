import Test.Dogfood.Proofs.HostTimeoutNumberPhaseFlow

/-!
Concepts: scope-lifetime-finalization R11 and translation-simulation R10.
Question: actual attempt source captures serve both Timeout numeric goals.
Consumer: the pending numeric role and its source callback annotation.
Reach: the actual captured source point, counter prefix, and numeric finalizer contract.
Limit: these data and local contracts supply no initialized command history.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.HostTimeoutNumberConfiguration
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutFlow HostTimeoutNumberPhase

/-- A pending attempt carries the predecessor phase and the source cursor that bounds its next count. -/
structure CountContext where
  before : Phase
  n : Fin 4
  cleanups : before.cleanups.length = before.count
  forms : before.count ≤ before.exits.length
  cursor : before.count ≤ n.val
  captured : Point
  fuel : Nat
  delay : Nat
  previous : Val

/-- The pending context's next phase names the actual counter increment. -/
def CountContext.entered (context : CountContext) : Phase :=
  context.before.counted context.n context.cleanups context.forms context.cursor

/-- The existing source entry carries all three allocated handles and the retry cursor. -/
def CountContext.point (context : CountContext) : Point :=
  HostTimeoutNumberEntry.attemptPoint context.captured (context.fuel + 1) context.delay context.n context.previous

/-- The actual pending source program installs its finalizer before its count binder. -/
def CountContext.entry (context : CountContext) : NCode :=
  resolve HostTimeoutSource.program context.point

/-- The actual count binder is the first body of the pending source program. -/
def CountContext.bound (context : CountContext) : NCode :=
  resolve HostTimeoutSource.program (context.point.child 0)

/-- The native counter update retains the exact lexical values of its source entry. -/
def CountContext.write (context : CountContext) : NCode :=
  .sync (.op (.refUpdate ⟨0⟩ HostTimeoutNumberEntry.countTerm context.point.env))

/-- Source control retains the actual attempt location and its captured cursor independently of refreshed metadata. -/
structure AttemptSource (context : CountContext) (point : Point) : Prop where
  path : point.path = [1,1,1,0,0,1,0,0,0,0,0,0]
  env : point.env = HostTimeoutSlots.ready (.cell ⟨0⟩) (.cell ⟨1⟩) (.cell ⟨2⟩)
    context.n context.delay context.previous
  fuel : point.fuel = context.fuel + 4

/-- The existing lexical assertion fixes the attempt environment after its four captured bindings. -/
theorem attempt_env_tail (B env : List Val)
    (slots : HostTimeoutSlots.EnvAt B [1,1,1,0,0,1,0,0,0,0,0,0] env) :
    env = env.take 4 ++ [.unit] := by
  cases slots
  rfl

/-- A retained binding prefix and the existing source assertion recover the actual finalizer capture. -/
theorem AttemptSource.of_prefix (context : CountContext) (point : Point) (B : List Val)
    (path : point.path = [1,1,1,0,0,1,0,0,0,0,0,0])
    (slots : HostTimeoutSlots.EnvAt B point.path point.env)
    (bindings : point.env.take 4 = HostTimeoutSlots.running (.cell ⟨0⟩) (.cell ⟨1⟩) (.cell ⟨2⟩)
      context.n context.delay context.previous)
    (fuel : point.fuel = context.fuel + 4) : AttemptSource context point := by
  refine ⟨path, ?_, fuel⟩
  rw [path] at slots
  rw [attempt_env_tail B point.env slots, bindings]
  rfl

/-- Reconstructing the numeric source point keeps all actual tape, call, and completed-exit metadata. -/
theorem AttemptSource.reconstruct (context : CountContext) (point : Point)
    (source : AttemptSource context point) :
    HostTimeoutNumberEntry.attemptPoint point (context.fuel + 1) context.delay context.n context.previous = point := by
  cases point with
  | mk path env fuel tape completed root params call =>
    cases source with
    | mk pathEq envEq fuelEq =>
      dsimp only [HostTimeoutNumberEntry.attemptPoint]
      dsimp only at pathEq envEq fuelEq
      rw [pathEq, envEq, fuelEq]

/-- The actual captured source finalizer supplies the numeric contract without fixing stale completed-exit metadata. -/
theorem AttemptSource.saved (context : CountContext) (point : Point)
    (source : AttemptSource context point) (view : View) (state : Stores) (body : NCode) :
    AnswerFlow.SavedAt (HostTimeoutNumberPhaseFlow.model view) (interpreter view).toPrimInterp state
      (.before context.entered) (.attempt context.before context.entered (by
        change context.before.count + 1 = context.before.cleanups.length + 1
        rw [context.cleanups])) (.onExit body (.fin point) false) := by
  have contract := HostTimeoutNumberPhaseFlow.flexible_attempt_saved view state context.before context.entered
    (by change context.before.count + 1 = context.before.cleanups.length + 1; rw [context.cleanups])
    point context.fuel context.delay context.n context.previous body
  rw [source.reconstruct context point] at contract
  exact contract

/-- The actual pending source entry establishes its capture assertion before installing the finalizer. -/
theorem CountContext.source (context : CountContext) : AttemptSource context context.point :=
  AttemptSource.of_prefix context context.point [] rfl
    (HostTimeoutSlots.EnvAt.attemptExit _ _ _ _ _ _) rfl rfl

/-- These are the actual three pre-count control positions, with their complete attempt-local stacks. -/
inductive CountFrameAt (context : CountContext) : HostTimeoutFrames.NativeFrame → Prop
  | entry (frame : HostTimeoutFrames.NativeFrame) (current : frame.current = context.entry)
      (stack : frame.stack = []) : CountFrameAt context frame
  | finalizer (frame : HostTimeoutFrames.NativeFrame) (current : frame.current = context.bound)
      (stack : frame.stack = [.onExit context.bound (.fin context.point) false]) : CountFrameAt context frame
  | binder (frame : HostTimeoutFrames.NativeFrame) (current : frame.current = context.write)
      (stack : frame.stack = [.onSuccess context.write (.cont (context.point.child 0)),
        .onExit context.bound (.fin context.point) false]) : CountFrameAt context frame

/-- The protected prefix has installed the actual source finalizer, rather than an unrelated saved frame. -/
def CountInstalled (context : CountContext) (frame : HostTimeoutFrames.NativeFrame) : Prop :=
  ∃ point body, AttemptSource context point ∧ (.onExit body (.fin point) false : NCode) ∈ frame.stack

/-- The original concrete entry supplies an actual installed source witness. -/
theorem CountInstalled.exact (context : CountContext) (frame : HostTimeoutFrames.NativeFrame)
    (member : (.onExit context.bound (.fin context.point) false : NCode) ∈ frame.stack) :
    CountInstalled context frame := ⟨context.point, context.bound, context.source, member⟩

/-- Retaining the actual saved frame retains its same source witness through native execution. -/
theorem CountInstalled.mono (context : CountContext) (before after : HostTimeoutFrames.NativeFrame)
    (subset : before.stack ⊆ after.stack) (held : CountInstalled context before) : CountInstalled context after := by
  obtain ⟨point, body, source, member⟩ := held
  exact ⟨point, body, source, subset member⟩

end Test.Dogfood.Proofs.HostTimeoutNumberConfiguration
