import Test.Dogfood.Scenario.Atomic.RootFrame
import Effect4.Laws.Program.PrimitiveEffects

/-!
Concept: reactive-scheduling R11 and store-typing R4.
Consumer: Atomic's actual after-interruption command and its native action producer.
The certificate retains the receiving binder or the ignored ordinary endpoint.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.RootGraph
open Effect4 Effect4.Machine Effect4.Program
open StageWorld

/-- Actual root interruption commands retain the receiving endpoint and its real saved suffix. -/
inductive AfterAt (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (kind : ParkKind) (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) : Prop
  | ordinary (noRace : ∀ race, kind ≠ .race race)
      (saved : Effect4.Contracts.Path (Edge root table world) .ordinary .ordinary frame.stack) :
      AfterAt root table world kind frame
  | binder (binder : Nat) (target : FiberId) (same : kind = .join target .awaitValue)
      (counter : world.nextId = RootSlots.rank (binder + 1)) (ignored : RootSlots.expected binder = none)
      (saved : Effect4.Contracts.Path (Edge root table world) (.rootAnswer binder) .ordinary frame.stack) :
      AfterAt root table world kind frame

/-- Retaining the actual saved suffix retains its receiving endpoint. -/
theorem AfterAt.stack (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (kind : ParkKind) (first last : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (same : last.stack = first.stack) (held : AfterAt root table world kind first) :
    AfterAt root table world kind last := by
  cases held with
  | ordinary noRace saved => exact .ordinary noRace (same.symm ▸ saved)
  | binder binder target kind counter ignored saved =>
    exact .binder binder target kind counter ignored (same.symm ▸ saved)

/-- Actual request writes retain receiving suffixes at the unchanged root counter. -/
theorem AfterAt.counter (root : NativeEff) (table : RowTable) (before after : StageWorld.World)
    (future : Future before after) (counter : before.nextId = after.nextId)
    (kind : ParkKind) (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (held : AfterAt root table before kind frame) : AfterAt root table after kind frame := by
  cases held with
  | ordinary noRace saved => exact .ordinary noRace (saved.map (edge_future root table before after future))
  | binder binder target kind captured ignored saved =>
    exact .binder binder target kind (counter.symm.trans captured) ignored
      (saved.map (edge_future root table before after future))

/-- Every emitted after-interruption command carries its actual receiving endpoint. -/
def AfterResult (root : NativeEff) (table : RowTable) (world : StageWorld.World) (result : Moves.NIteration) : Prop :=
  ∀ host yielding kind, .afterInterrupt host yielding kind ∈ result.nested →
    AfterAt root table world kind result.fiber.frame

/-- A quiet actual primitive owes no after-interruption receiver. -/
theorem AfterResult.of_quiet (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (result : Moves.NIteration) (quiet : Moves.QuietEffects result) : AfterResult root table world result := by
  intro host yielding kind member
  have impossible := quiet.2 (.afterInterrupt host yielding kind) member
  cases impossible

/-- An empty nested command list owes no after-interruption receiver. -/
theorem AfterResult.of_empty (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (result : Moves.NIteration) (empty : result.nested = []) : AfterResult root table world result := by
  intro host yielding kind member
  rw [empty] at member
  cases member

/-- Ignored interruption waits use the existing daemon await heads and actual observed exit. -/
theorem ignored_await (root : NativeEff) (table : RowTable) (machine : NativeMachine) (kind : ParkKind)
    (noRace : ∀ race, kind ≠ .race race) :
    DaemonGraph.CodeAt root table (awaitCode (interpOf root table) machine kind) := by
  cases kind with
  | race race => exact False.elim (noRace race rfl)
  | awaitAll targets => exact .awaitAll targets
  | join target mode =>
    dsimp only [awaitCode]
    split
    · rename_i exit found
      cases mode with
      | awaitValue => exact .success _
      | joinEffect => cases exit with
        | success value => exact .success value
        | failure cause => exact .failure cause
    · exact .join target mode

/-- The actual after-interruption command retains its root answer class and suffix. -/
theorem after_frame (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (machine : NativeMachine) (kind : ParkKind)
    (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (held : AfterAt root table world kind frame) :
    FrameAt root table world
      { frame with current := asVoidCode (interpOf root table) (awaitCode (interpOf root table) machine kind) } := by
  cases held with
  | ordinary noRace saved =>
    refine ⟨.ordinary, .ignored (.bound (ignored_await root table machine kind noRace) ?_), saved⟩
    intro view value
    exact .success .unit
  | binder binder target same counter ignored saved =>
    subst kind
    refine ⟨.rootAnswer binder, .bound (input := .rootAnswer binder) True.intro ?_ ?_, saved⟩
    · dsimp only [awaitCode]
      split
      · exact .success (ignored_answer world binder _ counter ignored)
      · exact .await counter ignored
    · intro after future view value good
      exact .success (ignored_answer after binder .unit good.1 ignored)

end Test.Dogfood.Scenario.Atomic.RootGraph
