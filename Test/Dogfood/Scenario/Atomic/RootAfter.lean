import Test.Dogfood.Scenario.Atomic.RootFrame

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

/-- Every emitted after-interruption command carries its actual receiving endpoint. -/
def AfterResult (root : NativeEff) (table : RowTable) (world : StageWorld.World) (result : Moves.NIteration) : Prop :=
  ∀ host yielding kind, .afterInterrupt host yielding kind ∈ result.nested →
    AfterAt root table world kind result.fiber.frame

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
