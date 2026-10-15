import Test.Dogfood.Scenario.Atomic.StageCleanup

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Consumer: the actual root spawn and request native producer of `Atomic.Store.shop_stages`.
A real request source point retains its captured cells and installs its real protected finalizer.
All point metadata and the older native suffix stay with their existing owners.
This source entry establishes no root counter or whole-history producer premise.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.StageEntry
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto
open StageWorld

/-- The actual request source starts with its authored protected finalizer. -/
def site (root : NativeEff) (id : Nat) : Bool :=
  match Node.at_ (.eff root) (SourcePaths.requestPath id) with
  | some (.eff (.onExit _ _)) => true
  | _ => false

theorem source_census :
    (Store.shopProgram.map fun root => requests.all (site root)) = some true := by
  kernel_rfl

theorem source_at (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) :
    ∃ body finalizer, Node.at_ (.eff built.program) (SourcePaths.requestPath id) = some (.eff (.onExit body finalizer)) := by
  have source : Store.shopProgram = some built.program := by
    unfold Store.shopProgram
    rw [(Api.Author.build_retains accepted).1]
    rfl
  have census := source_census
  rw [source] at census
  have selected := List.all_eq_true.mp (Option.some.inj census) id member
  unfold site at selected
  split at selected
  · rename_i body finalizer found
    exact ⟨body, finalizer, found⟩
  · cases selected

/-- Real request entry joins its body and finalizer source callbacks at every native view. -/
theorem request_code (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (point : Point)
    (located : point.path = SourcePaths.requestPath id) (sourceOwned : SourceScope.At built.program point)
    (cells : StageRequest.Cells point.env) (world : StageWorld.World) (waiting : world.stages id = .waiting) :
    StageGraph.CodeAt built.program built.table id world (.finalized id) (resolve built.program point) := by
  obtain ⟨body, finalizer, found⟩ := source_at built accepted id member
  rw [← located] at found
  rw [SourceScope.resolve_at _ _ _ found]
  cases amount : point.fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ amount]
    exact .frontier amount
  | succ fuel =>
    rw [Agreement.compileEff_onExit _ _ amount]
    apply StageGraph.CodeAt.guardedExit
    · rw [← SourceScope.resolve_at built.program (point.child 0) body (Agreement.at_child found 0)]
      apply StageRequest.body_code built accepted id member (point.child 0) _ _ cells world waiting
      · simp only [Point.child, located, StageRequest.bodyPath]
      · unfold SourceScope.At
        change SourceScope.levelAt (.eff built.program) 0 (point.path ++ [0]) = some point.env.length
        rw [SourceScope.levelAt_suffix _ _ point.path [0] 0 found, sourceOwned]
        rfl
    · intro nextWorld future view exit good
      let refreshed : Point := {point with completed := view}
      let next := refreshed.childWith 1 (reifyExitVal exit)
      have scope : SourceScope.At built.program next := by
        unfold SourceScope.At
        change SourceScope.levelAt (.eff built.program) 0 (point.path ++ [1]) = some (point.env ++ [reifyExitVal exit]).length
        rw [SourceScope.levelAt_suffix _ _ point.path [1] 0 found, sourceOwned]
        simp only [Option.bind_some, SourceScope.levelAt, Node.childLevel, Node.closedChild, Node.binders,
          List.length_append, List.length_singleton]
        rfl
      have prefixHeld : StageRequest.Cells next.env := AnswerSlots.childWith cells 1 _
      have locatedNext : next.path = StageCleanup.path id := by
        simp only [next, refreshed, Point.childWith, located, StageCleanup.path]
      have shape : StageCleanup.UnitKind id (StageGraph.FinalizerKind id exit) := by
        cases exit
        · exact Or.inr rfl
        · exact Or.inl rfl
      exact StageCleanup.cleanup_code built accepted id member next locatedNext scope prefixHeld nextWorld
        (StageGraph.FinalizerKind id exit) shape
end Test.Dogfood.Scenario.Atomic.StageEntry
