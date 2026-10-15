import Test.Dogfood.Scenario.Atomic.DaemonGraph

/-!
Concept: store-typing R4.
Consumer: the Atomic daemon native producer and actual history lift.
The finite daemon heads use the shared saved-family algebra and real recursive hook.
No compiler walk or callback traversal is repeated.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.DaemonGraph
open Effect4 Effect4.Machine Effect4.Program Effect4.Machine.AnswerFlow
open StageWorld

/-- Daemon saved binders retain their actual callbacks across all completed views. -/
theorem bound_edge (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (first : NCode) (name : EffName)
    (callback : ∀ view value, CodeAt root table ((interpAt root view table).contA name value)) :
    Edge root table world () () (.onSuccess first name) := by
  apply RecursiveFamilyEdge.saved
  constructor
  · intro view
    apply saved_success (model root table view) (interpAt root view table).toPrimInterp
    · intro after future answer good
      exact callback view answer
    · intro after future cause good
      exact True.intro
  · intro name cursor equal
    cases equal
  · intro name cursor equal
    cases equal

/-- A scheduler or cancellation wrapper resumes its actual already-certified next program. -/
theorem constant_edge (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (first next : NCode) (held : CodeAt root table next) :
    Edge root table world () () (.onSuccessConst first next) := by
  apply RecursiveFamilyEdge.saved
  constructor
  · intro view
    apply saved_constant (model root table view) (interpAt root view table).toPrimInterp
    · intro after future answer good
      exact held
    · intro after future cause good
      exact True.intro
  · intro name cursor equal
    cases equal
  · intro name cursor equal
    cases equal

/-- The actual sleep callback enters the one source refill operation. -/
theorem body_callback (root : NativeEff) (table : RowTable) (point : Point)
    (held : BodyPoint root point) (view : List (FiberId × ExitV)) (value : Val) :
    CodeAt root table ((interpAt root view table).contA (.cont point) value) := by
  change CodeAt root table (resolve root (({point with completed := view} : Point).childWith 1 value))
  exact .update (body_update root {point with completed := view} held value)

/-- The actual daemon sleep compiles to its native timer, or to the live fuel frontier. -/
theorem sleep_code (root : NativeEff) (table : RowTable) (point : Point) :
    CodeAt root table (compileEff (.perform .sleep (.lit (.nat 1000))) point) := by
  cases amount : point.fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ amount]
    exact .frontier amount
  | succ fuel =>
    simp only [compileEff, amount, NativeOp.kind, asyncRoute, evalTerm]
    exact .sleep

/-- The actual daemon loop suspension starts its checked recursive name. -/
theorem entry_suspend (root : NativeEff) (table : RowTable) (point : Point)
    (held : LoopPoint root point) : CodeAt root table (suspendBodyAt root (.body point)) := by
  cases amount : point.fuel with
  | zero =>
    simp only [suspendBodyAt, amount]
    exact .frontier amount
  | succ fuel =>
    simp only [suspendBodyAt, amount, held.1, DaemonSource.program, evalTerm, Lit.toVal]
    exact .loop held _

/-- Each actual daemon source entry exposes its single native head. -/
theorem entry_head (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (point : Point) (held : LoopPoint root point) (view : List (FiberId × ExitV)) :
    HeadAt (model root table view) (interpAt root view table).toPrimInterp (Edge root table)
      world () (resolve root point) := by
  rw [SourceScope.resolve_at _ _ _ held.1]
  cases amount : point.fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ amount]
    apply HeadAt.suspend
    exact entry_suspend root table {point with completed := view} held
  | succ fuel =>
    simp only [DaemonSource.program, compileEff, amount]
    apply HeadAt.suspend
    exact entry_suspend root table {point with completed := view} held

/-- The daemon body pushes its actual sleep continuation with the captured window cell. -/
theorem body_head (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (point : Point) (held : BodyPoint root point) (view : List (FiberId × ExitV)) :
    HeadAt (model root table view) (interpAt root view table).toPrimInterp (Edge root table)
      world () (resolve root point) := by
  rw [SourceScope.resolve_at _ _ _ held.1]
  cases amount : point.fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ amount]
    apply HeadAt.suspend
    change CodeAt root table (suspendBodyAt root (.body {point with completed := view}))
    simp only [suspendBodyAt, amount]
    exact .frontier rfl
  | succ fuel =>
    rw [show DaemonSource.body = .bind (.perform .sleep (.lit (.nat 1000)))
      (.perform (.refUpdateWith (Store.refillAt 5)) (.var 0)) from rfl,
      Agreement.compileEff_bind _ _ amount]
    exact .onSuccess () _ _ (sleep_code root table (point.child 0))
      (bound_edge root table world _ _ (body_callback root table point held))
/-- The actual daemon refill source exposes its captured window operation. -/
theorem update_head (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (point : Point) (held : UpdatePoint root point) (view : List (FiberId × ExitV)) :
    HeadAt (model root table view) (interpAt root view table).toPrimInterp (Edge root table)
      world () (resolve root point) := by
  rw [SourceScope.resolve_at _ _ _ held.1]
  cases amount : point.fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ amount]
    apply HeadAt.suspend
    change CodeAt root table (suspendBodyAt root (.body {point with completed := view}))
    simp only [suspendBodyAt, amount]
    exact .frontier rfl
  | succ fuel =>
    have captured : point.env[0]? = some (.cell ⟨0⟩) := held.2.2.read 0 (by decide)
    simp only [compileEff, amount, NativeOp.kind, evalTerm, captured, NativeOp.syncOpOf]
    exact .sync _ True.intro

/-- Every daemon current-code certificate supplies its actual native head. -/
theorem head (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (code : NCode) (held : CodeAt root table code) (view : List (FiberId × ExitV)) :
    HeadAt (model root table view) (interpAt root view table).toPrimInterp (Edge root table) world () code := by
  cases held with
  | success value => exact .success value True.intro
  | failure cause => exact .failure cause True.intro
  | entry owned => exact entry_head root table world _ owned view
  | body owned => exact body_head root table world _ owned view
  | update owned => exact update_head root table world _ owned view
  | @loop point owned cursor =>
    apply HeadAt.whileLoop
    · intro next body actual
      change loopNextAt root { point with completed := view } cursor = .continue next body at actual
      rw [loop_next root {point with completed := view} owned cursor] at actual
      cases actual
      exact ⟨(), CodeAt.body (loop_body root {point with completed := view} owned cursor),
        .cons (.loop cursor owned) (.nil ())⟩
    · intro body actual
      change loopNextAt root { point with completed := view } cursor = .finish body at actual
      rw [loop_next root {point with completed := view} owned cursor] at actual
      cases actual
  | @frontier point zero =>
    apply HeadAt.suspend
    change CodeAt root table (suspendBodyAt root (.body { point with completed := view }))
    simp only [suspendBodyAt, zero]
    exact .frontier rfl
  | suspended next => exact .suspend _ (next view)
  | sleep => exact .async _ _ _ CodeAt.sleep
  | refill length => exact .sync _ True.intro
  | cancelClock waiter token => exact .sync _ True.intro
  | join target mode => exact .suspend _ (.failure _)
  | awaitAll targets => exact .suspend _ (.failure _)
  | interruptAll targets who => exact .withFiber _ (.failure _)
  | dropObservers token => exact .withFiber _ (.failure _)
  | constant first next => exact .onSuccessConst () _ _ first (constant_edge root table world _ _ next)
  | pause priority => exact .yieldNowWith priority (.pause priority)
  | bound first callback => exact .onSuccess () _ _ first (bound_edge root table world _ _ callback)
end Test.Dogfood.Scenario.Atomic.DaemonGraph
