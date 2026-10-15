import Test.Dogfood.Scenario.Atomic.RootGraph
import Test.Dogfood.Scenario.Atomic.DaemonHead
import Effect4.Laws.Machine.AnswerFlowHead

/-!
Concept: store-typing R4.
Consumer: the actual Atomic root primitive evaluator and its coupled child-role assignment.
The fixed root source sequence exposes actual fork, wait, sleep, interruption and read heads.
No second compiler traversal occurs here.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.RootGraph
open Effect4 Effect4.Machine Effect4.Program Effect4.Machine.AnswerFlow
open StageWorld

/-- Ignored native root code uses the existing stable daemon head through one answer-class embedding. -/
theorem ignored_head (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (view : List (FiberId × ExitV)) (code : NCode) (held : DaemonGraph.CodeAt root table code) :
    HeadAt (model root table view) (interpAt root view table).toPrimInterp (Edge root table)
      world .ordinary code :=
  (ignored_embedding root table view).head_over (interpAt root view table).toPrimInterp
    (Semantic root table) (DaemonGraph.Edge root table) world trivial () code
    (DaemonGraph.head root table world code held view)

/-- The actual fork body retains the root binder that must receive its new child handle. -/
theorem fork_body (root : NativeEff) (table : RowTable) (world : StageWorld.World) (point : Point)
    (held : PointAt root world point) (body : NativeEff) (options : Supervision.ForkOptions) :
    CodeAt root table world (.rootAnswer point.env.length) (compileEff (.withFiber (.fork body options)) (point.child 0)) := by
  cases fuel : (point.child 0).fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ fuel]
    exact .frontier fuel
  | succ remaining =>
    simp only [compileEff, fuel]
    exact .action held

/-- The root's final interruption retains its actual source action and ignored binder answer. -/
theorem interrupt_body (root : NativeEff) (table : RowTable) (world : StageWorld.World) (point : Point)
    (held : PointAt root world point) :
    CodeAt root table world (.rootAnswer point.env.length)
      (compileEff (.withFiber (.interrupt (.var 3))) (point.child 0)) := by
  cases fuel : (point.child 0).fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ fuel]
    exact .frontier fuel
  | succ remaining =>
    simp only [compileEff, fuel]
    exact .action held

/-- A real root await reads its captured handle and accepts the exit representation it requested. -/
theorem await_body (root : NativeEff) (table : RowTable) (world : StageWorld.World) (point : Point)
    (held : PointAt root world point) (slot : Nat)
    (source : (9 ≤ point.env.length ∧ point.env.length < 14 ∧ slot = point.env.length - 5) ∨
      (point.env.length = 16 ∧ slot = 15)) :
    CodeAt root table world (.rootAnswer point.env.length) (compileEff (.awaitFiber (.var slot) .awaitValue) (point.child 0)) := by
  obtain ⟨target, captured⟩ := await_target point held.2.1 slot source
  have late : 9 ≤ point.env.length := by rcases source with early | late <;> omega
  have notFork : point.env.length ≠ 15 := by rcases source with early | late <;> omega
  have counter : world.nextId = RootSlots.rank (point.env.length + 1) :=
    held.2.2.2.2.trans (RootSlots.rank_unchanged point.env.length late notFork).symm
  have ignored := ignored_binder point.env.length late notFork
  cases fuel : (point.child 0).fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ fuel]
    exact .frontier fuel
  | succ remaining =>
    simp only [compileEff, fuel, evalTerm, show (point.child 0).env = point.env from rfl, captured]
    change CodeAt root table world (.rootAnswer point.env.length) (match (point.child 0).awaitExit target .awaitValue with | some exit => Prim.ofExit exit | none => .suspend (.park (.join target .awaitValue)))
    cases cached : (point.child 0).awaitExit target .awaitValue with
    | none => exact .await counter ignored
    | some exit =>
      cases exit with
      | success value => exact .success (ignored_answer world _ value counter ignored)
      | failure cause => exact .failure

/-- The actual root sleep retains the same allocation counter across its native timer answer. -/
theorem sleep_body (root : NativeEff) (table : RowTable) (world : StageWorld.World) (point : Point)
    (held : PointAt root world point) (atSleep : point.env.length = 14) :
    CodeAt root table world (.rootAnswer point.env.length)
      (compileEff (.perform .sleep (.lit (.nat 1500))) (point.child 0)) := by
  have counter : world.nextId = RootSlots.rank (point.env.length + 1) := by
    have previous := held.2.2.2.2
    rw [atSleep] at previous ⊢
    exact previous
  cases fuel : (point.child 0).fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ fuel]
    exact .frontier fuel
  | succ remaining =>
    simp only [compileEff, fuel, NativeOp.kind, asyncRoute, evalTerm]
    exact .sleep counter (by rw [atSleep]; rfl)
/-- A real root binder enters its actual body and saves the exact next-handle continuation. -/
theorem bind_head (root : NativeEff) (table : RowTable) (world : StageWorld.World) (view : List (FiberId × ExitV))
    (point : Point) (first rest : NativeEff) (held : PointAt root world point)
    (found : Node.at_ (.eff root) point.path = some (.eff (.bind first rest)))
    (remaining : point.env.length < 18)
    (body : CodeAt root table world (.rootAnswer point.env.length) (compileEff first (point.child 0))) :
    HeadAt (model root table view) (interpAt root view table).toPrimInterp (Edge root table)
      world .ordinary (resolve root point) := by
  rw [SourceScope.resolve_at _ _ _ found]
  cases amount : point.fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ amount]
    apply HeadAt.suspend
    change CodeAt root table world .ordinary (suspendBodyAt root (.body { point with completed := view }))
    simp only [suspendBodyAt, amount]
    exact .frontier rfl
  | succ fuel =>
    rw [Agreement.compileEff_bind _ _ amount]
    exact .onSuccess _ _ _ body (cont_edge root table world point first rest held found remaining _)

/-- Every actual root source entry exposes its fixed native head with its saved handle contract. -/
theorem entry_head (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (world : StageWorld.World) (point : Point) (held : PointAt built.program world point) (view : List (FiberId × ExitV)) :
    HeadAt (model built.program built.table view) (interpAt built.program view built.table).toPrimInterp
      (Edge built.program built.table) world .ordinary (resolve built.program point) := by
  have shapes := RootSource.forms built accepted point.env.length held.2.2.1 held.2.2.2.1
  rcases shapes with fork | awaiting | sleeping | interrupting | reading
  · obtain ⟨body, options, rest, position, found⟩ := fork
    rw [← held.2.1.2] at found
    exact bind_head built.program built.table world view point _ rest held found (by rcases position with early | late <;> omega)
      (fork_body built.program built.table world point held body options)
  · obtain ⟨slot, rest, position, found⟩ := awaiting
    rw [← held.2.1.2] at found
    exact bind_head built.program built.table world view point _ rest held found (by rcases position with early | late <;> omega)
      (await_body built.program built.table world point held slot position)
  · obtain ⟨rest, position, found⟩ := sleeping
    rw [← held.2.1.2] at found
    exact bind_head built.program built.table world view point _ rest held found (by omega)
      (sleep_body built.program built.table world point held position)
  · obtain ⟨rest, position, found⟩ := interrupting
    rw [← held.2.1.2] at found
    exact bind_head built.program built.table world view point _ rest held found (by omega)
      (interrupt_body built.program built.table world point held)
  · obtain ⟨position, found⟩ := reading
    rw [← held.2.1.2] at found
    have captured : point.env[0]? = some (.cell ⟨0⟩) := held.2.1.1 0 _ rfl (by have lower := held.2.2.1; omega)
    rw [SourceScope.resolve_at _ _ _ found]
    cases amount : point.fuel with
    | zero =>
      rw [Agreement.compileEff_at_zero _ amount]
      apply HeadAt.suspend
      change CodeAt built.program built.table world .ordinary (suspendBodyAt built.program (.body { point with completed := view }))
      simp only [suspendBodyAt, amount]
      exact .frontier rfl
    | succ fuel =>
      simp only [compileEff, amount, evalTerm, captured]
      exact .sync _ True.intro
/-- Every actual root current annotation exposes its existing source or ignored native head. -/
theorem head (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (world : StageWorld.World) (kind : StageWorld.Kind) (code : NCode)
    (held : CodeAt built.program built.table world kind code) (owns : Owns kind)
    (view : List (FiberId × ExitV)) :
    HeadAt (model built.program built.table view) (interpAt built.program view built.table).toPrimInterp
      (Edge built.program built.table) world kind code := by
  cases held with
  | ignored held => exact ignored_head built.program built.table world view _ held
  | success good => exact .success _ good
  | failure => exact .failure _ True.intro
  | entry owned => exact entry_head built accepted world _ owned view
  | frontier zero =>
    apply HeadAt.suspend
    change CodeAt built.program built.table world kind (suspendBodyAt built.program (.body _))
    simp only [suspendBodyAt, zero]
    exact .frontier rfl
  | action owned => exact .withFiber _ .failure
  | await counter ignored => exact .suspend _ .failure
  | sleep counter ignored => exact .async _ _ _ (.sleep counter ignored)
  | read => exact .sync _ True.intro
  | interrupting counter ignored => exact .withFiber _ .failure
  | join target mode captured => exact .suspend _ .failure
  | awaitAll targets captured => exact .suspend _ .failure
  | pause => exact .yieldNowWith _ .pause
  | pausing localKind next =>
    exact .onSuccessConst _ _ _ (CodeAt.pause)
      (pause_edge built.program built.table world _ localKind _ _ next)
  | bound localKind first callback =>
    exact .onSuccess _ _ _ first
      (bound_edge built.program built.table world _ _ _ _ localKind owns callback)

end Test.Dogfood.Scenario.Atomic.RootGraph
