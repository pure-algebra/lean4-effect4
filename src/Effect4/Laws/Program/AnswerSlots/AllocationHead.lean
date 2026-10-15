import Effect4.Laws.Program.AnswerSlots.AllocationFamily
import Effect4.Laws.Program.AnswerSlots.AllocationPhases
import Effect4.Laws.Machine.AnswerFlowHead
import Effect4.Laws.Machine.AnswerFlowFrames

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: initializer head entry retains exact pending allocation provenance.
Reach: actual saved callbacks and synthetic yield frames at every interpreter view.
Consumer: the common allocation native producer for Atomic and Timeout entry.
These local head facts do not establish a machine history.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.AllocationAdapter
open Effect4 Effect4.Machine Effect4.Program Effect4.Contracts

/-- A pending synthetic yield returns to the same exact heap and actual suspended code. -/
theorem yield_edge (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (world : World) (kind : Kind spec.stable.Kind) (priority : Nat) (next : NCode)
    (owned : CodeAt spec world kind next) :
    Edge spec fragment world (.yielded world.state.refs.length world.state.deferreds.cells.length) kind
      (.onSuccessConst (.yieldNowWith priority) next) := by
  apply AnswerFlow.EmbeddedEdgeOver.saved
  refine Semantic.saved ?_ (Or.inr (Or.inr ⟨_, _, priority, next, rfl, rfl⟩))
  refine ⟨?_, ?_, ?_⟩
  · intro view
    apply AnswerFlow.saved_constant (model spec view) (interpAt spec.root view spec.table).toPrimInterp
      world (.yielded world.state.refs.length world.state.deferreds.cells.length) kind (.yieldNowWith priority) next
    · intro nextWorld future answer good
      exact code_rebase spec world kind next owned nextWorld future good.2.1.symm good.2.2.1.symm
        good.2.2.2.2.2 (good.2.2.2.2.1.trans
          (congrArg (Initialization.values spec.initialization) good.2.1.symm))
    · intro _ _ _ good
      exact good
  · intro name cursor equal
    cases equal
  · intro name cursor equal
    cases equal

/-- Actual initializer children retain their native allocation rather than a pure fallback answer. -/
theorem allocation_code (spec : Spec) (world : World) (index : Nat) (point : Point)
    (small : index < spec.initialization.width) (stage : RootStage spec world index point) :
    CodeAt spec world (.allocated index)
      (compileEff (.perform .refMake (spec.initialization.request index)) (point.child 0)) := by
  cases amount : (point.child 0).fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ amount]
    exact .frontier amount (.inl stage.owner)
  | succ fuel =>
    rw [spec.initialization.operation index (point.child 0) fuel small amount]
    exact .allocating small stage

/-- The optional gate uses its actual deferred allocation and the same root provenance. -/
theorem gate_code (spec : Spec) (world : World) (point : Point)
    (stage : RootStage spec world spec.initialization.width point)
    (gate : Gate spec.root spec.initialization.width spec.bindings) (present : spec.gate = some gate) :
    CodeAt spec world .gate
      (compileEff (.perform (.deferredMakeOf gate.valueType gate.errorType) (.lit .unit)) (point.child 0)) := by
  cases amount : (point.child 0).fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ amount]
    exact .frontier amount (.inl stage.owner)
  | succ fuel =>
    rw [Agreement.compileEff_perform_sync _ _ amount rfl]
    apply CodeAt.gateAllocating stage
    rw [present]
    rfl

/-- A source frontier suspends without changing its current answer class. -/
theorem frontier_code (spec : Spec) (view : List (FiberId × ExitV)) (world : World)
    (kind : Kind spec.stable.Kind) (point : Point) (zero : point.fuel = 0) (phase : Phase spec world) :
    CodeAt spec world kind ((interpAt spec.root view spec.table).suspendBody (.body point)) := by
  change CodeAt spec world kind (suspendBodyAt spec.root (.body {point with completed := view}))
  simp only [suspendBodyAt, zero]
  exact .frontier rfl phase

/-- An actual prefix root exposes its structured allocation callback to the existing head contract. -/
theorem initial_head (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (view : List (FiberId × ExitV)) (world : World) (index : Nat) (point : Point)
    (stage : RootStage spec world index point) (active : Active spec index) :
    AnswerFlow.HeadAt (model spec view) (interpAt spec.root view spec.table).toPrimInterp
      (Edge spec fragment) world (.stable spec.stable.rootKind) (resolve spec.root point) := by
  change AnswerFlow.HeadAt (model spec view) (interpAt spec.root view spec.table).toPrimInterp
    (Edge spec fragment) world (.stable spec.stable.rootKind) (resolve spec.stable.root point)
  cases amount : point.fuel with
  | zero =>
    unfold resolve
    split
    · rw [Agreement.compileEff_at_zero _ amount]
      exact .suspend _ (frontier_code spec view world _ point amount (.inl stage.owner))
    · exact .failure _ (.inl stage.owner)
  | succ fuel =>
    by_cases small : index < spec.initialization.width
    · rw [spec.initialization.compile index point fuel small stage.stage.source.2.1 amount]
      refine .onSuccess (Kind.allocated index) _ _ (allocation_code spec world index point small stage) ?_
      exact .saved (.allocation world index point _ small stage ((model spec view).future_refl world))
    · have last : index = spec.initialization.width := by
        have bound := stage.stage.source.1
        omega
      subst index
      have available : spec.gate.isSome = true := active.resolve_left small
      cases present : spec.gate with
      | none => rw [present] at available; cases available
      | some gate =>
        obtain ⟨tail, found⟩ := gate.head
        rw [← stage.stage.source.2.1] at found
        rw [Agreement.resolve_of_at found, Agreement.compileEff_bind _ _ amount]
        refine .onSuccess Kind.gate _ _ (gate_code spec world point stage gate present) ?_
        exact .saved (.gate world point _ stage gate present ((model spec view).future_refl world))

/-- Native entry distinguishes the exact boundary marker from an ordinary current head.
The caller activates that marker jointly with its numeric invariant before evaluating it. -/
theorem head_or_entry (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (view : List (FiberId × ExitV)) (world : World) (kind : Kind spec.stable.Kind) (program : NCode)
    (owned : CodeAt spec world kind program) (noSync : ∀ thunk, program ≠ .sync thunk) :
    AnswerFlow.HeadAt (model spec view) (interpAt spec.root view spec.table).toPrimInterp
      (Edge spec fragment) world kind program ∨
    ∃ point, kind = .stable spec.stable.rootKind ∧ program = resolve spec.root point ∧ Entry spec world point := by
  cases owned with
  | success good => exact .inl (.success _ good)
  | failure phase => exact .inl (.failure _ phase)
  | initial stage active => exact .inl (initial_head spec fragment view world _ _ stage active)
  | allocating small stage | reading phase refs deferred pending contents entered => exact (noSync _ rfl).elim
  | gateAllocating stage available => exact (noSync _ rfl).elim
  | entered fragment entry => exact .inr ⟨_, rfl, rfl, entry⟩
  | stable ready held =>
    exact .inl (AnswerFlow.FamilyEmbedding.head_over (interpAt spec.root view spec.table).toPrimInterp
      (embedding spec view) (Semantic spec) (spec.laws fragment).Edge world ready _ program
      ((spec.laws fragment).head view _ program held))
  | frontier zero phase => exact .inl (.suspend _ (frontier_code spec view world kind _ zero phase))
  | yielding phase refs deferred pending contents entered =>
    exact .inl (.yieldNowWith _ (.yielding phase refs deferred pending contents entered))
  | yieldThen phase held pending =>
    apply Or.inl
    by_cases ready : Ready spec world
    · refine .onSuccessConst (Kind.stable spec.stable.rootKind) _ _ (.stable ready (spec.yield_code _)) ?_
      apply AnswerFlow.EmbeddedEdgeOver.saved
      refine Semantic.saved ?_ (Or.inl ready)
      refine ⟨?_, ?_, ?_⟩
      · intro nextView
        apply AnswerFlow.saved_constant
        · intro nextWorld future answer good
          exact code_future_ready spec world kind _ held nextWorld future ready
        · intro _ _ _ good
          exact good
      · intro name cursor equal
        cases equal
      · intro name cursor equal
        cases equal
    · obtain ⟨entered, contents⟩ := pending ready
      exact .onSuccessConst (Kind.yielded world.state.refs.length world.state.deferreds.cells.length) _ _
        (.yielding phase rfl rfl ready contents entered) (yield_edge spec fragment world kind _ _ held)

/-- The actual closed root starts with the empty exact reference prefix. -/
theorem initial_code (spec : Spec) (state : Stores) (fuel : Nat) (tape : List Bool)
    (refs : state.refs = []) (deferreds : state.deferreds.cells.length = 0) :
    CodeAt spec ⟨⟨0⟩, state, false⟩ (.stable spec.stable.rootKind)
      (compileEff spec.root (rootPoint fuel tape)) := by
  change CodeAt spec ⟨⟨0⟩, state, false⟩ (.stable spec.stable.rootKind) (resolve spec.root (rootPoint fuel tape))
  apply CodeAt.initial (index := 0)
  · refine ⟨rfl, ?_, deferreds, rfl⟩
    rw [refs]
    exact Initialization.exact_start spec.initialization fuel tape
  · exact .inl spec.positive

end Effect4.Program.AnswerSlots.AllocationAdapter
