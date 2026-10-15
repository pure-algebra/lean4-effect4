import Effect4.Laws.Program.CodeClosure.Qualified.Stored
import Effect4.Laws.Program.CodeClosure.Compile
import Effect4.Laws.Program.CodeClosure.Suspension
import Effect4.Laws.Program.NativeScope

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: callbacks retain supplied source-point and captured-environment assertions.
Consumer: the Prefix callback instance and Timeout's actual attempt-source refinement.
Reach: the existing direct source fragment and the existing native callback definitions.
Limit: this contract supplies neither initialization nor an actual command history.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Effect4.Program.CodeClosure.Qualified
open Effect4 Effect4.Machine Effect4.Program

/-- Source points retain their annotation through the operations used by native callbacks. -/
structure Transport (point : Point → Prop) (env : List Val → Prop) : Prop where
  environment : ∀ {p}, point p → env p.env
  child : ∀ {p}, point p → ∀ index, point (p.child index)
  childWith : ∀ {p}, point p → ∀ index value, point (p.childWith index value)
  capture : ∀ {p}, point p → ∀ value context, point (Point.ofCapture (p.capture value context))

/-- Native asynchronous routing introduces no captured source point. -/
theorem asyncRoute_at (point : Point → Prop) (env : List Val → Prop) (writes : SyncOp → Prop)
    (row : NativeOp) (request : Term) (p : Point) : CodeAt point env writes (asyncRoute row request p) := by
  fun_cases asyncRoute row request p
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [CodeAt, NameAt, StoreNameAt, badShape])

/-- One supplied operation permission extends the existing compiler leaf contract. -/
theorem compile_contract (root : NativeEff) (point : Point → Prop) (env : List Val → Prop) (writes : SyncOp → Prop)
    (transport : Transport point env)
    (operations : ∀ p row request value op,
      Node.at_ (.eff root) p.path = some (.eff (.perform row request)) → point p →
      evalTerm p.env request = some value → row.syncOpOf p.env value = some op →
      OpAt point env writes op) :
    CodeClosure.CompileContract root point (NameAt point env writes) (ThunkAt point env writes) := by
  refine {
    child := ?_, body := ?_, pure := ?_, act := ?_, operation := ?_, asynchronous := ?_,
    cont := ?_, caught := ?_, caughtError := ?_, onValue := ?_, onCause := ?_, fin := ?_,
    forkScoped := ?_, acquire := ?_, service := ?_, provideService := ?_, provideContext := ?_,
    getContext := ?_, captureMask := ?_, park := ?_ }
  case refine_1 => intro p e i found held selected; exact transport.child held i
  case refine_2 => intro p e found held; exact held
  case refine_3 => intro p term found held; exact held
  case refine_4 => intro p e found held; exact held
  case refine_5 =>
    intro p row request value op found held evaluated selected
    exact operations p row request value op found held evaluated selected
  case refine_6 =>
    intro p row request found held
    exact asyncRoute_at point env writes row request p
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [NameAt, ThunkAt, RegionAt]) (add safe apply [transport.child])

/-- Point transport and the existing compiler's leaf contract suffice for actual callback closure. -/
structure Contract (root : NativeEff) (point : Point → Prop) (env : List Val → Prop) (writes : SyncOp → Prop) : Prop where
  compilation : CodeClosure.CompileContract root point (NameAt point env writes) (ThunkAt point env writes)
  child : ∀ {p}, point p → ∀ index, point (p.child index)
  childWith : ∀ {p}, point p → ∀ index value, point (p.childWith index value)
  capture : ∀ {p}, point p → ∀ value context, point (Point.ofCapture (p.capture value context))

/-- A source compilation uses the shared compiler proof without another compiler walk. -/
theorem compile_at (root : NativeEff) (_fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) (writes : SyncOp → Prop) (contract : Contract root point env writes)
    (e : NativeEff) (p : Point) (found : Node.at_ (.eff root) p.path = some (.eff e))
    (held : point p) : CodeAt point env writes (compileEff e p) :=
  CodeClosure.compile_closure contract.compilation e p found held

/-- A shape refusal carries no delayed source point. -/
theorem badShape_at (point : Point → Prop) (env : List Val → Prop) (writes : SyncOp → Prop) : CodeAt point env writes badShape := trivial

/-- Source resolution consumes the same compiler leaf contract. -/
theorem resolve_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) (writes : SyncOp → Prop) (contract : Contract root point env writes)
    (p : Point) (held : point p) : CodeAt point env writes (resolve root p) := by
  unfold resolve
  split
  · rename_i e found
    exact compile_at root fragment point env writes contract e p found held
  · exact badShape_at point env writes

/-- An unbound callback child retains its source assertion. -/
theorem resolve_child_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) (writes : SyncOp → Prop) (contract : Contract root point env writes)
    (p : Point) (index : Nat) (held : point p) : CodeAt point env writes (resolve root (p.child index)) :=
  resolve_at root fragment point env writes contract _ (contract.child held index)

/-- A value callback child retains its source assertion. -/
theorem resolve_arg_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) (writes : SyncOp → Prop) (contract : Contract root point env writes)
    (p : Point) (index : Nat) (value : Val) (held : point p) :
    CodeAt point env writes (resolve root (p.childWith index value)) :=
  resolve_at root fragment point env writes contract _ (contract.childWith held index value)

/-- A direct region consumes the same source assertion. -/
theorem region_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) (writes : SyncOp → Prop) (contract : Contract root point env writes)
    (region : Region) (held : RegionAt point env writes region) : CodeAt point env writes (regionCode root region) := by
  cases region with
  | program p => exact resolve_at root fragment point env writes contract p held
  | build _ _ _ | buildAdding _ _ _ | construct _ _ => exact held.elim

/-- Registering an acquired release retains its actual capture assertion. -/
theorem capture_at (root : NativeEff) (point : Point → Prop) (env : List Val → Prop) (writes : SyncOp → Prop)
    (contract : Contract root point env writes) (p : Point) (value : Val) (ctx : Ctx)
    (held : point p) : FinAt point env writes (.foreign (p.capture value ctx)) := contract.capture held value ctx

/-- A selected arm retains its point with its optional bound value. -/
theorem childBind (root : NativeEff) (point : Point → Prop) (env : List Val → Prop) (writes : SyncOp → Prop)
    (contract : Contract root point env writes) {p : Point} (held : point p) (index : Nat) (value : Option Val) :
    point (p.childBind index value) := by
  cases value with
  | none => exact contract.child held index
  | some value => exact contract.childWith held index value

/-- Native value callbacks build existing code with source-qualified leaves.
Native builders cannot introduce an authored source continuation. -/
structure ValueBuilders (point : Point → Prop) (env : List Val → Prop) (writes : SyncOp → Prop)
    (P : NCode → Prop) : Prop where
  success : ∀ value, P (.success value)
  failure : ∀ cause, P (.failure cause)
  sync : ∀ thunk, ThunkAt point env writes thunk → P (.sync thunk)
  suspend : ∀ thunk, ThunkAt point env writes thunk → P (.suspend thunk)
  withFiber : ∀ thunk, ThunkAt point env writes thunk → P (.withFiber thunk)
  onSuccess : ∀ body name, P body → NameAt point env writes name →
    (∀ source, name ≠ .cont source) → P (.onSuccess body name)
  onSuccessConst : ∀ body next, P body → P next → P (.onSuccessConst body next)
  onFailure : ∀ body name, P body → NameAt point env writes name → P (.onFailure body name)
  onSuccessAndFailure : ∀ body value cause, P body → NameAt point env writes value →
    NameAt point env writes cause → P (.onSuccessAndFailure body value cause)
  onExit : ∀ body name flag, P body → NameAt point env writes name → P (.onExit body name flag)
  exitFrame : ∀ body, P body → P (.exitFrame body)
  setInterruptible : ∀ flag, P (.setInterruptible flag)
  iterator : ∀ name cursor, NameAt point env writes name → P (.iterator name cursor)
  whileLoop : ∀ name cursor, NameAt point env writes name → P (.whileLoop name cursor)
  async : ∀ name flag cancel, NameAt point env writes name →
    (∀ callback ∈ cancel, NameAt point env writes callback) → P (.async name flag cancel)
  asyncFinalizer : ∀ name, NameAt point env writes name → P (.asyncFinalizer name)

/-- Actual source and stored leaves feed the existing native value-callback producer. -/
structure ValueLeaves (root : NativeEff) (point : Point → Prop) (env : List Val → Prop)
    (writes : SyncOp → Prop) (P : NCode → Prop) : Prop where
  argument : ∀ p index value, point p → P (resolve root (p.childWith index value))
  child : ∀ p index, point p → P (resolve root (p.child index))
  region : ∀ region, RegionAt point env writes region → P (regionCode root region)
  stored : ∀ name value, StoreNameAt point env writes name → P (embed (Effect4.Machine.contAOf name value))
  finalizer : ∀ fin exit, FinAt point env writes fin → P (embed (finProgram fin exit))

/-- The single value-callback case analysis consumes supplied source leaves and native builders. -/
theorem contA_with (root : NativeEff)
    (point : Point → Prop) (env : List Val → Prop) (writes : SyncOp → Prop)
    (contract : Contract root point env writes) (P : NCode → Prop)
    (builders : ValueBuilders point env writes P) (leaves : ValueLeaves root point env writes P)
    (name : EffName) (value : Val) (held : NameAt point env writes name) : P (contAOf root name value) := by
  revert held
  fun_cases contAOf root name value
  all_goals intro held
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [leaves.argument, leaves.child, leaves.region, leaves.stored, leaves.finalizer,
      (capture_at root point env writes contract), ThunkAt, NameAt, StoreNameAt, OpAt, RegionAt, Prim.ofExit, badShape]) (add norm unfold [updateThenK, addCurrentMemoMapK, combineWithK, mergeContextsK, serviceLookupK, bindServiceK]) (add safe apply [contract.childWith, leaves.region, builders.success, builders.failure, builders.sync,
      builders.suspend, builders.withFiber, builders.onSuccess, builders.onSuccessConst, builders.onFailure,
      builders.onSuccessAndFailure, builders.onExit, builders.exitFrame, builders.setInterruptible,
      builders.iterator, builders.whileLoop, builders.async, builders.asyncFinalizer])

/-- The existing leaf fold instantiates the parameterized native builders. -/
theorem value_builders (point : Point → Prop) (env : List Val → Prop) (writes : SyncOp → Prop) :
    ValueBuilders point env writes (CodeAt point env writes) where
  success _ := trivial
  failure _ := trivial
  sync _ held := held
  suspend _ held := held
  withFiber _ held := held
  onSuccess _ _ held named _ := ⟨held, named⟩
  onSuccessConst _ _ first next := ⟨first, next⟩
  onFailure _ _ held named := ⟨held, named⟩
  onSuccessAndFailure _ _ _ held value cause := ⟨held, value, cause⟩
  onExit _ _ _ held named := ⟨held, named⟩
  exitFrame _ held := held
  setInterruptible _ := trivial
  iterator _ _ held := held
  whileLoop _ _ held := held
  async _ _ _ held cancel := ⟨held, cancel⟩
  asyncFinalizer _ held := held

/-- Calling any stable value callback retains the original statement through the shared producer. -/
theorem contA_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) (writes : SyncOp → Prop) (contract : Contract root point env writes) (name : EffName) (value : Val) (held : NameAt point env writes name) :
    CodeAt point env writes (contAOf root name value) :=
  contA_with root point env writes contract (CodeAt point env writes) (value_builders point env writes)
    { argument := fun p index value owned => resolve_arg_at root fragment point env writes contract p index value owned
      child := fun p index owned => resolve_child_at root fragment point env writes contract p index owned
      region := fun region owned => region_at root fragment point env writes contract region owned
      stored := fun name value owned => store_contA_at point env writes name value owned
      finalizer := fun fin exit owned => finProgram_at point env writes fin exit owned } name value held

/-- Calling any stable cause callback preserves all delayed source annotations. -/
theorem contE_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) (writes : SyncOp → Prop) (contract : Contract root point env writes) (name : EffName) (cause : CauseV) (held : NameAt point env writes name) :
    CodeAt point env writes (contEOf root name cause) := by
  revert held
  fun_cases contEOf root name cause
  all_goals intro held
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [(resolve_arg_at root fragment point env writes contract), store_contE_at,
    CodeAt, NameAt, Prim.ofExit])

/-- A loop's returned value carries no delayed source point. -/
theorem loopFinish_at (root : NativeEff) (point : Point → Prop) (env : List Val → Prop) (writes : SyncOp → Prop) (p : Point) (cursor : Val) :
    CodeAt point env writes (loopFinishAt root p cursor) := by
  fun_cases loopFinishAt root p cursor
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [CodeAt, badShape_at])

/-- Both branches of a source decision preserve source annotations. -/
theorem select_arg_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) (writes : SyncOp → Prop) (contract : Contract root point env writes) (p : Point) (first : Bool) (bound : Option Val)
    (held : point p) :
    CodeAt point env writes (resolve root (p.childBind (cond first 0 1) bound)) :=
  resolve_at root fragment point env writes contract _ (childBind root point env writes contract held _ bound)

/-- Every loop result retains the source annotation of its body. -/
def LoopAt (point : Point → Prop) (env : List Val → Prop) (writes : SyncOp → Prop) : LoopNext Val NCode → Prop
  | .continue _ body | .finish body => CodeAt point env writes body

/-- Entering an iterate body appends its cursor after source annotations. -/
theorem loopNext_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) (writes : SyncOp → Prop) (contract : Contract root point env writes) (p : Point) (cursor : Val) (held : point p) :
    LoopAt point env writes (loopNextAt root p cursor) := by
  fun_cases loopNextAt root p cursor
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [LoopAt, loopFinish_at, badShape_at]) (add safe apply [(resolve_arg_at root fragment point env writes contract)])

/-- A resumed iterate body starts from the same source annotations. -/
theorem loopResume_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) (writes : SyncOp → Prop) (contract : Contract root point env writes) (p : Point) (cursor answer : Val) (held : point p) :
    LoopAt point env writes (loopResumeAt root p cursor answer) := by
  unfold loopResumeAt
  cases h : loopAt root p with
  | none => exact badShape_at point env writes
  | some row =>
    rcases row with ⟨test, step, body⟩
    simp only []
    cases hstep : evalTerm (p.env ++ [cursor, answer]) step with
    | none => exact badShape_at point env writes
    | some next => exact loopNext_at root fragment point env writes contract p next held

/-- Executing a stable suspended body preserves all delayed source annotations. -/
theorem suspend_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) (writes : SyncOp → Prop) (contract : Contract root point env writes) (thunk : EffThunk) (held : ThunkAt point env writes thunk) :
    CodeAt point env writes (suspendBodyAt root thunk) := by
  cases thunk
  case body p =>
    exact CodeClosure.suspend_body_at root fragment point (CodeAt point env writes)
      { compiled := fun e p found held => compile_at root fragment point env writes contract e p found held
        frontier := fun _ held => held
        child := fun p held => resolve_child_at root fragment point env writes contract p 0 held
        selected := fun p first bound held => select_arg_at root fragment point env writes contract p first bound held
        loop := fun _ _ held => held
        badShape := trivial } p held
  case memoLookup => exact held.elim
  case store stored =>
    cases stored
    case body program => exact progOf_at point env writes program held
    case foreign capture exit => exact ⟨trivial, held⟩
    all_goals trivial
  all_goals trivial
/-- Actual asynchronous cancellation introduces no captured source point. -/
theorem cancel_at (point : Point → Prop) (env : List Val → Prop) (writes : SyncOp → Prop) (name : EffName) :
    CodeAt point env writes (cancelProgramOf name) := by
  fun_cases cancelProgramOf name
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [CodeAt, ThunkAt, OpAt, store_cancel_at])

/-- Callback invocation refreshes completed exits in these source point annotations. -/
def ViewStable (point : Point → Prop) : Prop :=
  ∀ p, point p → ∀ completed, point {p with completed}

/-- Actual value invocation preserves the annotation under the current completed-exit view. -/
theorem interp_contA_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) (writes : SyncOp → Prop) (contract : Contract root point env writes)
    (stable : ViewStable point) (completed) (table : RowTable)
    (name : EffName) (value : Val) (owned : NameAt point env writes name) :
    CodeAt point env writes ((interpAt root completed table).contA name value) := by
  apply contA_at root fragment point env writes contract
  cases name
  case cont p | onValue p => exact stable p owned completed
  case releaseBody p exit previous => exact stable p owned completed
  all_goals exact owned

/-- Actual cause invocation preserves the annotation under the current completed-exit view. -/
theorem interp_contE_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) (writes : SyncOp → Prop) (contract : Contract root point env writes)
    (stable : ViewStable point) (completed) (table : RowTable)
    (name : EffName) (cause : CauseV) (owned : NameAt point env writes name) :
    CodeAt point env writes ((interpAt root completed table).contE name cause) := by
  apply contE_at root fragment point env writes contract
  cases name
  case caught p | caughtError p | onCause p => exact stable p owned completed
  all_goals exact owned

/-- Actual suspended invocation preserves the annotation under the current completed-exit view. -/
theorem interp_suspend_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) (writes : SyncOp → Prop) (contract : Contract root point env writes)
    (stable : ViewStable point) (completed) (table : RowTable)
    (thunk : EffThunk) (owned : ThunkAt point env writes thunk) :
    CodeAt point env writes ((interpAt root completed table).suspendBody thunk) := by
  apply suspend_at root fragment point env writes contract
  cases thunk
  case body p => exact stable p owned completed
  all_goals exact owned

end Effect4.Program.CodeClosure.Qualified
