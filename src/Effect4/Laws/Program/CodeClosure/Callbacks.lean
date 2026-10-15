import Effect4.Laws.Program.CodeClosure.Stored
import Effect4.Laws.Program.CodeClosure.Compile
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
namespace Effect4.Program.CodeClosure.Slots
open Effect4 Effect4.Machine Effect4.Program

/-- Source points retain their annotation through the operations used by native callbacks. -/
structure Transport (point : Point → Prop) (env : List Val → Prop) : Prop where
  environment : ∀ {p}, point p → env p.env
  child : ∀ {p}, point p → ∀ index, point (p.child index)
  childWith : ∀ {p}, point p → ∀ index value, point (p.childWith index value)
  capture : ∀ {p}, point p → ∀ value context, point (Point.ofCapture (p.capture value context))

/-- Actual synchronous source leaves retain the environment assertion in every stored update. -/
theorem operation_at (point : Point → Prop) (env : List Val → Prop) (bindings : List Val)
    (row : NativeOp) (value : Val) (operation : SyncOp)
    (held : env bindings) (answer : row.syncOpOf bindings value = some operation) : OpAt point env operation := by
  fun_cases NativeOp.syncOpOf row bindings value
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [NativeOp.syncOpOf, OpAt])

/-- Native asynchronous routing introduces no captured source point. -/
theorem asyncRoute_at (point : Point → Prop) (env : List Val → Prop)
    (row : NativeOp) (request : Term) (p : Point) : CodeAt point env (asyncRoute row request p) := by
  fun_cases asyncRoute row request p
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [CodeAt, NameAt, StoreNameAt, badShape])

/-- Point transport discharges the existing compiler's local leaf contract. -/
theorem compile_contract (root : NativeEff) (point : Point → Prop) (env : List Val → Prop)
    (transport : Transport point env) :
    CodeClosure.CompileContract root point (NameAt point env) (ThunkAt point env) := by
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
    exact operation_at point env p.env row value op (transport.environment held) selected
  case refine_6 =>
    intro p row request found held
    exact asyncRoute_at point env row request p
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [NameAt, ThunkAt, RegionAt]) (add safe apply [transport.child])

/-- Point transport and the existing compiler's leaf contract suffice for actual callback closure. -/
structure Contract (root : NativeEff) (point : Point → Prop) (env : List Val → Prop) : Prop where
  compilation : CodeClosure.CompileContract root point (NameAt point env) (ThunkAt point env)
  child : ∀ {p}, point p → ∀ index, point (p.child index)
  childWith : ∀ {p}, point p → ∀ index value, point (p.childWith index value)
  capture : ∀ {p}, point p → ∀ value context, point (Point.ofCapture (p.capture value context))

/-- One point-transport certificate supplies both compiler and callback closure. -/
theorem Contract.of_transport (root : NativeEff) (point : Point → Prop) (env : List Val → Prop)
    (transport : Transport point env) : Contract root point env where
  compilation := compile_contract root point env transport
  child := transport.child
  childWith := transport.childWith
  capture := transport.capture

/-- A source compilation uses the shared compiler proof without another compiler walk. -/
theorem compile_at (root : NativeEff) (_fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) (contract : Contract root point env)
    (e : NativeEff) (p : Point) (found : Node.at_ (.eff root) p.path = some (.eff e))
    (held : point p) : CodeAt point env (compileEff e p) :=
  CodeClosure.compile_closure contract.compilation e p found held

/-- A shape refusal carries no delayed source point. -/
theorem badShape_at (point : Point → Prop) (env : List Val → Prop) : CodeAt point env badShape := trivial

/-- Source resolution consumes the same compiler leaf contract. -/
theorem resolve_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) (contract : Contract root point env)
    (p : Point) (held : point p) : CodeAt point env (resolve root p) := by
  unfold resolve
  split
  · rename_i e found
    exact compile_at root fragment point env contract e p found held
  · exact badShape_at point env

/-- An unbound callback child retains its source assertion. -/
theorem resolve_child_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) (contract : Contract root point env)
    (p : Point) (index : Nat) (held : point p) : CodeAt point env (resolve root (p.child index)) :=
  resolve_at root fragment point env contract _ (contract.child held index)

/-- A value callback child retains its source assertion. -/
theorem resolve_arg_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) (contract : Contract root point env)
    (p : Point) (index : Nat) (value : Val) (held : point p) :
    CodeAt point env (resolve root (p.childWith index value)) :=
  resolve_at root fragment point env contract _ (contract.childWith held index value)

/-- A direct region consumes the same source assertion. -/
theorem region_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) (contract : Contract root point env)
    (region : Region) (held : RegionAt point env region) : CodeAt point env (regionCode root region) := by
  cases region with
  | program p => exact resolve_at root fragment point env contract p held
  | build _ _ _ | buildAdding _ _ _ | construct _ _ => exact held.elim

/-- Registering an acquired release retains its actual capture assertion. -/
theorem capture_at (root : NativeEff) (point : Point → Prop) (env : List Val → Prop)
    (contract : Contract root point env) (p : Point) (value : Val) (ctx : Ctx)
    (held : point p) : FinAt point env (.foreign (p.capture value ctx)) := contract.capture held value ctx

/-- A selected arm retains its point with its optional bound value. -/
theorem childBind (root : NativeEff) (point : Point → Prop) (env : List Val → Prop)
    (contract : Contract root point env) {p : Point} (held : point p) (index : Nat) (value : Option Val) :
    point (p.childBind index value) := by
  cases value with
  | none => exact contract.child held index
  | some value => exact contract.childWith held index value

/-- Calling any stable value callback preserves all delayed source annotations. -/
theorem contA_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) (contract : Contract root point env) (name : EffName) (value : Val) (held : NameAt point env name) :
    CodeAt point env (contAOf root name value) := by
  revert held
  fun_cases contAOf root name value
  all_goals intro held
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [(resolve_arg_at root fragment point env contract), (resolve_child_at root fragment point env contract),
    (region_at root fragment point env contract), store_contA_at, finProgram_at, (capture_at root point env contract), CodeAt, ThunkAt,
    NameAt, StoreNameAt, OpAt, RegionAt, Prim.ofExit, badShape_at]) (add norm unfold [updateThenK, addCurrentMemoMapK, combineWithK, mergeContextsK,
      serviceLookupK, bindServiceK]) (add safe apply [contract.childWith, (region_at root fragment point env contract)])

/-- Calling any stable cause callback preserves all delayed source annotations. -/
theorem contE_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) (contract : Contract root point env) (name : EffName) (cause : CauseV) (held : NameAt point env name) :
    CodeAt point env (contEOf root name cause) := by
  revert held
  fun_cases contEOf root name cause
  all_goals intro held
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [(resolve_arg_at root fragment point env contract), store_contE_at,
    CodeAt, NameAt, Prim.ofExit])

/-- A loop's returned value carries no delayed source point. -/
theorem loopFinish_at (root : NativeEff) (point : Point → Prop) (env : List Val → Prop) (p : Point) (cursor : Val) :
    CodeAt point env (loopFinishAt root p cursor) := by
  fun_cases loopFinishAt root p cursor
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [CodeAt, badShape_at])

/-- Both branches of a source decision preserve source annotations. -/
theorem select_arg_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) (contract : Contract root point env) (p : Point) (first : Bool) (bound : Option Val)
    (held : point p) :
    CodeAt point env (resolve root (p.childBind (cond first 0 1) bound)) :=
  resolve_at root fragment point env contract _ (childBind root point env contract held _ bound)

/-- Every loop result retains the source annotation of its body. -/
def LoopAt (point : Point → Prop) (env : List Val → Prop) : LoopNext Val NCode → Prop
  | .continue _ body | .finish body => CodeAt point env body

/-- Entering an iterate body appends its cursor after source annotations. -/
theorem loopNext_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) (contract : Contract root point env) (p : Point) (cursor : Val) (held : point p) :
    LoopAt point env (loopNextAt root p cursor) := by
  fun_cases loopNextAt root p cursor
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [LoopAt, loopFinish_at, badShape_at]) (add safe apply [(resolve_arg_at root fragment point env contract)])

/-- A resumed iterate body starts from the same source annotations. -/
theorem loopResume_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) (contract : Contract root point env) (p : Point) (cursor answer : Val) (held : point p) :
    LoopAt point env (loopResumeAt root p cursor answer) := by
  unfold loopResumeAt
  cases h : loopAt root p with
  | none => exact badShape_at point env
  | some row =>
    rcases row with ⟨test, step, body⟩
    simp only []
    cases hstep : evalTerm (p.env ++ [cursor, answer]) step with
    | none => exact badShape_at point env
    | some next => exact loopNext_at root fragment point env contract p next held

/-- Executing a stable suspended body preserves all delayed source annotations. -/
theorem suspend_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) (contract : Contract root point env) (thunk : EffThunk) (held : ThunkAt point env thunk) :
    CodeAt point env (suspendBodyAt root thunk) := by
  revert held
  fun_cases suspendBodyAt root thunk
  case case2 p n fuel body found =>
    intro held
    exact resolve_child_at root fragment point env contract p 0 held
  all_goals intro held
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [CodeAt, ThunkAt, NameAt, StoreThunkAt, FinAt,
    badShape_at, SourceScope.directHead, progOf_at]) (add safe apply [(compile_at root fragment point env contract), (select_arg_at root fragment point env contract)]) (add safe forward [SourceScope.Fragment.at])
/-- Actual asynchronous cancellation introduces no captured source point. -/
theorem cancel_at (point : Point → Prop) (env : List Val → Prop) (name : EffName) :
    CodeAt point env (cancelProgramOf name) := by
  fun_cases cancelProgramOf name
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [CodeAt, ThunkAt, OpAt, store_cancel_at])

/-- Callback invocation refreshes completed exits in these source point annotations. -/
def ViewStable (point : Point → Prop) : Prop :=
  ∀ p, point p → ∀ completed, point {p with completed}

/-- Actual value invocation preserves the annotation under the current completed-exit view. -/
theorem interp_contA_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) (contract : Contract root point env)
    (stable : ViewStable point) (completed) (table : RowTable)
    (name : EffName) (value : Val) (owned : NameAt point env name) :
    CodeAt point env ((interpAt root completed table).contA name value) := by
  apply contA_at root fragment point env contract
  cases name
  case cont p | onValue p => exact stable p owned completed
  case releaseBody p exit previous => exact stable p owned completed
  all_goals exact owned

/-- Actual cause invocation preserves the annotation under the current completed-exit view. -/
theorem interp_contE_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) (contract : Contract root point env)
    (stable : ViewStable point) (completed) (table : RowTable)
    (name : EffName) (cause : CauseV) (owned : NameAt point env name) :
    CodeAt point env ((interpAt root completed table).contE name cause) := by
  apply contE_at root fragment point env contract
  cases name
  case caught p | caughtError p | onCause p => exact stable p owned completed
  all_goals exact owned

/-- Actual suspended invocation preserves the annotation under the current completed-exit view. -/
theorem interp_suspend_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) (contract : Contract root point env)
    (stable : ViewStable point) (completed) (table : RowTable)
    (thunk : EffThunk) (owned : ThunkAt point env thunk) :
    CodeAt point env ((interpAt root completed table).suspendBody thunk) := by
  apply suspend_at root fragment point env contract
  cases thunk
  case body p => exact stable p owned completed
  all_goals exact owned

end Effect4.Program.CodeClosure.Slots
