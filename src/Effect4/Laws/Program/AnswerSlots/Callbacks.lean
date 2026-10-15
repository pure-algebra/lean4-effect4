import Effect4.Laws.Program.AnswerSlots.Compile

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: stable callback closure serves both crew cleanup log claims.
Reach: the actual direct-fragment value, cause, loop and suspend callbacks.
Limit: this graph retains leading bindings, without proving initialization or acquired literals.
Consumer: the stable answer-flow class and the crew writer debits.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Effect4.Program.AnswerSlots
open Effect4 Effect4.Machine Effect4.Program

/-- A callback's child retains initialized leading bindings. -/
theorem resolve_child_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (bindings : List Val) (p : Point) (index : Nat) (held : Prefix bindings p.env) :
    CodeAt bindings (resolve root (p.child index)) := resolve_at root fragment bindings _ (child held index)

/-- A callback appends its answer after initialized leading bindings. -/
theorem resolve_arg_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (bindings : List Val) (p : Point) (index : Nat) (value : Val) (held : Prefix bindings p.env) :
    CodeAt bindings (resolve root (p.childWith index value)) :=
  resolve_at root fragment bindings _ (childWith held index value)

/-- A direct service region retains its leading environment under interpretation. -/
theorem region_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (bindings : List Val) (region : Region) (held : RegionAt bindings region) :
    CodeAt bindings (regionCode root region) := by
  cases region with
  | program p => exact resolve_at root fragment bindings p held
  | build _ _ _ | buildAdding _ _ _ | construct _ _ => exact held.elim

/-- Capturing an acquired answer preserves the leading environment. -/
theorem capture_at (bindings : List Val) (p : Point) (value : Val) (ctx : Ctx)
    (held : Prefix bindings p.env) : FinAt bindings (.foreign (p.capture value ctx)) :=
  capture held value ctx

/-- Calling any stable value callback preserves all delayed leading environments. -/
theorem contA_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (bindings : List Val) (name : EffName) (value : Val) (held : NameAt bindings name) :
    CodeAt bindings (contAOf root name value) := by
  revert held
  fun_cases contAOf root name value
  all_goals intro held
  all_goals aesop (add norm simp [(resolve_arg_at root fragment), (resolve_child_at root fragment),
    (region_at root fragment), store_contA_at, finProgram_at, capture_at, CodeAt, ThunkAt,
    NameAt, StoreNameAt, OpAt, RegionAt, Prim.ofExit, badShape_at]) (add norm unfold [updateThenK, addCurrentMemoMapK, combineWithK, mergeContextsK,
      serviceLookupK, bindServiceK]) (add safe apply [childWith, (region_at root fragment)])

/-- Calling any stable cause callback preserves all delayed leading environments. -/
theorem contE_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (bindings : List Val) (name : EffName) (cause : CauseV) (held : NameAt bindings name) :
    CodeAt bindings (contEOf root name cause) := by
  revert held
  fun_cases contEOf root name cause
  all_goals intro held
  all_goals aesop (add norm simp [(resolve_arg_at root fragment), store_contE_at,
    CodeAt, NameAt, Prim.ofExit])

/-- A loop's returned value carries no delayed lexical environment. -/
theorem loopFinish_at (bindings : List Val) (root : NativeEff) (p : Point) (cursor : Val) :
    CodeAt bindings (loopFinishAt root p cursor) := by
  fun_cases loopFinishAt root p cursor
  all_goals aesop (add norm simp [CodeAt, badShape_at])

/-- Both branches of a source decision preserve leading bindings. -/
theorem select_arg_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (bindings : List Val) (p : Point) (first : Bool) (bound : Option Val)
    (held : Prefix bindings p.env) :
    CodeAt bindings (resolve root (p.childBind (cond first 0 1) bound)) :=
  resolve_at root fragment bindings _ (childBind held _ bound)

/-- Every loop result retains the delayed environment of its body. -/
def LoopAt (bindings : List Val) : LoopNext Val NCode → Prop
  | .continue _ body | .finish body => CodeAt bindings body

/-- Entering an iterate body appends its cursor after initialized leading bindings. -/
theorem loopNext_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (bindings : List Val) (p : Point) (cursor : Val) (held : Prefix bindings p.env) :
    LoopAt bindings (loopNextAt root p cursor) := by
  fun_cases loopNextAt root p cursor
  all_goals aesop (add norm simp [LoopAt, loopFinish_at, badShape_at]) (add safe apply [(resolve_arg_at root fragment)])

/-- A resumed iterate body starts from the same initialized leading bindings. -/
theorem loopResume_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (bindings : List Val) (p : Point) (cursor answer : Val) (held : Prefix bindings p.env) :
    LoopAt bindings (loopResumeAt root p cursor answer) := by
  unfold loopResumeAt
  cases h : loopAt root p with
  | none => exact badShape_at bindings
  | some row =>
    rcases row with ⟨test, step, body⟩
    simp only []
    cases hstep : evalTerm (p.env ++ [cursor, answer]) step with
    | none => exact badShape_at bindings
    | some next => exact loopNext_at root fragment bindings p next held

/-- Executing a stable suspended body preserves all delayed leading environments. -/
theorem suspend_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (bindings : List Val) (thunk : EffThunk) (held : ThunkAt bindings thunk) :
    CodeAt bindings (suspendBodyAt root thunk) := by
  revert held
  fun_cases suspendBodyAt root thunk
  case case2 p n fuel body found =>
    intro held
    exact resolve_child_at root fragment bindings p 0 held
  all_goals intro held
  all_goals aesop (add norm simp [CodeAt, ThunkAt, NameAt, StoreThunkAt, FinAt,
    badShape_at, SourceScope.directHead, progOf_at]) (add safe apply [(compile_at root fragment), (select_arg_at root fragment)]) (add safe forward [SourceScope.Fragment.at])
end Effect4.Program.AnswerSlots
