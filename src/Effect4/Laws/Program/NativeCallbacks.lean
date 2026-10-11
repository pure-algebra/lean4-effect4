import Effect4.Laws.Program.NativeStoreScope

/-!
# Source scope through native callbacks

Concept: store-typing R4, serving `HeapSites.heap_sites_keep`.
The laws follow actual callback invocation through the direct lexical fragment.
They retain the interpreter's completed-exit view without adding stored syntax.
-/
set_option autoImplicit false
namespace Effect4.Program.SourceScope
open Effect4 Effect4.Machine Effect4.Program

/-- Resolving a callback's unchanged environment retains its child source scope. -/
theorem resolve_child_at (root : NativeEff) (fragment : Fragment root) (p : Point) (i : Nat)
    (owned : NextAt root p i 0) : CodeAt root (resolve root (p.child i)) :=
  resolve_scoped root fragment _ (child_at root p i owned)

/-- Resolving a callback's answer argument retains its child source scope. -/
theorem resolve_arg_at (root : NativeEff) (fragment : Fragment root) (p : Point) (i : Nat)
    (value : Val) (owned : NextAt root p i 1) : CodeAt root (resolve root (p.childWith i value)) :=
  resolve_scoped root fragment _ (childWith_at root p i value owned)

/-- A source service region retains its program's residual scope. -/
theorem region_at (root : NativeEff) (fragment : Fragment root) (region : Region)
    (owned : RegionAt root region) : CodeAt root (regionCode root region) := by
  cases region with
  | program p => exact resolve_scoped root fragment p owned
  | build _ _ _ => exact owned.elim
  | buildAdding _ _ _ => exact owned.elim
  | construct _ _ => exact owned.elim

/-- A context update retains the source region in its callback. -/
theorem update_at (root : NativeEff) (update : Env.ContextUpdate) (region : Region)
    (owned : RegionAt root region) : CodeAt root (updateContextAt update region) := by
  refine ⟨trivial, owned, ?_⟩
  intro _ _ wrong
  cases wrong

set_option maxHeartbeats 2000000 in
/-- Calling a saved value callback retains every residual source address it exposes. -/
theorem contA_at (root : NativeEff) (fragment : Fragment root) (name : EffName) (value : Val)
    (owned : NameAt root name) : CodeAt root (contAOf root name value) := by
  revert owned
  fun_cases contAOf root name value
  all_goals intro owned
  all_goals aesop (add norm simp [(resolve_arg_at root fragment), (resolve_child_at root fragment),
    (region_at root fragment), store_contA_at, finProgram_at, capture_at, CodeAt, AsyncCancelAt, ThunkAt,
    NameAt, StoreNameAt, OpAt, RegionAt, Prim.ofExit, badShape_at]) (add norm unfold [updateThenK, addCurrentMemoMapK, combineWithK, mergeContextsK, serviceLookupK, bindServiceK]) (add safe apply [childWith_at, (region_at root fragment)])

/-- Calling a saved cause callback retains its addressed handler. -/
theorem contE_at (root : NativeEff) (fragment : Fragment root) (name : EffName)
    (cause : CauseV) (owned : NameAt root name) : CodeAt root (contEOf root name cause) := by
  revert owned
  fun_cases contEOf root name cause
  all_goals intro owned
  all_goals aesop (add norm simp [(resolve_arg_at root fragment), store_contE_at,
    CodeAt, NameAt, Prim.ofExit])

/-- Every value-only loop result has no delayed source writer. -/
theorem loopFinish_at (root : NativeEff) (p : Point) (cursor : Val) :
    CodeAt root (loopFinishAt root p cursor) := by
  fun_cases loopFinishAt root p cursor
  all_goals aesop (add norm simp [CodeAt, badShape_at])

set_option maxHeartbeats 2000000 in
/-- A value decision binds exactly the source branch's generated lexical length. -/
theorem select_scope_at (root : NativeEff) (p : Point)
    (term : Term) (decision : Decision) (yes no : NativeEff) (value : Val)
    (first : Bool) (bound : Option Val)
    (found : Node.at_ (.eff root) p.path = some (.eff (.select term decision yes no)))
    (scope : At root p) (answer : decision.decide value = some (first, bound)) :
    At root (p.childBind (cond first 0 1) bound) := by
  have path : (p.childBind (cond first 0 1) bound).path = p.path ++ [cond first 0 1] := by
    cases bound <;> rfl
  have len : (p.childBind (cond first 0 1) bound).env.length = p.env.length + bound.toList.length := by
    cases bound <;> simp only [Point.childBind, Point.child, Point.childWith,
      Option.toList_none, Option.toList_some, List.length_nil, List.length_singleton,
      List.length_append, Nat.add_zero]
  unfold At
  rw [path, len, levelAt_suffix _ _ p.path _ 0 found, scope]
  fun_cases Decision.decide decision value
  case case6 tag payload hit =>
    simp only [Decision.decide, hit, Option.some.injEq, Prod.mk.injEq] at answer
    rcases answer with ⟨rfl, rfl⟩
    rfl
  case case8 tag =>
    simp only [Decision.decide, Option.some.injEq, Prod.mk.injEq] at answer
    rcases answer with ⟨rfl, rfl⟩
    cases h : Record.tagHit tag value <;> rfl
  all_goals aesop (erase simp [Nat.left_eq_add]) (add norm simp [Decision.decide, levelAt, Node.childLevel,
    Node.closedChild, Node.binders, Node.child, Option.toList_none, Option.toList_some,
    List.length_nil, List.length_singleton]) (add safe cases [Bool])


/-- Resolving the decided branch retains its exact generated lexical scope.
Consumer: native source interpretation and the existing heap history invariant. -/
theorem select_arg_at (root : NativeEff) (fragment : Fragment root) (p : Point)
    (term : Term) (decision : Decision) (yes no : NativeEff) (value : Val)
    (first : Bool) (bound : Option Val)
    (found : Node.at_ (.eff root) p.path = some (.eff (.select term decision yes no)))
    (scope : At root p) (answer : decision.decide value = some (first, bound)) :
    CodeAt root (resolve root (p.childBind (cond first 0 1) bound)) :=
  resolve_scoped root fragment _ (select_scope_at root p term decision yes no value first bound found scope answer)

/-- The source slots returned by an iterate command. -/
def LoopAt (root : NativeEff) : LoopNext Val NCode → Prop
  | .continue _ body | .finish body => CodeAt root body

/-- Reading an iterate head exposes its body's generated cursor binder. -/
theorem loop_head_at (root : NativeEff) (p : Point) (test step : Term) (body : NativeEff)
    (owned : At root p) (found : loopAt root p = some (test, step, body)) :
    NextAt root p 0 1 := by
  unfold loopAt at found
  split at found
  · rename_i cursorTy initial test' step' result body' source
    exact next_of_at root p _ 0 1 source owned (by rfl)
  · cases found

/-- Entering an iterate loop retains its cursor binder in the actual body. -/
theorem loopNext_at (root : NativeEff) (fragment : Fragment root) (p : Point) (cursor : Val)
    (owned : At root p) : LoopAt root (loopNextAt root p cursor) := by
  fun_cases loopNextAt root p cursor
  all_goals aesop (add norm simp [LoopAt, loopFinish_at, badShape_at]) (add safe apply [(resolve_arg_at root fragment), loop_head_at])

/-- Resuming an iterate loop retains the body scope at its next cursor. -/
theorem loopResume_at (root : NativeEff) (fragment : Fragment root) (p : Point)
    (cursor answer : Val) (owned : At root p) : LoopAt root (loopResumeAt root p cursor answer) := by
  unfold loopResumeAt
  cases h : loopAt root p with
  | none => exact badShape_at root
  | some row =>
    rcases row with ⟨test, step, body⟩
    simp only []
    cases hstep : evalTerm (p.env ++ [cursor, answer]) step with
    | none => exact badShape_at root
    | some next => exact loopNext_at root fragment p next owned

/-- Executing a suspended body retains the lexical source point it resolves. -/
theorem suspend_at (root : NativeEff) (fragment : Fragment root) (thunk : EffThunk)
    (owned : ThunkAt root thunk) : CodeAt root (suspendBodyAt root thunk) := by
  revert owned
  fun_cases suspendBodyAt root thunk
  case case2 p n fuel body found =>
    intro owned
    exact resolve_child_at root fragment p 0 (next_of_at root p _ 0 0 found owned (by rfl))
  all_goals intro owned
  all_goals aesop (add norm simp [CodeAt, ThunkAt, NameAt, StoreThunkAt, FinAt,
    badShape_at, directHead, progOf_at]) (add safe apply [(compile_at root fragment), (select_arg_at root fragment)]) (add safe forward [Fragment.at])

end Effect4.Program.SourceScope
