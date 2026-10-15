import Effect4.Laws.Program.AnswerSlots.Stored

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: compiled stable source code retains the bindings used by both crew log proofs.
Reach: the direct lexical source fragment and every compilation budget.
Limit: initialization and acquired identity remain separate obligations.
Consumer: saved callback transport and the stable answer-flow class.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Effect4.Program.AnswerSlots
open Effect4 Effect4.Machine Effect4.Program

/-- Native source operations retain their update environment's leading bindings. -/
theorem operation_at (bindings env : List Val) (row : NativeOp) (value : Val) (operation : SyncOp)
    (held : Prefix bindings env) (answer : row.syncOpOf env value = some operation) :
    OpAt bindings operation := by
  fun_cases NativeOp.syncOpOf row env value
  all_goals aesop (add norm simp [NativeOp.syncOpOf, OpAt])

/-- An external registration carries no lexical continuation environment. -/
theorem asyncRoute_at (bindings : List Val) (row : NativeOp) (request : Term) (p : Point) :
    CodeAt bindings (asyncRoute row request p) := by
  fun_cases asyncRoute row request p
  all_goals aesop (add norm simp [CodeAt, NameAt, StoreNameAt, badShape])

/-- A shape refusal carries no delayed environment. -/
theorem badShape_at (bindings : List Val) : CodeAt bindings badShape := trivial

/-- Direct source compilation preserves initialized leading bindings in all delayed fields. -/
theorem compile_at (root : NativeEff) (fragment : SourceScope.Fragment root) (bindings : List Val)
    (e : NativeEff) (p : Point) (found : Node.at_ (.eff root) p.path = some (.eff e))
    (held : Prefix bindings p.env) : CodeAt bindings (compileEff e p) := by
  revert found held
  fun_induction compileEff e p
  case case13 p n hf row request kind value hval operation hop nex ncall nparam =>
    intro found held
    simp only [kind, hval, hop]
    exact operation_at bindings p.env row value operation held hop
  case case18 p n hf first rest ih =>
    intro found held
    exact ⟨ih (Agreement.at_child found 0) held, held⟩
  case case20 p n hf body handler ih =>
    intro found held
    exact ⟨ih (Agreement.at_child found 0) held, held⟩
  case case21 p n hf test body handler ih =>
    intro found held
    exact ⟨ih (Agreement.at_child found 0) held, held⟩
  case case22 p n hf body success failure ih =>
    intro found held
    exact ⟨ih (Agreement.at_child found 0) held, held, held⟩
  case case23 p n hf body finalizer ih =>
    intro found held
    exact ⟨ih (Agreement.at_child found 0) held, held⟩
  case case25 p n hf body noexit ih =>
    intro found held
    exact ih (Agreement.at_child found 0) held
  case case37 p n hf acquire release =>
    intro found held
    exact ⟨trivial, held⟩
  case case40 p n hf key value body val read =>
    intro found held
    exact ⟨trivial, held⟩
  case case46 p n hf saved body mask ih =>
    intro found held
    exact ih (Agreement.at_child found 0) held
  all_goals intro found held
  all_goals have head := fragment.at found
  all_goals aesop (add norm simp [asyncRoute_at, badShape_at, CodeAt, NameAt, ThunkAt,
    SourceScope.directHead, Prim.ofExit, RegionAt, OpAt]) (add norm unfold [frontier, badShape, updateContextAt])

/-- Resolving a stable source point preserves initialized leading bindings. -/
theorem resolve_at (root : NativeEff) (fragment : SourceScope.Fragment root) (bindings : List Val)
    (p : Point) (held : Prefix bindings p.env) : CodeAt bindings (resolve root p) := by
  unfold resolve
  split
  · rename_i e found
    exact compile_at root fragment bindings e p found held
  · exact badShape_at bindings
end Effect4.Program.AnswerSlots
