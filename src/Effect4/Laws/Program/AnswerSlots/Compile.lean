import Effect4.Laws.Program.AnswerSlots.Stored
import Effect4.Laws.Program.CodeClosure.Callbacks

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
    OpAt bindings operation :=
  CodeClosure.Slots.operation_at (fun p => Prefix bindings p.env) (Prefix bindings)
    env row value operation held answer

/-- An external registration carries no lexical continuation environment. -/
theorem asyncRoute_at (bindings : List Val) (row : NativeOp) (request : Term) (p : Point) :
    CodeAt bindings (asyncRoute row request p) := by
  rw [codeAt_fold]
  exact CodeClosure.Slots.asyncRoute_at (fun p => Prefix bindings p.env) (Prefix bindings) row request p

/-- A shape refusal carries no delayed environment. -/
theorem badShape_at (bindings : List Val) : CodeAt bindings badShape := trivial

/-- Leading bindings instantiate the shared point transport operations. -/
theorem prefix_transport (bindings : List Val) :
    CodeClosure.Slots.Transport (fun p => Prefix bindings p.env) (Prefix bindings) where
  environment := fun held => held
  child := fun held index => child held index
  childWith := fun held index value => childWith held index value
  capture := fun held value context => capture held value context

/-- Leading-binding facts discharge the compiler's local leaf contract.
Consumer: `compile_at`; no compiler case analysis is repeated here. -/
theorem compile_contract (root : NativeEff) (bindings : List Val) :
    CodeClosure.CompileContract root (fun p => Prefix bindings p.env)
      (NameAt bindings) (ThunkAt bindings) :=
  CodeClosure.Slots.compile_contract root (fun p => Prefix bindings p.env) (Prefix bindings)
    (prefix_transport bindings)

/-- Direct source compilation preserves initialized leading bindings in all delayed fields. -/
theorem compile_at (root : NativeEff) (_fragment : SourceScope.Fragment root) (bindings : List Val)
    (e : NativeEff) (p : Point) (found : Node.at_ (.eff root) p.path = some (.eff e))
    (held : Prefix bindings p.env) : CodeAt bindings (compileEff e p) := by
  rw [codeAt_fold]
  exact CodeClosure.compile_closure (compile_contract root bindings) e p found held

/-- Resolving a stable source point preserves initialized leading bindings. -/
theorem resolve_at (root : NativeEff) (fragment : SourceScope.Fragment root) (bindings : List Val)
    (p : Point) (held : Prefix bindings p.env) : CodeAt bindings (resolve root p) := by
  unfold resolve
  split
  · rename_i e found
    exact compile_at root fragment bindings e p found held
  · exact badShape_at bindings
end Effect4.Program.AnswerSlots
