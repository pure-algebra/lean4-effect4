import Effect4.Laws.Program.AnswerSlots.Stored
import Effect4.Laws.Program.CodeClosure.Compile

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

/-- Leading-binding facts discharge the compiler's local leaf contract.
Consumer: `compile_at`; no compiler case analysis is repeated here. -/
theorem compile_contract (root : NativeEff) (bindings : List Val) :
    CodeClosure.CompileContract root (fun p => Prefix bindings p.env)
      (NameAt bindings) (ThunkAt bindings) := by
  refine {
    child := ?_, body := ?_, pure := ?_, act := ?_, operation := ?_, asynchronous := ?_,
    cont := ?_, caught := ?_, caughtError := ?_, onValue := ?_, onCause := ?_, fin := ?_,
    forkScoped := ?_, acquire := ?_, service := ?_, provideService := ?_, provideContext := ?_,
    getContext := ?_, captureMask := ?_, park := ?_ }
  case refine_1 => intro p e i found held selected; exact held
  case refine_2 => intro p e found held; exact held
  case refine_3 => intro p term found held; exact held
  case refine_4 => intro p e found held; exact held
  case refine_5 =>
    intro p row request value op found held evaluated selected
    exact operation_at bindings p.env row value op held selected
  case refine_6 =>
    intro p row request found held
    change cata_prim (CodeClosure.codeAlg (NameAt bindings) (ThunkAt bindings)) _
    rw [← codeAt_fold]
    exact asyncRoute_at bindings row request p
  all_goals aesop (add norm simp [NameAt, ThunkAt, RegionAt])

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
