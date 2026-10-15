import Effect4.Laws.Program.CodeClosure.Predicate
import Effect4.Laws.Program.Agreement
import Effect4.Laws.Program.CompileInduction

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Consumer: AnswerSlots.compile_at and the coupled Atomic, Timeout and crew invariants.
The contract describes leaves minted by the existing compiler and its recursive children.
Each predicate supplies local source facts; the compiler walk occurs only here.
No source admission, initialization or history assertion follows from this contract alone.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Effect4.Program.CodeClosure
open Effect4 Effect4.Machine Effect4.Program

/-- The compiler recursively visits only these immediate source children. -/
def RecursiveChild : NativeEff → Nat → Prop
  | .bind _ _, i | .catchCause _ _, i | .catchIf _ _ _, i | .matchCause _ _ _, i
  | .onExit _ _, i | .exit _, i | .provideContext _ _, i | .restore _ _, i => i = 0
  | .defs _ _ _ _, i => i = 1
  | _, _ => False

/-- Local facts for every leaf that the actual compiler can mint.
Consumer: `compile_closure`, shared by the source-point predicates. -/
structure CompileContract (root : NativeEff) (point : Point → Prop)
    (name : EffName → Prop) (thunk : EffThunk → Prop) : Prop where
  child : ∀ p e i, Node.at_ (.eff root) p.path = some (.eff e) → point p →
    RecursiveChild e i → point (p.child i)
  body : ∀ p e, Node.at_ (.eff root) p.path = some (.eff e) → point p → thunk (.body p)
  pure : ∀ p term, Node.at_ (.eff root) p.path = some (.eff (.sync term)) → point p → thunk (.pure p)
  act : ∀ p e, Node.at_ (.eff root) p.path = some (.eff e) → point p → thunk (.act p)
  operation : ∀ p row request value op,
    Node.at_ (.eff root) p.path = some (.eff (.perform row request)) → point p →
    evalTerm p.env request = some value → row.syncOpOf p.env value = some op → thunk (.op op)
  asynchronous : ∀ p row request,
    Node.at_ (.eff root) p.path = some (.eff (.perform row request)) → point p →
    Code name thunk (asyncRoute row request p)
  cont : ∀ p first rest, Node.at_ (.eff root) p.path = some (.eff (.bind first rest)) → point p → name (.cont p)
  caught : ∀ p body handler, Node.at_ (.eff root) p.path = some (.eff (.catchCause body handler)) → point p → name (.caught p)
  caughtError : ∀ p test body handler, Node.at_ (.eff root) p.path = some (.eff (.catchIf test body handler)) → point p → name (.caughtError p)
  onValue : ∀ p body success failure, Node.at_ (.eff root) p.path = some (.eff (.matchCause body success failure)) → point p → name (.onValue p)
  onCause : ∀ p body success failure, Node.at_ (.eff root) p.path = some (.eff (.matchCause body success failure)) → point p → name (.onCause p)
  fin : ∀ p body finalizer, Node.at_ (.eff root) p.path = some (.eff (.onExit body finalizer)) → point p → name (.fin p)
  forkScoped : ∀ p body options, Node.at_ (.eff root) p.path = some (.eff (.withFiber (.forkScoped body options))) → point p → name (.forkScopedIn p)
  acquire : ∀ p acquire release, Node.at_ (.eff root) p.path = some (.eff (.acquireRelease acquire release)) → point p → name (.acquireCtx p)
  service : ∀ key, name (.serviceLookup key)
  provideService : ∀ p key value body actual,
    Node.at_ (.eff root) p.path = some (.eff (.provideService key value body)) → point p →
    evalTerm p.env value = some actual →
    name (.provideMask (.provideService key actual) (.program (p.child 0)))
  provideContext : ∀ p context body actual,
    Node.at_ (.eff root) p.path = some (.eff (.provideContext context body)) → point p →
    (evalTerm p.env context).bind Val.context? = some actual →
    name (.provideMask (.provide actual.services) (.program (p.child 0)))
  getContext : thunk .getCtx
  captureMask : thunk .captureMask
  park : ∀ kind, thunk (.park kind)

/-- The compiler's generated-code predicate follows from its local minting contract. -/
theorem compile_closure {root : NativeEff} {point : Point → Prop}
    {name : EffName → Prop} {thunk : EffThunk → Prop}
    (contract : CompileContract root point name thunk) (e : NativeEff) (p : Point)
    (found : Node.at_ (.eff root) p.path = some (.eff e)) (held : point p) :
    Code name thunk (compileEff e p) := by
  revert found held
  fun_induction compileEff e p
  case case10 =>
    intro found held
    exact contract.asynchronous _ _ _ found held
  case case16 p n hf row request kind nex ncall nparam =>
    intro found held
    simpa only [kind] using contract.asynchronous p row request found held
  case case13 p n hf row request kind value evaluated operation op nex ncall nparam =>
    intro found held
    simp only [kind, evaluated, op]
    exact contract.operation p row request value operation found held evaluated op
  case case14 p n hf row request kind value evaluated missing nex ncall nparam =>
    intro found held
    simp only [kind, evaluated, missing]
    exact True.intro
  case case15 p n hf row request kind missing nex ncall nparam =>
    intro found held
    simp only [kind, missing]
    exact True.intro
  case case17 p n hf row request kind nex ncall nparam =>
    intro found held
    simp only [kind]
    exact contract.body p (.perform row request) found held
  case case18 p n hf first rest ih =>
    intro found held
    exact ⟨ih (Agreement.at_child found 0) (contract.child p _ 0 found held rfl), contract.cont p first rest found held⟩
  case case20 p n hf body handler ih =>
    intro found held
    exact ⟨ih (Agreement.at_child found 0) (contract.child p _ 0 found held rfl), contract.caught p body handler found held⟩
  case case21 p n hf test body handler ih =>
    intro found held
    exact ⟨ih (Agreement.at_child found 0) (contract.child p _ 0 found held rfl), contract.caughtError p test body handler found held⟩
  case case22 p n hf body success failure ih =>
    intro found held
    exact ⟨ih (Agreement.at_child found 0) (contract.child p _ 0 found held rfl),
      contract.onValue p body success failure found held, contract.onCause p body success failure found held⟩
  case case23 p n hf body finalizer ih =>
    intro found held
    exact ⟨ih (Agreement.at_child found 0) (contract.child p _ 0 found held rfl), contract.fin p body finalizer found held⟩
  case case25 p n hf body noexit ih =>
    intro found held
    exact ih (Agreement.at_child found 0) (contract.child p _ 0 found held rfl)
  case case40 =>
    intro found held
    exact ⟨contract.captureMask, contract.provideService _ _ _ _ _ found held (by assumption)⟩
  case case43 =>
    intro found held
    exact ⟨contract.captureMask, contract.provideContext _ _ _ _ found held (by assumption)⟩
  case case46 p n hf saved body mask ih =>
    intro found held
    exact ih (Agreement.at_child found 0) (contract.child p _ 0 found held rfl)
  case case48 p n hf declarations bodies main layers ih =>
    intro found held
    exact ih (Agreement.at_child found 1) (contract.child p _ 1 found held rfl)
  all_goals intro found held
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [Prim.ofExit, frontier, badShape, updateContextAt]) (add safe apply [contract.body, contract.pure, contract.act,
      contract.forkScoped, contract.acquire, contract.service, contract.getContext, contract.captureMask, contract.park])
end Effect4.Program.CodeClosure
