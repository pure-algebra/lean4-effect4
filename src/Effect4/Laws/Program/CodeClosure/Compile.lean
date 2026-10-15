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
structure RoleCompileContract (root : NativeEff) (point : Point → Prop)
    (name successName : EffName → Prop) (thunk : EffThunk → Prop) : Prop where
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
    RoleCode name successName thunk (asyncRoute row request p)
  cont : ∀ p first rest, Node.at_ (.eff root) p.path = some (.eff (.bind first rest)) → point p → successName (.cont p)
  caught : ∀ p body handler, Node.at_ (.eff root) p.path = some (.eff (.catchCause body handler)) → point p → name (.caught p)
  caughtError : ∀ p test body handler, Node.at_ (.eff root) p.path = some (.eff (.catchIf test body handler)) → point p → name (.caughtError p)
  onValue : ∀ p body success failure, Node.at_ (.eff root) p.path = some (.eff (.matchCause body success failure)) → point p → name (.onValue p)
  onCause : ∀ p body success failure, Node.at_ (.eff root) p.path = some (.eff (.matchCause body success failure)) → point p → name (.onCause p)
  fin : ∀ p body finalizer, Node.at_ (.eff root) p.path = some (.eff (.onExit body finalizer)) → point p → name (.fin p)
  forkScoped : ∀ p body options, Node.at_ (.eff root) p.path = some (.eff (.withFiber (.forkScoped body options))) → point p → successName (.forkScopedIn p)
  acquire : ∀ p acquire release, Node.at_ (.eff root) p.path = some (.eff (.acquireRelease acquire release)) → point p → successName (.acquireCtx p)
  service : ∀ key, successName (.serviceLookup key)
  provideService : ∀ p key value body actual,
    Node.at_ (.eff root) p.path = some (.eff (.provideService key value body)) → point p →
    evalTerm p.env value = some actual →
    successName (.provideMask (.provideService key actual) (.program (p.child 0)))
  provideContext : ∀ p context body actual,
    Node.at_ (.eff root) p.path = some (.eff (.provideContext context body)) → point p →
    (evalTerm p.env context).bind Val.context? = some actual →
    successName (.provideMask (.provide actual.services) (.program (p.child 0)))
  getContext : thunk .getCtx
  captureMask : thunk .captureMask
  park : ∀ kind, thunk (.park kind)

/-- An indexed constructor contract retains the actual compiled child at each binding site.
Consumers: QueueWorkers job classes and Finalizer's correlated scope-registration body. -/
structure IndexedCompileContract (root : NativeEff) (Kind : Type)
    (point : Kind → Point → Prop) (code : Kind → NCode → Prop) : Prop where
  failure : ∀ kind cause, code kind (.failure cause)
  success : ∀ p term value kind, Node.at_ (.eff root) p.path = some (.eff (.succeed term)) →
    point kind p → evalTerm p.env term = some value → code kind (.success value)
  body : ∀ p e kind, Node.at_ (.eff root) p.path = some (.eff e) → point kind p → code kind (.suspend (.body p))
  pure : ∀ p term kind, Node.at_ (.eff root) p.path = some (.eff (.sync term)) → point kind p → code kind (.sync (.pure p))
  act : ∀ p e kind, Node.at_ (.eff root) p.path = some (.eff e) → point kind p → code kind (.withFiber (.act p))
  operation : ∀ p row request value op kind,
    Node.at_ (.eff root) p.path = some (.eff (.perform row request)) → point kind p →
    evalTerm p.env request = some value → row.syncOpOf p.env value = some op → code kind (.sync (.op op))
  asynchronous : ∀ p row request kind,
    Node.at_ (.eff root) p.path = some (.eff (.perform row request)) → point kind p → code kind (asyncRoute row request p)
  bind : ∀ p first rest kind, Node.at_ (.eff root) p.path = some (.eff (.bind first rest)) → point kind p →
    ∃ input, point input (p.child 0) ∧ ∀ body, code input body → code kind (.onSuccess body (.cont p))
  caught : ∀ p first rest kind, Node.at_ (.eff root) p.path = some (.eff (.catchCause first rest)) → point kind p →
    ∃ input, point input (p.child 0) ∧ ∀ body, code input body → code kind (.onFailure body (.caught p))
  caughtError : ∀ p test first rest kind, Node.at_ (.eff root) p.path = some (.eff (.catchIf test first rest)) → point kind p →
    ∃ input, point input (p.child 0) ∧ ∀ body, code input body → code kind (.onFailure body (.caughtError p))
  matched : ∀ p first success failure kind, Node.at_ (.eff root) p.path = some (.eff (.matchCause first success failure)) → point kind p →
    ∃ input, point input (p.child 0) ∧ ∀ body, code input body → code kind (.onSuccessAndFailure body (.onValue p) (.onCause p))
  finalized : ∀ p first finalizer kind, Node.at_ (.eff root) p.path = some (.eff (.onExit first finalizer)) → point kind p →
    ∃ input, point input (p.child 0) ∧ ∀ body, code input body → code kind (.onExit body (.fin p) false)
  exited : ∀ p first kind, Node.at_ (.eff root) p.path = some (.eff (.exit first)) → point kind p →
    ∃ input, point input (p.child 0) ∧ ∀ body, code input body →
      code kind (match body.asExit? with | some exit => .success (reifyExitVal exit) | none => .exitFrame body)
  restored : ∀ p saved first kind, Node.at_ (.eff root) p.path = some (.eff (.restore saved first)) → point kind p → point kind (p.child 0)
  definitions : ∀ p declarations bodies main layers kind,
    Node.at_ (.eff root) p.path = some (.eff (.defs declarations bodies main layers)) → point kind p → point kind (p.child 1)
  yielding : ∀ p priority kind, Node.at_ (.eff root) p.path = some (.eff (.yieldNow priority)) → point kind p → code kind (.yieldNowWith priority)
  awaited : ∀ p term mode id exit kind,
    Node.at_ (.eff root) p.path = some (.eff (.awaitFiber term mode)) → point kind p →
    evalTerm p.env term = some (.fiber id) → p.awaitExit id mode = some exit → code kind (Prim.ofExit exit)
  parked : ∀ p term mode id kind,
    Node.at_ (.eff root) p.path = some (.eff (.awaitFiber term mode)) → point kind p →
    evalTerm p.env term = some (.fiber id) → p.awaitExit id mode = none → code kind (.suspend (.park (.join id mode)))
  forkScoped : ∀ p first options kind,
    Node.at_ (.eff root) p.path = some (.eff (.withFiber (.forkScoped first options))) → point kind p →
    code kind (.onSuccess (.withFiber (.act p)) (.forkScopedIn p))
  acquire : ∀ p first release kind,
    Node.at_ (.eff root) p.path = some (.eff (.acquireRelease first release)) → point kind p →
    code kind (.onSuccess (.withFiber .getCtx) (.acquireCtx p))
  service : ∀ p key kind, Node.at_ (.eff root) p.path = some (.eff (.service key)) → point kind p →
    code kind (.onSuccess (.withFiber .getCtx) (.serviceLookup key))
  provideService : ∀ p key value first actual kind,
    Node.at_ (.eff root) p.path = some (.eff (.provideService key value first)) → point kind p →
    evalTerm p.env value = some actual → code kind (updateContextAt (.provideService key actual) (.program (p.child 0)))
  context : ∀ p context first actual kind,
    Node.at_ (.eff root) p.path = some (.eff (.provideContext context first)) → point kind p →
    (evalTerm p.env context).bind Val.context? = some actual →
    ∃ input, point input (p.child 0) ∧ ∀ body, code input body →
      code kind (match body.asExit? with | some exit => Prim.ofExit exit | none => updateContextAt (.provide actual.services) (.program (p.child 0)))

/-- The sole compiler induction supports distinct actual input and output classes. -/
theorem indexed_compile_closure {root : NativeEff} {Kind : Type}
    {point : Kind → Point → Prop} {code : Kind → NCode → Prop}
    (contract : IndexedCompileContract root Kind point code) (e : NativeEff) (p : Point)
    (kind : Kind) (found : Node.at_ (.eff root) p.path = some (.eff e)) (held : point kind p) :
    code kind (compileEff e p) := by
  revert kind found held
  fun_induction compileEff e p
  case case18 p n hf first rest ih =>
    intro kind found held
    obtain ⟨input, child, build⟩ := contract.bind p first rest kind found held
    exact build _ (ih input (Agreement.at_child found 0) child)
  case case20 p n hf first rest ih =>
    intro kind found held
    obtain ⟨input, child, build⟩ := contract.caught p first rest kind found held
    exact build _ (ih input (Agreement.at_child found 0) child)
  case case21 p n hf test first rest ih =>
    intro kind found held
    obtain ⟨input, child, build⟩ := contract.caughtError p test first rest kind found held
    exact build _ (ih input (Agreement.at_child found 0) child)
  case case22 p n hf first success failure ih =>
    intro kind found held
    obtain ⟨input, child, build⟩ := contract.matched p first success failure kind found held
    exact build _ (ih input (Agreement.at_child found 0) child)
  case case23 p n hf first finalizer ih =>
    intro kind found held
    obtain ⟨input, child, build⟩ := contract.finalized p first finalizer kind found held
    exact build _ (ih input (Agreement.at_child found 0) child)
  case case24 p n hf first exit produced ih =>
    intro kind found held
    obtain ⟨input, child, build⟩ := contract.exited p first kind found held
    have good := build _ (ih input (Agreement.at_child found 0) child)
    simpa only [produced] using good
  case case25 p n hf first absent ih =>
    intro kind found held
    obtain ⟨input, child, build⟩ := contract.exited p first kind found held
    have good := build _ (ih input (Agreement.at_child found 0) child)
    simpa only [absent] using good
  case case42 p n hf context first actual evaluated exit produced ih =>
    intro kind found held
    obtain ⟨input, child, build⟩ := contract.context p context first actual kind found held evaluated
    have good := build _ (ih input (Agreement.at_child found 0) child)
    simpa only [produced] using good
  case case43 p n hf context first actual evaluated absent ih =>
    intro kind found held
    obtain ⟨input, child, build⟩ := contract.context p context first actual kind found held evaluated
    have good := build _ (ih input (Agreement.at_child found 0) child)
    simpa only [absent] using good
  case case46 p n hf saved first mask ih =>
    intro kind found held
    exact ih kind (Agreement.at_child found 0) (contract.restored p saved first kind found held)
  case case48 p n hf declarations bodies main layers ih =>
    intro kind found held
    exact ih kind (Agreement.at_child found 1) (contract.definitions p declarations bodies main layers kind found held)
  case case1 | case9 | case11 | case12 | case19 | case28 | case29 | case38 | case49 =>
    intro output found held
    exact contract.body _ _ output found held
  case case3 | case4 | case5 | case6 | case7 | case33 | case41 | case44 | case47 =>
    intro output _ _
    exact contract.failure output _
  case case2 =>
    intro output found held
    exact contract.success _ _ _ output found held (by assumption)
  case case8 =>
    intro output found held
    exact contract.pure _ _ output found held
  case case10 =>
    intro output found held
    exact contract.asynchronous _ _ _ output found held
  case case13 p n hf row request sourceKind value evaluated operation selected nex ncall nparam =>
    intro output found held
    simpa only [sourceKind, evaluated, selected] using
      contract.operation p row request value operation output found held evaluated selected
  case case14 p n hf row request sourceKind value evaluated missing nex ncall nparam =>
    intro output _ _
    simp only [sourceKind, evaluated, missing]
    exact contract.failure output _
  case case15 p n hf row request sourceKind missing nex ncall nparam =>
    intro output _ _
    simp only [sourceKind, missing]
    exact contract.failure output _
  case case16 p n hf row request sourceKind nex ncall nparam =>
    intro output found held
    simpa only [sourceKind] using contract.asynchronous p row request output found held
  case case17 p n hf row request sourceKind nex ncall nparam =>
    intro output found held
    simpa only [sourceKind, frontier] using contract.body p (.perform row request) output found held
  case case26 | case27 | case35 | case36 | case45 =>
    intro output found held
    exact contract.act _ _ output found held
  case case30 =>
    intro output found held
    exact contract.yielding _ _ output found held
  case case31 =>
    intro output found held
    exact contract.awaited _ _ _ _ _ output found held (by assumption) (by assumption)
  case case32 =>
    intro output found held
    exact contract.parked _ _ _ _ output found held (by assumption) (by assumption)
  case case34 =>
    intro output found held
    exact contract.forkScoped _ _ _ output found held
  case case37 =>
    intro output found held
    exact contract.acquire _ _ _ output found held
  case case39 =>
    intro output found held
    exact contract.service _ _ output found held
  case case40 =>
    intro output found held
    exact contract.provideService _ _ _ _ _ output found held (by assumption)


/-- The existing unindexed leaf contract is the one-class constructor instance. -/
theorem RoleCompileContract.indexed {root : NativeEff} {point : Point → Prop}
    {name successName : EffName → Prop} {thunk : EffThunk → Prop}
    (contract : RoleCompileContract root point name successName thunk) :
    IndexedCompileContract root Unit (fun _ => point) (fun _ => RoleCode name successName thunk) where
  failure _ _ := trivial
  success _ _ _ _ _ _ _ := trivial
  body p e _ found held := contract.body p e found held
  pure p term _ found held := contract.pure p term found held
  act p e _ found held := contract.act p e found held
  operation p row request value op _ found held evaluated selected := contract.operation p row request value op found held evaluated selected
  asynchronous p row request _ found held := contract.asynchronous p row request found held
  bind p first rest _ found held := ⟨(), contract.child p _ 0 found held rfl,
    fun _ good => ⟨good, contract.cont p first rest found held⟩⟩
  caught p first rest _ found held := ⟨(), contract.child p _ 0 found held rfl,
    fun _ good => ⟨good, contract.caught p first rest found held⟩⟩
  caughtError p test first rest _ found held := ⟨(), contract.child p _ 0 found held rfl,
    fun _ good => ⟨good, contract.caughtError p test first rest found held⟩⟩
  matched p first success failure _ found held := ⟨(), contract.child p _ 0 found held rfl,
    fun _ good => ⟨good, contract.onValue p first success failure found held, contract.onCause p first success failure found held⟩⟩
  finalized p first finalizer _ found held := ⟨(), contract.child p _ 0 found held rfl,
    fun _ good => ⟨good, contract.fin p first finalizer found held⟩⟩
  exited p first _ found held := by
    refine ⟨(), contract.child p _ 0 found held rfl, ?_⟩
    intro body good
    cases branch : body.asExit? with
    | none => exact good
    | some exit => trivial
  restored p saved first _ found held := contract.child p _ 0 found held rfl
  definitions p declarations bodies main layers _ found held := contract.child p _ 1 found held rfl
  yielding _ _ _ _ _ := trivial
  awaited _ _ _ _ exit _ _ _ _ _ := by cases exit <;> trivial
  parked _ _ mode id _ _ _ _ _ := contract.park (.join id mode)
  forkScoped p first options _ found held := ⟨contract.act p _ found held, contract.forkScoped p first options found held⟩
  acquire p first release _ found held := ⟨contract.getContext, contract.acquire p first release found held⟩
  service _ key _ _ _ := ⟨contract.getContext, contract.service key⟩
  provideService p key value first actual _ found held evaluated :=
    ⟨contract.captureMask, contract.provideService p key value first actual found held evaluated⟩
  context p context first actual _ found held evaluated := by
    refine ⟨(), contract.child p _ 0 found held rfl, ?_⟩
    intro body _
    cases branch : body.asExit? with
    | none => exact ⟨contract.captureMask, contract.provideContext p context first actual found held evaluated⟩
    | some exit => cases exit <;> trivial

/-- Distinct callback roles use the indexed constructor producer at one class. -/
theorem compile_roles {root : NativeEff} {point : Point → Prop}
    {name successName : EffName → Prop} {thunk : EffThunk → Prop}
    (contract : RoleCompileContract root point name successName thunk) (e : NativeEff) (p : Point)
    (found : Node.at_ (.eff root) p.path = some (.eff e)) (held : point p) :
    RoleCode name successName thunk (compileEff e p) :=
  indexed_compile_closure contract.indexed e p () found held

/-- Existing source predicates use one annotation for both callback roles. -/
abbrev CompileContract (root : NativeEff) (point : Point → Prop)
    (name : EffName → Prop) (thunk : EffThunk → Prop) := RoleCompileContract root point name name thunk

/-- The existing compiler closure is the equal-role instance of the single producer. -/
theorem compile_closure {root : NativeEff} {point : Point → Prop}
    {name : EffName → Prop} {thunk : EffThunk → Prop}
    (contract : CompileContract root point name thunk) (e : NativeEff) (p : Point)
    (found : Node.at_ (.eff root) p.path = some (.eff e)) (held : point p) :
    Code name thunk (compileEff e p) := compile_roles contract e p found held
end Effect4.Program.CodeClosure
