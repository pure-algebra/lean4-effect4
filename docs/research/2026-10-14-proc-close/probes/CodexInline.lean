import Effect4.Author
import Effect4.Program.Authoring.Module
import Effect4.Laws.Program.BlockMeaning
import Effect4.Laws.Program.Typed.ListFold
import Effect4.Laws.Program.Typing.Replace
import Effect4.Laws.Program.Typing.Splice

/-!
Independent Q3/Q4 probe at bff5c1ccb34742381b21011893877cbfe9fd4a24.
Review-only candidate obligations are definitions of Prop, not axioms or planned proofs.
The fold below is a concrete proposed substitution on the current BlockRows fragment.
Closed-layer controls expose the additional capture obligation for later widenings.
Consumers: close-out L3 inline-types, L2 inline-agrees, L4 definitions-agree.
No finite guard below proves a universal sandwich or host-runtime correspondence.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Effect4.Probes.CodexInline
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote
open Effect4.Machine.Env (Requirement)

/-- Iterate the existing shift; no second term-shift representation. -/
def weakenMany (cut count : Nat) (body : NativeEff) : NativeEff :=
  Nat.repeat (Eff.weaken cut) count body

/-- Original nodes plus their depth-indexed substitution, including statement-head binder data. -/
abbrev SubstCarrier (fam : EffFam) := EffSelfCarrier NativeOp fam × (Nat → EffSelfCarrier NativeOp fam)

/-- Candidate L3 fold. Node.childLevel is generated from binders.json.
Arguments are inserted once, never recursively substituted in their caller parameter frame.
The missing-index branch is a fixed refusing term, with the source meaning of badShape.
A production typed transform may instead return a located refusal for that unreachable typed case. -/
def substAlg (callerSize : Nat) (args : List NativeEff) : EffAlgebra NativeOp SubstCarrier where
  eff_succeed a0 := (Effect4.Program.Eff.succeed a0, fun _ => Effect4.Program.Eff.succeed a0)
  eff_fail a0 := (Effect4.Program.Eff.fail a0, fun _ => Effect4.Program.Eff.fail a0)
  eff_failCause a0 := (Effect4.Program.Eff.failCause a0, fun _ => Effect4.Program.Eff.failCause a0)
  eff_sync a0 := (Effect4.Program.Eff.sync a0, fun _ => Effect4.Program.Eff.sync a0)
  eff_suspend a0 := (Effect4.Program.Eff.suspend (a0.1), fun depth => Effect4.Program.Eff.suspend (a0.2 (Node.childLevel depth (Node.eff (Effect4.Program.Eff.suspend (a0.1))) 0)))
  eff_perform op request := (.perform op request, fun depth => match op with
    | .param i => match args[i]? with
      | some argument => .bind (.succeed request) (weakenMany callerSize depth argument)
      | none => .succeed (.tupleAt (.lit .unit) 0)
    | _ => .perform op request)
  eff_bind a0 a1 := (Effect4.Program.Eff.bind (a0.1) (a1.1), fun depth => Effect4.Program.Eff.bind (a0.2 (Node.childLevel depth (Node.eff (Effect4.Program.Eff.bind (a0.1) (a1.1))) 0)) (a1.2 (Node.childLevel depth (Node.eff (Effect4.Program.Eff.bind (a0.1) (a1.1))) 1)))
  eff_gen a0 := (Effect4.Program.Eff.gen (a0.1), fun depth => Effect4.Program.Eff.gen (a0.2 (Node.childLevel depth (Node.eff (Effect4.Program.Eff.gen (a0.1))) 0)))
  eff_catchCause a0 a1 := (Effect4.Program.Eff.catchCause (a0.1) (a1.1), fun depth => Effect4.Program.Eff.catchCause (a0.2 (Node.childLevel depth (Node.eff (Effect4.Program.Eff.catchCause (a0.1) (a1.1))) 0)) (a1.2 (Node.childLevel depth (Node.eff (Effect4.Program.Eff.catchCause (a0.1) (a1.1))) 1)))
  eff_matchCause a0 a1 a2 := (Effect4.Program.Eff.matchCause (a0.1) (a1.1) (a2.1), fun depth => Effect4.Program.Eff.matchCause (a0.2 (Node.childLevel depth (Node.eff (Effect4.Program.Eff.matchCause (a0.1) (a1.1) (a2.1))) 0)) (a1.2 (Node.childLevel depth (Node.eff (Effect4.Program.Eff.matchCause (a0.1) (a1.1) (a2.1))) 1)) (a2.2 (Node.childLevel depth (Node.eff (Effect4.Program.Eff.matchCause (a0.1) (a1.1) (a2.1))) 2)))
  eff_onExit a0 a1 := (Effect4.Program.Eff.onExit (a0.1) (a1.1), fun depth => Effect4.Program.Eff.onExit (a0.2 (Node.childLevel depth (Node.eff (Effect4.Program.Eff.onExit (a0.1) (a1.1))) 0)) (a1.2 (Node.childLevel depth (Node.eff (Effect4.Program.Eff.onExit (a0.1) (a1.1))) 1)))
  eff_exit a0 := (Effect4.Program.Eff.exit (a0.1), fun depth => Effect4.Program.Eff.exit (a0.2 (Node.childLevel depth (Node.eff (Effect4.Program.Eff.exit (a0.1))) 0)))
  eff_uninterruptible a0 := (Effect4.Program.Eff.uninterruptible (a0.1), fun depth => Effect4.Program.Eff.uninterruptible (a0.2 (Node.childLevel depth (Node.eff (Effect4.Program.Eff.uninterruptible (a0.1))) 0)))
  eff_interruptible a0 := (Effect4.Program.Eff.interruptible (a0.1), fun depth => Effect4.Program.Eff.interruptible (a0.2 (Node.childLevel depth (Node.eff (Effect4.Program.Eff.interruptible (a0.1))) 0)))
  eff_yieldNow a0 := (Effect4.Program.Eff.yieldNow a0, fun _ => Effect4.Program.Eff.yieldNow a0)
  eff_awaitFiber a0 a1 := (Effect4.Program.Eff.awaitFiber a0 a1, fun _ => Effect4.Program.Eff.awaitFiber a0 a1)
  eff_withFiber a0 := (Effect4.Program.Eff.withFiber (a0.1), fun depth => Effect4.Program.Eff.withFiber (a0.2 (Node.childLevel depth (Node.eff (Effect4.Program.Eff.withFiber (a0.1))) 0)))
  eff_scoped a0 := (Effect4.Program.Eff.scoped (a0.1), fun depth => Effect4.Program.Eff.scoped (a0.2 (Node.childLevel depth (Node.eff (Effect4.Program.Eff.scoped (a0.1))) 0)))
  eff_acquireRelease a0 a1 := (Effect4.Program.Eff.acquireRelease (a0.1) (a1.1), fun depth => Effect4.Program.Eff.acquireRelease (a0.2 (Node.childLevel depth (Node.eff (Effect4.Program.Eff.acquireRelease (a0.1) (a1.1))) 0)) (a1.2 (Node.childLevel depth (Node.eff (Effect4.Program.Eff.acquireRelease (a0.1) (a1.1))) 1)))
  eff_provideLayer a0 a1 a2 := (Effect4.Program.Eff.provideLayer (a0.1) a1 (a2.1), fun depth => Effect4.Program.Eff.provideLayer (a0.2 (Node.childLevel depth (Node.eff (Effect4.Program.Eff.provideLayer (a0.1) a1 (a2.1))) 0)) a1 (a2.2 (Node.childLevel depth (Node.eff (Effect4.Program.Eff.provideLayer (a0.1) a1 (a2.1))) 1)))
  eff_service a0 := (Effect4.Program.Eff.service a0, fun _ => Effect4.Program.Eff.service a0)
  eff_provideService a0 a1 a2 := (Effect4.Program.Eff.provideService a0 a1 (a2.1), fun depth => Effect4.Program.Eff.provideService a0 a1 (a2.2 (Node.childLevel depth (Node.eff (Effect4.Program.Eff.provideService a0 a1 (a2.1))) 0)))
  eff_catchIf a0 a1 a2 := (Effect4.Program.Eff.catchIf a0 (a1.1) (a2.1), fun depth => Effect4.Program.Eff.catchIf a0 (a1.2 (Node.childLevel depth (Node.eff (Effect4.Program.Eff.catchIf a0 (a1.1) (a2.1))) 0)) (a2.2 (Node.childLevel depth (Node.eff (Effect4.Program.Eff.catchIf a0 (a1.1) (a2.1))) 1)))
  eff_select a0 a1 a2 a3 := (Effect4.Program.Eff.select a0 a1 (a2.1) (a3.1), fun depth => Effect4.Program.Eff.select a0 a1 (a2.2 (Node.childLevel depth (Node.eff (Effect4.Program.Eff.select a0 a1 (a2.1) (a3.1))) 0)) (a3.2 (Node.childLevel depth (Node.eff (Effect4.Program.Eff.select a0 a1 (a2.1) (a3.1))) 1)))
  eff_iterate a0 a1 a2 a3 a4 a5 := (Effect4.Program.Eff.iterate a0 a1 a2 a3 a4 (a5.1), fun depth => Effect4.Program.Eff.iterate a0 a1 a2 a3 a4 (a5.2 (Node.childLevel depth (Node.eff (Effect4.Program.Eff.iterate a0 a1 a2 a3 a4 (a5.1))) 0)))
  eff_restore a0 a1 := (Effect4.Program.Eff.restore a0 (a1.1), fun depth => Effect4.Program.Eff.restore a0 (a1.2 (Node.childLevel depth (Node.eff (Effect4.Program.Eff.restore a0 (a1.1))) 0)))
  eff_defs a0 a1 a2 a3 := (Effect4.Program.Eff.defs a0 (a1.1) (a2.1) (a3.1), fun depth => Effect4.Program.Eff.defs a0 (a1.2 (Node.childLevel depth (Node.eff (Effect4.Program.Eff.defs a0 (a1.1) (a2.1) (a3.1))) 0)) (a2.2 (Node.childLevel depth (Node.eff (Effect4.Program.Eff.defs a0 (a1.1) (a2.1) (a3.1))) 1)) (a3.2 (Node.childLevel depth (Node.eff (Effect4.Program.Eff.defs a0 (a1.1) (a2.1) (a3.1))) 2)))
  eff_invoke a0 a1 a2 := (Effect4.Program.Eff.invoke a0 a1 (a2.1), fun depth => Effect4.Program.Eff.invoke a0 a1 (a2.2 (Node.childLevel depth (Node.eff (Effect4.Program.Eff.invoke a0 a1 (a2.1))) 0)))
  eff_provideContext a0 a1 := (Effect4.Program.Eff.provideContext a0 (a1.1), fun depth => Effect4.Program.Eff.provideContext a0 (a1.2 (Node.childLevel depth (Node.eff (Effect4.Program.Eff.provideContext a0 (a1.1))) 0)))
  stmt_bindYield a0 := (Effect4.Program.Stmt.bindYield (a0.1), fun depth => Effect4.Program.Stmt.bindYield (a0.2 (Node.childLevel depth (Node.stmt (Effect4.Program.Stmt.bindYield (a0.1))) 0)))
  stmt_yieldDiscard a0 := (Effect4.Program.Stmt.yieldDiscard (a0.1), fun depth => Effect4.Program.Stmt.yieldDiscard (a0.2 (Node.childLevel depth (Node.stmt (Effect4.Program.Stmt.yieldDiscard (a0.1))) 0)))
  stmt_ret a0 := (Effect4.Program.Stmt.ret a0, fun _ => Effect4.Program.Stmt.ret a0)
  stmt_ifElse a0 a1 a2 := (Effect4.Program.Stmt.ifElse a0 (a1.1) (a2.1), fun depth => Effect4.Program.Stmt.ifElse a0 (a1.2 (Node.childLevel depth (Node.stmt (Effect4.Program.Stmt.ifElse a0 (a1.1) (a2.1))) 0)) (a2.2 (Node.childLevel depth (Node.stmt (Effect4.Program.Stmt.ifElse a0 (a1.1) (a2.1))) 1)))
  stmt_whileTrue a0 := (Effect4.Program.Stmt.whileTrue (a0.1), fun depth => Effect4.Program.Stmt.whileTrue (a0.2 (Node.childLevel depth (Node.stmt (Effect4.Program.Stmt.whileTrue (a0.1))) 0)))
  stmt_breakLoop := (Effect4.Program.Stmt.breakLoop, fun _ => Effect4.Program.Stmt.breakLoop)
  stmts_nil := (Effect4.Program.Stmts.nil, fun _ => Effect4.Program.Stmts.nil)
  stmts_cons a0 a1 := (Effect4.Program.Stmts.cons (a0.1) (a1.1), fun depth => Effect4.Program.Stmts.cons (a0.2 (Node.childLevel depth (Node.stmts (Effect4.Program.Stmts.cons (a0.1) (a1.1))) 0)) (a1.2 (Node.childLevel depth (Node.stmts (Effect4.Program.Stmts.cons (a0.1) (a1.1))) 1)))
  effs_nil := (Effect4.Program.Effs.nil, fun _ => Effect4.Program.Effs.nil)
  effs_cons a0 a1 := (Effect4.Program.Effs.cons (a0.1) (a1.1), fun depth => Effect4.Program.Effs.cons (a0.2 (Node.childLevel depth (Node.effs (Effect4.Program.Effs.cons (a0.1) (a1.1))) 0)) (a1.2 (Node.childLevel depth (Node.effs (Effect4.Program.Effs.cons (a0.1) (a1.1))) 1)))
  action_fork a0 a1 := (Effect4.Program.ActionTerm.fork (a0.1) a1, fun depth => Effect4.Program.ActionTerm.fork (a0.2 (Node.childLevel depth (Node.action (Effect4.Program.ActionTerm.fork (a0.1) a1)) 0)) a1)
  action_forkIn a0 a1 a2 := (Effect4.Program.ActionTerm.forkIn (a0.1) a1 a2, fun depth => Effect4.Program.ActionTerm.forkIn (a0.2 (Node.childLevel depth (Node.action (Effect4.Program.ActionTerm.forkIn (a0.1) a1 a2)) 0)) a1 a2)
  action_forkScoped a0 a1 := (Effect4.Program.ActionTerm.forkScoped (a0.1) a1, fun depth => Effect4.Program.ActionTerm.forkScoped (a0.2 (Node.childLevel depth (Node.action (Effect4.Program.ActionTerm.forkScoped (a0.1) a1)) 0)) a1)
  action_runIn a0 a1 := (Effect4.Program.ActionTerm.runIn a0 a1, fun _ => Effect4.Program.ActionTerm.runIn a0 a1)
  action_interrupt a0 := (Effect4.Program.ActionTerm.interrupt a0, fun _ => Effect4.Program.ActionTerm.interrupt a0)
  action_interruptScoped a0 := (Effect4.Program.ActionTerm.interruptScoped a0, fun _ => Effect4.Program.ActionTerm.interruptScoped a0)
  action_interruptAll a0 a1 := (Effect4.Program.ActionTerm.interruptAll a0 a1, fun _ => Effect4.Program.ActionTerm.interruptAll a0 a1)
  action_awaitAll a0 := (Effect4.Program.ActionTerm.awaitAll a0, fun _ => Effect4.Program.ActionTerm.awaitAll a0)
  action_awaitAllFailFast a0 := (Effect4.Program.ActionTerm.awaitAllFailFast a0, fun _ => Effect4.Program.ActionTerm.awaitAllFailFast a0)
  action_snapshotChildren := (Effect4.Program.ActionTerm.snapshotChildren, fun _ => Effect4.Program.ActionTerm.snapshotChildren)
  action_awaitNewChildren a0 := (Effect4.Program.ActionTerm.awaitNewChildren a0, fun _ => Effect4.Program.ActionTerm.awaitNewChildren a0)
  action_raceAll a0 := (Effect4.Program.ActionTerm.raceAll (a0.1), fun depth => Effect4.Program.ActionTerm.raceAll (a0.2 (Node.childLevel depth (Node.action (Effect4.Program.ActionTerm.raceAll (a0.1))) 0)))
  action_getId := (Effect4.Program.ActionTerm.getId, fun _ => Effect4.Program.ActionTerm.getId)
  action_closeScope a0 a1 := (Effect4.Program.ActionTerm.closeScope a0 a1, fun _ => Effect4.Program.ActionTerm.closeScope a0 a1)
  action_getInterruptible := (Effect4.Program.ActionTerm.getInterruptible, fun _ => Effect4.Program.ActionTerm.getInterruptible)
  action_raceAllFirst a0 := (Effect4.Program.ActionTerm.raceAllFirst (a0.1), fun depth => Effect4.Program.ActionTerm.raceAllFirst (a0.2 (Node.childLevel depth (Node.action (Effect4.Program.ActionTerm.raceAllFirst (a0.1))) 0)))
  action_context a0 := (Effect4.Program.ActionTerm.context a0, fun _ => Effect4.Program.ActionTerm.context a0)
  layer_succeed a0 a1 := (Effect4.Program.LayerTerm.succeed a0 a1, fun _ => Effect4.Program.LayerTerm.succeed a0 a1)
  layer_effect a0 a1 := (Effect4.Program.LayerTerm.effect a0 (a1.1), fun depth => Effect4.Program.LayerTerm.effect a0 (a1.2 (Node.childLevel depth (Node.layer (Effect4.Program.LayerTerm.effect a0 (a1.1))) 0)))
  layer_effectDiscard a0 := (Effect4.Program.LayerTerm.effectDiscard (a0.1), fun depth => Effect4.Program.LayerTerm.effectDiscard (a0.2 (Node.childLevel depth (Node.layer (Effect4.Program.LayerTerm.effectDiscard (a0.1))) 0)))
  layer_provide a0 a1 := (Effect4.Program.LayerTerm.provide (a0.1) (a1.1), fun depth => Effect4.Program.LayerTerm.provide (a0.2 (Node.childLevel depth (Node.layer (Effect4.Program.LayerTerm.provide (a0.1) (a1.1))) 0)) (a1.2 (Node.childLevel depth (Node.layer (Effect4.Program.LayerTerm.provide (a0.1) (a1.1))) 1)))
  layer_provideMerge a0 a1 := (Effect4.Program.LayerTerm.provideMerge (a0.1) (a1.1), fun depth => Effect4.Program.LayerTerm.provideMerge (a0.2 (Node.childLevel depth (Node.layer (Effect4.Program.LayerTerm.provideMerge (a0.1) (a1.1))) 0)) (a1.2 (Node.childLevel depth (Node.layer (Effect4.Program.LayerTerm.provideMerge (a0.1) (a1.1))) 1)))
  layer_merge a0 a1 := (Effect4.Program.LayerTerm.merge (a0.1) (a1.1), fun depth => Effect4.Program.LayerTerm.merge (a0.2 (Node.childLevel depth (Node.layer (Effect4.Program.LayerTerm.merge (a0.1) (a1.1))) 0)) (a1.2 (Node.childLevel depth (Node.layer (Effect4.Program.LayerTerm.merge (a0.1) (a1.1))) 1)))
  layer_fresh a0 := (Effect4.Program.LayerTerm.fresh (a0.1), fun depth => Effect4.Program.LayerTerm.fresh (a0.2 (Node.childLevel depth (Node.layer (Effect4.Program.LayerTerm.fresh (a0.1))) 0)))
  layer_orDie a0 := (Effect4.Program.LayerTerm.orDie (a0.1), fun depth => Effect4.Program.LayerTerm.orDie (a0.2 (Node.childLevel depth (Node.layer (Effect4.Program.LayerTerm.orDie (a0.1))) 0)))
  layer_ref a0 := (Effect4.Program.LayerTerm.ref a0, fun _ => Effect4.Program.LayerTerm.ref a0)
  layer_mergeAll a0 := (Effect4.Program.LayerTerm.mergeAll (a0.1), fun depth => Effect4.Program.LayerTerm.mergeAll (a0.2 (Node.childLevel depth (Node.layer (Effect4.Program.LayerTerm.mergeAll (a0.1))) 0)))
  layers_nil := (Effect4.Program.LayerTerms.nil, fun _ => Effect4.Program.LayerTerms.nil)
  layers_cons a0 a1 := (Effect4.Program.LayerTerms.cons (a0.1) (a1.1), fun depth => Effect4.Program.LayerTerms.cons (a0.2 (Node.childLevel depth (Node.layers (Effect4.Program.LayerTerms.cons (a0.1) (a1.1))) 0)) (a1.2 (Node.childLevel depth (Node.layers (Effect4.Program.LayerTerms.cons (a0.1) (a1.1))) 1)))

/-- Substitute a definition body's parameters after relocating its term levels. -/
def substParams (callerSize : Nat) (args : List NativeEff) (depth : Nat) (body : NativeEff) : NativeEff :=
  (cata_eff (substAlg callerSize args) body).2 depth

def inlineInvoke (callerSize : Nat) (body : NativeEff) (request : Term) (args : List NativeEff) : NativeEff :=
  .bind (.succeed request) (substParams callerSize args 1 (weakenMany 0 callerSize body))

/-- Exact candidate semantic weakening law; no typing premise is needed for inserted-slot evaluation. -/
def DenoteWeakenObligation : Prop :=
  ∀ (table : RowTable) (bodies : List NativeEff) (k : Nat) (params : List (ParamTreeB table))
    (e : NativeEff) (ctx : Ctx) (pre post : List Val) (v : Val),
    denoteBlockB table bodies k params (Eff.weaken pre.length e) ctx (pre ++ v :: post) =
      denoteBlockB table bodies k params e ctx (pre ++ post)

/-- L3 obligation on BodyRows now; captures across closed layer bodies need a further connector.
The conclusion includes the requirement row, not only answer/error subtyping. -/
def CheckSubstParamsObligation : Prop :=
  ∀ (table : RowTable) (defs : List DefDecl) (d : DefDecl) (callerParams : List ParamDecl) (env : TyEnv)
    (args : Effs NativeOp) (body : NativeEff) (tb ta : EffTy),
    let sig := (nativeSignature table).withDefs defs
    BodyRows table body = true →
    d.formed = true → d.params.length = args.toList.length →
    Checker.check (sig.withParams d.params) [d.request.normalize] [] body = .ok tb →
    d.admits tb = true → Checker.checkEffs (sig.withParams callerParams) env [] d.params args = .ok ta →
    ∃ ti, Checker.check (sig.withParams callerParams) (env ++ [d.request.normalize]) []
      (substParams env.length args.toList 1 (weakenMany 0 env.length body)) = .ok ti ∧
      Ty.sub ti.answer.normalize d.answer.normalize = true ∧
      Ty.sub ti.error.normalize d.error.normalize = true ∧
      ti.requires.Subset ((Requirement.ofList d.requires).union ta.requires)

/-- The exact universal G7 step proposal. This is an obligation, not a theorem.
The higher-order frame is arbitrary; actual argument trees keep caller captures. -/
def UniversalInvokeSandwich : Prop :=
  ∀ (table : RowTable) (bodies : List NativeEff) (j k : Nat) (body : NativeEff)
    (params : List (ParamTreeB table)) (args : Effs NativeOp) (request : Term) (ctx : Ctx) (env : List Val),
    bodies[j]? = some body → BodyRows table body = true →
    (∀ arg ∈ args.toList, BodyRows table arg = true) →
    Effects.Program.Approx
      (denoteBlockB table bodies k params (inlineInvoke env.length body request args.toList) ctx env)
      (denoteBlockB table bodies (k + 1) params (.invoke j request args) ctx env) ∧
    Effects.Program.Approx
      (denoteBlockB table bodies (k + 1) params (.invoke j request args) ctx env)
      (denoteBlockB table bodies (k + 1) params (inlineInvoke env.length body request args.toList) ctx env)

/-- Calls and invocations at every subtree, including program arguments, enter the graph. -/
def callsIn (e : NativeEff) : List Nat :=
  foldMap_eff [] List.append e fun
    | .perform (.call j) _ | .invoke j _ _ => [j]
    | _ => []

/-- A finite dependency rank excludes every direct or indirect syntactic definition cycle. -/
def Acyclic (bodies : List NativeEff) : Prop :=
  ∃ rank : Nat → Nat, ∀ i body, bodies[i]? = some body → ∀ j ∈ callsIn body,
    j < bodies.length ∧ rank j < rank i

/-- Candidate L4 contract. Totality on the stated domain excludes an always-refusing expander.
The constructor returns a path and reason outside its admitted domain. -/
def DefinitionsAgreeObligation
    (expand : NativeEff → Except (List Nat × String) NativeEff) : Prop :=
  ∀ (table : RowTable) (root : NativeEff), BlockRows table root = true →
    (Checker.checkModule (nativeSignature table) root).isOk → Acyclic (bodiesOf root) →
    ∃ expanded, expand root = .ok expanded ∧ callsIn expanded = [] ∧
      ∀ {σ : Type} (host : Effects.Comodel (RowSig table) σ) (ctx : Ctx) (env : List Val)
        (s : Stores) (st : σ) (ex : ExitV) (out : Stores × σ),
        (∃ k, hostRunBlockB host (bodiesOf root) k [] root ctx env s st = some (some ex, out)) ↔
        (∃ k, hostRunBlockB host [] k [] expanded ctx env s st = some (some ex, out))

#check Eff.weaken
#check weaken_eq_cata_eff
#check check_weaken
#check check_replace
#check table_splice
#check evalTerm_weaken

/-- The authoring form admits an actual self-cycle, not merely forward edges. -/
eff_module Recursive using self where
  again : .nat := self.again

def recursiveBuilt : Option NativeEff :=
  let r := Recursive.make "recursive"
  (Api.Author.build (r.module r.again)).toOption.map (·.program)
#guard recursiveBuilt.isSome
#guard recursiveBuilt.map (fun p => (bodiesOf p).map callsIn) = some [[0]]
#guard recursiveBuilt.map (BlockRows []) = some true

/-- Declared columns can be strictly wider than a body's inferred columns. -/
def wideDecl : DefDecl := { name := "wide", request := .unit, answer := .nat, error := .string }
def wideBody : NativeEff := .succeed (.lit (.nat 42))
#guard Checker.check ((nativeSignature []).withDefs [wideDecl]) [] []
    (.perform (.call 0) (.lit .unit)) = .ok ⟨.nat, .string, Requirement.empty⟩
#guard Checker.check (nativeSignature []) [] [] (inlineInvoke 0 wideBody (.lit .unit) []) =
    .ok ⟨.nat, .never, Requirement.empty⟩

/-- A layer body is closed in terms, but its signature still exposes the definition parameter. -/
def captureParam : ParamDecl := { name := "f", request := .unit, answer := .nat }
def numberKey : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩
def captureBody : NativeEff :=
  .provideLayer (.effect numberKey (.perform (.param 0) (.lit .unit))) false (.succeed (.lit .unit))
def captureArgument : NativeEff := .succeed (.var 0)
#guard (Checker.check ((nativeSignature []).withParams [captureParam]) [.unit] [] captureBody).isOk
#guard (Checker.checkEffs (nativeSignature []) [.nat] [] [captureParam]
    (.cons captureArgument .nil)).isOk
#guard (Checker.check (nativeSignature []) [.nat, .unit] []
    (substParams 1 [captureArgument] 1 (weakenMany 0 1 captureBody))).toOption.isNone

/-- Nested parameter forwarding exercises the transformed argument's own request binder. -/
def leaf : NativeEff := .succeed (.lit (.nat 42))
def hop : NativeEff := .perform (.call 0) (.lit .unit)
def runParam : NativeEff := .perform (.param 0) (.lit .unit)
def forwardParam : NativeEff := .invoke 2 (.lit .unit) (.cons runParam .nil)
def bodies : List NativeEff := [leaf, hop, runParam, forwardParam]
def original : NativeEff := .invoke 3 (.lit .unit) (.cons (.perform (.call 1) (.lit .unit)) .nil)
def expanded : NativeEff := inlineInvoke 0 forwardParam (.lit .unit) [.perform (.call 1) (.lit .unit)]
def silent : Effects.Comodel (RowSig []) Unit where answer op := nomatch op
#guard hostRunBlockB silent bodies 2 [] original emptyCtx [] Stores.empty () =
  some (some (.success (.nat 42)), (Stores.empty, ()))
#guard hostRunBlockB silent bodies 1 [] expanded emptyCtx [] Stores.empty () =
  some (none, (Stores.empty, ()))
#guard hostRunBlockB silent bodies 2 [] expanded emptyCtx [] Stores.empty () =
  some (some (.success (.nat 42)), (Stores.empty, ()))

/-- The caller parameter frame survives an argument inserted under a nested invocation. -/
def outerFrame : List (ParamTreeB []) := [fun _ _ => pure (some (.success (.nat 73)))]
def withCallerParam : NativeEff := .invoke 3 (.lit .unit) (.cons runParam .nil)
def expandedCallerParam : NativeEff := inlineInvoke 0 forwardParam (.lit .unit) [runParam]
#guard hostRunBlockB silent bodies 2 outerFrame withCallerParam emptyCtx [] Stores.empty () =
  some (some (.success (.nat 73)), (Stores.empty, ()))
#guard hostRunBlockB silent bodies 2 outerFrame expandedCallerParam emptyCtx [] Stores.empty () =
  some (some (.success (.nat 73)), (Stores.empty, ()))

/-- A captured caller value must pass body-local and nested argument request binders. -/
def capturedArg : NativeEff := .succeed (.var 0)
def binderBody : NativeEff := .bind (.succeed (.lit .unit)) forwardParam
def binderBodies : List NativeEff := [leaf, hop, runParam, binderBody]
def binderOriginal : NativeEff := .invoke 3 (.lit .unit) (.cons capturedArg .nil)
def binderExpanded : NativeEff := inlineInvoke 1 binderBody (.lit .unit) [capturedArg]
#guard hostRunBlockB silent binderBodies 2 [] binderOriginal emptyCtx [.nat 91] Stores.empty () =
  some (some (.success (.nat 91)), (Stores.empty, ()))
#guard hostRunBlockB silent binderBodies 2 [] binderExpanded emptyCtx [.nat 91] Stores.empty () =
  some (some (.success (.nat 91)), (Stores.empty, ()))

/-- The argument's own request slot is shifted beyond all body and nested-argument binders. -/
def capturedPair : NativeEff := .succeed (.app "pair" (.cons (.var 0) (.cons (.var 1) .nil)))
#guard hostRunBlockB silent binderBodies 2 []
    (.invoke 3 (.lit .unit) (.cons capturedPair .nil)) emptyCtx [.nat 91] Stores.empty () =
  some (some (.success (.list [.nat 91, .unit])), (Stores.empty, ()))
#guard hostRunBlockB silent binderBodies 2 []
    (inlineInvoke 1 binderBody (.lit .unit) [capturedPair]) emptyCtx [.nat 91] Stores.empty () =
  some (some (.success (.list [.nat 91, .unit])), (Stores.empty, ()))

/-- Gemini's other direction: inlining at k+1 can finish while invocation at k+1 cuts. -/
def beforeParam : NativeEff := .bind (.perform (.call 0) (.lit .unit)) runParam
#guard hostRunBlockB silent [leaf, beforeParam] 1 []
    (.invoke 1 (.lit .unit) (.cons (.succeed (.lit (.nat 99))) .nil)) emptyCtx [] Stores.empty () =
  some (none, (Stores.empty, ()))
#guard hostRunBlockB silent [leaf, beforeParam] 1 []
    (inlineInvoke 0 beforeParam (.lit .unit) [.succeed (.lit (.nat 99))]) emptyCtx [] Stores.empty () =
  some (some (.success (.nat 99)), (Stores.empty, ()))

end Effect4.Probes.CodexInline
