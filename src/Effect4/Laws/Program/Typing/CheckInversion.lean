import Effect4.Program.Checker
import Effect4.Laws.Auto.Inversion

/-!
# Laws.Program.Typing.CheckInversion — what a successful check says of its parts

One inversion per arm of the fold checker `Checker.check` (`Program/Checker.lean`): from
`check sig env p e = .ok t`, the premises of that arm — the children's checks at their paths,
the rules' answers, and `t` in the rule's own terms. Every proof is `aesop`, with the checker's
equations and the generic `Except` inversions (`Laws/Auto/Inversion.lean`) as its normalisation
rules; `expect_eq_ok` is the one project-specific rule, for every rule that answers an
`Option`. The typing proof graph (`CheckSound.lean`) is built on these, and the path is carried
so that soundness and completeness hold at every path — which is what makes the success
projection path-independent.
-/

namespace Effect4.Program.Checker

open Effect4.Machine.Env (Requirement)

variable {Op : Type}

/-- An `Option`-answering rule succeeds exactly when it answers. -/
theorem expect_eq_ok {α : Type} (r : TypeRefusal) (o : Option α) (a : α) :
    expect r o = .ok a ↔ o = some a := by
  cases o with
  | none => simp only [expect, reduceCtorEq]
  | some b => simp only [expect, Except.ok.injEq, Option.some.injEq]

/-- The element type of a list type, inverted. -/
theorem listOf?_eq_some (t inner : Ty) : listOf? t = some inner ↔ t = .list inner := by
  cases t <;> simp only [listOf?, reduceCtorEq, Option.some.injEq, Ty.list.injEq]

/-- The value and error types of an exit type, inverted. -/
theorem exitOf?_eq_some (t : Ty) (x : Ty × Ty) : exitOf? t = some x ↔ t = .exitOf x.1 x.2 := by
  cases x
  cases t <;> simp only [exitOf?, reduceCtorEq, Option.some.injEq, Ty.exitOf.injEq, Prod.mk.injEq]

attribute [aesop norm simp] expect_eq_ok listOf?_eq_some exitOf?_eq_some term? check checkStmt
  checkStmts checkEffs checkAction checkLayer checkLayers StmtTy.fold GenTy.mergeT
  GenTy.joinAnswerT EffTy.joinAnswer_eq GenTy.merge_eq

/-! ## `check` — one lemma per constructor (`awaitFiber` splits on the observer mode) -/

theorem inv_succeed (sig : Signature Op) (env : TyEnv) (p : List Nat) (value : Term) :
    ∀ t, check sig env p (.succeed value) = .ok t →
      ∃ ty, termTy sig env value = some ty ∧ t = EffTy.pure ty := by
  aesop

theorem inv_fail (sig : Signature Op) (env : TyEnv) (p : List Nat) (error : Term) :
    ∀ t, check sig env p (.fail error) = .ok t →
      ∃ ty, termTy sig env error = some ty ∧ admittedErrTy ty = true ∧
        t = ⟨.never, ty, Requirement.empty⟩ := by
  aesop

theorem inv_failCause (sig : Signature Op) (env : TyEnv) (p : List Nat) (cause : CauseTerm) :
    ∀ t, check sig env p (.failCause cause) = .ok t →
      ∃ ty, causeTy sig env cause = some ty ∧ t = ⟨.never, ty, Requirement.empty⟩ := by
  aesop

theorem inv_sync (sig : Signature Op) (env : TyEnv) (p : List Nat) (thunk : Term) :
    ∀ t, check sig env p (.sync thunk) = .ok t →
      ∃ ty, termTy sig env thunk = some ty ∧ t = EffTy.pure ty := by
  aesop

theorem inv_suspend (sig : Signature Op) (env : TyEnv) (p : List Nat) (body : Eff Op) :
    ∀ t, check sig env p (.suspend body) = .ok t → check sig env (p ++ [0]) body = .ok t := by
  aesop

theorem inv_perform (sig : Signature Op) (env : TyEnv) (p : List Nat) (op : Op) (request : Term) :
    ∀ t, check sig env p (.perform op request) = .ok t →
      ∃ requestTy, sig.dom op = true ∧ termTy sig env request = some requestTy ∧
        rowTy (sig.rowOf op) requestTy = some t := by
  aesop

theorem inv_bind (sig : Signature Op) (env : TyEnv) (p : List Nat) (first rest : Eff Op) :
    ∀ t, check sig env p (.bind first rest) = .ok t →
      ∃ f r, check sig env (p ++ [0]) first = .ok f ∧
        check sig (env ++ [f.answer]) (p ++ [1]) rest = .ok r ∧
        t = ⟨r.answer, f.error.join r.error, f.requires.union r.requires⟩ := by
  aesop

theorem inv_gen (sig : Signature Op) (env : TyEnv) (p : List Nat) (body : Stmts Op) :
    ∀ t, check sig env p (.gen body) = .ok t →
      ∃ g, checkStmts sig env false none (p ++ [0]) body = .ok g ∧
        t = ⟨g.answer.getD .unit, g.error, g.requires⟩ := by
  aesop

theorem inv_catchCause (sig : Signature Op) (env : TyEnv) (p : List Nat) (body handler : Eff Op) :
    ∀ t, check sig env p (.catchCause body handler) = .ok t →
      ∃ b h, check sig env (p ++ [0]) body = .ok b ∧
        check sig (env ++ [.causeOf b.error]) (p ++ [1]) handler = .ok h ∧
        t = ⟨Ty.join b.answer h.answer, h.error, b.requires.union h.requires⟩ := by
  aesop

theorem inv_catchIf (sig : Signature Op) (env : TyEnv) (p : List Nat) (test : Term)
    (body handler : Eff Op) :
    ∀ t, check sig env p (.catchIf test body handler) = .ok t →
      ∃ b h, check sig env (p ++ [0]) body = .ok b ∧
        termTy sig (env ++ [b.error]) test = some .bool ∧
        check sig (env ++ [b.error]) (p ++ [1]) handler = .ok h ∧
        t = ⟨Ty.join b.answer h.answer, catchIfError test env.length b.error h.error,
          b.requires.union h.requires⟩ := by
  aesop

theorem inv_matchCause (sig : Signature Op) (env : TyEnv) (p : List Nat)
    (body onValue onCause : Eff Op) :
    ∀ t, check sig env p (.matchCause body onValue onCause) = .ok t →
      ∃ b v c, check sig env (p ++ [0]) body = .ok b ∧
        check sig (env ++ [b.answer]) (p ++ [1]) onValue = .ok v ∧
        check sig (env ++ [.causeOf b.error]) (p ++ [2]) onCause = .ok c ∧
        t = ⟨Ty.join v.answer c.answer, v.error.join c.error,
          (b.requires.union v.requires).union c.requires⟩ := by
  aesop

theorem inv_onExit (sig : Signature Op) (env : TyEnv) (p : List Nat) (body finalizer : Eff Op) :
    ∀ t, check sig env p (.onExit body finalizer) = .ok t →
      ∃ b f, check sig env (p ++ [0]) body = .ok b ∧
        check sig (env ++ [.exitOf b.answer b.error]) (p ++ [1]) finalizer = .ok f ∧
        t = ⟨b.answer, b.error.join f.error, b.requires.union f.requires⟩ := by
  aesop

theorem inv_exit (sig : Signature Op) (env : TyEnv) (p : List Nat) (body : Eff Op) :
    ∀ t, check sig env p (.exit body) = .ok t →
      ∃ b, check sig env (p ++ [0]) body = .ok b ∧
        t = ⟨.exitOf b.answer b.error, .never, b.requires⟩ := by
  aesop

theorem inv_uninterruptible (sig : Signature Op) (env : TyEnv) (p : List Nat) (body : Eff Op) :
    ∀ t, check sig env p (.uninterruptible body) = .ok t →
      check sig env (p ++ [0]) body = .ok t := by
  aesop

theorem inv_interruptible (sig : Signature Op) (env : TyEnv) (p : List Nat) (body : Eff Op) :
    ∀ t, check sig env p (.interruptible body) = .ok t →
      check sig env (p ++ [0]) body = .ok t := by
  aesop

theorem inv_select (sig : Signature Op) (env : TyEnv) (p : List Nat) (s : Term) (d : Decision)
    (a0 a1 : Eff Op) :
    ∀ t, check sig env p (.select s d a0 a1) = .ok t →
      ∃ ty arms t0 t1, termTy sig env s = some ty ∧ d.arms ty = some arms ∧
        check sig (env ++ arms.1) (p ++ [0]) a0 = .ok t0 ∧
        check sig (env ++ arms.2) (p ++ [1]) a1 = .ok t1 ∧
        t = ⟨Ty.join t0.answer t1.answer, t0.error.join t1.error,
          t0.requires.union t1.requires⟩ := by
  aesop

theorem inv_iterate (sig : Signature Op) (env : TyEnv) (p : List Nat) (cursorTy : Option Ty)
    (initial test step result : Term) (body : Eff Op) :
    ∀ t, check sig env p (.iterate cursorTy initial test step result body) = .ok t →
      ∃ c0 c1 d b, termTy sig env initial = some c0 ∧
        termTy sig (env ++ [cursorTy.getD c0]) test = some .bool ∧
        check sig (env ++ [cursorTy.getD c0]) (p ++ [0]) body = .ok b ∧
        termTy sig (env ++ [cursorTy.getD c0, b.answer]) step = some c1 ∧
        termTy sig (env ++ [cursorTy.getD c0]) result = some d ∧
        Ty.sub c0.normalize (cursorTy.getD c0).normalize = true ∧
        Ty.sub c1.normalize (cursorTy.getD c0).normalize = true ∧
        t = ⟨d, b.error, b.requires⟩ := by
  aesop

theorem inv_yieldNow (sig : Signature Op) (env : TyEnv) (p : List Nat) (priority : Nat) :
    ∀ t, check sig env p (.yieldNow priority) = .ok t → t = EffTy.pure .unit := by
  aesop

theorem inv_awaitFiber_join (sig : Signature Op) (env : TyEnv) (p : List Nat) (fiber : Term) :
    ∀ t, check sig env p (.awaitFiber fiber .joinEffect) = .ok t →
      ∃ (handle : Ty) (pair : Ty × Ty), termTy sig env fiber = some handle ∧
        fiberTy handle = some pair ∧ t = ⟨pair.1, pair.2, Requirement.empty⟩ := by
  aesop

theorem inv_awaitFiber_await (sig : Signature Op) (env : TyEnv) (p : List Nat) (fiber : Term) :
    ∀ t, check sig env p (.awaitFiber fiber .awaitValue) = .ok t →
      ∃ (handle : Ty) (pair : Ty × Ty), termTy sig env fiber = some handle ∧
        fiberTy handle = some pair ∧ t = EffTy.pure (.exitOf pair.1 pair.2) := by
  aesop

theorem inv_withFiber (sig : Signature Op) (env : TyEnv) (p : List Nat) (action : ActionTerm Op) :
    ∀ t, check sig env p (.withFiber action) = .ok t →
      checkAction sig env (p ++ [0]) action = .ok t := by
  aesop

theorem inv_scoped (sig : Signature Op) (env : TyEnv) (p : List Nat) (body : Eff Op) :
    ∀ t, check sig env p (.scoped body) = .ok t →
      ∃ b, check sig env (p ++ [0]) body = .ok b ∧
        t = { b with requires := bodyRequires sig b } := by
  aesop

theorem inv_acquireRelease (sig : Signature Op) (env : TyEnv) (p : List Nat)
    (acquire release : Eff Op) :
    ∀ t, check sig env p (.acquireRelease acquire release) = .ok t →
      ∃ a r, check sig env (p ++ [0]) acquire = .ok a ∧
        check sig (env ++ [a.answer, .exitOf a.answer a.error]) (p ++ [1]) release = .ok r ∧
        t = ⟨a.answer, a.error,
              (a.requires.union r.requires).union (Requirement.single sig.scopeKey)⟩ := by
  aesop

theorem inv_provideLayer (sig : Signature Op) (env : TyEnv) (p : List Nat) (layer : LayerTerm Op)
    (isLocal : Bool) (body : Eff Op) :
    ∀ t, check sig env p (.provideLayer layer isLocal body) = .ok t →
      ∃ l b, checkLayer sig (p ++ [0]) layer = .ok l ∧ check sig env (p ++ [1]) body = .ok b ∧
        t = ⟨b.answer, b.error.join l.error,
              Row.union l.requires (Row.diff b.requires l.out)⟩ := by
  aesop

theorem inv_service (sig : Signature Op) (env : TyEnv) (p : List Nat) (key : ServiceKey) :
    ∀ t, check sig env p (.service key) = .ok t →
      ∃ ty, sig.serviceTy key = some ty ∧ t = ⟨ty, .never, Requirement.single key⟩ := by
  aesop

theorem inv_provideService (sig : Signature Op) (env : TyEnv) (p : List Nat) (key : ServiceKey)
    (value : Term) (body : Eff Op) :
    ∀ t, check sig env p (.provideService key value body) = .ok t →
      ∃ ty valueTy b, sig.serviceTy key = some ty ∧ termTy sig env value = some valueTy ∧
        Ty.sub valueTy.normalize ty.normalize = true ∧
        check sig env (p ++ [0]) body = .ok b ∧
        t = ⟨b.answer, b.error, Row.diff b.requires (Requirement.single key)⟩ := by
  aesop

/-! ## `checkStmts` under `afterRet := none` — eight lemmas (`ret` splits on its tail) -/

theorem inv_stmts_nil (sig : Signature Op) (env : TyEnv) (inLoop : Bool) (p : List Nat) :
    ∀ g, checkStmts sig env inLoop none p .nil = .ok g →
      g = ⟨none, .never, Requirement.empty⟩ := by
  aesop

theorem inv_stmts_bindYield (sig : Signature Op) (env : TyEnv) (inLoop : Bool) (p : List Nat)
    (effect : Eff Op) (rest : Stmts Op) :
    ∀ g, checkStmts sig env inLoop none p (.cons (.bindYield effect) rest) = .ok g →
      ∃ t r, check sig env (p ++ [0, 0]) effect = .ok t ∧
        checkStmts sig (env ++ [t.answer]) inLoop none (p ++ [1]) rest = .ok r ∧
        g = ⟨r.answer, t.error.join r.error, t.requires.union r.requires⟩ := by
  aesop

theorem inv_stmts_yieldDiscard (sig : Signature Op) (env : TyEnv) (inLoop : Bool) (p : List Nat)
    (effect : Eff Op) (rest : Stmts Op) :
    ∀ g, checkStmts sig env inLoop none p (.cons (.yieldDiscard effect) rest) = .ok g →
      ∃ t r, check sig env (p ++ [0, 0]) effect = .ok t ∧
        checkStmts sig env inLoop none (p ++ [1]) rest = .ok r ∧
        g = ⟨r.answer, t.error.join r.error, t.requires.union r.requires⟩ := by
  aesop

theorem inv_stmts_ret (sig : Signature Op) (env : TyEnv) (inLoop : Bool) (p : List Nat)
    (value : Term) :
    ∀ g, checkStmts sig env inLoop none p (.cons (.ret value) .nil) = .ok g →
      ∃ ty, termTy sig env value = some ty ∧ g = ⟨some ty, .never, Requirement.empty⟩ := by
  aesop

theorem inv_stmts_ret_cons (sig : Signature Op) (env : TyEnv) (inLoop : Bool) (p : List Nat)
    (value : Term) (head : Stmt Op) (tail : Stmts Op) :
    ∀ g, checkStmts sig env inLoop none p (.cons (.ret value) (.cons head tail)) = .ok g →
      False := by
  aesop

theorem inv_stmts_ifElse (sig : Signature Op) (env : TyEnv) (inLoop : Bool) (p : List Nat)
    (test : Term) (thenB elseB rest : Stmts Op) :
    ∀ g, checkStmts sig env inLoop none p (.cons (.ifElse test thenB elseB) rest) = .ok g →
      termTy sig env test = some .bool ∧ ∃ a b r,
        checkStmts sig env inLoop none (p ++ [0, 0]) thenB = .ok a ∧
        checkStmts sig env inLoop none (p ++ [0, 1]) elseB = .ok b ∧
        checkStmts sig env inLoop none (p ++ [1]) rest = .ok r ∧
        g = GenTy.mergeT (GenTy.mergeT a b) r := by
  aesop

theorem inv_stmts_whileTrue (sig : Signature Op) (env : TyEnv) (inLoop : Bool) (p : List Nat)
    (body rest : Stmts Op) :
    ∀ g, checkStmts sig env inLoop none p (.cons (.whileTrue body) rest) = .ok g →
      ∃ b r, checkStmts sig env true none (p ++ [0, 0]) body = .ok b ∧
        checkStmts sig env inLoop none (p ++ [1]) rest = .ok r ∧ g = GenTy.mergeT b r := by
  aesop

theorem inv_stmts_breakLoop (sig : Signature Op) (env : TyEnv) (inLoop : Bool) (p : List Nat)
    (rest : Stmts Op) :
    ∀ g, checkStmts sig env inLoop none p (.cons .breakLoop rest) = .ok g →
      inLoop = true ∧ checkStmts sig env inLoop none (p ++ [1]) rest = .ok g := by
  aesop

/-! ## `checkEffs` — two arms -/

theorem inv_effs_nil (sig : Signature Op) (env : TyEnv) (p : List Nat) :
    ∀ t, checkEffs sig env p .nil = .ok t → t = ⟨.never, .never, Requirement.empty⟩ := by
  aesop

theorem inv_effs_cons (sig : Signature Op) (env : TyEnv) (p : List Nat) (head : Eff Op)
    (tail : Effs Op) :
    ∀ t, checkEffs sig env p (.cons head tail) = .ok t →
      ∃ h r, check sig env (p ++ [0]) head = .ok h ∧ checkEffs sig env (p ++ [1]) tail = .ok r ∧
        t = ⟨Ty.join h.answer r.answer, h.error.join r.error, h.requires.union r.requires⟩ := by
  aesop

/-! ## `checkAction` — sixteen constructors, seventeen lemmas -/

theorem inv_action_fork (sig : Signature Op) (env : TyEnv) (p : List Nat) (program : Eff Op)
    (options : Supervision.ForkOptions) :
    ∀ t, checkAction sig env p (.fork program options) = .ok t →
      ∃ q, check sig env (p ++ [0]) program = .ok q ∧
        t = ⟨.fiberOf q.answer q.error, .never, q.requires⟩ := by
  aesop

theorem inv_action_forkIn (sig : Signature Op) (env : TyEnv) (p : List Nat) (program : Eff Op)
    (options : Supervision.ForkOptions) (scope : Term) :
    ∀ t, checkAction sig env p (.forkIn program options scope) = .ok t →
      ∃ q, check sig env (p ++ [0]) program = .ok q ∧ termTy sig env scope = some Ty.scope ∧
        t = ⟨.fiberOf q.answer q.error, .never, q.requires⟩ := by
  aesop

theorem inv_action_forkScoped (sig : Signature Op) (env : TyEnv) (p : List Nat) (program : Eff Op)
    (options : Supervision.ForkOptions) :
    ∀ t, checkAction sig env p (.forkScoped program options) = .ok t →
      ∃ q, check sig env (p ++ [0]) program = .ok q ∧
        t = ⟨.fiberOf q.answer q.error, .never,
              q.requires.union (Requirement.single sig.scopeKey)⟩ := by
  aesop

theorem inv_action_runIn (sig : Signature Op) (env : TyEnv) (p : List Nat) (target scope : Term) :
    ∀ t, checkAction sig env p (.runIn target scope) = .ok t →
      ∃ (handle : Ty) (pair : Ty × Ty), termTy sig env target = some handle ∧
        fiberTy handle = some pair ∧ termTy sig env scope = some Ty.scope ∧
        t = EffTy.pure .unit := by
  aesop

theorem inv_action_interrupt (sig : Signature Op) (env : TyEnv) (p : List Nat) (target : Term) :
    ∀ t, checkAction sig env p (.interrupt target) = .ok t →
      ∃ (handle : Ty) (pair : Ty × Ty), termTy sig env target = some handle ∧
        fiberTy handle = some pair ∧ t = EffTy.pure .unit := by
  aesop

theorem inv_action_interruptScoped (sig : Signature Op) (env : TyEnv) (p : List Nat)
    (target : Term) :
    ∀ t, checkAction sig env p (.interruptScoped target) = .ok t →
      ∃ (handle : Ty) (pair : Ty × Ty), termTy sig env target = some handle ∧
        fiberTy handle = some pair ∧ t = EffTy.pure .unit := by
  aesop

theorem inv_action_interruptAll_self (sig : Signature Op) (env : TyEnv) (p : List Nat)
    (targets : Term) :
    ∀ t, checkAction sig env p (.interruptAll targets none) = .ok t →
      ∃ (inner : Ty) (pair : Ty × Ty), termTy sig env targets = some (.list inner) ∧
        fiberTy inner = some pair ∧ t = EffTy.pure .unit := by
  aesop

theorem inv_action_interruptAll_by (sig : Signature Op) (env : TyEnv) (p : List Nat)
    (targets who : Term) :
    ∀ t, checkAction sig env p (.interruptAll targets (some who)) = .ok t →
      ∃ (inner : Ty) (pair : Ty × Ty), termTy sig env targets = some (.list inner) ∧
        fiberTy inner = some pair ∧ termTy sig env who = some .nat ∧
        t = EffTy.pure .unit := by
  aesop

theorem inv_action_awaitAll (sig : Signature Op) (env : TyEnv) (p : List Nat) (targets : Term) :
    ∀ t, checkAction sig env p (.awaitAll targets) = .ok t →
      ∃ (inner : Ty) (pair : Ty × Ty), termTy sig env targets = some (.list inner) ∧
        fiberTy inner = some pair ∧ t = EffTy.pure (.list (.exitOf pair.1 pair.2)) := by
  aesop

theorem inv_action_awaitAllFailFast (sig : Signature Op) (env : TyEnv) (p : List Nat)
    (targets : Term) :
    ∀ t, checkAction sig env p (.awaitAllFailFast targets) = .ok t →
      ∃ (inner : Ty) (pair : Ty × Ty), termTy sig env targets = some (.list inner) ∧
        fiberTy inner = some pair ∧ t = EffTy.pure (.list (.exitOf pair.1 pair.2)) := by
  aesop

theorem inv_action_snapshotChildren (sig : Signature Op) (env : TyEnv) (p : List Nat) :
    ∀ t, checkAction sig env p (.snapshotChildren : ActionTerm Op) = .ok t →
      t = EffTy.pure (.list (.fiberOf (.handle "unknown") (.handle "unknown"))) := by
  aesop

theorem inv_action_awaitNewChildren (sig : Signature Op) (env : TyEnv) (p : List Nat)
    (snapshot : Term) :
    ∀ t, checkAction sig env p (.awaitNewChildren snapshot) = .ok t →
      termTy sig env snapshot =
          some (.list (.fiberOf (.handle "unknown") (.handle "unknown"))) ∧
        t = EffTy.pure .unit := by
  aesop

theorem inv_action_raceAll (sig : Signature Op) (env : TyEnv) (p : List Nat) (entrants : Effs Op) :
    ∀ t, checkAction sig env p (.raceAll entrants) = .ok t →
      checkEffs sig env (p ++ [0]) entrants = .ok t := by
  aesop

theorem inv_action_setContext (sig : Signature Op) (env : TyEnv) (p : List Nat) (context : Term) :
    ∀ t, checkAction sig env p (.setContext context) = .ok t →
      termTy sig env context = some Ty.context ∧ t = EffTy.pure .unit := by
  aesop

theorem inv_action_getContext (sig : Signature Op) (env : TyEnv) (p : List Nat) :
    ∀ t, checkAction sig env p (.getContext : ActionTerm Op) = .ok t →
      t = EffTy.pure Ty.context := by
  aesop

theorem inv_action_getId (sig : Signature Op) (env : TyEnv) (p : List Nat) :
    ∀ t, checkAction sig env p (.getId : ActionTerm Op) = .ok t → t = EffTy.pure .nat := by
  aesop

theorem inv_action_closeScope (sig : Signature Op) (env : TyEnv) (p : List Nat)
    (scope exit : Term) :
    ∀ t, checkAction sig env p (.closeScope scope exit) = .ok t →
      ∃ pair : Ty × Ty, termTy sig env scope = some Ty.scope ∧
        termTy sig env exit = some (.exitOf pair.1 pair.2) ∧ t = EffTy.pure .unit := by
  aesop

/-! ## `checkLayer` — ten arms, one of which is a refusal -/

theorem inv_layer_succeed (sig : Signature Op) (p : List Nat) (key : ServiceKey) (value : Lit) :
    ∀ l, checkLayer sig p (.succeed key value : LayerTerm Op) = .ok l →
      ∃ v, litVal value = some v ∧
        l = ⟨Requirement.single key, .never, Requirement.empty⟩ := by
  aesop

theorem inv_layer_effect (sig : Signature Op) (p : List Nat) (key : ServiceKey) (body : Eff Op) :
    ∀ l, checkLayer sig p (.effect key body) = .ok l →
      ∃ t, check sig [] (p ++ [0]) body = .ok t ∧
        l = ⟨Requirement.single key, t.error, bodyRequires sig t⟩ := by
  aesop

theorem inv_layer_effectDiscard (sig : Signature Op) (p : List Nat) (body : Eff Op) :
    ∀ l, checkLayer sig p (.effectDiscard body) = .ok l →
      ∃ t, check sig [] (p ++ [0]) body = .ok t ∧
        l = ⟨Requirement.empty, t.error, bodyRequires sig t⟩ := by
  aesop

theorem inv_layer_provide (sig : Signature Op) (p : List Nat) (self that : LayerTerm Op) :
    ∀ l, checkLayer sig p (.provide self that) = .ok l →
      ∃ s t, checkLayer sig (p ++ [0]) self = .ok s ∧ checkLayer sig (p ++ [1]) that = .ok t ∧
        l = s.provide t := by
  aesop

theorem inv_layer_provideMerge (sig : Signature Op) (p : List Nat) (self that : LayerTerm Op) :
    ∀ l, checkLayer sig p (.provideMerge self that) = .ok l →
      ∃ s t, checkLayer sig (p ++ [0]) self = .ok s ∧ checkLayer sig (p ++ [1]) that = .ok t ∧
        l = s.provideMerge t := by
  aesop

theorem inv_layer_merge (sig : Signature Op) (p : List Nat) (left right : LayerTerm Op) :
    ∀ l, checkLayer sig p (.merge left right) = .ok l →
      ∃ a b, checkLayer sig (p ++ [0]) left = .ok a ∧ checkLayer sig (p ++ [1]) right = .ok b ∧
        l = a.merge b := by
  aesop

theorem inv_layer_fresh (sig : Signature Op) (p : List Nat) (inner : LayerTerm Op) :
    ∀ l, checkLayer sig p (.fresh inner) = .ok l → checkLayer sig (p ++ [0]) inner = .ok l := by
  aesop

theorem inv_layer_orDie (sig : Signature Op) (p : List Nat) (inner : LayerTerm Op) :
    ∀ l, checkLayer sig p (.orDie inner) = .ok l →
      ∃ i, checkLayer sig (p ++ [0]) inner = .ok i ∧ l = i.orDie := by
  aesop

theorem inv_layer_ref (sig : Signature Op) (p : List Nat) (target : List Nat) :
    ∀ l, checkLayer sig p (.ref target : LayerTerm Op) = .ok l → False := by
  aesop

theorem inv_layer_mergeAll (sig : Signature Op) (p : List Nat) (layers : LayerTerms Op) :
    ∀ l, checkLayer sig p (.mergeAll layers) = .ok l →
      ∃ ls, checkLayers sig (p ++ [0]) layers = .ok ls ∧ LayerTy.mergeNonempty ls = some l := by
  aesop

/-! ## `checkLayers` — the list of signatures -/

theorem inv_layers_nil (sig : Signature Op) (p : List Nat) :
    ∀ ls, checkLayers sig p (.nil : LayerTerms Op) = .ok ls → ls = [] := by
  aesop

theorem inv_layers_cons (sig : Signature Op) (p : List Nat) (head : LayerTerm Op)
    (tail : LayerTerms Op) :
    ∀ ls, checkLayers sig p (.cons head tail) = .ok ls →
      ∃ h t, checkLayer sig (p ++ [0]) head = .ok h ∧ checkLayers sig (p ++ [1]) tail = .ok t ∧
        ls = h :: t := by
  aesop

end Effect4.Program.Checker
