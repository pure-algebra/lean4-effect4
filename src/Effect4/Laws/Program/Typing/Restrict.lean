import Effect4.Laws.Program.Typing.PartsTable
import Effect4.Laws.Auto.Semantics

/-!
# Laws.Program.Typing.Restrict — a whole program's table at a larger signature

C3's restriction half (`check_restrict`, `Laws/Program/Signature.lean`) says that the checker
answers the same at an extension of the signature, on a program that reads only the smaller
signature's operations and keys (`SigProgram`). This module lifts it to the address table: the
annotating traversal is a fold too (`Annotate.check.eq_cata`), so the same fold congruence
(`cata_eff_congr_on`) gives its restriction, once its algebra agrees with itself across the
extension. A typed program reads only its signature (`hasTy_sigProgram`), so a typed whole
program's table is unchanged when the signature grows.

| Statement | In words |
| --- | --- |
| `Annotate.check_alg_agreeOn` | the annotating algebra agrees with itself across an extension, on the read guard |
| `Annotate.check_restrict` | so the traversal answers the same at the extension |
| `annotateModule_restrict` | and so does a whole program's table, part by part |
| `hasTy_sigProgram` | a typed program reads only its signature |
| `moduleHasTy_sigProgram` | so does a typed whole program, part by part |

## Placement

Concept `initial-algebras-folds`; property: two folds agree where their algebras agree on the
nodes that a program has. Requirement R14, under decisions row 334.

- Every statement is a step of the claim `omit-splices-table` (pointer `Sketch.table_omit`,
  `Laws/Program/Edit.lean`): an omission grows the hole table, and a typed sketch's table stays
  (`Sketch.table_more_holes`). Reach: an extension of the signature (`SigExtends`). Not
  established: a program that reads an operation the smaller signature lacks.
-/

set_option autoImplicit false

namespace Effect4.Program

open Conform.Effect4.Typing

variable {Op : Type}

/-- **The annotating algebra agrees with itself across an extension**, on the read guard of the
smaller signature: at a leaf it is the checker's answer, whose algebra agrees
(`check_alg_agreeOn`), and every other field reads the signature only through the terms' checker
(`term?_ext`). A step of `omit-splices-table`. Its consumer is `Annotate.check_restrict`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Annotate.check_alg_agreeOn {s s' : Signature Op} (h : SigExtends s s') :
    (Annotate.check.alg s').AgreeOn (Annotate.check.alg s) (SigOkOp s) (SigOkKey s)
      (SigOkDef s) := by
  have hterm := term?_ext h
  have hcause := cause?_ext h
  have hbody : bodyRequires s' = bodyRequires s := funext h.bodyRequires
  exact {
    eff_succeed := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    eff_fail := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    eff_failCause := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    eff_sync := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    eff_suspend := rfl
    eff_perform := fun op hd => by
      have hdom : s.dom op = true := hd
      simp only [Annotate.check.alg, Checker.check, hterm, (h.row op hdom).1, (h.row op hdom).2,
        hdom, h.termUse]
    eff_bind := rfl
    eff_gen := rfl
    eff_catchCause := rfl
    eff_matchCause := rfl
    eff_onExit := rfl
    eff_exit := rfl
    eff_uninterruptible := rfl
    eff_interruptible := rfl
    eff_yieldNow := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    eff_awaitFiber := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    eff_withFiber := rfl
    eff_scoped := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    eff_acquireRelease := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    eff_provideLayer := rfl
    eff_service := fun key hk => by
      obtain ⟨ty, hty⟩ := Option.isSome_iff_exists.mp hk
      simp only [Annotate.check.alg, Checker.check, h.service key ty hty, hty]
    eff_provideService := fun key hk => by
      obtain ⟨ty, hty⟩ := Option.isSome_iff_exists.mp hk
      simp only [Annotate.check.alg, h.service key ty hty, hty, hterm]
    eff_catchIf := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    eff_select := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    eff_iterate := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    eff_restore := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    eff_defs := rfl
    eff_invoke := fun k hk => by
      obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hk
      simp only [Annotate.check.alg, h.defOf k d hd, hd, hterm]
    stmt_bindYield := rfl
    stmt_yieldDiscard := rfl
    stmt_ret := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    stmt_ifElse := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    stmt_whileTrue := rfl
    stmt_breakLoop := rfl
    stmts_nil := rfl
    stmts_cons := rfl
    effs_nil := rfl
    effs_cons := rfl
    action_fork := rfl
    action_forkIn := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    action_forkScoped := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    action_runIn := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    action_interrupt := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    action_interruptScoped := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    action_interruptAll := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    action_awaitAll := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    action_awaitAllFailFast := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    action_snapshotChildren := rfl
    action_awaitNewChildren := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    action_raceAll := rfl
    action_setContext := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    action_getContext := rfl
    action_getId := rfl
    action_closeScope := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    action_getInterruptible := rfl
    layer_succeed := fun key hk => by
      obtain ⟨ty, hty⟩ := Option.isSome_iff_exists.mp hk
      simp only [Annotate.check.alg, Checker.checkLayer, h.service key ty hty, hty]
    layer_effect := fun key hk => by
      obtain ⟨ty, hty⟩ := Option.isSome_iff_exists.mp hk
      simp only [Annotate.check.alg, h.service key ty hty, hty, hbody]
    layer_effectDiscard := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    layer_provide := rfl
    layer_provideMerge := rfl
    layer_merge := rfl
    layer_fresh := rfl
    layer_orDie := rfl
    layer_ref := rfl
    layer_mergeAll := rfl
    layers_nil := rfl
    layers_cons := rfl
  }

/-- **The annotating traversal answers the same at an extension**, on a program that reads only
the smaller signature. The fold congruence at `Annotate.check_alg_agreeOn`. A step of
`omit-splices-table`. Its consumers are `Table.bodies_restrict` and `annotateModule_restrict`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Annotate.check_restrict {s s' : Signature Op} (h : SigExtends s s') {e : Eff Op}
    (hp : SigProgram s e) (env : TyEnv) (p : List Nat) :
    Annotate.check s' env p e = Annotate.check s env p e := by
  rw [Annotate.check.eq_cata, Annotate.check.eq_cata]
  rw [cata_eff_congr_on (Annotate.check_alg_agreeOn h) e hp]

/-- The bodies' spine answers the same at an extension. A step of `omit-splices-table`. Its
consumer is `annotateModule_restrict`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Table.bodies_restrict {s s' : Signature Op} (h : SigExtends s s') :
    ∀ (decls : List DefDecl) (bodies : Effs Op) (base : List Nat),
      BodiesSigProgram s decls bodies →
      Table.bodies s' decls bodies base = Table.bodies s decls bodies base
  | d :: ds, .cons body rest, base, ⟨hbody, hrest⟩ => by
    simp only [Table.bodies, Annotate.check_restrict (h.withParams d.params) hbody,
      Table.bodies_restrict h ds rest (base ++ [1]) hrest]
  | [], .cons body rest, base, _ => by
    simp only [Table.bodies, Table.bodies_restrict h [] rest (base ++ [1]) trivial]
  | [], .nil, _, _ => rfl
  | _ :: _, .nil, _, _ => rfl

/-- **A whole program's table answers the same at an extension**, part by part, on a whole
program that reads only the smaller signature. A step of `omit-splices-table`. Its consumer is
`Sketch.table_more_holes`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem annotateModule_restrict {s s' : Signature Op} (h : SigExtends s s')
    (root : Except TypeRefusal EffTy) {e : Eff Op} (hp : ModuleSigProgram s e) :
    annotateModule s' root e = annotateModule s root e := by
  cases e
  case defs decls bodies main =>
    obtain ⟨hb, hm⟩ := hp
    simp only [annotateModule, Table.bodies_restrict (h.withDefs decls) decls bodies [0] hb,
      Annotate.check_restrict (h.withDefs decls) hm]
  all_goals
    simp only [annotateModule, annotate]
    rw [Annotate.check_restrict h hp]

/-- A key that a signature types has a carrier there. A step of `omit-splices-table`. Its
consumers are the service rules of `hasTy_sigProgram`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem sigOkKey_of_serviceTy {s : Signature Op} {key : ServiceKey} {ty : Ty}
    (hk : s.serviceTy key = some ty) : SigOkKey s key := by
  show (s.serviceTy key).isSome = true
  rw [hk]
  rfl

mutual
/-- **A typed program reads only its signature**: every operation it performs is in the
signature's domain, and every service key it reads has a carrier. One case for each typing rule,
judgment by judgment, as `hasTy_ext` is. A step of `omit-splices-table`. Its consumer is
`moduleHasTy_sigProgram`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem hasTy_sigProgram {s : Signature Op} :
    ∀ {env : TyEnv} {e : Eff Op} {t : EffTy}, HasTy s env e t → SigProgram s e
  | _, _, _, .succeed _ => True.intro
  | _, _, _, .fail _ _ => True.intro
  | _, _, _, .failCause _ => True.intro
  | _, _, _, .sync _ => True.intro
  | _, _, _, .suspend hb =>
    have hchild := hasTy_sigProgram hb
    hchild
  | _, _, _, .perform hdom _ _ => hdom
  | _, _, _, .bind hf hr => And.intro (hasTy_sigProgram hf) (hasTy_sigProgram hr)
  | _, _, _, .gen hb =>
    have hchild := stmtsHasTy_sigProgram hb
    hchild
  | _, _, _, .catchCause hb hh _ => And.intro (hasTy_sigProgram hb) (hasTy_sigProgram hh)
  | _, _, _, .catchIf hb _ _ hh _ => And.intro (hasTy_sigProgram hb) (hasTy_sigProgram hh)
  | _, _, _, .select _ _ h0 h1 _ => And.intro (hasTy_sigProgram h0) (hasTy_sigProgram h1)
  | _, _, _, .matchCause hb hv hc _ =>
    And.intro (hasTy_sigProgram hb) (And.intro (hasTy_sigProgram hv) (hasTy_sigProgram hc))
  | _, _, _, .onExit hb hf => And.intro (hasTy_sigProgram hb) (hasTy_sigProgram hf)
  | _, _, _, .exit hb =>
    have hchild := hasTy_sigProgram hb
    hchild
  | _, _, _, .uninterruptible hb =>
    have hchild := hasTy_sigProgram hb
    hchild
  | _, _, _, .interruptible hb =>
    have hchild := hasTy_sigProgram hb
    hchild
  | _, _, _, .iterate _ _ _ hb _ _ _ _ =>
    have hchild := hasTy_sigProgram hb
    hchild
  | _, _, _, .yieldNow _ => True.intro
  | _, _, _, .awaitFiber_join _ _ => True.intro
  | _, _, _, .awaitFiber_await _ _ => True.intro
  | _, _, _, .withFiber ha =>
    have hchild := actionHasTy_sigProgram ha
    hchild
  | _, _, _, .scoped hb =>
    have hchild := hasTy_sigProgram hb
    hchild
  | _, _, _, .acquireRelease ha hr _ => And.intro (hasTy_sigProgram ha) (hasTy_sigProgram hr)
  | _, _, _, .provideLayer _ hl hb => And.intro (layerHasTy_sigProgram hl) (hasTy_sigProgram hb)
  | _, _, _, .service hk => sigOkKey_of_serviceTy hk
  | _, _, _, .provideService hk _ _ hb =>
    And.intro (sigOkKey_of_serviceTy hk) (hasTy_sigProgram hb)
  | _, _, _, .restore _ _ hb =>
    have hbody := hasTy_sigProgram hb
    hbody
  | _, _, _, .invoke hd _ _ _ _ ha =>
    And.intro (Option.isSome_iff_exists.mpr ⟨_, hd⟩) (effsHasTy_sigProgram ha)

/-- A typed generator body reads only its signature. A step of `hasTy_sigProgram`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem stmtsHasTy_sigProgram {s : Signature Op} :
    ∀ {env : TyEnv} {inLoop : Bool} {b : Stmts Op} {g : GenTy},
      StmtsHasTy s env inLoop b g → cata_stmts (readsAlg (SigOkOp s) (SigOkKey s) (SigOkDef s)) b
  | _, _, _, _, .nil => True.intro
  | _, _, _, _, .bindYield he hr => And.intro (hasTy_sigProgram he) (stmtsHasTy_sigProgram hr)
  | _, _, _, _, .yieldDiscard he hr => And.intro (hasTy_sigProgram he) (stmtsHasTy_sigProgram hr)
  | _, _, _, _, .ret _ => And.intro True.intro True.intro
  | _, _, _, _, .ifElse _ _ ha hb hr _ _ =>
    And.intro (And.intro (stmtsHasTy_sigProgram ha) (stmtsHasTy_sigProgram hb))
      (stmtsHasTy_sigProgram hr)
  | _, _, _, _, .whileTrue hb hr _ => And.intro (stmtsHasTy_sigProgram hb) (stmtsHasTy_sigProgram hr)
  | _, _, _, _, .breakLoop hr => And.intro True.intro (stmtsHasTy_sigProgram hr)

/-- Typed race entrants read only their signature. A step of `hasTy_sigProgram`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem effsHasTy_sigProgram {s : Signature Op} :
    ∀ {env : TyEnv} {qs : List ParamDecl} {es : Effs Op} {t : EffTy},
      EffsHasTy s env qs es t → cata_effs (readsAlg (SigOkOp s) (SigOkKey s) (SigOkDef s)) es
  | _, _, _, _, .nil => True.intro
  | _, _, _, _, .cons hh ht _ => And.intro (hasTy_sigProgram hh) (effsHasTy_sigProgram ht)
  | _, _, _, _, .slot hh _ ht _ => And.intro (hasTy_sigProgram hh) (effsHasTy_sigProgram ht)

/-- A typed fiber action reads only its signature. A step of `hasTy_sigProgram`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem actionHasTy_sigProgram {s : Signature Op} :
    ∀ {env : TyEnv} {a : ActionTerm Op} {t : EffTy},
      ActionHasTy s env a t → cata_action (readsAlg (SigOkOp s) (SigOkKey s) (SigOkDef s)) a
  | _, _, _, .fork _ hp =>
    have hchild := hasTy_sigProgram hp
    hchild
  | _, _, _, .forkIn _ hp _ _ =>
    have hchild := hasTy_sigProgram hp
    hchild
  | _, _, _, .forkScoped _ hp =>
    have hchild := hasTy_sigProgram hp
    hchild
  | _, _, _, .runIn _ _ _ _ => True.intro
  | _, _, _, .interrupt _ _ => True.intro
  | _, _, _, .interruptScoped _ _ => True.intro
  | _, _, _, .interruptAll_self _ _ _ => True.intro
  | _, _, _, .interruptAll_by _ _ _ _ _ => True.intro
  | _, _, _, .awaitAll _ _ _ => True.intro
  | _, _, _, .awaitAllFailFast _ _ _ => True.intro
  | _, _, _, .snapshotChildren => True.intro
  | _, _, _, .awaitNewChildren _ _ => True.intro
  | _, _, _, .raceAll he =>
    have hchild := effsHasTy_sigProgram he
    hchild
  | _, _, _, .setContext _ _ => True.intro
  | _, _, _, .getContext => True.intro
  | _, _, _, .getId => True.intro
  | _, _, _, .closeScope _ _ _ _ => True.intro
  | _, _, _, .getInterruptible => True.intro

/-- A typed layer reads only its signature. A step of `hasTy_sigProgram`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem layerHasTy_sigProgram {s : Signature Op} :
    ∀ {l : LayerTerm Op} {t : LayerTy}, LayerHasTy s l t → cata_layer (readsAlg (SigOkOp s) (SigOkKey s) (SigOkDef s)) l
  | _, _, .succeed _ hk _ => sigOkKey_of_serviceTy hk
  | _, _, .effect hb hk _ => And.intro (sigOkKey_of_serviceTy hk) (hasTy_sigProgram hb)
  | _, _, .effectDiscard hb =>
    have hchild := hasTy_sigProgram hb
    hchild
  | _, _, .provide ha hb => And.intro (layerHasTy_sigProgram ha) (layerHasTy_sigProgram hb)
  | _, _, .provideMerge ha hb => And.intro (layerHasTy_sigProgram ha) (layerHasTy_sigProgram hb)
  | _, _, .merge ha hb => And.intro (layerHasTy_sigProgram ha) (layerHasTy_sigProgram hb)
  | _, _, .fresh hi =>
    have hchild := layerHasTy_sigProgram hi
    hchild
  | _, _, .orDie hi =>
    have hchild := layerHasTy_sigProgram hi
    hchild
  | _, _, .mergeAll hl =>
    have hchild := layersHasTy_sigProgram hl
    hchild

/-- A typed layer spine reads only its signature. A step of `hasTy_sigProgram`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem layersHasTy_sigProgram {s : Signature Op} :
    ∀ {ls : LayerTerms Op} {t : LayerTy},
      LayersHasTy s ls t → cata_layers (readsAlg (SigOkOp s) (SigOkKey s) (SigOkDef s)) ls
  | _, _, .one hl => And.intro (layerHasTy_sigProgram hl) True.intro
  | _, _, .cons hh ht => And.intro (layerHasTy_sigProgram hh) (layersHasTy_sigProgram ht)
end

/-- Typed bodies read only their signature. A step of `omit-splices-table`. Its consumer is
`moduleHasTy_sigProgram`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem bodiesHasTy_sigProgram {s : Signature Op} :
    ∀ {decls : List DefDecl} {bodies : Effs Op},
      BodiesHasTy s decls bodies → BodiesSigProgram s decls bodies
  | _, _, .nil => trivial
  | _, _, .cons _ hb _ hrest => ⟨hasTy_sigProgram hb, bodiesHasTy_sigProgram hrest⟩

/-- **A typed whole program reads only its signature**, part by part. A step of
`omit-splices-table`. Its consumer is `Sketch.table_more_holes`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem moduleHasTy_sigProgram {s : Signature Op} {e : Eff Op} {t : EffTy}
    (h : ModuleHasTy s e t) : ModuleSigProgram s e := by
  cases h with
  | defs hb hm => exact ⟨bodiesHasTy_sigProgram hb, hasTy_sigProgram hm⟩
  | plain hp =>
    cases e
    case defs => cases hp
    all_goals exact hasTy_sigProgram hp

end Effect4.Program
