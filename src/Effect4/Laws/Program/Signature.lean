import Effect4.Program.Typing.SignatureSupport
import Effect4.Laws.Program.Typing.Sound
import Effect4.Laws.Program.Folds.Checker
import Effect4.Laws.Program.Template
import Effect4.Program.SigApp

/-!
# Laws.Program.Signature — Σ_app: the signature as data, its extension and its lawfulness

Decisions rows 111–116 (ruled 2026-10-01). The open part of the signature is Σ_app: the host-row
table and the application's service declarations (`SigApp`). The core alphabet (`NativeOp`,
`SyncOp`, `FiberOp`, the atoms) stays fixed and grows only under DI-47's finite gate. The
definitions are the core's (`Program/SigApp.lean`): `SigApp`, its signature and its located
refusal `admitSig`, which program admission runs. This module holds their laws.

* **The signature an application's tables give the checker** (`SigApp.signature`). Service
  carriers are per code (row 113; `Machine/Key.lean`'s `carrier_def`: "selection is by the
  code, never by the nominal name"): the reserved `Scope` key keeps its exception, the machine's
  reserved names type nothing, and a free name's code reads the application's declarations
  before the built-in codes. With no declarations it is `nativeSignature` (`signature_nil`).
* **Extension** (`SigExtends`, moved from the model probe's `R2Probe.lean` §B): the same atoms
  and scope key, every operation the smaller signature admits admitted at the same row, every
  key it types typed at the same carrier. Typing is preserved along it for all six judgments
  (`hasTy_ext`), so for the checker at every path (`check_ext`): C3's monotone half. Its
  instances: rows appended (`rows_append`) and declarations appended at fresh codes
  (`SigApp.services_append`). The red controls (`prepend_not_extends`, `shadow_not_extends`,
  `one_code_two_carriers`) are fixtures in `Test/Program/SignatureControls.lean`.
* **`π` for services** (C5; `restrictWorld`): a world read at a signature's service table. A
  context's services fit at the restriction exactly when they fit at the world, as long as the
  two tables agree on its keys (`servicesFit_restrict`); along an extension, membership survives
  the restriction (`fits_restrict`).
-/

set_option autoImplicit false

namespace Effect4.Program

open Effect4 (ServiceKey ServiceTypeCode)
open Effect4.Machine.Env (Requirement)
open Conform.Effect4.Typing

/-! ## The term typer reads atoms only -/



section Extend
variable {Op : Type} {s s' : Signature Op}

mutual
/-- Typing is preserved along an extension, judgment by judgment. -/
theorem hasTy_ext (h : SigExtends s s') :
    ∀ {env : TyEnv} {e : Eff Op} {t : EffTy}, HasTy s env e t → HasTy s' env e t
  | _, _, _, .succeed ht => .succeed ((h.termTy _ _).trans ht)
  | _, _, _, .fail ht hadm => .fail ((h.termTy _ _).trans ht) hadm
  | _, _, _, .failCause hc => .failCause ((h.causeTy _ _).trans hc)
  | _, _, _, .sync ht => .sync ((h.termTy _ _).trans ht)
  | _, _, _, .suspend hb => .suspend (hasTy_ext h hb)
  | _, _, _, .perform hdom hreq hrow =>
    .perform (h.row _ hdom).1 ((h.termTy _ _).trans hreq)
      (by rw [(h.row _ hdom).2, h.termUse]; exact hrow)
  | _, _, _, .bind hf hr => .bind (hasTy_ext h hf) (hasTy_ext h hr)
  | _, _, _, .gen hb => .gen (stmtsHasTy_ext h hb)
  | _, _, _, .catchCause hb hh hj => .catchCause (hasTy_ext h hb) (hasTy_ext h hh) hj
  | _, _, _, .catchIf hb ht hsub hh hj =>
    .catchIf (hasTy_ext h hb) ((h.termTy _ _).trans ht) hsub (hasTy_ext h hh) hj
  | _, _, _, .select ht hd h0 h1 hj =>
    .select ((h.termTy _ _).trans ht) (by rw [h.types]; exact hd) (hasTy_ext h h0) (hasTy_ext h h1) hj
  | _, _, _, .matchCause hb hv hc hj =>
    .matchCause (hasTy_ext h hb) (hasTy_ext h hv) (hasTy_ext h hc) hj
  | _, _, _, .onExit hb hf => .onExit (hasTy_ext h hb) (hasTy_ext h hf)
  | _, _, _, .exit hb => .exit (hasTy_ext h hb)
  | _, _, _, .uninterruptible hb => .uninterruptible (hasTy_ext h hb)
  | _, _, _, .interruptible hb => .interruptible (hasTy_ext h hb)
  | _, _, _, .iterate hi ht hsub hb hs hr hs0 hs1 =>
    .iterate ((h.termTy _ _).trans hi) ((h.termTy _ _).trans ht) hsub (hasTy_ext h hb)
      ((h.termTy _ _).trans hs) ((h.termTy _ _).trans hr) hs0 hs1
  | _, _, _, .yieldNow priority => .yieldNow priority
  | _, _, _, .awaitFiber_join ht hf => .awaitFiber_join ((h.termTy _ _).trans ht) hf
  | _, _, _, .awaitFiber_await ht hf => .awaitFiber_await ((h.termTy _ _).trans ht) hf
  | _, _, _, .withFiber ha => .withFiber (actionHasTy_ext h ha)
  | _, _, _, .scoped (t := t) hb => by
    rw [← h.bodyRequires t]
    exact .scoped (hasTy_ext h hb)
  | _, _, _, .acquireRelease ha hr hn => by
    rw [← h.scopeKey]
    exact .acquireRelease (hasTy_ext h ha) (hasTy_ext h hr) hn
  | _, _, _, .provideLayer isLocal hl hb =>
    .provideLayer isLocal (layerHasTy_ext h hl) (hasTy_ext h hb)
  | _, _, _, .service hk => .service (h.service _ _ hk)
  | _, _, _, .provideService hk hv hsub hb =>
    .provideService (h.service _ _ hk) ((h.termTy _ _).trans hv) hsub (hasTy_ext h hb)
  | _, _, _, .provideContext hc hs hb =>
    .provideContext ((h.termTy _ _).trans hc) hs (hasTy_ext h hb)
  | _, _, _, .restore hs hsub hb => .restore ((h.termTy _ _).trans hs) hsub (hasTy_ext h hb)
  | _, _, _, .invoke hd hne hlen hreq hrow ha =>
    .invoke (h.defOf _ _ hd) hne hlen ((h.termTy _ _).trans hreq) hrow (effsHasTy_ext h ha)

theorem stmtsHasTy_ext (h : SigExtends s s') :
    ∀ {env : TyEnv} {inLoop : Bool} {b : Stmts Op} {g : GenTy},
      StmtsHasTy s env inLoop b g → StmtsHasTy s' env inLoop b g
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .bindYield he hr => .bindYield (hasTy_ext h he) (stmtsHasTy_ext h hr)
  | _, _, _, _, .yieldDiscard he hr => .yieldDiscard (hasTy_ext h he) (stmtsHasTy_ext h hr)
  | _, _, _, _, .ret ht => .ret ((h.termTy _ _).trans ht)
  | _, _, _, _, .ifElse ht hsub ha hb hr hab hg =>
    .ifElse ((h.termTy _ _).trans ht) hsub (stmtsHasTy_ext h ha) (stmtsHasTy_ext h hb)
      (stmtsHasTy_ext h hr) hab hg
  | _, _, _, _, .whileTrue hb hr hg => .whileTrue (stmtsHasTy_ext h hb) (stmtsHasTy_ext h hr) hg
  | _, _, _, _, .breakLoop hr => .breakLoop (stmtsHasTy_ext h hr)

theorem effsHasTy_ext (h : SigExtends s s') :
    ∀ {env : TyEnv} {qs : List ParamDecl} {es : Effs Op} {t : EffTy},
      EffsHasTy s env qs es t → EffsHasTy s' env qs es t
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons hh ht hj => .cons (hasTy_ext h hh) (effsHasTy_ext h ht) hj
  | _, _, _, _, .slot hh hadm ht hj =>
    .slot (hasTy_ext h hh) hadm (effsHasTy_ext h ht) hj

theorem actionHasTy_ext (h : SigExtends s s') :
    ∀ {env : TyEnv} {a : ActionTerm Op} {t : EffTy}, ActionHasTy s env a t → ActionHasTy s' env a t
  | _, _, _, .fork options hp => .fork options (hasTy_ext h hp)
  | _, _, _, .forkIn options hp hsc hsub => .forkIn options (hasTy_ext h hp) ((h.termTy _ _).trans hsc) hsub
  | _, _, _, .forkScoped options hp => by
    rw [← h.scopeKey]
    exact .forkScoped options (hasTy_ext h hp)
  | _, _, _, .runIn ht hf hsc hsub => .runIn ((h.termTy _ _).trans ht) hf ((h.termTy _ _).trans hsc) hsub
  | _, _, _, .interrupt ht hf => .interrupt ((h.termTy _ _).trans ht) hf
  | _, _, _, .interruptScoped ht hf => .interruptScoped ((h.termTy _ _).trans ht) hf
  | _, _, _, .interruptAll_self ht hl hf => .interruptAll_self ((h.termTy _ _).trans ht) hl hf
  | _, _, _, .interruptAll_by ht hl hf hw hsub =>
    .interruptAll_by ((h.termTy _ _).trans ht) hl hf ((h.termTy _ _).trans hw) hsub
  | _, _, _, .awaitAll ht hl hf => .awaitAll ((h.termTy _ _).trans ht) hl hf
  | _, _, _, .awaitAllFailFast ht hl hf => .awaitAllFailFast ((h.termTy _ _).trans ht) hl hf
  | _, _, _, .snapshotChildren => .snapshotChildren
  | _, _, _, .awaitNewChildren ht hsub => .awaitNewChildren ((h.termTy _ _).trans ht) hsub
  | _, _, _, .raceAll he => .raceAll (effsHasTy_ext h he)
  | _, _, _, .raceAllFirst he => .raceAllFirst (effsHasTy_ext h he)
  | _, _, _, .context hkeys => .context fun key hk => by
    obtain ⟨carrier, hc⟩ := hkeys key hk
    exact ⟨carrier, h.service key carrier hc⟩
  | _, _, _, .getId => .getId
  | _, _, _, .closeScope hs hsub he hx => .closeScope ((h.termTy _ _).trans hs) hsub ((h.termTy _ _).trans he) hx
  | _, _, _, .getInterruptible => .getInterruptible

theorem layerHasTy_ext (h : SigExtends s s') :
    ∀ {l : LayerTerm Op} {t : LayerTy}, LayerHasTy s l t → LayerHasTy s' l t
  | _, _, .succeed hv hk hs => .succeed hv (h.service _ _ hk) hs
  | _, _, .effect (t := t) hb hk hs => by
    rw [← h.bodyRequires t]
    exact .effect (hasTy_ext h hb) (h.service _ _ hk) hs
  | _, _, .effectDiscard (t := t) hb => by
    rw [← h.bodyRequires t]
    exact .effectDiscard (hasTy_ext h hb)
  | _, _, .provide ha hb => .provide (layerHasTy_ext h ha) (layerHasTy_ext h hb)
  | _, _, .provideMerge ha hb => .provideMerge (layerHasTy_ext h ha) (layerHasTy_ext h hb)
  | _, _, .merge ha hb => .merge (layerHasTy_ext h ha) (layerHasTy_ext h hb)
  | _, _, .fresh hi => .fresh (layerHasTy_ext h hi)
  | _, _, .orDie hi => .orDie (layerHasTy_ext h hi)
  | _, _, .mergeAll hl => .mergeAll (layersHasTy_ext h hl)

theorem layersHasTy_ext (h : SigExtends s s') :
    ∀ {ls : LayerTerms Op} {t : LayerTy}, LayersHasTy s ls t → LayersHasTy s' ls t
  | _, _, .one hl => .one (layerHasTy_ext h hl)
  | _, _, .cons hl hr => .cons (layerHasTy_ext h hl) (layersHasTy_ext h hr)
end

/-- **C3's monotone half at the checker**: a program the checker accepts under `s` it accepts
under every extension `s'`, at the same type and at every path. -/
theorem check_ext (h : SigExtends s s') {env : TyEnv} {p : List Nat} {e : Eff Op} {t : EffTy}
    (hc : Checker.check s env p e = .ok t) : Checker.check s' env p e = .ok t :=
  check_complete s' e env t (hasTy_ext h (check_sound s e env p t hc)) p

theorem effTy_ext (h : SigExtends s s') {env : TyEnv} {e : Eff Op} {t : EffTy}
    (he : effTy s env e = some t) : effTy s' env e = some t :=
  effTy_complete s' e env t (hasTy_ext h (effTy_sound s e env t he))

theorem checkLayer_ext (h : SigExtends s s') {p : List Nat} {l : LayerTerm Op} {t : LayerTy}
    (hc : Checker.checkLayer s p l = .ok t) : Checker.checkLayer s' p l = .ok t :=
  checkLayer_complete s' l t (layerHasTy_ext h (checkLayer_sound s l p t hc)) p

end Extend


/-! ## Σ_app (`SigApp`, `Program/SigApp.lean`) -/

namespace SigApp

/-- With no declarations the service table is the built-in one. -/
theorem serviceTy_nil (rows : RowTable) : (SigApp.ofTable rows).serviceTy = nativeServiceTy :=
  rfl

/-- With no declarations the signature is the native one. -/
theorem signature_nil (rows : RowTable) : (SigApp.ofTable rows).signature = nativeSignature rows :=
  rfl

/-- **Per code (row 113).** Two keys with one code under free names have one carrier. -/
theorem serviceTy_code (app : SigApp) {key key' : ServiceKey} (hcode : key.service = key'.service)
    (hfree : Effect4.Machine.Env.firstFreeName ≤ key.name.value)
    (hfree' : Effect4.Machine.Env.firstFreeName ≤ key'.name.value)
    (hres : nativeReservedServiceTypes.find? (fun entry => entry.1 == key) = none)
    (hres' : nativeReservedServiceTypes.find? (fun entry => entry.1 == key') = none) :
    app.serviceTy key = app.serviceTy key' := by
  unfold serviceTy
  rw [hres, hres', if_neg (Nat.not_lt.mpr hfree), if_neg (Nat.not_lt.mpr hfree'), hcode]


/-- A declaration appended at a code that neither the application nor the built-in table
types. -/
def FreshCode (app : SigApp) (entry : ServiceKey × Ty) : Prop :=
  app.codeTy entry.1.service = none ∧ builtinCodeTy entry.1.service = none

/-- Declarations appended at fresh codes extend the signature: every key the shorter table
types keeps its carrier. -/
theorem services_append (app : SigApp) (s' : List (ServiceKey × Ty))
    (fresh : ∀ entry ∈ s', FreshCode app entry) :
    SigExtends app.signature (SigApp.mk app.rows (app.services ++ s') app.types).signature := by
  refine ⟨rfl, rfl, rfl, fun _ h => ⟨h, rfl⟩, ?_, rfl, rfl, fun _ _ hk => hk, rfl, rfl⟩
  intro key ty hk
  change app.serviceTy key = some ty at hk
  change SigApp.serviceTy ⟨app.rows, app.services ++ s', app.types⟩ key = some ty
  unfold serviceTy at hk ⊢
  split at hk
  · exact hk
  · split at hk
    · cases hk
    · rename_i hfree
      rw [if_neg hfree]
      have happ : (SigApp.mk app.rows (app.services ++ s') app.types).codeTy key.service =
          (app.codeTy key.service).or
            ((s'.find? (fun entry => entry.1.service == key.service)).map Prod.snd) := by
        simp only [codeTy, List.find?_append, Option.map_or]
      rw [happ]
      cases hc : app.codeTy key.service with
      | some c =>
        rw [hc] at hk
        exact hk
      | none =>
        rw [hc] at hk
        change builtinCodeTy key.service = some ty at hk
        have hnone : s'.find? (fun entry => entry.1.service == key.service) = none := by
          apply List.find?_eq_none.mpr
          intro entry hmem heq
          have hcode : entry.1.service = key.service := beq_iff_eq.mp heq
          have hbuiltin := (fresh entry hmem).2
          rw [hcode, hk] at hbuiltin
          cases hbuiltin
        rw [hnone]
        exact hk

end SigApp

/-! ## Fold congruence on a program's reads (TY-04)

The checker is one fold of the program (`Checker.check.eq_cata`,
`Laws/Program/Folds/Checker.lean`), so two signatures give the same checker answer on a program
when their checker algebras agree on the nodes of that program. `EffAlgebra.AgreeOn` says which
agreement is needed: outright at every constructor that carries no operation or service key, and
at the ones that do for the operations and keys a guard admits. `cata_eff_congr_on` (and its six
siblings over the family) is that fact for every fold over the program family, proved once by
structural recursion; C3's reflection (`check_restrict`) is an instance with no induction of its
own. -/

/-- **Along an extension the checker's two algebras agree on the reads the smaller signature
admits** (proved): field by field, outright where the field reads only atoms and the scope key,
guarded where it reads an operation's row, a key's carrier or a definition's declaration. -/
theorem check_alg_agreeOn {Op : Type} {s s' : Signature Op} (h : SigExtends s s') :
    (Checker.check.alg s').AgreeOn (Checker.check.alg s) (SigOkOp s) (SigOkKey s)
      (SigOkDef s) := by
  have hterm := term?_ext h
  have hcause := cause?_ext h
  have hbody : bodyRequires s' = bodyRequires s := funext h.bodyRequires
  exact {
    eff_succeed := by simp only [Checker.check.alg, hterm]
    eff_fail := by simp only [Checker.check.alg, hterm]
    eff_failCause := by simp only [Checker.check.alg, hcause]
    eff_sync := by simp only [Checker.check.alg, hterm]
    eff_suspend := rfl
    eff_perform := fun op hd => by
      have hdom : s.dom op = true := hd
      simp only [Checker.check.alg, hterm, (h.row op hdom).1, (h.row op hdom).2, hdom,
        h.termUse]
    eff_bind := rfl
    eff_gen := rfl
    eff_catchCause := rfl
    eff_matchCause := rfl
    eff_onExit := rfl
    eff_exit := rfl
    eff_uninterruptible := rfl
    eff_interruptible := rfl
    eff_yieldNow := rfl
    eff_awaitFiber := by simp only [Checker.check.alg, hterm]
    eff_withFiber := rfl
    eff_scoped := by simp only [Checker.check.alg, hbody]
    eff_acquireRelease := by simp only [Checker.check.alg, h.scopeKey]
    eff_provideLayer := rfl
    eff_service := fun key hk => by
      obtain ⟨ty, hty⟩ := Option.isSome_iff_exists.mp hk
      simp only [Checker.check.alg, h.service key ty hty, hty]
    eff_provideService := fun key hk => by
      obtain ⟨ty, hty⟩ := Option.isSome_iff_exists.mp hk
      simp only [Checker.check.alg, h.service key ty hty, hty, hterm]
    eff_provideContext := by simp only [Checker.check.alg, hterm]
    eff_catchIf := by simp only [Checker.check.alg, hterm]
    eff_select := by simp only [Checker.check.alg, hterm, h.types]
    eff_iterate := by simp only [Checker.check.alg, hterm]
    eff_restore := by simp only [Checker.check.alg, hterm]
    eff_defs := rfl
    eff_invoke := fun k hk => by
      obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hk
      simp only [Checker.check.alg, h.defOf k d hd, hd, hterm]
    stmt_bindYield := rfl
    stmt_yieldDiscard := rfl
    stmt_ret := by simp only [Checker.check.alg, hterm]
    stmt_ifElse := by simp only [Checker.check.alg, hterm]
    stmt_whileTrue := rfl
    stmt_breakLoop := rfl
    stmts_nil := rfl
    stmts_cons := rfl
    effs_nil := rfl
    effs_cons := rfl
    action_fork := rfl
    action_forkIn := by simp only [Checker.check.alg, hterm]
    action_forkScoped := by simp only [Checker.check.alg, h.scopeKey]
    action_runIn := by simp only [Checker.check.alg, hterm]
    action_interrupt := by simp only [Checker.check.alg, hterm]
    action_interruptScoped := by simp only [Checker.check.alg, hterm]
    action_interruptAll := by simp only [Checker.check.alg, hterm]
    action_awaitAll := by simp only [Checker.check.alg, hterm]
    action_awaitAllFailFast := by simp only [Checker.check.alg, hterm]
    action_snapshotChildren := rfl
    action_awaitNewChildren := by simp only [Checker.check.alg, hterm]
    action_raceAll := rfl
    action_raceAllFirst := rfl
    action_context := fun keys hk => by
      apply Prod.ext
      · rfl
      · funext env p
        have old : ∀ key ∈ keys.elems, ∃ carrier, s.serviceTy key = some carrier :=
          fun key hkey => Option.isSome_iff_exists.mp (hk key hkey)
        have newer : ∀ key ∈ keys.elems, ∃ carrier, s'.serviceTy key = some carrier := by
          intro key hkey
          obtain ⟨carrier, hc⟩ := old key hkey
          exact ⟨carrier, h.service key carrier hc⟩
        exact (checkAction_complete s' (.context keys) env _ (.context newer) p).trans
          (checkAction_complete s (.context keys) env _ (.context old) p).symm
    action_getId := rfl
    action_closeScope := by simp only [Checker.check.alg, hterm]
    action_getInterruptible := rfl
    layer_succeed := fun key hk => by
      obtain ⟨ty, hty⟩ := Option.isSome_iff_exists.mp hk
      simp only [Checker.check.alg, h.service key ty hty, hty]
    layer_effect := fun key hk => by
      obtain ⟨ty, hty⟩ := Option.isSome_iff_exists.mp hk
      simp only [Checker.check.alg, h.service key ty hty, hty, hbody]
    layer_effectDiscard := by simp only [Checker.check.alg, hbody]
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

/-- **C3's reflection** (TY-04, proved): on a Σ-program, the checker answers the same under every
extension of Σ, refusals included, at every environment and path. -/
theorem check_restrict {Op : Type} {s s' : Signature Op} (h : SigExtends s s') {e : Eff Op}
    (hp : SigProgram s e) (env : TyEnv) (p : List Nat) :
    Checker.check s' env p e = Checker.check s env p e := by
  rw [Checker.check.eq_cata, Checker.check.eq_cata]
  rw [cata_eff_congr_on (check_alg_agreeOn h) e hp]

/-- The success projection, likewise. -/
theorem effTy_restrict {Op : Type} {s s' : Signature Op} (h : SigExtends s s') {e : Eff Op}
    (hp : SigProgram s e) (env : TyEnv) : effTy s' env e = effTy s env e := by
  unfold effTy
  rw [check_restrict h hp]

/-! ## Lawful signatures (rows 97, 113, 114, 127; TY-05)

`LawfulSig` gathers the conditions an application's signature must meet behind one located
refusal (`admitSig`, `Program/SigApp.lean`, which program admission runs) and proves the two
agree (`admitSig_ok_iff`). Its shape is C6's
(the synthesis §2.2, as Codex's audit amends it): every row and every declaration meets its own
conditions, the rows and the declarations are pairwise compatible, and every key a row requires
has a carrier (the third clause shape, which points from rows to services and is monotone under
append). So `LawfulSig (Σ ++ ε)` splits into the parts and the cross terms by
`List.forall_mem_append` and `List.pairwise_append` (`lawful_append`). -/

/-- `firstFailing` (`Program/SigApp.lean`) names no reason exactly when every check holds. A step
of `sigRefusal?_eq_none_iff`. -/
theorem firstFailing_eq_none_iff {β : Type} (checks : List (Bool × β)) :
    firstFailing checks = none ↔ ∀ c ∈ checks, c.1 = true := by
  unfold firstFailing
  rw [Option.map_eq_none_iff, List.find?_eq_none]
  constructor
  · intro h c hc
    have := h c hc
    cases hc1 : c.1
    · rw [hc1] at this
      exact absurd rfl this
    · rfl
  · intro h c hc hbad
    rw [h c hc] at hbad
    cases hbad

/-- `firstIndexed` (`Program/SigApp.lean`) finds no position exactly when the check refuses no
element. A step of `sigRefusal?_eq_none_iff`. -/
theorem firstIndexed_eq_none_iff {α β : Type} (f : α → Option β) :
    ∀ (i : Nat) (xs : List α), firstIndexed f i xs = none ↔ ∀ x ∈ xs, f x = none
  | _, [] => ⟨fun _ _ hx => (nomatch hx), fun _ => rfl⟩
  | i, x :: xs => by
    unfold firstIndexed
    cases hx : f x with
    | some b =>
      refine ⟨fun h => (nomatch h), fun h => ?_⟩
      rw [h x List.mem_cons_self] at hx
      cases hx
    | none =>
      rw [firstIndexed_eq_none_iff f (i + 1) xs]
      constructor
      · intro h y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hx
        · exact h y hy
      · intro h y hy
        exact h y (List.mem_cons_of_mem x hy)

/-- `firstDup` (`Program/SigApp.lean`) finds no repeat exactly when the list has none. A step of
`sigRefusal?_eq_none_iff`. -/
theorem firstDup_eq_none_iff {α : Type} [DecidableEq α] :
    ∀ xs : List α, firstDup xs = none ↔ xs.Nodup
  | [] => ⟨fun _ => List.nodup_nil, fun _ => rfl⟩
  | x :: xs => by
    unfold firstDup
    rw [List.nodup_cons]
    by_cases hx : x ∈ xs
    · rw [if_pos hx]
      exact ⟨fun h => (nomatch h), fun h => absurd hx h.1⟩
    · rw [if_neg hx, firstDup_eq_none_iff xs]
      exact ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩

/-- `firstConflict` (`Program/SigApp.lean`) names no name exactly when no name has two bodies.
A step of `sigRefusal?_eq_none_iff`. -/
theorem firstConflict_eq_none_iff :
    ∀ ds : TyDecls, firstConflict ds = none ↔ ds.Pairwise fun d e => d.1 = e.1 → d.2 = e.2
  | [] => ⟨fun _ => List.Pairwise.nil, fun _ => rfl⟩
  | d :: rest => by
    unfold firstConflict
    rw [List.pairwise_cons]
    cases h : rest.any (fun e => e.1 == d.1 && e.2 != d.2) with
    | true =>
      rw [if_pos rfl]
      refine ⟨fun hn => (nomatch hn), fun hp => ?_⟩
      obtain ⟨e, he, hbad⟩ := List.any_eq_true.mp h
      rw [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hbad
      exact absurd (hp.1 e he hbad.1.symm).symm hbad.2
    | false =>
      rw [if_neg Bool.false_ne_true, firstConflict_eq_none_iff rest]
      refine ⟨fun hr => ⟨fun e he hde => ?_, hr⟩, fun hp => hp.2⟩
      have hno := List.any_eq_false.mp h e he
      cases hb : (e.2 == d.2) with
      | true => exact (beq_iff_eq.mp hb).symm
      | false =>
        rw [hde, beq_iff_eq.mpr (rfl : e.1 = e.1), Bool.true_and, bne, hb] at hno
        exact absurd rfl hno

/-- **The lawful signatures** (rows 97, 113, 114, 127; C6's shape; the named types of rows 401
and 402). -/
structure LawfulSig (app : SigApp) : Prop where
  /-- Every row meets its local conditions. -/
  rows : ∀ r ∈ app.rows, ∀ c ∈ rowChecks r, c.1 = true
  /-- No two rows share a key. -/
  rowsDistinct : app.rows.Pairwise fun r r' => rowKey r ≠ rowKey r'
  /-- Every declaration meets its local conditions. -/
  services : ∀ e ∈ app.services, ∀ c ∈ serviceChecks e, c.1 = true
  /-- No two declarations share a code (row 113). -/
  codesDistinct : app.services.Pairwise fun e e' => e.1.service ≠ e'.1.service
  /-- Every key a row requires has a carrier. -/
  served : ∀ r ∈ app.rows, ∀ k ∈ r.requires, (app.serviceTy k).isSome = true
  /-- Every named type's declaration meets its local conditions (decisions row 401 (2)). -/
  decls : ∀ d ∈ app.types, ∀ c ∈ declChecks app.types d, c.1 = true
  /-- Every row spells each name with one meaning under the table (decisions row 406 (1)). -/
  rowNames : ∀ r ∈ app.rows, ∀ c ∈ nameChecks app.types r.spelledNames, c.1 = true
  /-- No name has two bodies (decisions row 402 (5)). -/
  declsConsistent : app.types.Pairwise fun d e => d.1 = e.1 → d.2 = e.2
  /-- The table is guarded: the ranking ranks every name (decisions row 401 (2)). -/
  guarded : app.types.guarded = true

/-- **The located refusal is complete** (proved): no refusal exactly at a lawful signature. -/
theorem sigRefusal?_eq_none_iff (app : SigApp) : sigRefusal? app = none ↔ LawfulSig app := by
  unfold sigRefusal?
  rw [Option.or_eq_none_iff, Option.or_eq_none_iff, Option.or_eq_none_iff, Option.or_eq_none_iff,
    Option.or_eq_none_iff, Option.or_eq_none_iff, Option.or_eq_none_iff, Option.or_eq_none_iff,
    Option.map_eq_none_iff, Option.map_eq_none_iff, Option.map_eq_none_iff,
    Option.map_eq_none_iff, Option.map_eq_none_iff, Option.map_eq_none_iff,
    Option.map_eq_none_iff, Option.map_eq_none_iff, Option.map_eq_none_iff,
    firstIndexed_eq_none_iff, firstDup_eq_none_iff, firstIndexed_eq_none_iff,
    firstDup_eq_none_iff, firstIndexed_eq_none_iff, firstIndexed_eq_none_iff,
    firstIndexed_eq_none_iff, firstConflict_eq_none_iff, ← Option.isNone_iff_eq_none]
  constructor
  · rintro ⟨hrows, hkeys, hsvc, hcodes, hserved, hdecls, hnames, hconsistent, hguarded⟩
    refine ⟨fun r hr => (firstFailing_eq_none_iff _).mp (hrows r hr), List.pairwise_map.mp hkeys,
      fun e he => (firstFailing_eq_none_iff _).mp (hsvc e he), List.pairwise_map.mp hcodes, ?_,
      fun d hd => (firstFailing_eq_none_iff _).mp (hdecls d hd),
      fun r hr => (firstFailing_eq_none_iff _).mp (hnames r hr), hconsistent, hguarded⟩
    intro r hr k hk
    have hk' := List.find?_eq_none.mp (hserved r hr) k hk
    cases hks : (app.serviceTy k).isSome
    · rw [hks] at hk'
      exact absurd rfl hk'
    · rfl
  · rintro ⟨hrows, hkeys, hsvc, hcodes, hserved, hdecls, hnames, hconsistent, hguarded⟩
    refine ⟨fun r hr => (firstFailing_eq_none_iff _).mpr (hrows r hr), List.pairwise_map.mpr hkeys,
      fun e he => (firstFailing_eq_none_iff _).mpr (hsvc e he), List.pairwise_map.mpr hcodes,
      fun r hr => List.find?_eq_none.mpr fun k hk hbad => ?_,
      fun d hd => (firstFailing_eq_none_iff _).mpr (hdecls d hd),
      fun r hr => (firstFailing_eq_none_iff _).mpr (hnames r hr), hconsistent, hguarded⟩
    rw [hserved r hr k hk] at hbad
    cases hbad

/-- **`admitSig_ok_iff`** (proved): the executable check admits exactly the lawful signatures. -/
theorem admitSig_ok_iff (app : SigApp) : admitSig app = .ok () ↔ LawfulSig app := by
  rw [← sigRefusal?_eq_none_iff]
  unfold admitSig
  cases sigRefusal? app with
  | some why => exact ⟨fun hok => (nomatch hok), fun hn => (nomatch hn)⟩
  | none => exact ⟨fun _ => rfl, fun _ => rfl⟩

instance (app : SigApp) : Decidable (LawfulSig app) :=
  decidable_of_iff _ (sigRefusal?_eq_none_iff app)

/-- **A lawful signature's rows meet the program-plane table check** (proved): distinct row keys
are `Table.lawful`'s uniqueness clause, and each row's local checks contain its built-in-collision
and value-row clauses. So the typed state's `LawfulSource`, which reads this structure, contains
the `Table.lawful` premise it read before seat A's field (integration seat I2). -/
theorem LawfulSig.tableLawful {app : SigApp} (h : LawfulSig app) : Table.lawful app.rows = true := by
  have collision : ∀ r ∈ app.rows, (!builtinKeys.contains (rowKey r)) = true :=
    fun r hr => h.rows r hr _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have trailing : ∀ r ∈ app.rows, (!(r.shape == .value) || r.trailing.isEmpty) = true :=
    fun r hr => h.rows r hr _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  unfold Table.lawful
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  exact ⟨⟨List.pairwise_map.mpr h.rowsDistinct, collision⟩, trailing⟩

/-- **A lawful signature's rows are the runner's to register** (proved): every row is an external
asynchronous row, `rowChecks`' first two checks (`checkTable`'s two conditions). A step of the
claim `admitted-source-lawful`, read off program admission's certificate. Consumer:
`build_runnable` (`Laws/Program/Author.lean`), the registration fact of a built program, which the
certificate held as a field until admission ran `admitSig`. -/
theorem LawfulSig.registered {app : SigApp} (h : LawfulSig app) :
    ∀ r ∈ app.rows, r.registration = .external ∧ r.kind = .async := fun r hr =>
  ⟨beq_iff_eq.mp (h.rows r hr _ List.mem_cons_self),
    beq_iff_eq.mp (h.rows r hr _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩

/-- The empty signature is lawful: what every source with no rows and no declarations carries. -/
theorem SigApp.lawful_empty : LawfulSig (SigApp.mk [] [] []) :=
  ⟨fun _ h => (nomatch h), List.Pairwise.nil, fun _ h => (nomatch h), List.Pairwise.nil,
    fun _ h => (nomatch h), fun _ h => (nomatch h), fun _ h => (nomatch h), List.Pairwise.nil, rfl⟩

/-- **C6 (proved)**: an appended signature is lawful exactly when each part's local clauses
hold, each part's pairwise clauses hold, the cross terms hold, and the whole serves every
required key: `List.forall_mem_append` and `List.pairwise_append`. -/
theorem lawful_append (app : SigApp) (rows' : RowTable) (services' : List (ServiceKey × Ty)) :
    LawfulSig (SigApp.mk (app.rows ++ rows') (app.services ++ services') app.types) ↔
      ((∀ r ∈ app.rows, ∀ c ∈ rowChecks r, c.1 = true) ∧
        (∀ r ∈ rows', ∀ c ∈ rowChecks r, c.1 = true)) ∧
      (app.rows.Pairwise (fun r r' => rowKey r ≠ rowKey r') ∧
        rows'.Pairwise (fun r r' => rowKey r ≠ rowKey r') ∧
        ∀ r ∈ app.rows, ∀ r' ∈ rows', rowKey r ≠ rowKey r') ∧
      ((∀ e ∈ app.services, ∀ c ∈ serviceChecks e, c.1 = true) ∧
        (∀ e ∈ services', ∀ c ∈ serviceChecks e, c.1 = true)) ∧
      (app.services.Pairwise (fun e e' => e.1.service ≠ e'.1.service) ∧
        services'.Pairwise (fun e e' => e.1.service ≠ e'.1.service) ∧
        ∀ e ∈ app.services, ∀ e' ∈ services', e.1.service ≠ e'.1.service) ∧
      (∀ r ∈ app.rows ++ rows', ∀ k ∈ r.requires,
        ((SigApp.mk (app.rows ++ rows') (app.services ++ services') app.types).serviceTy k).isSome =
          true) ∧
      ((∀ d ∈ app.types, ∀ c ∈ declChecks app.types d, c.1 = true) ∧
        (∀ r ∈ app.rows ++ rows', ∀ c ∈ nameChecks app.types r.spelledNames, c.1 = true) ∧
        (app.types.Pairwise fun d e => d.1 = e.1 → d.2 = e.2) ∧ app.types.guarded = true) := by
  constructor
  · rintro ⟨hrows, hkeys, hsvc, hcodes, hserved, hdecls, hnames, hconsistent, hguarded⟩
    exact ⟨List.forall_mem_append.mp hrows, List.pairwise_append.mp hkeys,
      List.forall_mem_append.mp hsvc, List.pairwise_append.mp hcodes, hserved,
      hdecls, hnames, hconsistent, hguarded⟩
  · rintro ⟨hrows, hkeys, hsvc, hcodes, hserved, hdecls, hnames, hconsistent, hguarded⟩
    exact ⟨List.forall_mem_append.mpr hrows, List.pairwise_append.mpr hkeys,
      List.forall_mem_append.mpr hsvc, List.pairwise_append.mpr hcodes, hserved,
      hdecls, hnames, hconsistent, hguarded⟩
end Effect4.Program
