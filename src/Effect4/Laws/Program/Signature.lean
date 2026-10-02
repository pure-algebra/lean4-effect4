import Effect4.Laws.Program.Typing.Sound
import Effect4.Laws.Program.Folds.Checker
import Effect4.Laws.Program.Template
import Effect4.Program.Admission

/-!
# Laws.Program.Signature — Σ_app: the signature as data, its extension and its lawfulness

Decisions rows 111–116 (ruled 2026-10-01). The open part of the signature is Σ_app: the host-row
table and the application's service declarations (`SigApp`). The core alphabet (`NativeOp`,
`SyncOp`, `FiberOp`, the atoms) stays fixed and grows only under DI-47's finite gate.

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

section Congr
variable {Op Op' : Type} {s₁ : Signature Op} {s₂ : Signature Op'}

mutual
theorem argTy_congr (ha : s₁.atomOf = s₂.atomOf) (hc : s₁.constAtom = s₂.constAtom)
    (env : TyEnv) : ∀ (c : Bool) (t : Term), argTy s₁ env c t = argTy s₂ env c t
  | _, .var _ => rfl
  | _, .lit _ => rfl
  | _, .app atom args => by
    simp only [argTy, argsTy_congr ha hc env, ha, hc]

theorem argsTy_congr (ha : s₁.atomOf = s₂.atomOf) (hc : s₁.constAtom = s₂.constAtom)
    (env : TyEnv) : ∀ (c : Bool) (ts : Terms), argsTy s₁ env c ts = argsTy s₂ env c ts
  | _, .nil => rfl
  | c, .cons head tail => by
    simp only [argsTy, argTy_congr ha hc env c head, argsTy_congr ha hc env c tail]
end

theorem termTy_congr (ha : s₁.atomOf = s₂.atomOf) (hc : s₁.constAtom = s₂.constAtom)
    (env : TyEnv) (t : Term) : termTy s₁ env t = termTy s₂ env t :=
  argTy_congr ha hc env false t

theorem causeTy_congr (ha : s₁.atomOf = s₂.atomOf) (hc : s₁.constAtom = s₂.constAtom)
    (env : TyEnv) : ∀ c : CauseTerm, causeTy s₁ env c = causeTy s₂ env c
  | .fail error => by simp only [causeTy, termTy_congr ha hc env error]
  | .die defect => by simp only [causeTy, termTy_congr ha hc env defect]
  | .interrupt none => rfl
  | .interrupt (some who) => by simp only [causeTy, termTy_congr ha hc env who]
  | .both left right => by
    simp only [causeTy, causeTy_congr ha hc env left, causeTy_congr ha hc env right]

end Congr

/-! ## Signature extension -/

/-- `s'` extends `s`: the same atoms and scope key, every operation `s` admits admitted by `s'`
at the same row, every key `s` types typed by `s'` at the same carrier. -/
structure SigExtends {Op : Type} (s s' : Signature Op) : Prop where
  atomOf : s'.atomOf = s.atomOf
  constAtom : s'.constAtom = s.constAtom
  scopeKey : s'.scopeKey = s.scopeKey
  row : ∀ op, s.dom op = true → s'.dom op = true ∧ s'.rowOf op = s.rowOf op
  service : ∀ key ty, s.serviceTy key = some ty → s'.serviceTy key = some ty

namespace SigExtends

variable {Op : Type} {s s' s'' : Signature Op}

theorem refl (s : Signature Op) : SigExtends s s :=
  ⟨rfl, rfl, rfl, fun _ h => ⟨h, rfl⟩, fun _ _ h => h⟩

theorem trans (h₁ : SigExtends s s') (h₂ : SigExtends s' s'') : SigExtends s s'' :=
  ⟨h₂.atomOf.trans h₁.atomOf, h₂.constAtom.trans h₁.constAtom, h₂.scopeKey.trans h₁.scopeKey,
    fun op hd =>
      ⟨(h₂.row op (h₁.row op hd).1).1, (h₂.row op (h₁.row op hd).1).2.trans (h₁.row op hd).2⟩,
    fun key ty hk => h₂.service key ty (h₁.service key ty hk)⟩

theorem termTy (h : SigExtends s s') (env : TyEnv) (t : Term) :
    Effect4.Program.termTy s' env t = Effect4.Program.termTy s env t :=
  termTy_congr h.atomOf h.constAtom env t

theorem causeTy (h : SigExtends s s') (env : TyEnv) (c : CauseTerm) :
    Effect4.Program.causeTy s' env c = Effect4.Program.causeTy s env c :=
  causeTy_congr h.atomOf h.constAtom env c

theorem bodyRequires (h : SigExtends s s') (t : EffTy) :
    Effect4.Program.bodyRequires s' t = Effect4.Program.bodyRequires s t := by
  simp only [Effect4.Program.bodyRequires, h.scopeKey]

end SigExtends

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
    .perform (h.row _ hdom).1 ((h.termTy _ _).trans hreq) (by rw [(h.row _ hdom).2]; exact hrow)
  | _, _, _, .bind hf hr => .bind (hasTy_ext h hf) (hasTy_ext h hr)
  | _, _, _, .gen hb => .gen (stmtsHasTy_ext h hb)
  | _, _, _, .catchCause hb hh hj => .catchCause (hasTy_ext h hb) (hasTy_ext h hh) hj
  | _, _, _, .catchIf hb ht hh hj =>
    .catchIf (hasTy_ext h hb) ((h.termTy _ _).trans ht) (hasTy_ext h hh) hj
  | _, _, _, .select ht hd h0 h1 hj =>
    .select ((h.termTy _ _).trans ht) hd (hasTy_ext h h0) (hasTy_ext h h1) hj
  | _, _, _, .matchCause hb hv hc hj =>
    .matchCause (hasTy_ext h hb) (hasTy_ext h hv) (hasTy_ext h hc) hj
  | _, _, _, .onExit hb hf => .onExit (hasTy_ext h hb) (hasTy_ext h hf)
  | _, _, _, .exit hb => .exit (hasTy_ext h hb)
  | _, _, _, .uninterruptible hb => .uninterruptible (hasTy_ext h hb)
  | _, _, _, .interruptible hb => .interruptible (hasTy_ext h hb)
  | _, _, _, .iterate hi ht hb hs hr hs0 hs1 =>
    .iterate ((h.termTy _ _).trans hi) ((h.termTy _ _).trans ht) (hasTy_ext h hb)
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

theorem stmtsHasTy_ext (h : SigExtends s s') :
    ∀ {env : TyEnv} {inLoop : Bool} {b : Stmts Op} {g : GenTy},
      StmtsHasTy s env inLoop b g → StmtsHasTy s' env inLoop b g
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .bindYield he hr => .bindYield (hasTy_ext h he) (stmtsHasTy_ext h hr)
  | _, _, _, _, .yieldDiscard he hr => .yieldDiscard (hasTy_ext h he) (stmtsHasTy_ext h hr)
  | _, _, _, _, .ret ht => .ret ((h.termTy _ _).trans ht)
  | _, _, _, _, .ifElse ht ha hb hr hab hg =>
    .ifElse ((h.termTy _ _).trans ht) (stmtsHasTy_ext h ha) (stmtsHasTy_ext h hb)
      (stmtsHasTy_ext h hr) hab hg
  | _, _, _, _, .whileTrue hb hr hg => .whileTrue (stmtsHasTy_ext h hb) (stmtsHasTy_ext h hr) hg
  | _, _, _, _, .breakLoop hr => .breakLoop (stmtsHasTy_ext h hr)

theorem effsHasTy_ext (h : SigExtends s s') :
    ∀ {env : TyEnv} {es : Effs Op} {t : EffTy}, EffsHasTy s env es t → EffsHasTy s' env es t
  | _, _, _, .nil => .nil
  | _, _, _, .cons hh ht hj => .cons (hasTy_ext h hh) (effsHasTy_ext h ht) hj

theorem actionHasTy_ext (h : SigExtends s s') :
    ∀ {env : TyEnv} {a : ActionTerm Op} {t : EffTy}, ActionHasTy s env a t → ActionHasTy s' env a t
  | _, _, _, .fork options hp => .fork options (hasTy_ext h hp)
  | _, _, _, .forkIn options hp hsc => .forkIn options (hasTy_ext h hp) ((h.termTy _ _).trans hsc)
  | _, _, _, .forkScoped options hp => by
    rw [← h.scopeKey]
    exact .forkScoped options (hasTy_ext h hp)
  | _, _, _, .runIn ht hf hsc => .runIn ((h.termTy _ _).trans ht) hf ((h.termTy _ _).trans hsc)
  | _, _, _, .interrupt ht hf => .interrupt ((h.termTy _ _).trans ht) hf
  | _, _, _, .interruptScoped ht hf => .interruptScoped ((h.termTy _ _).trans ht) hf
  | _, _, _, .interruptAll_self ht hf => .interruptAll_self ((h.termTy _ _).trans ht) hf
  | _, _, _, .interruptAll_by ht hf hw =>
    .interruptAll_by ((h.termTy _ _).trans ht) hf ((h.termTy _ _).trans hw)
  | _, _, _, .awaitAll ht hf => .awaitAll ((h.termTy _ _).trans ht) hf
  | _, _, _, .awaitAllFailFast ht hf => .awaitAllFailFast ((h.termTy _ _).trans ht) hf
  | _, _, _, .snapshotChildren => .snapshotChildren
  | _, _, _, .awaitNewChildren ht hsub => .awaitNewChildren ((h.termTy _ _).trans ht) hsub
  | _, _, _, .raceAll he => .raceAll (effsHasTy_ext h he)
  | _, _, _, .setContext ht => .setContext ((h.termTy _ _).trans ht)
  | _, _, _, .getContext => .getContext
  | _, _, _, .getId => .getId
  | _, _, _, .closeScope hs he => .closeScope ((h.termTy _ _).trans hs) ((h.termTy _ _).trans he)

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

theorem typeOfProgram_ext (h : SigExtends s s') {e : Eff Op} {t : EffTy}
    (he : typeOfProgram s e = some t) : typeOfProgram s' e = some t := by
  unfold typeOfProgram at he ⊢
  split at he
  · rw [if_pos ‹_›]
    exact effTy_ext h he
  · cases he

theorem checkLayer_ext (h : SigExtends s s') {p : List Nat} {l : LayerTerm Op} {t : LayerTy}
    (hc : Checker.checkLayer s p l = .ok t) : Checker.checkLayer s' p l = .ok t :=
  checkLayer_complete s' l t (layerHasTy_ext h (checkLayer_sound s l p t hc)) p

end Extend

/-- Rows appended to the table extend the signature: an index the shorter table admits is
admitted by the longer one at the same row. -/
theorem rows_append (t t' : RowTable) :
    SigExtends (nativeSignature t) (nativeSignature (t ++ t')) := by
  refine ⟨rfl, rfl, rfl, ?_, fun _ _ hk => hk⟩
  intro op hd
  cases op with
  | external i =>
    have hi : i < t.length := of_decide_eq_true hd
    refine ⟨decide_eq_true (Nat.lt_of_lt_of_le hi (by simp only [List.length_append]; omega)), ?_⟩
    show ((nativeRowOf (t ++ t') (.external i)).normalizeTypes) =
      (nativeRowOf t (.external i)).normalizeTypes
    simp only [nativeRowOf, List.getElem?_append_left hi]
  | _ => exact ⟨rfl, rfl⟩

/-! ## Σ_app -/

/-- The application's part of the signature (row 111): the host-row table and the service
declarations, each a key and its carrier. -/
structure SigApp where
  rows : RowTable := []
  services : List (ServiceKey × Ty) := []

namespace SigApp

/-- The carrier the application declares for a service code: its first declaration there. -/
def codeTy (app : SigApp) (code : ServiceTypeCode) : Option Ty :=
  (app.services.find? (fun entry => entry.1.service == code)).map Prod.snd

/-- The carrier the built-in table gives a service code. -/
def builtinCodeTy (code : ServiceTypeCode) : Option Ty :=
  (nativeServiceTypes.find? (fun entry => entry.1 == code.value)).map Prod.snd

/-- A key's carrier under the application's signature, selected by its code (row 113): the
reserved `Scope` key keeps its exception, the machine's reserved names type nothing, and a
free name's code reads the application's declarations before the built-in codes. -/
def serviceTy (app : SigApp) (key : ServiceKey) : Option Ty :=
  match nativeReservedServiceTypes.find? (fun entry => entry.1 == key) with
  | some (_, ty) => some ty
  | none =>
    if key.name.value < Effect4.Machine.Env.firstFreeName then none
    else match app.codeTy key.service with
      | some ty => some ty
      | none => builtinCodeTy key.service

/-- The checker's signature over an application's tables. -/
def signature (app : SigApp) : Signature NativeOp :=
  { nativeSignature app.rows with serviceTy := app.serviceTy }

/-- With no declarations the service table is the built-in one. -/
theorem serviceTy_nil (rows : RowTable) : (⟨rows, []⟩ : SigApp).serviceTy = nativeServiceTy :=
  rfl

/-- With no declarations the signature is the native one. -/
theorem signature_nil (rows : RowTable) : (⟨rows, []⟩ : SigApp).signature = nativeSignature rows :=
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

/-- An application signature over a longer table extends the shorter one. -/
theorem rows_append (app : SigApp) (t' : RowTable) :
    SigExtends app.signature (SigApp.mk (app.rows ++ t') app.services).signature := by
  have h := Effect4.Program.rows_append app.rows t'
  exact ⟨rfl, rfl, rfl, h.row, fun _ _ hk => hk⟩

/-- A declaration appended at a code that neither the application nor the built-in table
types. -/
def FreshCode (app : SigApp) (entry : ServiceKey × Ty) : Prop :=
  app.codeTy entry.1.service = none ∧ builtinCodeTy entry.1.service = none

/-- Declarations appended at fresh codes extend the signature: every key the shorter table
types keeps its carrier. -/
theorem services_append (app : SigApp) (s' : List (ServiceKey × Ty))
    (fresh : ∀ entry ∈ s', FreshCode app entry) :
    SigExtends app.signature (SigApp.mk app.rows (app.services ++ s')).signature := by
  refine ⟨rfl, rfl, rfl, fun _ h => ⟨h, rfl⟩, ?_⟩
  intro key ty hk
  change app.serviceTy key = some ty at hk
  change SigApp.serviceTy ⟨app.rows, app.services ++ s'⟩ key = some ty
  unfold serviceTy at hk ⊢
  split at hk
  · exact hk
  · split at hk
    · cases hk
    · rename_i hfree
      rw [if_neg hfree]
      have happ : (SigApp.mk app.rows (app.services ++ s')).codeTy key.service =
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

section FoldCongr
universe u
/-- Two algebras over the program family agree at every constructor that carries no operation
or service key outright, and at the four that do (`perform`, `service`, `provideService`, the
layers' `succeed` and `effect`) for the operations and keys the guards admit. -/
structure EffAlgebra.AgreeOn {Op : Type} {R : EffFam → Type u} (alg₁ alg₂ : EffAlgebra Op R)
    (okOp : Op → Prop) (okKey : ServiceKey → Prop) : Prop where
  eff_succeed : alg₁.eff_succeed = alg₂.eff_succeed
  eff_fail : alg₁.eff_fail = alg₂.eff_fail
  eff_failCause : alg₁.eff_failCause = alg₂.eff_failCause
  eff_sync : alg₁.eff_sync = alg₂.eff_sync
  eff_suspend : alg₁.eff_suspend = alg₂.eff_suspend
  eff_perform : ∀ op, okOp op → alg₁.eff_perform op = alg₂.eff_perform op
  eff_bind : alg₁.eff_bind = alg₂.eff_bind
  eff_gen : alg₁.eff_gen = alg₂.eff_gen
  eff_catchCause : alg₁.eff_catchCause = alg₂.eff_catchCause
  eff_matchCause : alg₁.eff_matchCause = alg₂.eff_matchCause
  eff_onExit : alg₁.eff_onExit = alg₂.eff_onExit
  eff_exit : alg₁.eff_exit = alg₂.eff_exit
  eff_uninterruptible : alg₁.eff_uninterruptible = alg₂.eff_uninterruptible
  eff_interruptible : alg₁.eff_interruptible = alg₂.eff_interruptible
  eff_yieldNow : alg₁.eff_yieldNow = alg₂.eff_yieldNow
  eff_awaitFiber : alg₁.eff_awaitFiber = alg₂.eff_awaitFiber
  eff_withFiber : alg₁.eff_withFiber = alg₂.eff_withFiber
  eff_scoped : alg₁.eff_scoped = alg₂.eff_scoped
  eff_acquireRelease : alg₁.eff_acquireRelease = alg₂.eff_acquireRelease
  eff_provideLayer : alg₁.eff_provideLayer = alg₂.eff_provideLayer
  eff_service : ∀ key, okKey key → alg₁.eff_service key = alg₂.eff_service key
  eff_provideService : ∀ key, okKey key → alg₁.eff_provideService key = alg₂.eff_provideService key
  eff_catchIf : alg₁.eff_catchIf = alg₂.eff_catchIf
  eff_select : alg₁.eff_select = alg₂.eff_select
  eff_iterate : alg₁.eff_iterate = alg₂.eff_iterate
  stmt_bindYield : alg₁.stmt_bindYield = alg₂.stmt_bindYield
  stmt_yieldDiscard : alg₁.stmt_yieldDiscard = alg₂.stmt_yieldDiscard
  stmt_ret : alg₁.stmt_ret = alg₂.stmt_ret
  stmt_ifElse : alg₁.stmt_ifElse = alg₂.stmt_ifElse
  stmt_whileTrue : alg₁.stmt_whileTrue = alg₂.stmt_whileTrue
  stmt_breakLoop : alg₁.stmt_breakLoop = alg₂.stmt_breakLoop
  stmts_nil : alg₁.stmts_nil = alg₂.stmts_nil
  stmts_cons : alg₁.stmts_cons = alg₂.stmts_cons
  effs_nil : alg₁.effs_nil = alg₂.effs_nil
  effs_cons : alg₁.effs_cons = alg₂.effs_cons
  action_fork : alg₁.action_fork = alg₂.action_fork
  action_forkIn : alg₁.action_forkIn = alg₂.action_forkIn
  action_forkScoped : alg₁.action_forkScoped = alg₂.action_forkScoped
  action_runIn : alg₁.action_runIn = alg₂.action_runIn
  action_interrupt : alg₁.action_interrupt = alg₂.action_interrupt
  action_interruptScoped : alg₁.action_interruptScoped = alg₂.action_interruptScoped
  action_interruptAll : alg₁.action_interruptAll = alg₂.action_interruptAll
  action_awaitAll : alg₁.action_awaitAll = alg₂.action_awaitAll
  action_awaitAllFailFast : alg₁.action_awaitAllFailFast = alg₂.action_awaitAllFailFast
  action_snapshotChildren : alg₁.action_snapshotChildren = alg₂.action_snapshotChildren
  action_awaitNewChildren : alg₁.action_awaitNewChildren = alg₂.action_awaitNewChildren
  action_raceAll : alg₁.action_raceAll = alg₂.action_raceAll
  action_setContext : alg₁.action_setContext = alg₂.action_setContext
  action_getContext : alg₁.action_getContext = alg₂.action_getContext
  action_getId : alg₁.action_getId = alg₂.action_getId
  action_closeScope : alg₁.action_closeScope = alg₂.action_closeScope
  layer_succeed : ∀ key, okKey key → alg₁.layer_succeed key = alg₂.layer_succeed key
  layer_effect : ∀ key, okKey key → alg₁.layer_effect key = alg₂.layer_effect key
  layer_effectDiscard : alg₁.layer_effectDiscard = alg₂.layer_effectDiscard
  layer_provide : alg₁.layer_provide = alg₂.layer_provide
  layer_provideMerge : alg₁.layer_provideMerge = alg₂.layer_provideMerge
  layer_merge : alg₁.layer_merge = alg₂.layer_merge
  layer_fresh : alg₁.layer_fresh = alg₂.layer_fresh
  layer_orDie : alg₁.layer_orDie = alg₂.layer_orDie
  layer_ref : alg₁.layer_ref = alg₂.layer_ref
  layer_mergeAll : alg₁.layer_mergeAll = alg₂.layer_mergeAll
  layers_nil : alg₁.layers_nil = alg₂.layers_nil
  layers_cons : alg₁.layers_cons = alg₂.layers_cons

/-- The reads a program makes of a signature, as a fold: every operation it performs satisfies
`okOp`, every service key it reads satisfies `okKey`. -/
def readsAlg {Op : Type} (okOp : Op → Prop) (okKey : ServiceKey → Prop) :
    EffAlgebra Op (fun _ => Prop) where
  eff_succeed _ := True
  eff_fail _ := True
  eff_failCause _ := True
  eff_sync _ := True
  eff_suspend r0 := r0
  eff_perform op _ := okOp op
  eff_bind r0 r1 := r0 ∧ r1
  eff_gen r0 := r0
  eff_catchCause r0 r1 := r0 ∧ r1
  eff_matchCause r0 r1 r2 := r0 ∧ r1 ∧ r2
  eff_onExit r0 r1 := r0 ∧ r1
  eff_exit r0 := r0
  eff_uninterruptible r0 := r0
  eff_interruptible r0 := r0
  eff_yieldNow _ := True
  eff_awaitFiber _ _ := True
  eff_withFiber r0 := r0
  eff_scoped r0 := r0
  eff_acquireRelease r0 r1 := r0 ∧ r1
  eff_provideLayer r0 _ r2 := r0 ∧ r2
  eff_service key := okKey key
  eff_provideService key _ r2 := okKey key ∧ r2
  eff_catchIf _ r1 r2 := r1 ∧ r2
  eff_select _ _ r2 r3 := r2 ∧ r3
  eff_iterate _ _ _ _ _ r5 := r5
  stmt_bindYield r0 := r0
  stmt_yieldDiscard r0 := r0
  stmt_ret _ := True
  stmt_ifElse _ r1 r2 := r1 ∧ r2
  stmt_whileTrue r0 := r0
  stmt_breakLoop := True
  stmts_nil := True
  stmts_cons r0 r1 := r0 ∧ r1
  effs_nil := True
  effs_cons r0 r1 := r0 ∧ r1
  action_fork r0 _ := r0
  action_forkIn r0 _ _ := r0
  action_forkScoped r0 _ := r0
  action_runIn _ _ := True
  action_interrupt _ := True
  action_interruptScoped _ := True
  action_interruptAll _ _ := True
  action_awaitAll _ := True
  action_awaitAllFailFast _ := True
  action_snapshotChildren := True
  action_awaitNewChildren _ := True
  action_raceAll r0 := r0
  action_setContext _ := True
  action_getContext := True
  action_getId := True
  action_closeScope _ _ := True
  layer_succeed key _ := okKey key
  layer_effect key r1 := okKey key ∧ r1
  layer_effectDiscard r0 := r0
  layer_provide r0 r1 := r0 ∧ r1
  layer_provideMerge r0 r1 := r0 ∧ r1
  layer_merge r0 r1 := r0 ∧ r1
  layer_fresh r0 := r0
  layer_orDie r0 := r0
  layer_ref _ := True
  layer_mergeAll r0 := r0
  layers_nil := True
  layers_cons r0 r1 := r0 ∧ r1

variable {Op : Type} {R : EffFam → Type u} {alg₁ alg₂ : EffAlgebra Op R}
  {okOp : Op → Prop} {okKey : ServiceKey → Prop}

mutual
/-- Fold congruence at `Eff`. -/
theorem cata_eff_congr_on (h : alg₁.AgreeOn alg₂ okOp okKey) (e : Eff Op)
    (hr : cata_eff (readsAlg okOp okKey) e) : cata_eff alg₁ e = cata_eff alg₂ e := by
  cases e with
  | succeed a0 =>
    show alg₁.eff_succeed a0 = alg₂.eff_succeed a0
    rw [h.eff_succeed]
  | fail a0 =>
    show alg₁.eff_fail a0 = alg₂.eff_fail a0
    rw [h.eff_fail]
  | failCause a0 =>
    show alg₁.eff_failCause a0 = alg₂.eff_failCause a0
    rw [h.eff_failCause]
  | sync a0 =>
    show alg₁.eff_sync a0 = alg₂.eff_sync a0
    rw [h.eff_sync]
  | suspend a0 =>
    show alg₁.eff_suspend (cata_eff alg₁ a0) = alg₂.eff_suspend (cata_eff alg₂ a0)
    rw [h.eff_suspend, cata_eff_congr_on h a0 hr]
  | perform a0 a1 =>
    show alg₁.eff_perform a0 a1 = alg₂.eff_perform a0 a1
    rw [h.eff_perform a0 hr]
  | bind a0 a1 =>
    show alg₁.eff_bind (cata_eff alg₁ a0) (cata_eff alg₁ a1) =
      alg₂.eff_bind (cata_eff alg₂ a0) (cata_eff alg₂ a1)
    rw [h.eff_bind, cata_eff_congr_on h a0 hr.1, cata_eff_congr_on h a1 hr.2]
  | gen a0 =>
    show alg₁.eff_gen (cata_stmts alg₁ a0) = alg₂.eff_gen (cata_stmts alg₂ a0)
    rw [h.eff_gen, cata_stmts_congr_on h a0 hr]
  | catchCause a0 a1 =>
    show alg₁.eff_catchCause (cata_eff alg₁ a0) (cata_eff alg₁ a1) =
      alg₂.eff_catchCause (cata_eff alg₂ a0) (cata_eff alg₂ a1)
    rw [h.eff_catchCause, cata_eff_congr_on h a0 hr.1, cata_eff_congr_on h a1 hr.2]
  | matchCause a0 a1 a2 =>
    show alg₁.eff_matchCause (cata_eff alg₁ a0) (cata_eff alg₁ a1) (cata_eff alg₁ a2) =
      alg₂.eff_matchCause (cata_eff alg₂ a0) (cata_eff alg₂ a1) (cata_eff alg₂ a2)
    rw [h.eff_matchCause, cata_eff_congr_on h a0 hr.1, cata_eff_congr_on h a1 hr.2.1,
      cata_eff_congr_on h a2 hr.2.2]
  | onExit a0 a1 =>
    show alg₁.eff_onExit (cata_eff alg₁ a0) (cata_eff alg₁ a1) =
      alg₂.eff_onExit (cata_eff alg₂ a0) (cata_eff alg₂ a1)
    rw [h.eff_onExit, cata_eff_congr_on h a0 hr.1, cata_eff_congr_on h a1 hr.2]
  | exit a0 =>
    show alg₁.eff_exit (cata_eff alg₁ a0) = alg₂.eff_exit (cata_eff alg₂ a0)
    rw [h.eff_exit, cata_eff_congr_on h a0 hr]
  | uninterruptible a0 =>
    show alg₁.eff_uninterruptible (cata_eff alg₁ a0) = alg₂.eff_uninterruptible (cata_eff alg₂ a0)
    rw [h.eff_uninterruptible, cata_eff_congr_on h a0 hr]
  | interruptible a0 =>
    show alg₁.eff_interruptible (cata_eff alg₁ a0) = alg₂.eff_interruptible (cata_eff alg₂ a0)
    rw [h.eff_interruptible, cata_eff_congr_on h a0 hr]
  | yieldNow a0 =>
    show alg₁.eff_yieldNow a0 = alg₂.eff_yieldNow a0
    rw [h.eff_yieldNow]
  | awaitFiber a0 a1 =>
    show alg₁.eff_awaitFiber a0 a1 = alg₂.eff_awaitFiber a0 a1
    rw [h.eff_awaitFiber]
  | withFiber a0 =>
    show alg₁.eff_withFiber (cata_action alg₁ a0) = alg₂.eff_withFiber (cata_action alg₂ a0)
    rw [h.eff_withFiber, cata_action_congr_on h a0 hr]
  | «scoped» a0 =>
    show alg₁.eff_scoped (cata_eff alg₁ a0) = alg₂.eff_scoped (cata_eff alg₂ a0)
    rw [h.eff_scoped, cata_eff_congr_on h a0 hr]
  | acquireRelease a0 a1 =>
    show alg₁.eff_acquireRelease (cata_eff alg₁ a0) (cata_eff alg₁ a1) =
      alg₂.eff_acquireRelease (cata_eff alg₂ a0) (cata_eff alg₂ a1)
    rw [h.eff_acquireRelease, cata_eff_congr_on h a0 hr.1, cata_eff_congr_on h a1 hr.2]
  | provideLayer a0 a1 a2 =>
    show alg₁.eff_provideLayer (cata_layer alg₁ a0) a1 (cata_eff alg₁ a2) =
      alg₂.eff_provideLayer (cata_layer alg₂ a0) a1 (cata_eff alg₂ a2)
    rw [h.eff_provideLayer, cata_layer_congr_on h a0 hr.1, cata_eff_congr_on h a2 hr.2]
  | service a0 =>
    show alg₁.eff_service a0 = alg₂.eff_service a0
    rw [h.eff_service a0 hr]
  | provideService a0 a1 a2 =>
    show alg₁.eff_provideService a0 a1 (cata_eff alg₁ a2) =
      alg₂.eff_provideService a0 a1 (cata_eff alg₂ a2)
    rw [h.eff_provideService a0 hr.1, cata_eff_congr_on h a2 hr.2]
  | catchIf a0 a1 a2 =>
    show alg₁.eff_catchIf a0 (cata_eff alg₁ a1) (cata_eff alg₁ a2) =
      alg₂.eff_catchIf a0 (cata_eff alg₂ a1) (cata_eff alg₂ a2)
    rw [h.eff_catchIf, cata_eff_congr_on h a1 hr.1, cata_eff_congr_on h a2 hr.2]
  | select a0 a1 a2 a3 =>
    show alg₁.eff_select a0 a1 (cata_eff alg₁ a2) (cata_eff alg₁ a3) =
      alg₂.eff_select a0 a1 (cata_eff alg₂ a2) (cata_eff alg₂ a3)
    rw [h.eff_select, cata_eff_congr_on h a2 hr.1, cata_eff_congr_on h a3 hr.2]
  | iterate a0 a1 a2 a3 a4 a5 =>
    show alg₁.eff_iterate a0 a1 a2 a3 a4 (cata_eff alg₁ a5) =
      alg₂.eff_iterate a0 a1 a2 a3 a4 (cata_eff alg₂ a5)
    rw [h.eff_iterate, cata_eff_congr_on h a5 hr]
termination_by structural e

/-- Fold congruence at `Stmt`. -/
theorem cata_stmt_congr_on (h : alg₁.AgreeOn alg₂ okOp okKey) (e : Stmt Op)
    (hr : cata_stmt (readsAlg okOp okKey) e) : cata_stmt alg₁ e = cata_stmt alg₂ e := by
  cases e with
  | bindYield a0 =>
    show alg₁.stmt_bindYield (cata_eff alg₁ a0) = alg₂.stmt_bindYield (cata_eff alg₂ a0)
    rw [h.stmt_bindYield, cata_eff_congr_on h a0 hr]
  | yieldDiscard a0 =>
    show alg₁.stmt_yieldDiscard (cata_eff alg₁ a0) = alg₂.stmt_yieldDiscard (cata_eff alg₂ a0)
    rw [h.stmt_yieldDiscard, cata_eff_congr_on h a0 hr]
  | ret a0 =>
    show alg₁.stmt_ret a0 = alg₂.stmt_ret a0
    rw [h.stmt_ret]
  | ifElse a0 a1 a2 =>
    show alg₁.stmt_ifElse a0 (cata_stmts alg₁ a1) (cata_stmts alg₁ a2) =
      alg₂.stmt_ifElse a0 (cata_stmts alg₂ a1) (cata_stmts alg₂ a2)
    rw [h.stmt_ifElse, cata_stmts_congr_on h a1 hr.1, cata_stmts_congr_on h a2 hr.2]
  | whileTrue a0 =>
    show alg₁.stmt_whileTrue (cata_stmts alg₁ a0) = alg₂.stmt_whileTrue (cata_stmts alg₂ a0)
    rw [h.stmt_whileTrue, cata_stmts_congr_on h a0 hr]
  | breakLoop =>
    show alg₁.stmt_breakLoop = alg₂.stmt_breakLoop
    rw [h.stmt_breakLoop]
termination_by structural e

/-- Fold congruence at `Stmts`. -/
theorem cata_stmts_congr_on (h : alg₁.AgreeOn alg₂ okOp okKey) (e : Stmts Op)
    (hr : cata_stmts (readsAlg okOp okKey) e) : cata_stmts alg₁ e = cata_stmts alg₂ e := by
  cases e with
  | nil =>
    show alg₁.stmts_nil = alg₂.stmts_nil
    rw [h.stmts_nil]
  | cons a0 a1 =>
    show alg₁.stmts_cons (cata_stmt alg₁ a0) (cata_stmts alg₁ a1) =
      alg₂.stmts_cons (cata_stmt alg₂ a0) (cata_stmts alg₂ a1)
    rw [h.stmts_cons, cata_stmt_congr_on h a0 hr.1, cata_stmts_congr_on h a1 hr.2]
termination_by structural e

/-- Fold congruence at `Effs`. -/
theorem cata_effs_congr_on (h : alg₁.AgreeOn alg₂ okOp okKey) (e : Effs Op)
    (hr : cata_effs (readsAlg okOp okKey) e) : cata_effs alg₁ e = cata_effs alg₂ e := by
  cases e with
  | nil =>
    show alg₁.effs_nil = alg₂.effs_nil
    rw [h.effs_nil]
  | cons a0 a1 =>
    show alg₁.effs_cons (cata_eff alg₁ a0) (cata_effs alg₁ a1) =
      alg₂.effs_cons (cata_eff alg₂ a0) (cata_effs alg₂ a1)
    rw [h.effs_cons, cata_eff_congr_on h a0 hr.1, cata_effs_congr_on h a1 hr.2]
termination_by structural e

/-- Fold congruence at `ActionTerm`. -/
theorem cata_action_congr_on (h : alg₁.AgreeOn alg₂ okOp okKey) (e : ActionTerm Op)
    (hr : cata_action (readsAlg okOp okKey) e) : cata_action alg₁ e = cata_action alg₂ e := by
  cases e with
  | fork a0 a1 =>
    show alg₁.action_fork (cata_eff alg₁ a0) a1 = alg₂.action_fork (cata_eff alg₂ a0) a1
    rw [h.action_fork, cata_eff_congr_on h a0 hr]
  | forkIn a0 a1 a2 =>
    show alg₁.action_forkIn (cata_eff alg₁ a0) a1 a2 = alg₂.action_forkIn (cata_eff alg₂ a0) a1 a2
    rw [h.action_forkIn, cata_eff_congr_on h a0 hr]
  | forkScoped a0 a1 =>
    show alg₁.action_forkScoped (cata_eff alg₁ a0) a1 = alg₂.action_forkScoped (cata_eff alg₂ a0) a1
    rw [h.action_forkScoped, cata_eff_congr_on h a0 hr]
  | runIn a0 a1 =>
    show alg₁.action_runIn a0 a1 = alg₂.action_runIn a0 a1
    rw [h.action_runIn]
  | interrupt a0 =>
    show alg₁.action_interrupt a0 = alg₂.action_interrupt a0
    rw [h.action_interrupt]
  | interruptScoped a0 =>
    show alg₁.action_interruptScoped a0 = alg₂.action_interruptScoped a0
    rw [h.action_interruptScoped]
  | interruptAll a0 a1 =>
    show alg₁.action_interruptAll a0 a1 = alg₂.action_interruptAll a0 a1
    rw [h.action_interruptAll]
  | awaitAll a0 =>
    show alg₁.action_awaitAll a0 = alg₂.action_awaitAll a0
    rw [h.action_awaitAll]
  | awaitAllFailFast a0 =>
    show alg₁.action_awaitAllFailFast a0 = alg₂.action_awaitAllFailFast a0
    rw [h.action_awaitAllFailFast]
  | snapshotChildren =>
    show alg₁.action_snapshotChildren = alg₂.action_snapshotChildren
    rw [h.action_snapshotChildren]
  | awaitNewChildren a0 =>
    show alg₁.action_awaitNewChildren a0 = alg₂.action_awaitNewChildren a0
    rw [h.action_awaitNewChildren]
  | raceAll a0 =>
    show alg₁.action_raceAll (cata_effs alg₁ a0) = alg₂.action_raceAll (cata_effs alg₂ a0)
    rw [h.action_raceAll, cata_effs_congr_on h a0 hr]
  | setContext a0 =>
    show alg₁.action_setContext a0 = alg₂.action_setContext a0
    rw [h.action_setContext]
  | getContext =>
    show alg₁.action_getContext = alg₂.action_getContext
    rw [h.action_getContext]
  | getId =>
    show alg₁.action_getId = alg₂.action_getId
    rw [h.action_getId]
  | closeScope a0 a1 =>
    show alg₁.action_closeScope a0 a1 = alg₂.action_closeScope a0 a1
    rw [h.action_closeScope]
termination_by structural e

/-- Fold congruence at `LayerTerm`. -/
theorem cata_layer_congr_on (h : alg₁.AgreeOn alg₂ okOp okKey) (e : LayerTerm Op)
    (hr : cata_layer (readsAlg okOp okKey) e) : cata_layer alg₁ e = cata_layer alg₂ e := by
  cases e with
  | succeed a0 a1 =>
    show alg₁.layer_succeed a0 a1 = alg₂.layer_succeed a0 a1
    rw [h.layer_succeed a0 hr]
  | effect a0 a1 =>
    show alg₁.layer_effect a0 (cata_eff alg₁ a1) = alg₂.layer_effect a0 (cata_eff alg₂ a1)
    rw [h.layer_effect a0 hr.1, cata_eff_congr_on h a1 hr.2]
  | effectDiscard a0 =>
    show alg₁.layer_effectDiscard (cata_eff alg₁ a0) = alg₂.layer_effectDiscard (cata_eff alg₂ a0)
    rw [h.layer_effectDiscard, cata_eff_congr_on h a0 hr]
  | provide a0 a1 =>
    show alg₁.layer_provide (cata_layer alg₁ a0) (cata_layer alg₁ a1) =
      alg₂.layer_provide (cata_layer alg₂ a0) (cata_layer alg₂ a1)
    rw [h.layer_provide, cata_layer_congr_on h a0 hr.1, cata_layer_congr_on h a1 hr.2]
  | provideMerge a0 a1 =>
    show alg₁.layer_provideMerge (cata_layer alg₁ a0) (cata_layer alg₁ a1) =
      alg₂.layer_provideMerge (cata_layer alg₂ a0) (cata_layer alg₂ a1)
    rw [h.layer_provideMerge, cata_layer_congr_on h a0 hr.1, cata_layer_congr_on h a1 hr.2]
  | merge a0 a1 =>
    show alg₁.layer_merge (cata_layer alg₁ a0) (cata_layer alg₁ a1) =
      alg₂.layer_merge (cata_layer alg₂ a0) (cata_layer alg₂ a1)
    rw [h.layer_merge, cata_layer_congr_on h a0 hr.1, cata_layer_congr_on h a1 hr.2]
  | fresh a0 =>
    show alg₁.layer_fresh (cata_layer alg₁ a0) = alg₂.layer_fresh (cata_layer alg₂ a0)
    rw [h.layer_fresh, cata_layer_congr_on h a0 hr]
  | orDie a0 =>
    show alg₁.layer_orDie (cata_layer alg₁ a0) = alg₂.layer_orDie (cata_layer alg₂ a0)
    rw [h.layer_orDie, cata_layer_congr_on h a0 hr]
  | ref a0 =>
    show alg₁.layer_ref a0 = alg₂.layer_ref a0
    rw [h.layer_ref]
  | mergeAll a0 =>
    show alg₁.layer_mergeAll (cata_layers alg₁ a0) = alg₂.layer_mergeAll (cata_layers alg₂ a0)
    rw [h.layer_mergeAll, cata_layers_congr_on h a0 hr]
termination_by structural e

/-- Fold congruence at `LayerTerms`. -/
theorem cata_layers_congr_on (h : alg₁.AgreeOn alg₂ okOp okKey) (e : LayerTerms Op)
    (hr : cata_layers (readsAlg okOp okKey) e) : cata_layers alg₁ e = cata_layers alg₂ e := by
  cases e with
  | nil =>
    show alg₁.layers_nil = alg₂.layers_nil
    rw [h.layers_nil]
  | cons a0 a1 =>
    show alg₁.layers_cons (cata_layer alg₁ a0) (cata_layers alg₁ a1) =
      alg₂.layers_cons (cata_layer alg₂ a0) (cata_layers alg₂ a1)
    rw [h.layers_cons, cata_layer_congr_on h a0 hr.1, cata_layers_congr_on h a1 hr.2]
termination_by structural e

end

end FoldCongr

/-! ## C3's reflection (TY-04): a Σ-program is checked the same under every extension -/

/-- The operations a signature admits: the checker reads an operation's domain bit and row. -/
def SigOkOp {Op : Type} (s : Signature Op) (op : Op) : Prop := s.dom op = true

/-- The service keys a signature types: the checker reads a key's carrier. -/
def SigOkKey {Op : Type} (s : Signature Op) (key : ServiceKey) : Prop := (s.serviceTy key).isSome = true

/-- **A Σ-program** (TY-04): every operation it performs is in `dom s`, every service key it reads
has a carrier in `s` — exactly the reads the checker's algebra makes of the signature. -/
def SigProgram {Op : Type} (s : Signature Op) (e : Eff Op) : Prop :=
  cata_eff (readsAlg (SigOkOp s) (SigOkKey s)) e

/-- The term reader agrees along an extension. -/
theorem term?_ext {Op : Type} {s s' : Signature Op} (h : SigExtends s s') :
    Checker.term? s' = Checker.term? s := by
  funext env p t
  unfold Checker.term?
  rw [h.termTy]

/-- **Along an extension the checker's two algebras agree on the reads the smaller signature
admits** (proved): field by field, outright where the field reads only atoms and the scope key,
guarded where it reads an operation's row or a key's carrier. -/
theorem check_alg_agreeOn {Op : Type} {s s' : Signature Op} (h : SigExtends s s') :
    (Checker.check.alg s').AgreeOn (Checker.check.alg s) (SigOkOp s) (SigOkKey s) := by
  have hterm := term?_ext h
  have hcause : causeTy s' = causeTy s := funext fun env => funext fun c => h.causeTy env c
  have hbody : bodyRequires s' = bodyRequires s := funext h.bodyRequires
  exact {
    eff_succeed := by simp only [Checker.check.alg, hterm]
    eff_fail := by simp only [Checker.check.alg, hterm]
    eff_failCause := by simp only [Checker.check.alg, hcause]
    eff_sync := by simp only [Checker.check.alg, hterm]
    eff_suspend := rfl
    eff_perform := fun op hd => by
      have hdom : s.dom op = true := hd
      simp only [Checker.check.alg, hterm, (h.row op hdom).1, (h.row op hdom).2, hdom]
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
    eff_catchIf := by simp only [Checker.check.alg, hterm]
    eff_select := by simp only [Checker.check.alg, hterm]
    eff_iterate := by simp only [Checker.check.alg, hterm]
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
    action_setContext := by simp only [Checker.check.alg, hterm]
    action_getContext := rfl
    action_getId := rfl
    action_closeScope := by simp only [Checker.check.alg, hterm]
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
refusal (`admitSig`) and proves the two agree (`admitSig_ok_iff`). Its shape is C6's
(the synthesis §2.2, as Codex's audit amends it): every row and every declaration meets its own
conditions, the rows and the declarations are pairwise compatible, and every key a row requires
has a carrier (the third clause shape, which points from rows to services and is monotone under
append). So `LawfulSig (Σ ++ ε)` splits into the parts and the cross terms by
`List.forall_mem_append` and `List.pairwise_append` (`lawful_append`). -/

/-- A row's local conditions, with the reason each one gives when it fails. -/
inductive RowReason
  /-- `checkTable`: the runner registers only external rows. -/
  | notExternal
  /-- `checkTable`: only asynchronous rows. -/
  | notAsync
  /-- `Table.lawful`: the row's key collides with a built-in operation's. -/
  | builtinCollision
  /-- `Table.lawful`: a value row has trailing names. -/
  | valueRowTrailing
  /-- DB-15: the column mentions the reserved integer type. -/
  | intType (column : String)
  /-- Row 97: the answer or error column mentions an internal handle kind. -/
  | internalHandle (column : String)
  /-- Row 127: the column is empty and is not `never`. -/
  | emptyColumn (column : String)
  /-- Row 42: a template parameter sits under a union in the column. -/
  | templateNotAdmissible (column : String)
  /-- Row 42: the answer or error names a parameter the request does not bind. -/
  | notWellScoped
deriving DecidableEq, Repr

/-- A row's local checks, in the order a refusal names the first failing one. -/
def rowChecks (r : Row) : List (Bool × RowReason) :=
  [(r.registration == .external, .notExternal),
   (r.kind == .async, .notAsync),
   (!(NativeOp.all.map (fun op => (nativeRowOf [] op).key)).contains (rowKey r), .builtinCollision),
   (!(r.shape == .value) || r.trailing.isEmpty, .valueRowTrailing),
   ((findInt [] r.request).isNone, .intType "request"),
   ((findInt [] r.answer).isNone, .intType "answer"),
   ((findInt [] r.error).isNone, .intType "error"),
   ((findInternalHandle [] r.answer).isNone, .internalHandle "answer"),
   ((findInternalHandle [] r.error).isNone, .internalHandle "error"),
   (admitColumn r.request, .emptyColumn "request"),
   (admitColumn r.answer, .emptyColumn "answer"),
   (admitColumn r.error, .emptyColumn "error"),
   (r.request.templateAdmissible, .templateNotAdmissible "request"),
   (r.answer.templateAdmissible, .templateNotAdmissible "answer"),
   (r.error.templateAdmissible, .templateNotAdmissible "error"),
   (r.wellScoped, .notWellScoped)]

/-- A declaration's local conditions (row 114), with their reasons. -/
inductive ServiceReason
  /-- The key's name is one the machine reserves (`Env.firstFreeName`). -/
  | reservedName
  /-- The carrier is not flat (`unit`, `nat`, `bool`, `string`, a non-context handle). -/
  | nonFlatCarrier
  /-- The built-in table gives the key's code another carrier. -/
  | conflictsBuiltin
deriving DecidableEq, Repr

/-- The flat carriers, as a fold: the scalars and every handle but the context. -/
def flatCarrierAlg : TyAlgebra (fun _ => Bool) where
  ty_never := false
  ty_unit := true
  ty_nat := true
  ty_int := false
  ty_string := true
  ty_bool := true
  ty_handle target := target != Ty.contextTarget
  ty_option _ := false
  ty_list _ := false
  ty_prod _ _ := false
  ty_except _ _ := false
  ty_exitOf _ _ := false
  ty_causeOf _ := false
  ty_fiberOf _ _ := false
  ty_union _ _ := false
  ty_lit _ := false
  ty_refOf _ := false
  ty_deferredOf _ _ := false
  ty_var _ := false
  ty_unknown := false
  -- structured carriers are row 118's; the data wave's leaves are not service carriers yet
  ty_record _ := false
  ty_map _ _ := false
  ty_tuple _ := false
  ty_app _ _ := false
  ty_null := false
  ty_undefined := false
  ty_number := false
  ty_bytes := false

/-- A flat carrier (row 114; row 118 owns structured carriers). -/
def flatCarrier (t : Ty) : Bool := cata_ty flatCarrierAlg t

/-- A declaration's local checks, in order. -/
def serviceChecks (e : ServiceKey × Ty) : List (Bool × ServiceReason) :=
  [(decide (Effect4.Machine.Env.firstFreeName ≤ e.1.name.value), .reservedName),
   (flatCarrier e.2, .nonFlatCarrier),
   ((SigApp.builtinCodeTy e.1.service).all (· == e.2), .conflictsBuiltin)]

/-- The first failing check's reason. -/
def firstFailing {β : Type} (checks : List (Bool × β)) : Option β :=
  (checks.find? fun c => !c.1).map Prod.snd

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

/-- The first position of a list whose element a check refuses, with the refusal. -/
def firstIndexed {α β : Type} (f : α → Option β) : Nat → List α → Option (Nat × β)
  | _, [] => none
  | i, x :: xs =>
    match f x with
    | some b => some (i, b)
    | none => firstIndexed f (i + 1) xs

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

/-- The first repeated element of a list. -/
def firstDup {α : Type} [DecidableEq α] : List α → Option α
  | [] => none
  | x :: xs => if x ∈ xs then some x else firstDup xs

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

/-- Why a signature is not lawful, located: a row by its position, a declaration by its
position, a repeated row key or service code, a required key with no carrier. -/
inductive SigRefusal
  | row (index : Nat) (reason : RowReason)
  | duplicateRow (key : String × List String)
  | service (index : Nat) (reason : ServiceReason)
  | duplicateCode (code : ServiceTypeCode)
  | unservedKey (row : Nat) (key : ServiceKey)
deriving DecidableEq, Repr

/-- The first refusal, in the order rows, row keys, declarations, codes, required keys. -/
def sigRefusal? (app : SigApp) : Option SigRefusal :=
  ((firstIndexed (fun r => firstFailing (rowChecks r)) 0 app.rows).map
      fun found => .row found.1 found.2).or <|
  ((firstDup (app.rows.map rowKey)).map .duplicateRow).or <|
  ((firstIndexed (fun e => firstFailing (serviceChecks e)) 0 app.services).map
      fun found => .service found.1 found.2).or <|
  ((firstDup (app.services.map (·.1.service))).map .duplicateCode).or <|
  (firstIndexed (fun r => r.requires.find? fun k => !(app.serviceTy k).isSome) 0 app.rows).map
      fun found => .unservedKey found.1 found.2

/-- **Admit a signature**: a located refusal, or `ok`. -/
def admitSig (app : SigApp) : Except SigRefusal Unit :=
  match sigRefusal? app with
  | some why => .error why
  | none => .ok ()

/-- **The lawful signatures** (rows 97, 113, 114, 127; C6's shape). -/
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

/-- **The located refusal is complete** (proved): no refusal exactly at a lawful signature. -/
theorem sigRefusal?_eq_none_iff (app : SigApp) : sigRefusal? app = none ↔ LawfulSig app := by
  unfold sigRefusal?
  rw [Option.or_eq_none_iff, Option.or_eq_none_iff, Option.or_eq_none_iff, Option.or_eq_none_iff,
    Option.map_eq_none_iff, Option.map_eq_none_iff, Option.map_eq_none_iff,
    Option.map_eq_none_iff, Option.map_eq_none_iff,
    firstIndexed_eq_none_iff, firstDup_eq_none_iff, firstIndexed_eq_none_iff,
    firstDup_eq_none_iff, firstIndexed_eq_none_iff]
  constructor
  · rintro ⟨hrows, hkeys, hsvc, hcodes, hserved⟩
    refine ⟨fun r hr => (firstFailing_eq_none_iff _).mp (hrows r hr), List.pairwise_map.mp hkeys,
      fun e he => (firstFailing_eq_none_iff _).mp (hsvc e he), List.pairwise_map.mp hcodes, ?_⟩
    intro r hr k hk
    have hk' := List.find?_eq_none.mp (hserved r hr) k hk
    cases hks : (app.serviceTy k).isSome
    · rw [hks] at hk'
      exact absurd rfl hk'
    · rfl
  · rintro ⟨hrows, hkeys, hsvc, hcodes, hserved⟩
    refine ⟨fun r hr => (firstFailing_eq_none_iff _).mpr (hrows r hr), List.pairwise_map.mpr hkeys,
      fun e he => (firstFailing_eq_none_iff _).mpr (hsvc e he), List.pairwise_map.mpr hcodes,
      fun r hr => List.find?_eq_none.mpr fun k hk hbad => ?_⟩
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
  have collision : ∀ r ∈ app.rows,
      (!(NativeOp.all.map (fun op => (nativeRowOf [] op).key)).contains (rowKey r)) = true :=
    fun r hr => h.rows r hr _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have trailing : ∀ r ∈ app.rows, (!(r.shape == .value) || r.trailing.isEmpty) = true :=
    fun r hr => h.rows r hr _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  unfold Table.lawful
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  exact ⟨⟨List.pairwise_map.mpr h.rowsDistinct, collision⟩, trailing⟩

/-- The empty signature is lawful: what every source with no rows and no declarations carries. -/
theorem SigApp.lawful_empty : LawfulSig (SigApp.mk [] []) :=
  ⟨fun _ h => (nomatch h), List.Pairwise.nil, fun _ h => (nomatch h), List.Pairwise.nil,
    fun _ h => (nomatch h)⟩

/-- **C6 (proved)**: an appended signature is lawful exactly when each part's local clauses
hold, each part's pairwise clauses hold, the cross terms hold, and the whole serves every
required key: `List.forall_mem_append` and `List.pairwise_append`. -/
theorem lawful_append (app : SigApp) (rows' : RowTable) (services' : List (ServiceKey × Ty)) :
    LawfulSig (SigApp.mk (app.rows ++ rows') (app.services ++ services')) ↔
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
        ((SigApp.mk (app.rows ++ rows') (app.services ++ services')).serviceTy k).isSome = true) := by
  constructor
  · rintro ⟨hrows, hkeys, hsvc, hcodes, hserved⟩
    exact ⟨List.forall_mem_append.mp hrows, List.pairwise_append.mp hkeys,
      List.forall_mem_append.mp hsvc, List.pairwise_append.mp hcodes, hserved⟩
  · rintro ⟨hrows, hkeys, hsvc, hcodes, hserved⟩
    exact ⟨List.forall_mem_append.mpr hrows, List.pairwise_append.mpr hkeys,
      List.forall_mem_append.mpr hsvc, List.pairwise_append.mpr hcodes, hserved⟩
end Effect4.Program
