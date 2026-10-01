import Effect4.Laws.Program.Typing.Sound
import Effect4.Laws.Program.Typed.Admission

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

/-! ## `π` for services (C5) -/

namespace Typed

open Effect4.Machine

/-- A world read at a signature's service table. -/
def restrictWorld (app : SigApp) (w : World) : World := { w with serviceTy := app.serviceTy }

/-- A context's services fit at the restriction exactly when they fit at the world, when the
two tables agree on the context's keys. -/
theorem servicesFit_restrict (app : SigApp) (w : World) (services : Env.Ctx)
    (hagree : ∀ key sv, services.getV key = some sv → w.serviceTy key = app.serviceTy key) :
    ServicesFit (restrictWorld app w) services ↔ ServicesFit w services := by
  constructor
  · intro h key sv sty hget hty
    have hty' : app.serviceTy key = some sty := by
      rw [← hagree key sv hget]
      exact hty
    exact h key sv sty hget hty'
  · intro h key sv sty hget hty
    change app.serviceTy key = some sty at hty
    have hty' : w.serviceTy key = some sty := by
      rw [hagree key sv hget]
      exact hty
    exact h key sv sty hget hty'

/-- Along an extension of the application's signature, membership survives the restriction to
the smaller table: the restriction reads no carrier the world does not. -/
theorem fits_restrict {app app' : SigApp} (hext : SigExtends app.signature app'.signature)
    (w : World) (hw : w.serviceTy = app'.serviceTy) (ty : Ty) (v : Val) (h : Fits w v ty) :
    Fits (restrictWorld app w) v ty :=
  @fits_map w (restrictWorld app w) (table_refl _) (table_refl _) (table_refl _) (fun _ _ hx => hx)
    (fun key sty hk => by
      change app.serviceTy key = some sty at hk
      rw [hw]
      exact hext.service key sty hk) ty v h

end Typed

end Effect4.Program
