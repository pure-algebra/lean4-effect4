import Effect4.Laws.Program.Typing.Sound
import Effect4.Laws.Program.LoopSound
import Effect4.Laws.Program.TypedRun
import Effect4.Laws.Program.Typed.Admission
import Effect4.Program.Authoring.Services

/-!
# Seat TREE, R2 probe: is typing preserved when the signature grows?

Research probe (docs/research/2026-09-30-model-probe/TREE). Nothing here is imported by the tree.

* §A The term typer reads only `atomOf` and `constAtom` (congruence, by induction; not `rfl`).
* §B `SigExtends s s'`: same atoms and scope key; every operation `s` admits, `s'` admits at the
  same row; every key `s` types, `s'` types at the same carrier. Typing is preserved along it, for
  all six judgments (`hasTy_ext`, by recursion on the derivation), and so for the checker at every
  path (`check_ext`), `effTy`, and `typeOfProgram`.
* §C Instances. Rows appended to the table: an extension (`rows_append`). Services appended
  under a freshness premise: an extension (`services_append`). The tree's signature into
  `nativeSignatureWith` with fresh keys: an extension.
* §D Red controls, kept: prepending rows is not an extension, and the type of a program changes
  (`prepend_not_extends`; tested); a service entry that re-types a key the six codes already type
  is not an extension (`shadow_not_extends`; tested).
* §E The soundness theorems need no restatement: a looped (hence straight) program reads no
  host row and no service, so its type under any `nativeSignatureWith t s` is its type under
  the built-in signature (`hasTy_restrict_looped`), and `meaning_typed`, `run_typed`,
  `meaningB_typed` carry over as corollaries.
* §F The typed state's source admission is monotone in the row table (`pointTyped_rows_append`).
-/

set_option autoImplicit false

namespace Conform.Effect4.Typing.TreeProbeR2

open _root_.Effect4
open _root_.Effect4.Program
open _root_.Effect4.Machine.Env (Requirement)

/-! ## §A The term typer reads atoms only -/

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

/-! ## §B Signature extension -/

/-- `s'` extends `s`: the same atoms and scope key, every operation `s` admits admitted by `s'` at
the same row, every key `s` types typed by `s'` at the same carrier. -/
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
    _root_.Effect4.Program.termTy s' env t = _root_.Effect4.Program.termTy s env t :=
  termTy_congr h.atomOf h.constAtom env t

theorem causeTy (h : SigExtends s s') (env : TyEnv) (c : CauseTerm) :
    _root_.Effect4.Program.causeTy s' env c = _root_.Effect4.Program.causeTy s env c :=
  causeTy_congr h.atomOf h.constAtom env c

theorem bodyRequires (h : SigExtends s s') (t : EffTy) :
    _root_.Effect4.Program.bodyRequires s' t = _root_.Effect4.Program.bodyRequires s t := by
  simp only [_root_.Effect4.Program.bodyRequires, h.scopeKey]

end SigExtends

section Extend
variable {Op : Type} {s s' : Signature Op}

mutual
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
  | _, _, .succeed hv => .succeed hv
  | _, _, .effect (t := t) hb => by
    rw [← h.bodyRequires t]
    exact .effect (hasTy_ext h hb)
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

/-- **R2 at the checker**: a program the checker accepts under `s` it accepts under every
extension `s'`, at the same type and at every path. -/
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

/-! ## §C Instances -/

/-- Rows appended to the table extend the signature: an index the shorter table admits is
admitted by the longer one at the same row. -/
theorem rows_append (t t' : RowTable) : SigExtends (nativeSignature t) (nativeSignature (t ++ t')) := by
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

/-- A key the supplied list types: `find?` on the appended list finds the same entry. -/
private theorem serviceTyWith_append (s s' : List (ServiceKey × Ty))
    (fresh : ∀ entry ∈ s', nativeServiceTyWith s entry.1 = none)
    (key : ServiceKey) (ty : Ty) (hk : nativeServiceTyWith s key = some ty) :
    nativeServiceTyWith (s ++ s') key = some ty := by
  unfold nativeServiceTyWith at hk ⊢
  rw [List.find?_append]
  cases hs : s.find? (fun entry => entry.1 == key) with
  | some entry =>
    rw [hs] at hk
    simp only [Option.some_or]
    exact hk
  | none =>
    rw [hs] at hk
    simp only [Option.none_or]
    cases hs' : s'.find? (fun entry => entry.1 == key) with
    | none => exact hk
    | some entry =>
      have hmem : entry ∈ s' := List.mem_of_find?_eq_some hs'
      have hp := List.find?_some hs'
      have hkey : entry.1 = key := beq_iff_eq.mp hp
      have hfresh := fresh entry hmem
      rw [hkey] at hfresh
      unfold nativeServiceTyWith at hfresh
      rw [hs] at hfresh
      rw [hk] at hfresh
      cases hfresh

/-- Services appended under a freshness premise extend the signature: no appended key is
already typed, by the earlier entries or by the six type codes. -/
theorem services_append (t : RowTable) (s s' : List (ServiceKey × Ty))
    (fresh : ∀ entry ∈ s', nativeServiceTyWith s entry.1 = none) :
    SigExtends (nativeSignatureWith t s) (nativeSignatureWith t (s ++ s')) :=
  ⟨rfl, rfl, rfl, fun _ hd => ⟨hd, rfl⟩, serviceTyWith_append s s' fresh⟩

/-- The tree's signature into the application's: fresh keys only. -/
theorem native_into_with (t : RowTable) (s : List (ServiceKey × Ty))
    (fresh : ∀ entry ∈ s, nativeServiceTy entry.1 = none) :
    SigExtends (nativeSignature t) (nativeSignatureWith t s) :=
  services_append t [] s fresh

/-- Both at once: a longer table and fresh services. -/
theorem rows_and_services (t t' : RowTable) (s s' : List (ServiceKey × Ty))
    (fresh : ∀ entry ∈ s', nativeServiceTyWith s entry.1 = none) :
    SigExtends (nativeSignatureWith t s) (nativeSignatureWith (t ++ t') (s ++ s')) :=
  SigExtends.trans
    (show SigExtends (nativeSignatureWith t s) (nativeSignatureWith (t ++ t') s) from
      ⟨rfl, rfl, rfl, (rows_append t t').row, fun _ _ hk => hk⟩)
    (services_append (t ++ t') s s' fresh)

/-- An application's own service under a key the six codes do not type (the coordinator's demo,
code 12). Its freshness is a kernel computation. -/
def greetKey : ServiceKey := ⟨⟨12⟩, ⟨12⟩⟩

theorem greetKey_fresh : nativeServiceTy greetKey = none := by decide +kernel

theorem native_into_greet (t : RowTable) :
    SigExtends (nativeSignature t) (nativeSignatureWith t [(greetKey, .string)]) :=
  native_into_with t _ (fun entry hmem => by
    rw [List.mem_singleton] at hmem
    rw [hmem]
    exact greetKey_fresh)

/-! ## §D Red controls (kept) -/

/-- Two host rows that differ in their answer and in their printed shape. -/
def rowA : Row :=
  { name := "a", spelling := "A.a", kind := .async, request := .unit, answer := .nat,
    cite := "probe", registration := .external }
def rowB : Row := { rowA with name := "b", spelling := "B.b", shape := .value, answer := .string }

/-- `yield* A.a()`: the host row at index 0. -/
def callA : NativeEff := .perform (.external 0) (.lit .unit)

-- tested: under `[rowA]` the call answers a number; prepend `rowB` and the same program, unchanged,
-- answers a string: index 0 now names another row
#guard effTy (nativeSignature [rowA]) [] callA = some ⟨.nat, .never, Requirement.empty⟩
#guard effTy (nativeSignature ([rowB] ++ [rowA])) [] callA = some ⟨.string, .never, Requirement.empty⟩
-- tested: appending keeps it
#guard effTy (nativeSignature ([rowA] ++ [rowB])) [] callA = some ⟨.nat, .never, Requirement.empty⟩

/-- Prepending is not an extension: index 0 is admitted by both tables at different rows. -/
theorem prepend_not_extends : ¬ SigExtends (nativeSignature [rowA]) (nativeSignature ([rowB] ++ [rowA])) := by
  intro h
  have hrow := (h.row (.external 0) rfl).2
  have hshape := congrArg Row.shape hrow
  exact absurd hshape (by decide)

/-- A key with type code 4 (a number) under a free name (`firstFreeName` is 4). -/
def natKey : ServiceKey := ⟨⟨100⟩, ⟨4⟩⟩

theorem natKey_ty : nativeServiceTy natKey = some .nat := by decide +kernel

-- tested: an application entry at that key re-types `yield* key` from number to boolean
#guard effTy (nativeSignature) [] (.service natKey) =
  some ⟨.nat, .never, Requirement.single natKey⟩
#guard effTy (nativeSignatureWith [] [(natKey, .bool)]) [] (.service natKey) =
  some ⟨.bool, .never, Requirement.single natKey⟩

/-- An entry that re-types a key the six codes already type is not an extension: the freshness
premise of `services_append` is needed. -/
theorem shadow_not_extends :
    ¬ SigExtends (nativeSignature) (nativeSignatureWith [] [(natKey, .bool)]) := by
  intro h
  have hk := h.service natKey .nat natKey_ty
  have hb : (nativeSignatureWith [] [(natKey, .bool)]).serviceTy natKey = some .bool := by
    decide +kernel
  rw [hb] at hk
  cases hk

/-! ## §E The soundness theorems carry over without restatement -/

/-- What a looped program can read of a signature: atoms, and the rows of synchronous
operations (a looped program names no host row, service, layer, scope or fork). -/
structure AgreeOnLooped (s s' : Signature NativeOp) : Prop where
  atomOf : s'.atomOf = s.atomOf
  constAtom : s'.constAtom = s.constAtom
  row : ∀ op : NativeOp, op.kind = .sync → s'.dom op = s.dom op ∧ s'.rowOf op = s.rowOf op

/-- A looped program's typing under `s'` is a typing under `s`. -/
theorem hasTy_restrict_looped {s s' : Signature NativeOp} (h : AgreeOnLooped s s') :
    ∀ (e : NativeEff) {env : TyEnv} {t : EffTy}, Denote.Looped e = true →
      HasTy s' env e t → HasTy s env e t
  | .succeed _, _, _, _, .succeed ht => .succeed ((termTy_congr h.atomOf h.constAtom _ _).symm.trans ht)
  | .fail _, _, _, _, .fail ht hadm =>
    .fail ((termTy_congr h.atomOf h.constAtom _ _).symm.trans ht) hadm
  | .failCause _, _, _, _, .failCause hc =>
    .failCause ((causeTy_congr h.atomOf h.constAtom _ _).symm.trans hc)
  | .sync _, _, _, _, .sync ht => .sync ((termTy_congr h.atomOf h.constAtom _ _).symm.trans ht)
  | .suspend b, _, _, hl, .suspend hb =>
    .suspend (hasTy_restrict_looped h b (Denote.Looped.suspend hl) hb)
  | .perform op _, _, _, hl, .perform hdom hreq hrow => by
    have hk : op.kind = .sync := by
      cases op with
      | external _ => contradiction
      | sleep => contradiction
      | deferredAwait => contradiction
      | _ => rfl
    obtain ⟨hd, hr⟩ := h.row op hk
    exact .perform (hd ▸ hdom) ((termTy_congr h.atomOf h.constAtom _ _).symm.trans hreq)
      (by rw [← hr]; exact hrow)
  | .bind a b, _, _, hl, .bind hf hr =>
    .bind (hasTy_restrict_looped h a (Denote.Looped.bind hl).1 hf)
      (hasTy_restrict_looped h b (Denote.Looped.bind hl).2 hr)
  | .select _ _ a0 a1, _, _, hl, .select ht hd h0 h1 hj =>
    .select ((termTy_congr h.atomOf h.constAtom _ _).symm.trans ht) hd
      (hasTy_restrict_looped h a0 (Denote.Looped.select hl).1 h0)
      (hasTy_restrict_looped h a1 (Denote.Looped.select hl).2 h1) hj
  | .exit b, _, _, hl, .exit hb =>
    .exit (hasTy_restrict_looped h b (Denote.Looped.exit hl) hb)
  | .catchCause b hd, _, _, hl, .catchCause hb hh hj =>
    .catchCause (hasTy_restrict_looped h b (Denote.Looped.catchCause hl).1 hb)
      (hasTy_restrict_looped h hd (Denote.Looped.catchCause hl).2 hh) hj
  | .matchCause b v c, _, _, hl, .matchCause hb hv hc hj =>
    .matchCause (hasTy_restrict_looped h b (Denote.Looped.matchCause hl).1 hb)
      (hasTy_restrict_looped h v (Denote.Looped.matchCause hl).2.1 hv)
      (hasTy_restrict_looped h c (Denote.Looped.matchCause hl).2.2 hc) hj
  | .onExit b f, _, _, hl, .onExit hb hf =>
    .onExit (hasTy_restrict_looped h b (Denote.Looped.onExit hl).1 hb)
      (hasTy_restrict_looped h f (Denote.Looped.onExit hl).2 hf)
  | .iterate _ _ _ _ _ body, _, _, hl, .iterate hi ht hb hs hr hs0 hs1 =>
    .iterate ((termTy_congr h.atomOf h.constAtom _ _).symm.trans hi)
      ((termTy_congr h.atomOf h.constAtom _ _).symm.trans ht)
      (hasTy_restrict_looped h body (Denote.Looped.iterate hl) hb)
      ((termTy_congr h.atomOf h.constAtom _ _).symm.trans hs)
      ((termTy_congr h.atomOf h.constAtom _ _).symm.trans hr) hs0 hs1
  | .gen _, _, _, hl, _ | .uninterruptible _, _, _, hl, _ | .interruptible _, _, _, hl, _
  | .yieldNow _, _, _, hl, _ | .awaitFiber _ _, _, _, hl, _ | .withFiber _, _, _, hl, _
  | .scoped _, _, _, hl, _ | .acquireRelease _ _, _, _, hl, _ | .provideLayer _ _ _, _, _, hl, _
  | .service _, _, _, hl, _ | .provideService _ _ _, _, _, hl, _ | .catchIf _ _ _, _, _, hl, _ =>
    absurd hl Bool.false_ne_true

/-- Any table and any service list agree with the built-in signature on what a looped
program reads: a synchronous operation is never a host row (`NativeOp.kind`, Native.lean:125-133). -/
theorem agree_native (t : RowTable) (s : List (ServiceKey × Ty)) :
    AgreeOnLooped (nativeSignature) (nativeSignatureWith t s) := by
  refine ⟨rfl, rfl, ?_⟩
  intro op hk
  cases op with
  | external i => cases hk
  | _ => exact ⟨rfl, rfl⟩

/-- **`meaning_typed` at any table and any service list**, as a corollary. -/
theorem meaning_typed_any (t : RowTable) (s : List (ServiceKey × Ty)) (e : NativeEff) (ty : EffTy)
    (hs : Denote.Straight e = true) (hty : effTy (nativeSignatureWith t s) [] e = some ty) :
    Denote.ExitOk ty.answer ty.error (Denote.meaning e [] Machine.Stores.empty).2
      (Denote.meaning e [] Machine.Stores.empty).1 :=
  Denote.meaning_typed e ty hs
    (effTy_complete _ e [] ty (hasTy_restrict_looped (agree_native t s) e
      (Denote.Looped.of_straight e hs) (effTy_sound _ e [] ty hty)))

/-- **`run_typed` (the machine) at any table and any service list**, as a corollary. -/
theorem run_typed_any (t : RowTable) (s : List (ServiceKey × Ty)) (e : NativeEff) (ty : EffTy)
    (fuel : Nat) (hs : Denote.Straight e = true)
    (hty : effTy (nativeSignatureWith t s) [] e = some ty)
    (hd : Agreement.depth e ≤ fuel) (hfuel : 2 * Agreement.steps e + 6 ≤ fuel) :
    (Api.run e fuel).outcome = Api.Outcome.finished ∧
      ∃ ex, (Api.run e fuel).exit = some ex ∧
        Denote.ExitOk ty.answer ty.error (Api.run e fuel).stores ex :=
  Denote.run_typed e ty fuel hs
    (effTy_complete _ e [] ty (hasTy_restrict_looped (agree_native t s) e
      (Denote.Looped.of_straight e hs) (effTy_sound _ e [] ty hty))) hd hfuel

/-- **`meaningB_typed` (loops, any budget) at any table and any service list**, as a corollary. -/
theorem meaningB_typed_any (t : RowTable) (s : List (ServiceKey × Ty)) (k : Nat) (e : NativeEff)
    (ty : EffTy) (hl : Denote.Looped e = true)
    (hty : effTy (nativeSignatureWith t s) [] e = some ty) {ex : Machine.ExitV}
    {s' : Machine.Stores} (h : Denote.meaningB k e [] Machine.Stores.empty = (some ex, s')) :
    Denote.ExitOk ty.answer ty.error s' ex :=
  Denote.meaningB_typed k e ty hl
    (effTy_complete _ e [] ty (hasTy_restrict_looped (agree_native t s) e hl
      (effTy_sound _ e [] ty hty))) h

/-- A certificate at any table and service list restricts, for a looped program, to a certificate
at the built-in signature: the "both soundness statements" of row 21 and receipt C2
(`TypedProgram.run_sound`, `TypedProgram.run_soundB`, Laws/Program/TypedRun.lean:83, :112)
apply to it unchanged. -/
def restrictCertificate (t : RowTable) (s : List (ServiceKey × Ty)) {e : NativeEff}
    (tp : TypedProgram (nativeSignatureWith t s) e) (hl : Denote.Looped e = true) :
    TypedProgram (nativeSignature) e :=
  ⟨tp.ty, by
    rw [Denote.typeOfProgram_looped _ e hl]
    have hty : effTy (nativeSignatureWith t s) [] e = some tp.ty := by
      rw [← Denote.typeOfProgram_looped _ e hl]
      exact tp.typed
    exact effTy_complete _ e [] tp.ty
      (hasTy_restrict_looped (agree_native t s) e hl (effTy_sound _ e [] tp.ty hty))⟩

theorem restrictCertificate_ty (t : RowTable) (s : List (ServiceKey × Ty)) {e : NativeEff}
    (tp : TypedProgram (nativeSignatureWith t s) e) (hl : Denote.Looped e = true) :
    (restrictCertificate t s tp hl).ty = tp.ty := rfl

/-- **`TypedProgram.run_sound` at any table and service list**, as a corollary. -/
theorem run_sound_any (t : RowTable) (s : List (ServiceKey × Ty)) {e : NativeEff}
    (tp : TypedProgram (nativeSignatureWith t s) e) (hs : Denote.Straight e = true) (fuel : Nat)
    (hd : Agreement.depth e ≤ fuel) (hfuel : 2 * Agreement.steps e + 6 ≤ fuel) :
    (Api.run e fuel).outcome = Api.Outcome.finished ∧
      ∃ ex, (Api.run e fuel).exit = some ex ∧
        Denote.ExitOk tp.ty.answer tp.ty.error (Api.run e fuel).stores ex :=
  Denote.TypedProgram.run_sound (restrictCertificate t s tp (Denote.Looped.of_straight e hs))
    hs fuel hd hfuel

/-- **`TypedProgram.run_soundB` at any table and service list**, as a corollary. -/
theorem run_soundB_any (t : RowTable) (s : List (ServiceKey × Ty)) {e : NativeEff}
    (tp : TypedProgram (nativeSignatureWith t s) e) (hl : Denote.Looped e = true) {k : Nat}
    {ex : Machine.ExitV} {s' : Machine.Stores}
    (h : Denote.meaningB k e [] Machine.Stores.empty = (some ex, s')) :
    Denote.ExitOk tp.ty.answer tp.ty.error s' ex ∧
      ∃ bound, ∀ fuel, bound ≤ fuel →
        (Api.run e fuel).outcome = Api.Outcome.finished ∧
          (Api.run e fuel).exit = some ex ∧ (Api.run e fuel).stores = s' :=
  Denote.TypedProgram.run_soundB (restrictCertificate t s tp hl) hl h

/-! ## §F The typed state's source admission is monotone in the row table -/

open _root_.Effect4.Program.Typed in
/-- `PointTyped` survives appending rows to the source's table: the program, the addressed node
and the environment's values are unchanged, and the check is preserved (`check_ext`). -/
theorem pointTyped_rows_append (src : ProgramSource) (t' : RowTable) (w : World) (point : Point)
    (ty : EffTy) (h : PointTyped src w point ty) :
    PointTyped { src with table := src.table ++ t' } w point ty := by
  obtain ⟨e, env, hat, hcheck, henv⟩ := h
  exact ⟨e, env, hat, check_ext (rows_append src.table t') hcheck, henv⟩

/-- Red control for the typed state's R2 (kept): the host-row protocol entry `asyncPre … .external
op _` (Typed/Residual.lean:110-112) reads `rowOf op` without `dom op`. At an index outside the
source's table the row is the placeholder (Native.lean:118-120), whose columns are `never`, and
`never` is below every type (Ty.lean:440), so the entry holds at every certificate; under a longer
table the same index names a real row and the entry constrains. `TypedProg` is therefore not
monotone in the table unless a registered host row is known to be in the table. -/
example : True := trivial

-- tested: the placeholder's columns are below any certificate
#guard ((nativeSignature []).rowOf (.external 5)).answer.sub .nat = true
#guard ((nativeSignature []).rowOf (.external 5)).error.sub .bool = true
-- tested: with six rows, index 5 is `rowB` and constrains (string is not below nat)
#guard ((nativeSignature [rowA, rowB, rowA, rowB, rowA, rowB]).rowOf (.external 5)).answer.sub .nat
  = false

end Conform.Effect4.Typing.TreeProbeR2

#print axioms Conform.Effect4.Typing.TreeProbeR2.argTy_congr
#print axioms Conform.Effect4.Typing.TreeProbeR2.termTy_congr
#print axioms Conform.Effect4.Typing.TreeProbeR2.causeTy_congr
#print axioms Conform.Effect4.Typing.TreeProbeR2.SigExtends.trans
#print axioms Conform.Effect4.Typing.TreeProbeR2.hasTy_ext
#print axioms Conform.Effect4.Typing.TreeProbeR2.stmtsHasTy_ext
#print axioms Conform.Effect4.Typing.TreeProbeR2.layerHasTy_ext
#print axioms Conform.Effect4.Typing.TreeProbeR2.check_ext
#print axioms Conform.Effect4.Typing.TreeProbeR2.effTy_ext
#print axioms Conform.Effect4.Typing.TreeProbeR2.typeOfProgram_ext
#print axioms Conform.Effect4.Typing.TreeProbeR2.checkLayer_ext
#print axioms Conform.Effect4.Typing.TreeProbeR2.rows_append
#print axioms Conform.Effect4.Typing.TreeProbeR2.services_append
#print axioms Conform.Effect4.Typing.TreeProbeR2.native_into_with
#print axioms Conform.Effect4.Typing.TreeProbeR2.rows_and_services
#print axioms Conform.Effect4.Typing.TreeProbeR2.greetKey_fresh
#print axioms Conform.Effect4.Typing.TreeProbeR2.native_into_greet
#print axioms Conform.Effect4.Typing.TreeProbeR2.prepend_not_extends
#print axioms Conform.Effect4.Typing.TreeProbeR2.natKey_ty
#print axioms Conform.Effect4.Typing.TreeProbeR2.shadow_not_extends
#print axioms Conform.Effect4.Typing.TreeProbeR2.hasTy_restrict_looped
#print axioms Conform.Effect4.Typing.TreeProbeR2.agree_native
#print axioms Conform.Effect4.Typing.TreeProbeR2.meaning_typed_any
#print axioms Conform.Effect4.Typing.TreeProbeR2.run_typed_any
#print axioms Conform.Effect4.Typing.TreeProbeR2.meaningB_typed_any
#print axioms Conform.Effect4.Typing.TreeProbeR2.restrictCertificate
#print axioms Conform.Effect4.Typing.TreeProbeR2.run_sound_any
#print axioms Conform.Effect4.Typing.TreeProbeR2.run_soundB_any
#print axioms Conform.Effect4.Typing.TreeProbeR2.pointTyped_rows_append
