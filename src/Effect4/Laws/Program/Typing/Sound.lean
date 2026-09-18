import Effect4.Laws.Program.Typing.CheckSound

/-!
# Conform.Effect4.Typing.Sound — the checker's projections and the rules agree

`effTy` is the success of the fold checker at the root (`Program/Typing.lean`), and the fold
checker is sound and complete against `HasTy` at every path (`CheckSound.lean`). So every
theorem this module used to prove by two mutual inductions of six theorems each is a corollary:
soundness and completeness of `effTy` and the five siblings, the algorithm and the rules as
one relation (`effTy_eq_hasTy`), `WellTyped` as inhabitation of the judgment, determinism, and
weakening on the relation. The names are the ones the proof graph has always used.

The last section states the projection's equations at the arms other proofs unfold
(`effTy_bind`, `effTy_onExit`, `effTy_succeed`): the fold's arm, the projection pushed through
its connectives, and the children's checks at their paths read back as `effTy` through
`check_toOption_eq_effTy`.
-/

namespace Conform.Effect4.Typing

open _root_.Effect4
open _root_.Effect4.Program
open _root_.Effect4.Program.Checker
open _root_.Effect4.Laws.Auto (toOption_eq_some)
open _root_.Effect4.Machine.Env (Requirement)

variable {Op : Type}

/-! ## The projection at any path -/

/-- The success projection at any path is `effTy`. -/
theorem check_toOption_eq_effTy (sig : Signature Op) (env : TyEnv) (p : List Nat) (e : Eff Op) :
    (check sig env p e).toOption = effTy sig env e :=
  check_toOption sig env p [] e

/-- An `ok` at any path is an `effTy` answer. -/
theorem ok_effTy {sig : Signature Op} {env : TyEnv} {p : List Nat} {e : Eff Op} {t : EffTy}
    (h : check sig env p e = .ok t) : effTy sig env e = some t := by
  rw [← check_toOption_eq_effTy sig env p e, h]; rfl

/-- An `effTy` answer is an `ok` at every path. -/
theorem effTy_ok {sig : Signature Op} {env : TyEnv} {e : Eff Op} {t : EffTy}
    (h : effTy sig env e = some t) (p : List Nat) : check sig env p e = .ok t :=
  check_complete sig e env t (check_sound sig e env [] t (toOption_eq_some.mp h)) p

/-! ## Soundness and completeness, per sort -/

theorem effTy_sound (sig : Signature Op) (e : Eff Op) :
    ∀ (env : TyEnv) (t : EffTy), effTy sig env e = some t → HasTy sig env e t :=
  fun env t h => check_sound sig e env [] t (toOption_eq_some.mp h)

theorem effTy_complete (sig : Signature Op) (e : Eff Op) :
    ∀ (env : TyEnv) (t : EffTy), HasTy sig env e t → effTy sig env e = some t :=
  fun env t hd => ok_effTy (check_complete sig e env t hd [])

theorem stmtsTy_sound (sig : Signature Op) (body : Stmts Op) :
    ∀ (env : TyEnv) (inLoop : Bool) (g : GenTy),
      stmtsTy sig env inLoop body = some g → StmtsHasTy sig env inLoop body g :=
  fun env inLoop g h => checkStmts_sound sig body env inLoop [] g (toOption_eq_some.mp h)

theorem stmtsTy_complete (sig : Signature Op) (body : Stmts Op) :
    ∀ (env : TyEnv) (inLoop : Bool) (g : GenTy),
      StmtsHasTy sig env inLoop body g → stmtsTy sig env inLoop body = some g :=
  fun env inLoop g hd => by
    unfold stmtsTy; rw [checkStmts_complete sig body env inLoop g hd []]; rfl

theorem effsTy_sound (sig : Signature Op) (entrants : Effs Op) :
    ∀ (env : TyEnv) (t : EffTy), effsTy sig env entrants = some t →
      EffsHasTy sig env entrants t :=
  fun env t h => checkEffs_sound sig entrants env [] t (toOption_eq_some.mp h)

theorem effsTy_complete (sig : Signature Op) (entrants : Effs Op) :
    ∀ (env : TyEnv) (t : EffTy), EffsHasTy sig env entrants t →
      effsTy sig env entrants = some t :=
  fun env t hd => by unfold effsTy; rw [checkEffs_complete sig entrants env t hd []]; rfl

theorem actionTy_sound (sig : Signature Op) (action : ActionTerm Op) :
    ∀ (env : TyEnv) (t : EffTy), actionTy sig env action = some t →
      ActionHasTy sig env action t :=
  fun env t h => checkAction_sound sig action env [] t (toOption_eq_some.mp h)

theorem actionTy_complete (sig : Signature Op) (action : ActionTerm Op) :
    ∀ (env : TyEnv) (t : EffTy), ActionHasTy sig env action t →
      actionTy sig env action = some t :=
  fun env t hd => by unfold actionTy; rw [checkAction_complete sig action env t hd []]; rfl

theorem layerTy_sound (sig : Signature Op) (layer : LayerTerm Op) :
    ∀ (s : LayerTy), layerTy sig layer = some s → LayerHasTy sig layer s :=
  fun s h => checkLayer_sound sig layer [] s (toOption_eq_some.mp h)

theorem layerTy_complete (sig : Signature Op) (layer : LayerTerm Op) :
    ∀ (s : LayerTy), LayerHasTy sig layer s → layerTy sig layer = some s :=
  fun s hd => by unfold layerTy; rw [checkLayer_complete sig layer s hd []]; rfl

theorem layersTy_sound (sig : Signature Op) (layers : LayerTerms Op) :
    ∀ (s : LayerTy), layersTy sig layers = some s → LayersHasTy sig layers s := by
  intro s h
  unfold layersTy at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨ls, hls, hm⟩ := h
  exact checkLayers_sound sig layers [] ls s (toOption_eq_some.mp hls) hm

theorem layersTy_complete (sig : Signature Op) (layers : LayerTerms Op) :
    ∀ (s : LayerTy), LayersHasTy sig layers s → layersTy sig layers = some s := by
  intro s hd
  obtain ⟨ls, hls, hm⟩ := checkLayers_complete sig layers s hd []
  unfold layersTy
  rw [hls]
  exact hm

/-! ## The three consequences -/

/-- The algorithm and the rules define the same relation, arm for arm. -/
theorem effTy_eq_hasTy (sig : Signature Op) (env : TyEnv) (e : Eff Op) (t : EffTy) :
    effTy sig env e = some t ↔ HasTy sig env e t :=
  ⟨effTy_sound sig e env t, effTy_complete sig e env t⟩

/-- `WellTyped` — the algorithm answers at the empty environment — is inhabitation of the
judgment. -/
theorem wellTyped_iff (sig : Signature Op) (program : Eff Op) :
    WellTyped sig program ↔ ∃ t, HasTy sig [] program t := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp h
    exact ⟨t, effTy_sound sig program [] t ht⟩
  · rintro ⟨t, ht⟩
    exact Option.isSome_iff_exists.mpr ⟨t, effTy_complete sig program [] t ht⟩

/-- The judgment is deterministic: a program has at most one type. -/
theorem hasTy_unique (sig : Signature Op) (env : TyEnv) (e : Eff Op) {t₁ t₂ : EffTy}
    (h₁ : HasTy sig env e t₁) (h₂ : HasTy sig env e t₂) : t₁ = t₂ :=
  Option.some.inj ((effTy_complete sig e env t₁ h₁).symm.trans (effTy_complete sig e env t₂ h₂))

/-- The four sibling determinisms, by the same argument. -/
theorem stmtsHasTy_unique (sig : Signature Op) (env : TyEnv) (inLoop : Bool) (b : Stmts Op)
    {g₁ g₂ : GenTy} (h₁ : StmtsHasTy sig env inLoop b g₁)
    (h₂ : StmtsHasTy sig env inLoop b g₂) : g₁ = g₂ :=
  Option.some.inj
    ((stmtsTy_complete sig b env inLoop g₁ h₁).symm.trans (stmtsTy_complete sig b env inLoop g₂ h₂))

theorem effsHasTy_unique (sig : Signature Op) (env : TyEnv) (es : Effs Op) {t₁ t₂ : EffTy}
    (h₁ : EffsHasTy sig env es t₁) (h₂ : EffsHasTy sig env es t₂) : t₁ = t₂ :=
  Option.some.inj ((effsTy_complete sig es env t₁ h₁).symm.trans (effsTy_complete sig es env t₂ h₂))

theorem actionHasTy_unique (sig : Signature Op) (env : TyEnv) (a : ActionTerm Op)
    {t₁ t₂ : EffTy} (h₁ : ActionHasTy sig env a t₁) (h₂ : ActionHasTy sig env a t₂) : t₁ = t₂ :=
  Option.some.inj
    ((actionTy_complete sig a env t₁ h₁).symm.trans (actionTy_complete sig a env t₂ h₂))

theorem layerHasTy_unique (sig : Signature Op) (l : LayerTerm Op) {s₁ s₂ : LayerTy}
    (h₁ : LayerHasTy sig l s₁) (h₂ : LayerHasTy sig l s₂) : s₁ = s₂ :=
  Option.some.inj ((layerTy_complete sig l s₁ h₁).symm.trans (layerTy_complete sig l s₂ h₂))

/-- Weakening, restated on the relation: inserting an environment slot the shifted program
does not use changes no derivation (`effTy_weaken`). -/
theorem hasTy_weaken (sig : Signature Op) (pre post : TyEnv) (inserted : Ty)
    (program : Eff Op) (t : EffTy) :
    HasTy sig (pre ++ inserted :: post) (Eff.weaken pre.length program) t ↔
      HasTy sig (pre ++ post) program t := by
  rw [← effTy_eq_hasTy, ← effTy_eq_hasTy, effTy_weaken]

/-- A closed program may be placed under a new surrounding binder without changing its
derivation (`typeOf_weaken`). -/
theorem hasTy_weaken_closed (sig : Signature Op) (inserted : Ty) (program : Eff Op)
    (t : EffTy) :
    HasTy sig [inserted] (Eff.weaken 0 program) t ↔ HasTy sig [] program t :=
  hasTy_weaken sig [] [] inserted program t

/-! ## The projection's equations at the arms other proofs unfold -/

theorem effTy_succeed (sig : Signature Op) (env : TyEnv) (value : Term) :
    effTy sig env (.succeed value) = (termTy sig env value).map EffTy.pure := by
  rw [effTy]
  simp only [check, toOption_bind, toOption_pure, toOption_term?]
  cases termTy sig env value <;> rfl

theorem effTy_bind (sig : Signature Op) (env : TyEnv) (first rest : Eff Op) :
    effTy sig env (.bind first rest) =
      (do
        let f ← effTy sig env first
        let r ← effTy sig (env ++ [f.answer]) rest
        some ⟨r.answer, f.error.join r.error, f.requires.union r.requires⟩) := by
  rw [effTy]
  simp only [check, toOption_bind, toOption_pure, check_toOption_eq_effTy, Option.bind_eq_bind]

theorem effTy_onExit (sig : Signature Op) (env : TyEnv) (body finalizer : Eff Op) :
    effTy sig env (.onExit body finalizer) =
      (do
        let b ← effTy sig env body
        let f ← effTy sig (env ++ [.exitOf b.answer b.error]) finalizer
        some ⟨b.answer, b.error.join f.error, b.requires.union f.requires⟩) := by
  rw [effTy]
  simp only [check, toOption_bind, toOption_pure, check_toOption_eq_effTy, Option.bind_eq_bind]

theorem effTy_scoped (sig : Signature Op) (env : TyEnv) (body : Eff Op) :
    effTy sig env (.scoped body) =
      (effTy sig env body).map (fun t => { t with requires := bodyRequires sig t }) := by
  rw [effTy]
  simp only [check, toOption_bind, toOption_pure, check_toOption_eq_effTy]
  cases effTy sig env body <;> rfl

end Conform.Effect4.Typing
