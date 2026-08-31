import Cas.Schema.Described
import Cas.Schema.El

/-!
# Attack witnesses against `EC1-T003E` / `workshop/s1/T003E.lean`

BREAKER file. Nothing here is proposed for the estate. Run from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s1/attack-T003E.lean
```

The target's carrier is REPLICATED verbatim below so every attack is stated
against the same objects the target quantifies over.
-/

namespace AttackT003E

open Cas.Schema

/-! ## §0 — the target's carrier, replicated verbatim -/

inductive ValueTy where
  | unit
  | bool
  | int
  | text
  | addr (tag : UInt8)
  | list (item : ValueTy)
  | nat
  | option (item : ValueTy)
  deriving DecidableEq, Repr

def Value : ValueTy → Type
  | .unit => Unit
  | .bool => Bool
  | .int => SafeInt
  | .text => String
  | .addr t => StoreRef t
  | .list e => List (Value e)
  | .nat => Nat
  | .option e => Option (Value e)

def toAst? : ValueTy → Option Ast
  | .unit => some .null
  | .bool => some .bool
  | .int => some .int
  | .text => some .str
  | .addr t => some (.ref t)
  | .list e => (toAst? e).map Ast.arr
  | .nat => none
  | .option _ => none

/-! ## §1 — `code_determines_meaning` never fires off the diagonal

The target's §8 claims to REFUSE `EC1-F86` clause 1 ("add a second value
meaning for an inhabited `Cas.Schema.El` code"). Its hypothesis pair is
`toAst? σ = some ast` and `toAst? τ = some ast`. Over this carrier that pair
FORCES `σ = τ`: the code map is injective on the supported fragment. The
statement is therefore only ever instantiated at `σ = τ`, where it is
discharged by the identity with no reference to `El`, `Described`, or the
bridge. -/

theorem toAst?_injective : ∀ (σ τ : ValueTy) {ast : Ast},
    toAst? σ = some ast → toAst? τ = some ast → σ = τ := by
  intro σ
  induction σ with
  | unit =>
      intro τ ast hσ hτ; injection hσ with hσ; subst hσ
      cases τ <;> simp_all [toAst?]
  | bool =>
      intro τ ast hσ hτ; injection hσ with hσ; subst hσ
      cases τ <;> simp_all [toAst?]
  | int =>
      intro τ ast hσ hτ; injection hσ with hσ; subst hσ
      cases τ <;> simp_all [toAst?]
  | text =>
      intro τ ast hσ hτ; injection hσ with hσ; subst hσ
      cases τ <;> simp_all [toAst?]
  | addr t =>
      intro τ ast hσ hτ; injection hσ with hσ; subst hσ
      cases τ <;> simp_all [toAst?]
  | list e ih =>
      intro τ ast hσ hτ
      have hσ' : (toAst? e).map Ast.arr = some ast := hσ
      cases he : toAst? e with
      | none => rw [he] at hσ'; exact absurd hσ' (by simp)
      | some a =>
          rw [he] at hσ'
          simp only [Option.map_some] at hσ'
          injection hσ' with hσ'
          subst hσ'
          cases τ
          case list f =>
            have hτ' : (toAst? f).map Ast.arr = some (Ast.arr a) := hτ
            cases hf : toAst? f with
            | none => rw [hf] at hτ'; exact absurd hτ' (by simp)
            | some b =>
                rw [hf] at hτ'
                simp only [Option.map_some] at hτ'
                injection hτ' with hτ'
                injection hτ' with hab
                subst hab
                exact congrArg ValueTy.list (ih f he hf)
          all_goals simp_all [toAst?]
  | nat => intro τ ast hσ _; simp [toAst?] at hσ
  | option e _ => intro τ ast hσ _; simp [toAst?] at hσ

/-- **The target's `code_determines_meaning`, reproved with the bridge, `El`
and `Described` all DELETED.** Injectivity of `toAst?` alone discharges it, so
the theorem carries no information about `Cas.Schema.El` and refuses nothing:
the second meaning `EC1-F86` clause 1 asks for is not expressible over this
carrier. -/
theorem code_determines_meaning_without_the_bridge {σ τ : ValueTy} {ast : Ast}
    (hσ : toAst? σ = some ast) (hτ : toAst? τ = some ast) :
    ∃ (f : Value σ → Value τ) (g : Value τ → Value σ),
      (∀ x, g (f x) = x) ∧ (∀ y, f (g y) = y) := by
  have hst : σ = τ := toAst?_injective σ τ hσ hτ
  subst hst
  exact ⟨id, id, fun _ => rfl, fun _ => rfl⟩

/-! ## §2 — the definitional collapse, measured

The target's own omissions record that `Value τ` and `El ast` are definitionally
equal on the supported fragment, and offer PARTIALITY of `toAst?` as the
anti-tautology evidence. Partiality is about the arms where `toAst?` answers
`none`; it says nothing about the arms where it answers `some`. Here is what
the row actually costs on those arms. -/

/-- The collapse, as a type EQUALITY, closed by `rfl` at every supported arm. -/
theorem value_eq_el : ∀ (τ : ValueTy) {ast : Ast}, toAst? τ = some ast →
    Value τ = El ast := by
  intro τ
  induction τ with
  | unit => intro ast h; injection h with h; subst h; rfl
  | bool => intro ast h; injection h with h; subst h; rfl
  | int => intro ast h; injection h with h; subst h; rfl
  | text => intro ast h; injection h with h; subst h; rfl
  | addr t => intro ast h; injection h with h; subst h; rfl
  | list e ih =>
      intro ast h
      have h' : (toAst? e).map Ast.arr = some ast := h
      cases he : toAst? e with
      | none => rw [he] at h'; exact absurd h' (by simp)
      | some a =>
          rw [he] at h'
          simp only [Option.map_some] at h'
          injection h' with h'
          subst h'
          show List (Value e) = El (Ast.arr a)
          rw [ih he]
          rfl
  | nat => intro ast h; simp [toAst?] at h
  | option e _ => intro ast h; simp [toAst?] at h

/-- Every code the map produces is well-formed, and each is `trivial`. -/
theorem toAst?_range_wf : ∀ (τ : ValueTy) {ast : Ast}, toAst? τ = some ast →
    ast.WF := by
  intro τ
  induction τ with
  | unit => intro ast h; injection h with h; subst h; trivial
  | bool => intro ast h; injection h with h; subst h; trivial
  | int => intro ast h; injection h with h; subst h; trivial
  | text => intro ast h; injection h with h; subst h; trivial
  | addr t => intro ast h; injection h with h; subst h; trivial
  | list e ih =>
      intro ast h
      have h' : (toAst? e).map Ast.arr = some ast := h
      cases he : toAst? e with
      | none => rw [he] at h'; exact absurd h' (by simp)
      | some a =>
          rw [he] at h'
          simp only [Option.map_some] at h'
          injection h' with h'
          subst h'
          exact (show Ast.WF a from ih he)
  | nat => intro ast h; simp [toAst?] at h
  | option e _ => intro ast h; simp [toAst?] at h

theorem cast_symm_cast {α β : Type} (h : α = β) (x : α) :
    cast h.symm (cast h x) = x := by subst h; rfl

theorem cast_cast_symm {α β : Type} (h : α = β) (y : β) :
    cast h (cast h.symm y) = y := by subst h; rfl

/-- A `Described` built from a TYPE EQUALITY and a `WF` proof: identity maps,
`rfl` laws, no content. -/
@[instance_reducible]
def descOfEq {α : Type} {ast : Ast} (w : ast.WF) (h : α = El ast) :
    Described α where
  code := ast
  wf := w
  toEl := fun x => cast h x
  ofEl := fun y => cast h.symm y
  ofEl_toEl := fun x => cast_symm_cast h x
  toEl_ofEl := fun y => cast_cast_symm h y

/-- **The target's `EC1-T003E`, reproved with every shipped `Described`
instance DELETED.** No `instDescribedUnit`, `instDescribedBool`,
`instDescribedSafeInt`, `instDescribedString`, `instDescribedStoreRef` or
`instDescribedList` is used: the witness is `cast` along the definitional
collapse. The row's whole content over this carrier is `value_eq_el` (how
`Value` was written, arm by arm) plus `toAst?_range_wf` (every produced code is
`trivial`ly `WF`). -/
theorem bridge_without_any_shipped_instance : ∀ (τ : ValueTy) {ast : Ast},
    toAst? τ = some ast → ∃ d : Described (Value τ), d.code = ast := by
  intro τ _ h
  exact ⟨descOfEq (toAst?_range_wf τ h) (value_eq_el τ h), rfl⟩

/-! ## §3 — the `option` arm is NOT an insufficiency

The target declares `.option` UNSUPPORTED and justifies it by citing
`Cas/Schema/Described/Instances.lean:5-7` ("unrestricted `Nat` and top-level
`Option` do not [receive instances]"). That comment says which instances are
SHIPPED. It does not say what the schema universe can REPRESENT. `Option α` is
represented exactly, by a one-optional-field struct — constructed here. -/

def optionCode (c : Ast) : Ast := .struct [("v", true, c)]

theorem optionCode_wf {c : Ast} (h : c.WF) : (optionCode c).WF := by
  refine ⟨?_, ?_⟩
  · simp
  · exact ⟨h, trivial⟩

theorem el_optionCode (c : Ast) : El (optionCode c) = (Option (El c) × Unit) := rfl

/-- **`Option α` is described exactly**, given a description of `α`. -/
@[instance_reducible]
def describedOption {α : Type} (d : Described α) : Described (Option α) where
  code := optionCode d.code
  wf := optionCode_wf d.wf
  toEl := fun o => cast (el_optionCode d.code).symm (o.map d.toEl, ())
  ofEl := fun y => ((cast (el_optionCode d.code) y).1).map d.ofEl
  ofEl_toEl := by
    intro o
    show (((cast (el_optionCode d.code)
        (cast (el_optionCode d.code).symm (o.map d.toEl, ()))).1).map d.ofEl) = o
    rw [cast_cast_symm]
    cases o with
    | none => rfl
    | some x => show some (d.ofEl (d.toEl x)) = some x; rw [d.ofEl_toEl]
  toEl_ofEl := by
    intro y
    have hp : ∀ p : Option (El d.code) × Unit,
        (((p.1.map d.ofEl).map d.toEl), ()) = p := by
      intro p
      obtain ⟨o, u⟩ := p
      cases u
      cases o with
      | none => rfl
      | some z =>
          show (some (d.toEl (d.ofEl z)), ()) = (some z, ())
          rw [d.toEl_ofEl]
    show cast (el_optionCode d.code).symm
        ((((cast (el_optionCode d.code) y).1).map d.ofEl).map d.toEl, ()) = y
    refine Eq.trans ?_ (cast_symm_cast (el_optionCode d.code) y)
    exact congrArg (cast (el_optionCode d.code).symm) (hp _)

/-- **The target's insufficiency boundary is wrong by one arm.** `.option e`
is inside the supported overlap whenever `e` is, so a `toAst?` answering `none`
there UNDERSTATES the overlap. `ALGEBRA.md:76-84` lists `option element` in
`ValueTy` proper, and `ALGEBRA.md:99-102` does NOT name `Option` among `El`'s
insufficiencies — those are declaration, enum, tuple, reference, suspension,
and the undiscriminated union. -/
theorem option_arm_is_actually_supported : ∀ (τ : ValueTy) {ast : Ast},
    toAst? τ = some ast →
    ∃ d : Described (Value (.option τ)), d.code = optionCode ast := by
  intro τ _ h
  exact ⟨describedOption (descOfEq (toAst?_range_wf τ h) (value_eq_el τ h)), rfl⟩

/-- Concretely, at a leaf. -/
theorem option_bool_is_described :
    ∃ d : Described (Value (.option .bool)), d.code = optionCode .bool :=
  option_arm_is_actually_supported .bool rfl

/-! ## §3b — the `nat` arm is not an insufficiency either

Same misreading, second arm. `List Unit` is the unary numeral, and `El .null`
is `Unit`, so `El (.arr .null)` is `List Unit` and `Nat` is represented
exactly. Both of the target's UNSUPPORTED arms are therefore inside the schema
universe's reach; the exclusion recorded at `Instances.lean:5-7` is instance
POLICY, not a boundary of `El`. -/

theorem el_natCode : El (Ast.arr .null) = List Unit := rfl

@[instance_reducible]
def describedNat : Described Nat where
  code := .arr .null
  wf := trivial
  toEl := fun n => List.replicate n ()
  ofEl := fun xs => List.length xs
  ofEl_toEl := by
    intro n
    show (List.replicate n ()).length = n
    simp
  toEl_ofEl := by
    intro xs
    show List.replicate (List.length xs) () = xs
    induction xs with
    | nil => rfl
    | cons u us ih => cases u; exact congrArg (fun t => () :: t) ih

/-- **The target's second excluded arm is also supported.** -/
theorem nat_arm_is_actually_supported :
    ∃ d : Described (Value .nat), d.code = Ast.arr .null :=
  ⟨describedNat, rfl⟩

/-- Together with `option_arm_is_actually_supported`: EVERY arm the target
excludes is representable, so the model's answer to §17 freeze condition 13
("the exact supported overlap and explicit insufficiency boundary") places both
of its boundary points on the wrong side. -/
theorem both_excluded_arms_are_representable :
    (∃ d : Described (Value .nat), d.code = Ast.arr .null) ∧
    (∃ d : Described (Value (.option .bool)), d.code = optionCode .bool) :=
  ⟨nat_arm_is_actually_supported, option_bool_is_described⟩

/-! ## §4 — the `EC1-F86` clause-1 attack the target's carrier cannot express

Clause 1 asks for a SECOND value meaning at one inhabited `El` code. §1 shows
this carrier's code map is injective, so the attack has no instance there. Run
it on a carrier that does admit it: the attack defeats the BRIDGE. So the
bridge is the refusal, and §8 of the target adds nothing to §3/§9. -/

section Clause1

inductive VTy2 where
  | u
  | b

def Val2 : VTy2 → Type
  | .u => Unit
  | .b => Bool

/-- Two distinct value types, one code. -/
def toAst2? : VTy2 → Option Ast
  | .u => some .null
  | .b => some .null

theorem toAst2?_is_not_injective :
    toAst2? .u = some .null ∧ toAst2? .b = some .null := ⟨rfl, rfl⟩

/-- **`EC1-F86` clause 1, run.** The bridge is FALSE at a code carrying a
second meaning. -/
theorem bridge_fails_at_a_subsingleton_arm {V : Type} {ast : Ast}
    (hU : El ast = Unit) (x y : V) (hxy : x ≠ y) :
    ¬ ∃ d : Described V, d.code = ast := by
  rintro ⟨d, rfl⟩
  apply hxy
  have hsub : Subsingleton (El d.code) := by rw [hU]; infer_instance
  have hEq : d.toEl x = d.toEl y := Subsingleton.elim _ _
  calc x = d.ofEl (d.toEl x) := (d.ofEl_toEl x).symm
    _ = d.ofEl (d.toEl y) := by rw [hEq]
    _ = y := d.ofEl_toEl y

theorem f86_clause1_defeats_the_bridge :
    ¬ ∀ (τ : VTy2) (ast : Ast), toAst2? τ = some ast →
        ∃ d : Described (Val2 τ), d.code = ast := fun bridge =>
  bridge_fails_at_a_subsingleton_arm (V := Val2 .b) (ast := Ast.null) rfl
    true false (fun h => Bool.noConfusion h) (bridge .b .null rfl)

end Clause1

/-! ## §5 — the target's clause-2 refusal, re-run independently -/

def phantomAst : Ast := .enum [("A", .str "a")]

theorem el_phantomAst : El phantomAst = Empty := by
  simp only [phantomAst, El]

theorem phantomAst_wf : phantomAst.WF := ⟨by simp, by simp⟩

/-- `EC1-F86` clause 2 confirmed independently. -/
theorem bridge_fails_at_an_empty_arm {V : Type} {ast : Ast}
    (hE : El ast = Empty) (x : V) : ¬ ∃ d : Described V, d.code = ast := by
  rintro ⟨d, rfl⟩
  exact Empty.elim (hE ▸ d.toEl x)

theorem f86_clause2_defeats_the_bridge :
    ¬ ∃ d : Described Nat, d.code = phantomAst :=
  bridge_fails_at_an_empty_arm el_phantomAst 0

/-! ## §6 — fairness control: the bridge is NOT only provable at a collapsed
carrier

§2 measures THIS model; it is not a claim that the row is inherently
tautological. A carrier written as a `Sum`, with genuinely non-identity
transport, still bridges. -/

abbrev SumBool : Type := Unit ⊕ Unit

def sumBoolToEl : SumBool → Bool
  | .inl _ => true
  | .inr _ => false

def sumBoolOfEl : Bool → SumBool := fun b => cond b (Sum.inl ()) (Sum.inr ())

@[instance_reducible]
def describedSumBool : Described SumBool where
  code := .bool
  wf := trivial
  toEl := sumBoolToEl
  ofEl := sumBoolOfEl
  ofEl_toEl := by intro x; cases x <;> rfl
  toEl_ofEl := by intro b; cases b <;> rfl

theorem sumBool_bridges : ∃ d : Described SumBool, d.code = .bool :=
  ⟨describedSumBool, rfl⟩

theorem sumBool_transport_is_not_the_identity :
    sumBoolToEl (Sum.inl ()) = true ∧ sumBoolToEl (Sum.inr ()) = false :=
  ⟨rfl, rfl⟩

/-! ## Receipts -/

#print axioms toAst?_injective
#print axioms code_determines_meaning_without_the_bridge
#print axioms value_eq_el
#print axioms toAst?_range_wf
#print axioms cast_symm_cast
#print axioms cast_cast_symm
#print axioms bridge_without_any_shipped_instance
#print axioms optionCode_wf
#print axioms el_optionCode
#print axioms option_arm_is_actually_supported
#print axioms option_bool_is_described
#print axioms el_natCode
#print axioms nat_arm_is_actually_supported
#print axioms both_excluded_arms_are_representable
#print axioms toAst2?_is_not_injective
#print axioms bridge_fails_at_a_subsingleton_arm
#print axioms f86_clause1_defeats_the_bridge
#print axioms el_phantomAst
#print axioms phantomAst_wf
#print axioms bridge_fails_at_an_empty_arm
#print axioms f86_clause2_defeats_the_bridge
#print axioms sumBool_transport_is_not_the_identity
#print axioms sumBool_bridges

end AttackT003E
