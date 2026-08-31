import Cas.Schema.Described
import Cas.Schema.El

/-!
# `EC1-T003E` — `value_el_bridge`, proved at a minimal supported-overlap carrier

Row under implementation (`../../PROOF-DAG.md:192`):

> `EC1-T003E` | PENDING THEOREM |
> `value_el_bridge : toAst? τ = some ast -> Value τ ≃ Cas.Schema.El ast`
> | supported overlap only; empty/unsupported `El` arms excluded explicitly

Written 2026-08-31 against the working tree, Lean `leanprover/lean4:v4.33.1`.
Skill stage: `lean-model-invariants`
(`.claude/skills/lean/workflows/lean-model-invariants/SKILL.md`) — this row is
about representation: which native carrier a first-order type code denotes, and
where the boundary between the Core's value universe and `Cas.Schema.El` runs.
The stage's mechanism table selects **canonical form + bridge to an existing
denotation**, and its boundary rule ("keep an explicit projection/erasure from
checked values to raw or semantic values") is what the `Described` witness is.

Outside every lake target, exactly like `../exhibits.lean`,
`../counterexamples/Nondeterminism.lean` and the nine sibling scouts. It adds
nothing to `Cas`, moves no byte, and promotes no name.

Run it from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s1/T003E.lean
```

## What is proved, and what it is NOT

`EC1-D001 ValueTy`, `EC1-D002 Value` and `toAst?` DO NOT EXIST:
`formal/effect-core-v1/EffectCore/Foundation/Value.lean` is an 11-line
namespace stub, and §17 freeze conditions **1** (the precise `ValueTy`
universe) and **13** (the exact supported overlap and insufficiency boundary
against `El`) are both **OPEN** (`PROOF-DAG.md:540,556`). Condition 13 IS this
row. §4 below therefore declares a MINIMAL carrier of its own — eight arms, no
more than the row needs — and proves the bridge there. That is a MODEL of the
row, not the row at the frozen carrier. A green check here is assurance about
the propositions stated in this file and nothing else; it does not close
`EC1-T003E`.

Two of the results are carrier-FREE (§3) and do transfer verbatim to whatever
`ValueTy` the packet freezes.

| § | Result | Bears on |
| --- | --- | --- |
| 3 | the bridge FORCES the empty-arm exclusion, at any carrier | `EC1-F86` clause 2 |
| 5 | `value_el_bridge` — the row, premise-free beyond `= some ast` | `EC1-T003E` |
| 6 | `value_el_equiv` — the same, with `≃` spelled out in full | `EC1-T003E` |
| 7 | the excluded arms are inhabited; the code is pinned; the codec follows | §17 cond. 13 |
| 8 | `code_determines_meaning` — no second meaning for one code | `EC1-F86` clause 1 |
| 9 | the row is FALSE one arm away; the pin is necessary | non-vacuity |

## Three departures from the schematic signature, each forced

1. **`≃` becomes `Cas.Schema.Described`.** There is no `Equiv` in this
   toolchain — `library/cas/lake-manifest.json` lists zero packages, so no
   Mathlib — and `Cas.Core.Canonicalize.Equiv` is a relation on VALUES at a
   fixed type, not a type equivalence. `Cas/Schema/Described/Core.lean:16`
   already carries exactly the four components of an equivalence
   (`toEl`, `ofEl`, `ofEl_toEl`, `toEl_ofEl`) plus the `Ast.WF` side condition
   the schematic row omits. §16's Values row forbids duplicating an inhabited
   `El` meaning; minting a second equivalence type would be that. §6 unbundles
   the witness back into the four components so the reader can see the `≃` the
   row asked for, with nothing hidden inside a class.
2. **The code is pinned (`d.code = ast`).** `El` is not injective (§9), so an
   unpinned equivalence leaves `ast` underdetermined and any downstream row
   reading identity off the bridge reads something that is not there.
3. **NO `Supported` premise is added.** The row's dependency column says
   "empty/unsupported `El` arms excluded explicitly", and the scout for this
   row recommended promoting that into the signature as a hypothesis. It is
   not needed, and carrying it would be weaker: the exclusion belongs in the
   DEFINITION of `toAst?`, which answers `none` off the supported fragment.
   §9's `f86_empty_arm_is_refused` proves that choice is load-bearing — change
   `toAst?` on one arm and the row is false — so the exclusion is discharged
   rather than assumed. This is the cheapest constructive way to close §17
   condition 13.

## Axiom ceiling, declared

Every statement mentioning `Cas.Schema.Described` or `Cas.Schema.Ast.WF`
reports `[propext, Classical.choice, Quot.sound]`. That ceiling is the
ESTATE's, not this file's, and it is not a modelling choice made here:
`Cas.Schema.Ast.WF` is compiled by well-founded recursion and
`#print axioms Cas.Schema.Ast.WF` alone reports the same triple, as does the
shipped `Cas.Schema.Described.decode_encode`. Statements about `El` that never
touch `WF` report `[propext]`. No `sorry`, no `axiom`, no `sorryAx`, no
`native_decide`, no `#eval` carrying a claim. `#print axioms` on every theorem,
at the foot.
-/

namespace EC1T003E

open Cas.Schema

/-! ## §3 — carrier-free: the bridge forces the exclusion

These three transfer to the real `ValueTy` unchanged. They say that the row is
not merely COMPATIBLE with "empty/unsupported `El` arms excluded explicitly" —
it IMPLIES it. `EC1-F86`'s second clause ("silently inhabit one of `El`'s empty
arms") is refused by the shape of `Described`, not by a side condition someone
has to remember to check. -/

section CarrierFree

/-- A described type whose code denotes `Empty` has no inhabitants: `toEl`
would have to produce a member of `Empty`. -/
theorem described_empty_code_is_uninhabited {α : Type} (d : Described α)
    (h : El d.code = Empty) (x : α) : False :=
  Empty.elim (h ▸ d.toEl x)

/-- No bridge exists at an empty arm for an inhabited carrier. This is the
refutation `EC1-F86` clause 2 runs into. -/
theorem bridge_fails_at_an_empty_arm {V : Type} {ast : Ast}
    (hEmpty : El ast = Empty) (x : V) : ¬ ∃ d : Described V, d.code = ast := by
  rintro ⟨d, rfl⟩
  exact described_empty_code_is_uninhabited d hEmpty x

/-- **Carrier-free.** For ANY value universe, value family and code map, the
bridge implies that every code in the map's range with an inhabited carrier has
an inhabited denotation. The dependency column's exclusion is a CONSEQUENCE of
the row, not an extra hypothesis on it. -/
theorem bridge_implies_arms_excluded {VTy : Type} {Val : VTy → Type}
    {code? : VTy → Option Ast}
    (bridge : ∀ (τ : VTy) (ast : Ast), code? τ = some ast →
      ∃ d : Described (Val τ), d.code = ast)
    {τ : VTy} {ast : Ast} (h : code? τ = some ast) (x : Val τ) :
    El ast ≠ Empty := fun hEmpty =>
  bridge_fails_at_an_empty_arm hEmpty x (bridge τ ast h)

end CarrierFree

/-! ## §4 — the carrier

Minimal and first-order (`EFFECTS-BACKEND.md` R14a: effect-free work stays
OUTSIDE `Prog` as plain definitions on first-order data). Six SUPPORTED arms,
one per shipped `Described` instance
(`Cas/Schema/Described/Instances.lean:13,21,29,37,45,53`), and two UNSUPPORTED
arms.

The two unsupported arms are not invented for convenience. Both are named in
`ALGEBRA.md:76-84`'s own `ValueTy` sketch (`nat`, `option element`), and both
are refused by the estate's own recorded insufficiency —
`Cas/Schema/Described/Instances.lean:5-7`: "Only carriers represented exactly
by the current schema universe receive instances. In particular, unrestricted
`Nat` and top-level `Option` do not." `ALGEBRA.md:99-102` says the same about
the effect-specific cause/exit/fiber/resource handles; those are modelled here
by these two arms rather than by minting handle structures, so this file mints
no carrier the estate does not already discuss.

`Value` is defined by a recursion that mentions neither `El` nor `toAst?`. That
is what keeps §5 a theorem: `Value τ := El (toAst? τ)` would make the bridge
`rfl` and prove nothing about the Core's value universe — the tautology hazard
`PROOF-DAG.md:206-208` records for the two deleted `EC1-T003` forms. It is also
not even definable here, because `toAst?` is genuinely partial (§7). -/

section Carrier

/-- Scratch `EC1-D001` stand-in. NOT proposed for the estate. -/
inductive ValueTy where
  | unit
  | bool
  | int
  | text
  | addr (tag : UInt8)
  | list (item : ValueTy)
  /-- Unsupported: unbounded `Nat` has no exact code
      (`Cas/Schema/Described/Instances.lean:5-7`). -/
  | nat
  /-- Unsupported: top-level `Option` has no code (same note). -/
  | option (item : ValueTy)
  deriving DecidableEq, Repr

/-- Scratch `EC1-D002` stand-in: the NATIVE Lean carrier of each code. Defined
independently of `El` and of `toAst?`. -/
def Value : ValueTy → Type
  | .unit => Unit
  | .bool => Bool
  | .int => SafeInt
  | .text => String
  | .addr t => StoreRef t
  | .list e => List (Value e)
  | .nat => Nat
  | .option e => Option (Value e)

/-- The partial code map. The exclusion the row's dependency column states in
prose lives HERE, as `none`, and propagates through `.list`. -/
def toAst? : ValueTy → Option Ast
  | .unit => some .null
  | .bool => some .bool
  | .int => some .int
  | .text => some .str
  | .addr t => some (.ref t)
  | .list e => (toAst? e).map Ast.arr
  | .nat => none
  | .option _ => none

end Carrier

/-! ## §5 — `EC1-T003E`

The hypothesis is the row's, unchanged and alone. No `Supported` premise, no
`Ast.WF` premise (it is a field of the witness), no duplicate-free premise. -/

/-- **`EC1-T003E`.** Every value type with a code has a bridge to that code's
denotation, and the bridge carries THAT code.

`Cas.Schema.Described (Value τ)` is `Value τ ≃ El d.code` unbundled into its
four components plus `d.code.WF`; `d.code = ast` pins the code, which §9 shows
is not free. -/
theorem value_el_bridge : ∀ (τ : ValueTy) {ast : Ast}, toAst? τ = some ast →
    ∃ d : Described (Value τ), d.code = ast := by
  intro τ
  induction τ with
  | unit =>
      intro ast h
      show ∃ d : Described Unit, d.code = ast
      injection h with h; exact ⟨inferInstance, h⟩
  | bool =>
      intro ast h
      show ∃ d : Described Bool, d.code = ast
      injection h with h; exact ⟨inferInstance, h⟩
  | int =>
      intro ast h
      show ∃ d : Described SafeInt, d.code = ast
      injection h with h; exact ⟨inferInstance, h⟩
  | text =>
      intro ast h
      show ∃ d : Described String, d.code = ast
      injection h with h; exact ⟨inferInstance, h⟩
  | addr t =>
      intro ast h
      show ∃ d : Described (StoreRef t), d.code = ast
      injection h with h; exact ⟨inferInstance, h⟩
  | list e ih =>
      intro ast h
      show ∃ d : Described (List (Value e)), d.code = ast
      have h' : (toAst? e).map Ast.arr = some ast := h
      cases he : toAst? e with
      | none => rw [he] at h'; exact absurd h' (by simp)
      | some a =>
          rw [he] at h'
          simp only [Option.map_some] at h'
          injection h' with h'
          obtain ⟨d, hd⟩ := ih he
          refine ⟨@instDescribedList _ d, ?_⟩
          show Ast.arr d.code = ast
          rw [hd]; exact h'
  | nat => intro ast h; simp [toAst?] at h
  | option e _ => intro ast h; simp [toAst?] at h

/-! ## §6 — the same statement with `≃` written out

Nothing is hidden inside a class here: this is the four components of a type
equivalence, at the code the row names, plus the well-formedness side condition
the schematic signature does not carry. It is what `Value τ ≃ Cas.Schema.El
ast` means in a toolchain with no `Equiv`. -/

/-- **`EC1-T003E`, unbundled.** -/
theorem value_el_equiv {τ : ValueTy} {ast : Ast} (h : toAst? τ = some ast) :
    ∃ (f : Value τ → El ast) (g : El ast → Value τ),
      (∀ x, g (f x) = x) ∧ (∀ y, f (g y) = y) ∧ ast.WF := by
  obtain ⟨d, hd⟩ := value_el_bridge τ h
  subst hd
  exact ⟨d.toEl, d.ofEl, d.ofEl_toEl, d.toEl_ofEl, d.wf⟩

/-! ## §7 — the companions the row needs to mean something

`EC1-T003E` alone is satisfied by a `toAst?` that answers `none` everywhere.
These three are what stop that reading, and they are the content of §17
condition 13. -/

/-- `toAst?` is genuinely PARTIAL. This is `ALGEBRA.md:99-102`'s statement that
the Effect-specific handles have no `Ast` image, discharged. It is also why
`Value := El ∘ toAst?` is not definable, which is what keeps §5 a theorem
rather than `rfl`. -/
theorem toAst?_is_partial : ∃ τ : ValueTy, toAst? τ = none := ⟨.nat, rfl⟩

/-- Partiality PROPAGATES: a list of an unsupported element is unsupported. The
exclusion is structural, not a lookup table with holes patched at the leaves. -/
theorem toAst?_partial_propagates : toAst? (.list .nat) = none := rfl

/-- The supported fragment is INHABITED. Without this the bridge is discharged
by mapping the whole supported fragment onto empty arms. -/
theorem value_inhabited : ∀ (τ : ValueTy) {ast : Ast}, toAst? τ = some ast →
    Nonempty (Value τ) := by
  intro τ
  induction τ with
  | unit => intro _ _; exact ⟨()⟩
  | bool => intro _ _; exact ⟨true⟩
  | int => intro _ _; exact ⟨⟨0, Nat.zero_le _⟩⟩
  | text => intro _ _; exact ⟨""⟩
  | addr t => intro _ _; exact ⟨⟨⟨List.replicate 32 0, by simp⟩⟩⟩
  | list e _ => intro _ _; exact ⟨([] : List (Value e))⟩
  | nat => intro ast h; simp [toAst?] at h
  | option e _ => intro ast h; simp [toAst?] at h

/-- **The excluded arms, excluded — proved rather than stipulated.** No code in
`toAst?`'s range denotes `Empty`. This is the dependency column's
"empty/unsupported `El` arms excluded explicitly", discharged as a theorem
through the carrier-free §3 lemma. -/
theorem supported_denotation_nonempty {τ : ValueTy} {ast : Ast}
    (h : toAst? τ = some ast) : El ast ≠ Empty := by
  obtain ⟨x⟩ := value_inhabited τ h
  exact bridge_implies_arms_excluded (fun σ _ hσ => value_el_bridge σ hσ) h x

/-- What the bridge BUYS, and evidence it is not idle: the generic schema codec
and its round trip land at `Value τ` for free, through the shipped
`Cas.Schema.Described.decode_encode`. -/
theorem value_codec_roundtrip {τ : ValueTy} {ast : Ast} (h : toAst? τ = some ast) :
    ∃ d : Described (Value τ), d.code = ast ∧
      ∀ x : Value τ, @Described.decode _ d (@Described.encode _ d x) = some x := by
  obtain ⟨d, hd⟩ := value_el_bridge τ h
  exact ⟨d, hd, fun x => @Described.decode_encode _ d x⟩

/-! ## §8 — `EC1-F86` clause 1: no second meaning for one code

`CONTRACT-PACKET.md:746` puts two attacks on this row. Clause 2 (inhabit an
empty arm) is refused in §3 and §9. Clause 1 is "add a second value meaning for
an inhabited `Cas.Schema.El` code" — refused here: two supported value types
sharing a code have equivalent carriers, so `El` really is the meaning owner
and the Core's universe adds no rival meaning over the overlap. -/

/-- **`EC1-F86` clause 1, refused.** -/
theorem code_determines_meaning {σ τ : ValueTy} {ast : Ast}
    (hσ : toAst? σ = some ast) (hτ : toAst? τ = some ast) :
    ∃ (f : Value σ → Value τ) (g : Value τ → Value σ),
      (∀ x, g (f x) = x) ∧ (∀ y, f (g y) = y) := by
  obtain ⟨fσ, gσ, hgfσ, hfgσ, -⟩ := value_el_equiv hσ
  obtain ⟨fτ, gτ, hgfτ, hfgτ, -⟩ := value_el_equiv hτ
  refine ⟨fun x => gτ (fσ x), fun y => gσ (fτ y), fun x => ?_, fun y => ?_⟩
  · show gσ (fτ (gτ (fσ x))) = x
    rw [hfgτ, hgfσ]
  · show gτ (fσ (gσ (fτ y))) = y
    rw [hfgσ, hgfτ]

/-! ## §9 — non-vacuity: the row is false one arm away, and the pin is not free

§5 states the row with NO `Supported` premise. That is only honest if the
exclusion built into `toAst?` is doing work. It is: move one arm and the row
becomes false. -/

section Adversaries

/-- A well-formed enum code. `El` sends it to `Empty` (named obligation
`enumEl`, `Cas/Schema/El.lean`), so it is a supported CODE with no supported
DENOTATION — exactly the gap the row's prose excludes. -/
def phantomAst : Ast := .enum [("A", .str "a")]

theorem el_phantomAst : El phantomAst = Empty := by
  simp only [phantomAst, El]

theorem phantomAst_wf : phantomAst.WF := by
  refine ⟨?_, ?_⟩
  · simp
  · simp

/-- `EC1-F86` clause 2, as a mutation of THIS file's `toAst?`: one arm moved,
from `none` to a well-formed code whose denotation is empty. -/
def toAstF86 : ValueTy → Option Ast
  | .nat => some phantomAst
  | τ => toAst? τ

theorem toAstF86_moves_one_arm :
    toAstF86 .nat = some phantomAst ∧ toAst? .nat = none :=
  ⟨rfl, rfl⟩

/-- **The row is FALSE for `toAstF86`.** So `EC1-T003E` as stated in §5 is not
a tautology, the definitional exclusion in `toAst?` is load-bearing, and the
`Supported` premise the scout recommended is unnecessary rather than merely
omitted: the work it would do is already done. -/
theorem f86_empty_arm_is_refused :
    ¬ ∀ (τ : ValueTy) (ast : Ast), toAstF86 τ = some ast →
        ∃ d : Described (Value τ), d.code = ast := fun bridge =>
  bridge_fails_at_an_empty_arm (V := Value .nat) el_phantomAst (0 : Nat)
    (bridge .nat phantomAst rfl)

/-- `El` is not injective: two distinct codes denote the same type. -/
theorem el_not_injective : ∃ a b : Ast, a ≠ b ∧ El a = El b :=
  ⟨.null, .lit (.str ""), fun h => Ast.noConfusion h, by simp only [El]⟩

/-- A bridge for `Value .unit` at the WRONG code. Nothing is broken here — this
is a legitimate `Described Unit`; it is why the equivalence alone cannot say
which code a value type has. -/
@[instance_reducible]
def unitAtALiteralCode : Described (Value .unit) where
  code := .lit (.str "x")
  wf := by trivial
  toEl := id
  ofEl := id
  ofEl_toEl _ := rfl
  toEl_ofEl _ := rfl

/-- **The pin is necessary.** Drop `d.code = ast` from §5 and the conclusion is
satisfied by a witness at a code `toAst?` never produces, so nothing downstream
may read identity off an unpinned bridge. -/
theorem code_pin_is_necessary :
    ∃ (τ : ValueTy) (ast : Ast) (d : Described (Value τ)),
      toAst? τ = some ast ∧ d.code ≠ ast :=
  ⟨.unit, .null, unitAtALiteralCode, rfl, fun h => Ast.noConfusion h⟩

end Adversaries

/-! ## §10 — positive control

A nested supported type, so §5 is known to fire on something with real
structure rather than only on leaves. -/

theorem nested_list_is_supported :
    toAst? (.list (.list .int)) = some (.arr (.arr .int)) := rfl

theorem nested_list_bridges :
    ∃ d : Described (Value (.list (.list .int))), d.code = .arr (.arr .int) :=
  value_el_bridge _ nested_list_is_supported

/-! ## Receipts

`Classical.choice` appears exactly where `Cas.Schema.Ast.WF` does; see the
header. It is the estate's ceiling, reached through `Described.wf`, not a
modelling choice made in this file. -/

#print axioms described_empty_code_is_uninhabited
#print axioms bridge_fails_at_an_empty_arm
#print axioms bridge_implies_arms_excluded
#print axioms value_el_bridge
#print axioms value_el_equiv
#print axioms toAst?_is_partial
#print axioms toAst?_partial_propagates
#print axioms value_inhabited
#print axioms supported_denotation_nonempty
#print axioms value_codec_roundtrip
#print axioms code_determines_meaning
#print axioms el_phantomAst
#print axioms phantomAst_wf
#print axioms toAstF86_moves_one_arm
#print axioms f86_empty_arm_is_refused
#print axioms el_not_injective
#print axioms code_pin_is_necessary
#print axioms nested_list_is_supported
#print axioms nested_list_bridges

end EC1T003E
