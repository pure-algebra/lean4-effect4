import Cas.Schema.Described
import Cas.Schema.El

/-!
# `EC1-T003E` — forward scout probe

Row under scout (`../../PROOF-DAG.md:192`):

> `EC1-T003E` | PENDING THEOREM |
> `value_el_bridge : toAst? τ = some ast -> Value τ ≃ Cas.Schema.El ast`
> | supported overlap only; empty/unsupported `El` arms excluded explicitly

Written 2026-08-31 against the working tree, Lean `leanprover/lean4:v4.33.1`.
Stage: `lean-formalization-strategy` **Pass A** (`.claude/skills/lean/workflows/`)
— no contract exists for this row: `ValueTy`, `Value` and `toAst?` are all
`PROPOSED TERM` (`PROOF-DAG.md:74-75`) and
`formal/effect-core-v1/EffectCore/Foundation/Value.lean` is an empty stub.
Pass B is unreachable: there is no declaration to elaborate.

Outside every lake target, exactly like `../exhibits.lean` and
`../counterexamples/Nondeterminism.lean`. It adds nothing to `Cas`, moves no
byte, and promotes no name.

Run it from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s1/scout-T003E.lean
```

## What this file settles

1. **The anchor resolves and it is not `El` — it is `Described`.**
   `Cas/Schema/Described/Core.lean:16` already carries the *equivalence*
   `α ≃ El code`, unbundled into four fields, without Mathlib. §P0.
2. **The premise the row's dependency column names is not in its signature,
   and it is load-bearing.** §P3 exhibits carriers satisfying the stated
   hypothesis where the conclusion is false.
3. **The estate's shape enforces that premise structurally.** §P1/§P2: a
   `Described` instance at an empty `El` arm forces its carrier uninhabited,
   so `EC1-F86`'s attack ("silently inhabit one of `El`'s empty arms") is
   refused by the class, not by a side condition someone must remember.
4. **`≃` cannot be spelled here.** `lake-manifest.json` lists zero packages;
   there is no Mathlib and no `Equiv` in the corpus (`Cas.Core.Canonicalize.Equiv`
   is a relation on VALUES, not a type equivalence). §P0 shows the spelling
   that does exist.
5. **The row is a tautology under the obvious definition.** §P5: if `Value` is
   defined as `El ∘ toAst?` on the supported fragment, the bridge is `id` and
   proves nothing — the same defect `PROOF-DAG.md:203` records for the two
   deleted `T003` forms.

No `sorry`, no `axiom`, no `native_decide`, no `#eval` carrying a claim.
`#print axioms` on every theorem, at the foot.
-/

namespace ScoutT003E

open Cas.Schema

/-! ## §P0 — the anchor, verbatim

The estate's `Described` class IS the bridge `EC1-T003E` proposes to prove,
already spelled for a toolchain with no `Equiv`:

```lean
class Described (α : Type u) where
  code : Ast
  wf : code.WF
  toEl : α → El code
  ofEl : El code → α
  ofEl_toEl : ∀ x, ofEl (toEl x) = x
  toEl_ofEl : ∀ x, toEl (ofEl x) = x
```

Four fields are exactly the four components of a type equivalence. The row's
`toAst?` is the `code` field; the row's partiality (`= some ast`) is instance
existence; the row's missing `Ast.WF` premise is the `wf` field. -/

section Anchor

/-- The bridge in the forward direction is a field, not a theorem. -/
example {α : Type} [d : Described α] : α → El d.code := d.toEl

/-- And in the backward direction. -/
example {α : Type} [d : Described α] : El d.code → α := d.ofEl

/-- Both round trips, which is what `≃` means. -/
example {α : Type} [d : Described α] :
    (∀ x, d.ofEl (d.toEl x) = x) ∧ (∀ y, d.toEl (d.ofEl y) = y) :=
  ⟨d.ofEl_toEl, d.toEl_ofEl⟩

/-- The code carried by the instance is well-formed — a premise the row's
schematic signature does not carry at all. -/
example {α : Type} [d : Described α] : d.code.WF := d.wf

end Anchor

/-! ## §P1 — the excluded-arm premise, enforced structurally

The row's dependency column says "empty/unsupported `El` arms excluded
explicitly". Under `Described` the exclusion is not a side condition: an
instance whose code denotes `Empty` forces its own carrier uninhabited. -/

section EmptyArms

/-- **The general fact.** If a described type's code denotes `Empty`, the
type has no inhabitants. Nothing here is specific to which arm. -/
theorem described_empty_code_is_uninhabited {α : Type}
    (d : Described α) (h : El d.code = Empty) (x : α) : False :=
  Empty.elim (h ▸ d.toEl x)

/-- Contrapositive, in the form the packet wants: an inhabited carrier can
only be described by a code with an inhabited denotation. -/
theorem inhabited_forces_inhabited_denotation {α : Type}
    (d : Described α) (x : α) : El d.code ≠ Empty := fun h =>
  described_empty_code_is_uninhabited d h x

end EmptyArms

/-! ## §P2 — the six empty arms, one theorem each

`Cas/Schema/El.lean:178` gives `Empty` for `.decl`, `.enum`, `.tuple`,
`.reference`, `.susp`, and for `.union` when `discriminatedB` is false. Each
is closed here through §P1, the undiscriminated union through the estate's own
`El_union_undiscriminated`. -/

section Arms

theorem no_inhabited_decl {α : Type} {gid : DeclarationId.General}
    {p : DeclPayload} {ps : List Ast} (d : Described α)
    (hc : d.code = .decl gid p ps) (x : α) : False :=
  described_empty_code_is_uninhabited d (by rw [hc]; simp only [El]) x

theorem no_inhabited_enum {α : Type} {ms : List (String × EnumValue)}
    (d : Described α) (hc : d.code = .enum ms) (x : α) : False :=
  described_empty_code_is_uninhabited d (by rw [hc]; simp only [El]) x

theorem no_inhabited_tuple {α : Type} {e : Bool × Ast} {es : List (Bool × Ast)}
    {r : Option Ast} (d : Described α)
    (hc : d.code = .tuple e es r) (x : α) : False :=
  described_empty_code_is_uninhabited d (by rw [hc]; simp only [El]) x

theorem no_inhabited_reference {α : Type} {n : String} (d : Described α)
    (hc : d.code = .reference n) (x : α) : False :=
  described_empty_code_is_uninhabited d (by rw [hc]; simp only [El]) x

theorem no_inhabited_susp {α : Type} {a : Ast} (d : Described α)
    (hc : d.code = .susp a) (x : α) : False :=
  described_empty_code_is_uninhabited d (by rw [hc]; simp only [El]) x

/-- The undiscriminated union, through the estate's shipped theorem rather
than a fresh reduction. -/
theorem no_inhabited_undiscriminated_union {α : Type} {ms : List Ast}
    {m : UnionMode} (d : Described α)
    (hc : d.code = .union ms m) (hd : discriminatedB ms = false) (x : α) :
    False :=
  described_empty_code_is_uninhabited d
    (by rw [hc]; exact El_union_undiscriminated (m := m) hd) x

end Arms

/-! ## §P3 — the row AS WRITTEN is not provable: the premise is load-bearing

`EC1-T003E`'s signature quantifies over `τ` with only `toAst? τ = some ast`.
The dependency column's exclusion is prose, not a hypothesis. This section
exhibits `ValueTy`/`Value`/`toAst?` that satisfy every constraint the
SIGNATURE states, and refutes the conclusion.

The stand-ins below are scout scaffolding. They are not proposed for the
estate and they mint nothing: `ScoutValue` is a local two-point family used
only to show the quantifier is too wide. -/

section PremiseIsNecessary

set_option linter.unusedSimpArgs false

inductive ScoutTy where
  | unit
  | phantom
  deriving DecidableEq

/-- A `WF` enum code. `El` sends it to `Empty` (obligation `enumEl`,
`Cas/Schema/El.lean`), so it is a supported *code* with no supported
*denotation* — precisely the gap the row's prose excludes and its signature
does not. -/
def phantomAst : Ast := .enum [("A", .int ⟨1, by decide⟩)]

/-- `El` sends it to `Empty`, by the definition at `Cas/Schema/El.lean:178`. -/
theorem el_phantomAst : El phantomAst = Empty := by
  simp only [phantomAst, El]

theorem phantomAst_wf : phantomAst.WF := by
  refine ⟨?_, ?_⟩
  · simp [phantomAst]
  · simp [phantomAst]

/-- Total, as the row's `toAst?` is allowed to be. -/
def scoutToAst? : ScoutTy → Option Ast
  | .unit => some .null
  | .phantom => some phantomAst

/-- Inhabited at both codes — nothing in the row forbids it. -/
def ScoutValue : ScoutTy → Type
  | .unit => Unit
  | .phantom => Unit

/-- **The refutation.** At `τ = .phantom` the hypothesis `toAst? τ = some ast`
holds with `ast = phantomAst`, and there is no function `ScoutValue τ → El ast`
at all — so a fortiori no equivalence. -/
theorem bridge_fails_without_the_premise
    (_h : scoutToAst? .phantom = some phantomAst)
    (f : ScoutValue .phantom → El phantomAst) : False :=
  Empty.elim (el_phantomAst ▸ f ())

/-- Stated as the packet should read it: the row's own hypothesis does not
imply the exclusion its dependency column claims. -/
theorem hypothesis_does_not_exclude_empty_arms :
    ∃ (τ : ScoutTy) (ast : Ast),
      scoutToAst? τ = some ast ∧ ast.WF ∧ El ast = Empty ∧ Nonempty (ScoutValue τ) :=
  ⟨.phantom, phantomAst, rfl, phantomAst_wf, el_phantomAst, ⟨()⟩⟩

/-- Same fact in the shape the failure takes: at `.phantom` the equivalence
would have to send an inhabitant to a member of `Empty`. -/
theorem no_bridge_at_phantom : (ScoutValue .phantom → El phantomAst) → False :=
  fun f => Empty.elim (el_phantomAst ▸ f ())

end PremiseIsNecessary

/-! ## §P4 — the bridge alone pins no code

`El` is not injective. Two distinct codes denote the same type, so an
equivalence `Value τ ≃ El ast` carries no information about WHICH code `τ`
maps to. Any downstream row that reads identity off this bridge is reading
something that is not there. -/

section NotInjective

theorem el_null_eq_el_lit (v : LitVal) : El .null = El (.lit v) := by
  simp only [El]

theorem el_not_injective :
    ∃ a b : Ast, a ≠ b ∧ El a = El b :=
  ⟨.null, .lit (.str ""), by intro h; exact Ast.noConfusion h,
    el_null_eq_el_lit (.str "")⟩

end NotInjective

/-! ## §P5 — the row is a tautology under the obvious definition

`PROOF-DAG.md:203` records that two `T003` forms were deleted as tautologies.
`T003E` has the same hazard in a different key: if `Value` is defined THROUGH
`El` on the supported fragment — the natural reading of §16's "restrict/bridge
the overlapping structural fragment to `Cas.Schema.El`" — the bridge is the
identity and the row proves nothing about the Core's value universe.

Below, `El a` is `Described` by `a` itself for every well-formed `a`: the four
equivalence fields are `id` and `rfl`. -/

section Tautology

/-- The denotation of a code is described by that code, by identity. If
`Value τ := El (toAst? τ)` then `value_el_bridge` is this instance. -/
@[instance_reducible]
def elIsDescribedByItsOwnCode (a : Ast) (ha : a.WF) : Described (El a) where
  code := a
  wf := ha
  toEl := id
  ofEl := id
  ofEl_toEl _ := rfl
  toEl_ofEl _ := rfl

/-- The bridge, discharged by `rfl`, for any code at all. -/
theorem bridge_is_rfl_when_Value_is_El (a : Ast) (x : El a) :
    (fun y : El a => y) ((fun y : El a => y) x) = x := rfl

end Tautology

/-! ## §P6 — the statement this row should actually carry

Spelled over abstract carriers, because the concrete ones do not exist:
`ValueTy`, `Value`, `toAst?` are `PROPOSED TERM` and §17 conditions **1** and
**13** — the `ValueTy` universe, and the exact supported/insufficient boundary
against `El` — are both **OPEN** (`PROOF-DAG.md:540,556`). Condition 13 IS this
row. The definitions below elaborate at every arity-compatible choice, so the
SHAPE is settled even though the carriers are not. -/

section RecommendedStatement

variable (VTy : Type) (Val : VTy → Type) (toAst? : VTy → Option Ast)
  (Supported : VTy → Prop)

/-- **`EC1-T003E`, restated.** Three changes from the DAG signature, each
forced above:

1. `≃` becomes an instance of the estate's shipped `Cas.Schema.Described`.
   There is no `Equiv` in this toolchain (zero Lake packages, no Mathlib) and
   §16's Values row forbids duplicating an inhabited `El` meaning — `Described`
   already IS `α ≃ El code` with the `Ast.WF` side condition as a field.
2. `Supported τ` is promoted from the dependency column into the signature.
   §P3 shows the row's own hypothesis does not imply it.
3. The code is pinned (`d.code = ast`) because `El` is not injective (§P4), so
   an unpinned equivalence would leave `toAst?` unconstrained. -/
def ValueElBridge : Prop :=
  ∀ (τ : VTy) (ast : Ast), Supported τ → toAst? τ = some ast →
    ∃ d : Described (Val τ), d.code = ast

/-- **Companion 1 — non-vacuity.** Without it the bridge is discharged by
sending the whole supported fragment to empty arms. -/
def SupportedIsInhabited : Prop :=
  ∀ (τ : VTy) (ast : Ast), Supported τ → toAst? τ = some ast → El ast ≠ Empty

/-- **Companion 2 — non-triviality.** If `toAst?` is total then `Val` can be
defined as `El ∘ toAst?` and the bridge is `rfl` (§P5). `EC1-A02`'s own text
says the Effect-specific cause/exit/fiber/resource handles have no `Ast`
image; that is this obligation, stated. -/
def ToAstIsPartial : Prop := ∃ τ : VTy, toAst? τ = none

end RecommendedStatement

/-- **`Supported` need not be stipulated for inhabited value types.** Given
any bridge instance and one inhabitant, the exclusion follows — so the premise
can be discharged from the carrier rather than carried as a separate predicate.
This is `EC1-F86` refused by the shape. -/
theorem supported_is_forced_by_inhabitation {V : Type} (ast : Ast)
    (d : Described V) (hc : d.code = ast) (x : V) : El ast ≠ Empty := by
  subst hc
  exact inhabited_forces_inhabited_denotation d x

/-! ## Receipts

Axiom note, declared as the house rules require. Every theorem that mentions
`Cas.Schema.Described` or `Cas.Schema.Ast.WF` reports
`[propext, Classical.choice, Quot.sound]`. That ceiling is the ESTATE's, not
this file's: `Cas.Schema.Ast.WF` is compiled by well-founded recursion, and
the shipped `Cas.Schema.Described.decode_encode` reports the identical triple.
Isolated: `theorem wf_null : (Ast.null).WF := by simp [Ast.WF]` alone reports
`[propext, Classical.choice, Quot.sound]`, while every statement about `El`
that does not touch `WF` reports `[propext]`. No `sorryAx` anywhere. -/

#print axioms described_empty_code_is_uninhabited
#print axioms inhabited_forces_inhabited_denotation
#print axioms no_inhabited_decl
#print axioms no_inhabited_enum
#print axioms no_inhabited_tuple
#print axioms no_inhabited_reference
#print axioms no_inhabited_susp
#print axioms no_inhabited_undiscriminated_union
#print axioms el_phantomAst
#print axioms phantomAst_wf
#print axioms bridge_fails_without_the_premise
#print axioms hypothesis_does_not_exclude_empty_arms
#print axioms no_bridge_at_phantom
#print axioms el_null_eq_el_lit
#print axioms el_not_injective
#print axioms bridge_is_rfl_when_Value_is_El
#print axioms supported_is_forced_by_inhabitation

end ScoutT003E
