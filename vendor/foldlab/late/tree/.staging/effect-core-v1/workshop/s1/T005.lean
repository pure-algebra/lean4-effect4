import Cas.Lang.Defun

/-!
# `EC1-T005` — `serialized_fields_first_order`

Slice `EC1-S1`. Skill stage: `lean-model-invariants` (the row is about the
representation of a raw carrier and the boundary that validates it, so the
stage's `wire/raw -> parse -> validate -> checked core` discipline and its
`Except Diagnostic` boundary rule are the ones applied below).

Run from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s1/T005.lean
```

This file is OUTSIDE every lake target. It modifies nothing under `library/`
and nothing under `formal/effect-core-v1/`. Its intended home,
`formal/effect-core-v1/EffectCore/Syntax/Raw.lean`, is an eleven-line reserved
stub and is deliberately not written to; a later integration step moves proofs
into modules.

## The DAG row

```text
EC1-T005 | serialized_fields_first_order : SerializableField raw field -> not FunctionVal field | D2
```
(`PROOF-DAG.md:197`.)

`RawProgram` (`EC1-D020`), `SerializableField` and `FunctionVal` exist NOWHERE
in the tree. `grep -rn 'SerializableField\|FunctionVal'` over the repo returns
exactly one non-worktree hit: `PROOF-DAG.md:197`, the row itself. So the row's
two principal predicates have never been written, and this file must supply
them before it can say anything. It supplies them twice, because the row admits
two readings and they do not agree.

## What is proved here

| § | Statement | Result |
|---|---|---|
| 1 | the DAG row, verbatim, at the estate's real serializable carrier | TRUE, and VACUOUS |
| 1 | `row_survives_any_premise` — the row holds with `SerializableField` replaced by ANY relation | TRUE; strictly implies the row |
| 2 | the first-order content that is NOT vacuous: the serialization walk round-trips and is injective | TRUE |
| 3 | `EC1-K12`'s first-order-closure clause is FALSE on raw content | TRUE (this is `EC1-F08`'s input) |
| 3 | the repaired row: a first-error checker, sound and complete, in the estate's `checkRefs_ok_iff` shape | TRUE |
| 4 | the dichotomy: T005 has no non-vacuous reading at `D2` alone | TRUE |

### §1 — the tautology horn

`FunctionVal` cannot honestly be written as anything but the empty predicate
over a first-order field universe: no arm holds a function, so no arm can
satisfy it. The row is then discharged by case split with BOTH the premise and
the program `raw` unused. `row_survives_any_premise` makes that mechanical: the
row is provable with `SerializableField` replaced by `fun _ _ => True`, by
`fun _ _ => False`, or by anything else. That is precisely the criterion
`PROOF-DAG.md:206-209` applied when it deleted `exists! v, evalPure e env = v`
and the same-input function-equality forms. By the DAG's own rule this row is
deletable.

The sharp consequence: the row's own falsifier cannot attack it. `EC1-F08`
(`CONTRACT-PACKET.md:737`) is "put an unregistered host callback in raw
content", and §3 shows that mutation is invisible to `¬ FunctionVal field`.

### §2 — where the first-order content actually lives

`ALGEBRA.md:224` says `EC1-A11 RawProgram` "contains only serializable
first-order data". The mechanized content of that sentence is not a safety
predicate; it is that the serialization walk LOSES NOTHING — `parseFields` is a
left inverse of `fieldsOf`, so the line is recoverable from its first-order
fields, and the walk is therefore injective. A carrier with a host-function
field has no such pair: it must either put the function in a field, breaking
first-orderness, or drop it, breaking injectivity. This is the estate's own
`decodeProg_encodeProg` shape (`Cas/Lang/Defun.lean:998`) one level down.

No second serializer is minted (`EC1-XT018`, and `PROOF-DAG.md` §16's CAS row
prohibits "minting another serializer"). `fieldsOf`/`parseFields` is a WALK over
the estate's own `PLine` into a scratch field universe; it produces no bytes and
no wire format. §2.3 instantiates the estate's shipped byte codec instead of
writing one.

### §3 — the contentful horn, and why it needs `D3`

`ALGEBRA.md:242-244` says host-function payloads "are deliberately
representable" in the raw carrier. That sits beside `ALGEBRA.md:224` only under
`EC1-K12` (`CONTRACT-PACKET.md:348-356`): a stored continuation is "a `CodeId`
plus explicit captures", so raw content never HOLDS a function — it can only
NAME one that no `codeTable` row defines. `EC1-F08`'s input is exactly that
naming failure, and it is slot resolution, not a property of a field's value.

Stated premise-free, that property is FALSE on raw programs
(`firstOrderClosed_is_false_on_raw`) — by the packet's own design, since
otherwise `EC1-F08` would have no input. So the row needs a checker premise,
i.e. `D3` (`EC1-D021 ProgramWF` / `EC1-D024 check`), not the `D2` the DAG lists.

The checker is FIRST-ERROR, per ruling **R16** and `EC1-CE031`: it reports the
first condemning slot, not a set. The admissible pair is first-error soundness
plus existential rejection completeness, and both are proved. §3.5 exhibits a
two-violation program on which an accumulating specification is FALSE, so the
weaker completeness is not a convenience.

## Scratch carriers

`RawField`, `CodeId`, `RawCodeDef`, `Slot` and `RawProg` are THROWAWAY. They
decide the SHAPE of the row's statement and are not proposals for `EC1-D020`'s
field universe or table set. Nothing here competes with an estate type: the
serializable carrier is the estate's own `PIn`/`PLine`/`PProg`
(`Cas/Lang/Defun.lean:167,180,187`), code-definition bodies are `PProg`
(`EC1-XT018`, `EC1-F76`), and captures are `PIn`.

## Checks OMITTED

* No claim is made about `RawProgram`'s eventual field universe or table set;
  `EC1-D020` does not exist and §17 condition 1 is OPEN.
* No claim about the TypeScript source hoover's ability to detect a host
  callback BEFORE decoding. If `EC1-D020` is built so that §3's witness is
  unrepresentable, `EC1-F08` stops being a Lean-side falsifier and degrades to a
  decoder/hoover obligation in the `EC1-H*` family. That is a design question
  this file cannot settle.
* `EC1-F08` is not exercised in executable form; §3.4 is its Lean-side analogue.
* §2 does NOT prove that `Prog` admits no `DecidableEq`. The elaboration
  observation is that `example : DecidableEq (Prog CasSig Cas.Addr32) :=
  inferInstance` fails to synthesize; failure to synthesize is not a proof of
  non-existence and is used in no theorem below.
* No interaction with `EC1-T006`'s `normalizeRaw` was probed. If `check` runs
  after `normalizeRaw`, the FIRST condemning slot is first in NORMALIZED order,
  not source order — a live `T005`/`T006`/`T015` interaction that is flagged and
  not formalized.
* Every one of the 33 theorems below reports `#print axioms`. Ceiling is
  `[propext, Quot.sound]`; eleven depend on no axioms at all. No `sorry`, no
  `axiom`, no `native_decide`, no `#eval` carrying a claim, and no
  `Classical.choice` anywhere — which is itself part of the finding, since the
  decidability results in §2 and §3 are what a function-valued field would cost.
-/

namespace EffectCoreV1.T005

open Cas.Lang
open Cas (Bytes Addr32)

/-! ## §1 — the DAG row at the estate's real carrier, and its vacuity -/

/-- THROWAWAY. What one step of a serialization walk over the estate's real
`PLine` (`Cas/Lang/Defun.lean:180`) yields. Every arm is a first-order estate
type; scratch only, not a proposal for `EC1-D020`'s field universe. -/
inductive RawField where
  | u8 (b : UInt8)
  | payload (bs : Bytes)
  | operand (i : PIn)
  deriving DecidableEq

/-- The reference walk, spelled recursively rather than through `flatMap` so
that §2's parser is a plain structural inverse. -/
def refFields : List (UInt8 × PIn) → List RawField
  | [] => []
  | (b, i) :: rest => .u8 b :: .operand i :: refFields rest

/-- The serialization walk over one estate code point. -/
def fieldsOf : PLine → List RawField
  | .put v t payload refs => .u8 v :: .u8 t :: .payload payload :: refFields refs
  | .load src => [.operand src]

/-- `SerializableField raw field`, spelled at the estate's carrier: the field
is one the walk over `raw` yields. -/
def SerializableField (raw : PLine) (field : RawField) : Prop :=
  field ∈ fieldsOf raw

/-- `FunctionVal`, in the only way it can honestly be written over a
first-order field universe: no constructor holds a function, so the predicate
is empty on every arm. Writing it any other way would be writing a DIFFERENT
predicate — which is §3. -/
def FunctionVal : RawField → Prop
  | .u8 _ => False
  | .payload _ => False
  | .operand _ => False

/-- The conclusion of the DAG row holds of every field, with no program and no
premise anywhere in sight. This is the whole of the row's content. -/
theorem functionVal_is_empty (field : RawField) : ¬ FunctionVal field := by
  cases field <;> exact not_false

/-- **`EC1-T005`, the DAG row, proved verbatim.** Note the premise binder is
`_h`: it is never eliminated. -/
theorem serialized_fields_first_order (raw : PLine) (field : RawField)
    (_h : SerializableField raw field) : ¬ FunctionVal field :=
  functionVal_is_empty field

/-- **THE VACUITY WITNESS.** The row is provable with `SerializableField`
replaced by ANY relation whatsoever. The premise is never used and the program
`raw` is never inspected, so the row's conclusion carries no information about
either. This is the criterion `PROOF-DAG.md:206-209` used to delete two rows. -/
theorem row_survives_any_premise (P : PLine → RawField → Prop) :
    ∀ raw field, P raw field → ¬ FunctionVal field :=
  fun _ field _ => functionVal_is_empty field

/-- And it is STRICTLY STRONGER than the row: instantiating at
`SerializableField` gives the row back. -/
theorem row_survives_any_premise_implies_the_row
    (h : ∀ (P : PLine → RawField → Prop) (raw : PLine) (field : RawField),
        P raw field → ¬ FunctionVal field) :
    ∀ (raw : PLine) (field : RawField),
      SerializableField raw field → ¬ FunctionVal field :=
  h SerializableField

/-- Two concrete instantiations, so the point is not abstract: the row holds
with its premise replaced by `True` … -/
theorem row_holds_with_premise_True :
    ∀ (raw : PLine) (field : RawField),
      (fun (_ : PLine) (_ : RawField) => True) raw field → ¬ FunctionVal field :=
  row_survives_any_premise _

/-- … and with its premise replaced by `False`. -/
theorem row_holds_with_premise_False :
    ∀ (raw : PLine) (field : RawField),
      (fun (_ : PLine) (_ : RawField) => False) raw field → ¬ FunctionVal field :=
  row_survives_any_premise _

/-- The row is LOGICALLY EQUIVALENT to its `True` instance — i.e. to a statement
that mentions neither the serialization walk nor the raw program. -/
theorem row_is_the_True_instance :
    (∀ (raw : PLine) (field : RawField),
        SerializableField raw field → ¬ FunctionVal field)
      ↔ (∀ (raw : PLine) (field : RawField),
            (fun (_ : PLine) (_ : RawField) => True) raw field →
              ¬ FunctionVal field) :=
  ⟨fun _ => row_holds_with_premise_True,
   fun _ raw field h => serialized_fields_first_order raw field h⟩

/-! ## §2 — the first-order content that is not vacuous

`EC1-K12`'s sentence "the serialization walk finds no function-valued field"
has a mechanized content, and it is not a safety predicate. It is that the walk
is INVERTIBLE. -/

/-- The parser for the reference segment: pairs of `(u8, operand)`. -/
def parseRefs : List RawField → Option (List (UInt8 × PIn))
  | [] => some []
  | .u8 b :: .operand i :: rest => (parseRefs rest).map (fun rs => (b, i) :: rs)
  | _ => none

/-- The parser for one code point. This is the `parse` leg of the
`wire/raw -> parse -> validate -> checked core` boundary; §3 is the `validate`
leg. -/
def parseFields : List RawField → Option PLine
  | .u8 v :: .u8 t :: .payload p :: rest =>
      (parseRefs rest).map (fun refs => PLine.put v t p refs)
  | [.operand src] => some (.load src)
  | _ => none

theorem parseRefs_refFields (refs : List (UInt8 × PIn)) :
    parseRefs (refFields refs) = some refs := by
  induction refs with
  | nil => rfl
  | cons r rest ih =>
    obtain ⟨b, i⟩ := r
    simp [refFields, parseRefs, ih]

/-- **THE ROUND TRIP.** The serialization walk loses nothing: every code point
is recoverable from the first-order fields it yields. A carrier with a
host-function field admits no such pair — it must either put the function in a
field, breaking first-orderness, or drop it, breaking this equation.

Estate model: `Cas/Lang/Defun.lean:998 decodeProg_encodeProg`. -/
theorem parseFields_fieldsOf (l : PLine) : parseFields (fieldsOf l) = some l := by
  cases l with
  | put v t p refs => simp [fieldsOf, parseFields, parseRefs_refFields]
  | load src => rfl

/-- **INJECTIVITY**, the corollary that makes the walk a faithful presentation
of the code point rather than a lossy summary. -/
theorem fieldsOf_injective {l l' : PLine} (h : fieldsOf l = fieldsOf l') :
    l = l' := by
  have hl : parseFields (fieldsOf l) = some l := parseFields_fieldsOf l
  rw [h, parseFields_fieldsOf l'] at hl
  exact (Option.some.inj hl).symm

/-- Equality of serialized fields is DECIDED, not assumed. The `dite` resolves
the DERIVED `DecidableEq RawField`; the axiom receipt is the evidence that no
choice principle was needed. This is the mechanized residue of "first-order"
that survives at the level of a single field. -/
theorem rawField_equality_is_decided (f g : RawField) : f = g ∨ f ≠ g :=
  if h : f = g then Or.inl h else Or.inr h

/-- Same at the estate's own code-point carrier. -/
theorem pline_equality_is_decided (l l' : PLine) : l = l' ∨ l ≠ l' :=
  if h : l = l' then Or.inl h else Or.inr h

/-! ### §2.3 — the estate's byte serializer, REUSED and not re-minted

`EC1-XT018` permits no second CAS serialization and `PROOF-DAG.md` §16's CAS
row prohibits "minting another serializer". The walk above produces no bytes.
The byte-level round trip is the estate's, instantiated here rather than
rewritten. -/

/-- A concrete 32-byte address, for the witnesses below. -/
def zeroAddr : Addr32 := ⟨List.replicate 32 0, by simp⟩

/-- The estate's shipped byte codec round-trips a first-order code point. Both
premises of `decodeProg_encodeProg` are discharged at a singleton table: `hwf`
because `PIn.WF (.lit _)` is `True`, `hsep` because both quantified lines are
the same line. -/
theorem estate_serializer_round_trips (H : Bytes → Addr32) :
    decodeProg (encodeProg H [PLine.load (.lit zeroAddr)])
      = some [PLine.load (.lit zeroAddr)] := by
  refine decodeProg_encodeProg H _ ?_ ?_
  · intro l hl
    simp only [List.mem_singleton] at hl
    subst hl
    trivial
  · intro l hl l' hl' _
    simp only [List.mem_singleton] at hl hl'
    subst hl; subst hl'
    rfl

/-! ## §3 — the contentful horn: `EC1-K12`'s first-order closure

`CONTRACT-PACKET.md:352` — "Every stored continuation, handler body, finalizer,
child body, error arm, and race arm is a `CodeId` plus explicit captures."

So a raw program never HOLDS a function. It can only NAME one that no
`codeTable` row defines, and that is the mutation `EC1-F08` performs. -/

abbrev CodeId := Nat

/-- THROWAWAY: a registered first-order code definition. The body is the
estate's `PProg` (`EC1-XT018`, `EC1-F76`: no second straight-line carrier). -/
structure RawCodeDef where
  id : CodeId
  body : PProg
  deriving DecidableEq

/-- THROWAWAY: `EC1-K12`'s continuation slot — a `CodeId` plus explicit
captures, never a function. Captures are the estate's `PIn`. -/
structure Slot where
  code : CodeId
  captures : List PIn
  deriving DecidableEq

/-- THROWAWAY: the two `EC1-A11` tables the property actually relates
(`ALGEBRA.md:224-235` `codeTable` and the slots held across `blockTable`). -/
structure RawProg where
  codeTable : List RawCodeDef
  slots : List Slot
  deriving DecidableEq

/-- Decidable equality of the WHOLE raw carrier — tables, slots and captures —
derived, not assumed. This, and not `¬ FunctionVal field`, is what a
host-function field would destroy. The receipt shows no `Classical.choice`. -/
theorem rawProg_equality_is_decided (r r' : RawProg) : r = r' ∨ r ≠ r' :=
  if h : r = r' then Or.inl h else Or.inr h

/-- The property `EC1-F08` installs: a stored continuation naming no registered
code definition. -/
def HostCallback (r : RawProg) (s : Slot) : Prop :=
  ∀ d ∈ r.codeTable, d.id ≠ s.code

/-- `EC1-K12`'s first-order-closure clause, as a property of a raw program. -/
def FirstOrderClosed (r : RawProg) : Prop :=
  ∀ s ∈ r.slots, ∃ d ∈ r.codeTable, d.id = s.code

/-! ### §3.1 — `EC1-F08`'s input is representable, so the premise-free property
is FALSE on raw content -/

/-- `EC1-F08`: one slot, empty code table — the unregistered host callback. -/
def f08 : RawProg := { codeTable := [], slots := [⟨7, []⟩] }

theorem f08_carries_an_unregistered_callback :
    ∃ s ∈ f08.slots, HostCallback f08 s := by
  refine ⟨⟨7, []⟩, by simp [f08], ?_⟩
  intro d hd
  simp [f08] at hd

/-- **THE FALSIFICATION.** Stated premise-free, `EC1-K12`'s closure clause is
false on raw content — by the packet's own design (`ALGEBRA.md:242-244`),
because otherwise `EC1-F08` would have no input to feed. Consequently the
contentful reading of `EC1-T005` is NOT a `D2` theorem. -/
theorem firstOrderClosed_is_false_on_raw : ¬ FirstOrderClosed f08 := by
  intro h
  obtain ⟨d, hd, _⟩ := h ⟨7, []⟩ (by simp [f08])
  simp [f08] at hd

/-! ### §3.2 — the checker

Boundary discipline (`lean-model-invariants`): failure at a raw/wire boundary
must explain itself, so the door returns `Except`. The payload is the offending
slot; no diagnostic family is minted, since `EC1-D025` does not exist and a real
`Diagnostic` will wrap this. The door is FIRST-ERROR, per ruling **R16**. -/

/-- One slot's clause, decided. -/
def resolves (r : RawProg) (s : Slot) : Bool :=
  r.codeTable.any (fun d => d.id == s.code)

/-- The Bool gate: whether every stored continuation resolves. -/
def checkFirstOrderB (r : RawProg) : Bool :=
  r.slots.all (fun s => resolves r s)

/-- The diagnostic door: scan in order, name the FIRST unresolved slot. Shape
copied from `Cas/Core/Admission.lean:49 checkRefs`. -/
def checkFirstOrder (r : RawProg) : Except Slot Unit :=
  match r.slots.find? (fun s => !resolves r s) with
  | some s => .error s
  | none => .ok ()

theorem resolves_iff (r : RawProg) (s : Slot) :
    resolves r s = true ↔ ∃ d ∈ r.codeTable, d.id = s.code := by
  simp [resolves]

/-- The Bool gate decides exactly the Prop clause. Estate model:
`Cas/Schema/Declarations.lean:183 payloadWf_iff`. -/
theorem checkFirstOrderB_iff (r : RawProg) :
    checkFirstOrderB r = true ↔ FirstOrderClosed r := by
  simp [checkFirstOrderB, FirstOrderClosed, resolves]

/-- First-order closure is therefore DECIDABLE — the validation cost the
`lean-model-invariants` inventory asks to be recorded. -/
instance instDecidableFirstOrderClosed (r : RawProg) :
    Decidable (FirstOrderClosed r) :=
  decidable_of_iff _ (checkFirstOrderB_iff r)

/-! ### §3.3 — soundness and completeness of the diagnostic door

Both halves in one `iff`, the estate's `Cas/Core/Admission.lean:60
checkRefs_ok_iff` shape. This is `PROOF-DAG.md:516`'s sanctioned Checker route —
"structural recursion plus decidable per-clause reflection" — and not its
prohibited shortcut, "using successful examples as completeness". -/

/-- The door agrees with the gate. -/
theorem checkFirstOrder_ok_iff_gate (r : RawProg) :
    checkFirstOrder r = .ok () ↔ checkFirstOrderB r = true := by
  unfold checkFirstOrder checkFirstOrderB
  cases h : r.slots.find? (fun s => !resolves r s) with
  | some s =>
    have hmem : s ∈ r.slots := List.mem_of_find?_eq_some h
    have hbad := List.find?_some h
    simp only [Bool.not_eq_true'] at hbad
    constructor
    · intro hc; exact absurd hc (by simp)
    · intro hall
      exact absurd (List.all_eq_true.mp hall s hmem) (by simp [hbad])
  | none =>
    have hnone := List.find?_eq_none.mp h
    simp only [List.all_eq_true, true_iff]
    intro s hs
    have := hnone s hs
    simp only [Bool.not_eq_true', Bool.not_eq_false] at this
    exact this

/-- **THE REPAIRED ROW.** `checkFirstOrder` accepts exactly the raw programs
whose stored continuations all resolve. Soundness is the forward direction,
completeness the backward one. -/
theorem checkFirstOrder_ok_iff (r : RawProg) :
    checkFirstOrder r = .ok () ↔ FirstOrderClosed r :=
  (checkFirstOrder_ok_iff_gate r).trans (checkFirstOrderB_iff r)

/-- **FIRST-ERROR SOUNDNESS** (R16, part 1): what the door reports is a real
violation — the named slot is in the program and names no registered code.
This is strictly more than the `iff` gives; the `iff` says nothing about WHICH
slot comes back. Estate model: `Cas/Core/Admission.lean:41
AdmissionError.Condemns`. -/
theorem checkFirstOrder_error_condemns {r : RawProg} {s : Slot}
    (h : checkFirstOrder r = .error s) : s ∈ r.slots ∧ HostCallback r s := by
  unfold checkFirstOrder at h
  cases hf : r.slots.find? (fun s => !resolves r s) with
  | none => rw [hf] at h; exact absurd h (by simp)
  | some s' =>
    rw [hf] at h
    have hs : s' = s := by
      simpa using h
    subst hs
    refine ⟨List.mem_of_find?_eq_some hf, ?_⟩
    have hbad := List.find?_some hf
    simp only [Bool.not_eq_true'] at hbad
    intro d hd hid
    have : resolves r s' = true := (resolves_iff r s').mpr ⟨d, hd, hid⟩
    simp [this] at hbad

/-- **EXISTENTIAL REJECTION COMPLETENESS** (R16, part 2): a violating program is
rejected — though not necessarily with every clause. -/
theorem checkFirstOrder_rejects {r : RawProg} (h : ¬ FirstOrderClosed r) :
    ∃ s, checkFirstOrder r = .error s := by
  unfold checkFirstOrder
  cases hf : r.slots.find? (fun s => !resolves r s) with
  | some s => exact ⟨s, rfl⟩
  | none =>
    exact absurd ((checkFirstOrder_ok_iff r).mp (by unfold checkFirstOrder; rw [hf])) h

/-! ### §3.4 — `EC1-F08` observed, and a positive control -/

/-- `EC1-F08`'s red control: the non-first-order-field diagnostic, at the exact
offending slot. -/
theorem f08_diagnostic : checkFirstOrder f08 = .error ⟨7, []⟩ := rfl

theorem f08_gate_false : checkFirstOrderB f08 = false := rfl

/-- Positive control. The code definition's body is the estate's `PProg`; the
capture is the estate's `PIn`. -/
def ok1 : RawProg :=
  { codeTable := [⟨7, [PLine.load (.lit zeroAddr)]⟩]
    slots := [⟨7, [PIn.lit zeroAddr]⟩] }

theorem ok1_is_closed : FirstOrderClosed ok1 := by
  intro s hs
  simp only [ok1, List.mem_singleton] at hs
  subst hs
  exact ⟨⟨7, [PLine.load (.lit zeroAddr)]⟩, by simp [ok1], rfl⟩

theorem ok1_accepted : checkFirstOrder ok1 = .ok () := rfl

theorem ok1_gate_true : checkFirstOrderB ok1 = true := rfl

/-! ### §3.5 — why completeness is EXISTENTIAL and not per-clause

`EC1-CE031` (`VERIFIED-KERNEL`) defeats "a fail-fast checker returns a
diagnostic for every condemning clause" at the estate's reference checker.
Transplanted here with an independent witness. -/

/-- Two unregistered slots, one empty code table. -/
def twoBad : RawProg := { codeTable := [], slots := [⟨7, []⟩, ⟨9, []⟩] }

theorem twoBad_has_two_violations :
    HostCallback twoBad ⟨7, []⟩ ∧ HostCallback twoBad ⟨9, []⟩ := by
  constructor <;> (intro d hd; simp [twoBad] at hd)

theorem twoBad_second_slot_is_a_slot : (⟨9, []⟩ : Slot) ∈ twoBad.slots := by
  simp [twoBad]

/-- The door reports only the first. -/
theorem checker_reports_only_the_first :
    checkFirstOrder twoBad = .error ⟨7, []⟩ := rfl

/-- **`EC1-CE031` at this carrier.** A specification demanding a diagnostic per
condemning clause is FALSE of this checker. R16's ruling is therefore honored
rather than cited: what §3.3 proves is first-error soundness plus existential
rejection completeness, and nothing stronger is available without a separate
accumulating census pass. -/
theorem accumulating_diagnostic_is_false :
    ¬ ∀ (r : RawProg) (s : Slot), s ∈ r.slots → HostCallback r s →
        checkFirstOrder r = .error s := by
  intro h
  have hbad := h twoBad ⟨9, []⟩ twoBad_second_slot_is_a_slot
    twoBad_has_two_violations.2
  rw [checker_reports_only_the_first] at hbad
  simp at hbad

/-! ## §4 — the dichotomy

There is no reading on which `EC1-T005` is a non-vacuous `D2` theorem. -/

/-- The contentful clause is not a theorem about arbitrary raw programs. -/
theorem first_order_closure_is_not_a_d2_theorem :
    ¬ ∀ r : RawProg, FirstOrderClosed r :=
  fun h => firstOrderClosed_is_false_on_raw (h f08)

/-- **THE DICHOTOMY, in one statement.** Left: under the literal reading the row
survives every premise, so it says nothing (`PROOF-DAG.md:206-209`'s deleted
family). Right: under the reading that gives `EC1-F08` an input, the
premise-free property is false. `EC1-T005` must therefore either be struck and
recorded as a clause of `EC1-D021 ProgramWF` discharged by `T010`/`T011`/`T012`,
or be restated with a `D3` checker premise — it cannot stay as a `D2` theorem
row. -/
theorem t005_dichotomy :
    (∀ (P : PLine → RawField → Prop) (raw : PLine) (field : RawField),
        P raw field → ¬ FunctionVal field)
      ∧ ¬ (∀ r : RawProg, FirstOrderClosed r) :=
  ⟨fun P => row_survives_any_premise P, first_order_closure_is_not_a_d2_theorem⟩

/-! ## §5 — receipts -/

#print axioms functionVal_is_empty
#print axioms serialized_fields_first_order
#print axioms row_survives_any_premise
#print axioms row_survives_any_premise_implies_the_row
#print axioms row_holds_with_premise_True
#print axioms row_holds_with_premise_False
#print axioms row_is_the_True_instance
#print axioms parseRefs_refFields
#print axioms parseFields_fieldsOf
#print axioms fieldsOf_injective
#print axioms rawField_equality_is_decided
#print axioms pline_equality_is_decided
#print axioms estate_serializer_round_trips
#print axioms rawProg_equality_is_decided
#print axioms f08_carries_an_unregistered_callback
#print axioms firstOrderClosed_is_false_on_raw
#print axioms resolves_iff
#print axioms checkFirstOrderB_iff
#print axioms checkFirstOrder_ok_iff_gate
#print axioms checkFirstOrder_ok_iff
#print axioms checkFirstOrder_error_condemns
#print axioms checkFirstOrder_rejects
#print axioms f08_diagnostic
#print axioms f08_gate_false
#print axioms ok1_is_closed
#print axioms ok1_accepted
#print axioms ok1_gate_true
#print axioms twoBad_has_two_violations
#print axioms twoBad_second_slot_is_a_slot
#print axioms checker_reports_only_the_first
#print axioms accumulating_diagnostic_is_false
#print axioms first_order_closure_is_not_a_d2_theorem
#print axioms t005_dichotomy

end EffectCoreV1.T005
