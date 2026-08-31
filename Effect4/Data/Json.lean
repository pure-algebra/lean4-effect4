import Std

/-!
# Data.Json.lean

Owner: the binary64 payload datum and the raw JSON tree of the Schema
representation payload carrier.

Contract packet: `test/contracts/schema-payload.contract.md`, sections D0 and
D1. Battery: `Effect4Test/Schema/PayloadContract.lean`. This module declares
the two leaf types the payload tree hangs off; it declares no representation
node, no admission clause, and no codec.

## What `Float64` is

`Float64` is the **IEEE 754 binary64 interchange datum**: the 64-bit pattern
itself, carried as a `UInt64`.

```text
bit 63      sign
bits 62..52 biased exponent field, 0 .. 2047
bits 51..0  trailing significand field
```

The representation is a bijection with the 2^64 binary64 bit patterns, and it
is proved so in both directions: `toBits_ofBits` and `ofBits_toBits`. So the
carrier holds every finite number that arrives off the wire, every subnormal,
both infinities, both signed zeros, and every NaN payload. It is a genuine
format model, not an enumeration of the five named constants: `nan`,
`posInfinity`, `negInfinity`, `zero`, and `negZero` are ordinary values of the
same type, picked out by name only because the battery names them.

The single-field encoding is chosen over a three-field `(sign, exponent,
significand)` record for a proof reason, recorded rather than left implicit. A
field-split carrier cannot prove `toBits_ofBits` without reasoning over all
2^64 patterns, which on this toolchain means `bv_decide` and therefore the
`Lean.ofReduceBool` axiom. Here both round trips are `rfl`, and the exponent
field is recovered arithmetically inside `isFinite`.

`isFinite` is the format's own finiteness test — the exponent field is not
all-ones — so it is `false` on both infinities and on every NaN, and `true` on
everything else, including both zeros and every subnormal.

Nothing here is arithmetic. No addition, comparison, ordering, rounding,
parsing, printing, or host conversion is declared, and none is claimed. The
datum is syntax.

## Why Lean's `Float` cannot be the carrier

`SC-REP-03`'s payload half claims decidable structural equality on the stored
datum. Lean's `Float` has no `DecidableEq`, and its `BEq` is IEEE equality,
under which `nan == nan` is `false` and `0.0 == -0.0` is `true`. Both halves of
the ruling would fail. The ruling, from the contract's answer (b), is that the
equality is:

- **reflexive**, so `Float64.nan = Float64.nan` — unlike the host's `===`; and
- **finer than the host's `===`**, so `Float64.negZero ≠ Float64.zero` — signed
  zero is therefore *not* normalized at construction, because the raw carrier
  must be able to hold what the wire packet will later normalize (`R1`,
  `E4-SCHEMA-CE-041`).

Both fall out of the bit-pattern encoding: `nan` is a concrete numeral and
equals itself by `rfl`, and `negZero` and `zero` differ in the sign bit.

## Non-canonical duplicates: yes, and deliberately

Stated plainly rather than glossed. The encoding is **not** canonical with
respect to the number denoted:

- **NaN.** All 2^53 - 2 patterns with an all-ones exponent field and a non-zero
  significand field are NaNs, and they are pairwise distinct under this
  equality. `Float64.nan` is one of them — the positive quiet NaN
  `0x7ff8000000000000`, the pattern the battery pins — and no theorem here
  privileges it beyond naming it.
- **Signed zero.** `zero` and `negZero` are two distinct data denoting the one
  real number 0. That duplication is required by the ruling, not tolerated.

Every other binary64 value — every normal and every subnormal — has exactly one
encoding, so those two families are the whole of the non-canonicity. What it
costs is recorded, not hidden: this equality is **equality of the stored
datum**, strictly finer than equality of the denoted extended real. It is not
the host's `===`, not wire equality (`SC-WIRE-05` is open, and rc.112's
`JSON.stringify` writes `-0` as `0`), and not denotational equality
(`SC-DEN-*`). A canonicalizing map is a wire-packet obligation and is declared
nowhere in this fence.

## What `Json` is

`Json` is the raw JSON tree: `null | boolean | number | string | array |
object`, matching `Schema.Json`. Object entries are an ordered
`List (String × Json)` and **never** a map, because raw JSON must preserve
ordered duplicate keys until the profile rejects them (`SC-WIRE-01`,
`E4-SCHEMA-CE-012`). That requirement is also what rules out reusing
`Lean.Json`, whose object is a balanced tree keyed by name.

`Json.null` is unrelated to the absent `LiteralKind.null` and to the `Null`
representation tag; `E4-SCHEMA-CE-021` opened that confusion family and this
constructor is its third member.

`NumbersFinite` is `isJsonLeaf`'s finiteness requirement
(`SchemaAST.ts:4271-4274`) lifted to the tree. It is declared here and applied
nowhere here. Persisted/decode-side field admission applies it both to
representation-annotation payloads and to every retained ordinary annotation
entry. Encode-side pruning of a wider live annotation value is a different,
later wire arrow.

## Structural companions

`deriving DecidableEq` does not apply to a `List`/`List (String × _)`-nested
inductive on this toolchain, so `DecidableEq Json` is built by hand from
`Json.beq` and `Json.beq_iff`. `Json.ind`, `Json.beqList`, `Json.beqEntries`,
`Json.beqList_iff`, `Json.beqEntries_iff`, `Json.numbersFiniteList`,
`Json.numbersFiniteEntries`, `Json.numbersFiniteList_iff`,
`Json.numbersFiniteEntries_iff`, `Json.NumbersFiniteList`,
`Json.NumbersFiniteEntries`, `Json.numbersFiniteList_forall`, and
`Json.numbersFiniteEntries_forall` are the structural companions that recursion
over the nested inductive forces. They are scaffolding for the frozen surface,
not part of it, and no frozen theorem is stated in terms of one.

Every recursive function here is structural, not well-founded. That is a trust
choice, not an accident: `WellFounded.fix` would put `Quot.sound` into the
receipt of every consequence, and the structural elaborator does not refuse
this carrier, so there is no reason to spend it.
-/

namespace Effect4

/--
The IEEE 754 binary64 interchange datum: the 64-bit pattern itself.

Equality is equality of the stored datum — reflexive on NaN and finer than the
host's `===` on signed zero. See the module docstring for the field layout, the
equality ruling it discharges, and the two families of non-canonical duplicates
it admits.
-/
structure Float64 where
  /-- The binary64 interchange bit pattern, most significant bit is the sign. -/
  bits : UInt64
deriving DecidableEq, Repr, Inhabited

namespace Float64

/-- The stored bit pattern. -/
def toBits (value : Float64) : UInt64 := value.bits

/-- Every 64-bit pattern is a datum. This is what makes the carrier the whole
of binary64 rather than a chosen subset. -/
def ofBits (bits : UInt64) : Float64 := ⟨bits⟩

/-- `ofBits` loses nothing: every bit pattern is recovered. -/
theorem toBits_ofBits (bits : UInt64) : toBits (ofBits bits) = bits := rfl

/-- `toBits` loses nothing: every datum is recovered. With `toBits_ofBits` this
is the bijection with the 2^64 binary64 patterns. -/
theorem ofBits_toBits (value : Float64) : ofBits (toBits value) = value := rfl

/--
The format's finiteness test: the biased exponent field is not all-ones.

The exponent field is bits 62..52, extracted here as
`bits / 2^52 % 2^11`; `0x10000000000000` is `2^52`, `0x800` is `2^11`, and
`0x7ff` is the all-ones field that encodes the infinities and the NaNs. The
division discards the significand and the remainder discards the sign, so the
test reads that field alone.

`false` on both infinities and on every NaN payload; `true` on every zero,
subnormal, and normal number. This is not a range check on a real number.
-/
def isFinite (value : Float64) : Bool :=
  value.bits.toNat / 0x10000000000000 % 0x800 != 0x7ff

/--
A NaN: the positive quiet NaN `0x7ff8000000000000`.

One of the 2^53 - 2 NaN data. `Float64` holds every other NaN payload
distinctly, reachable through `ofBits`.
-/
def nan : Float64 := ⟨0x7ff8000000000000⟩

/-- Positive infinity. -/
def posInfinity : Float64 := ⟨0x7ff0000000000000⟩

/-- Negative infinity. -/
def negInfinity : Float64 := ⟨0xfff0000000000000⟩

/-- Positive zero. -/
def zero : Float64 := ⟨0x0000000000000000⟩

/--
Negative zero, kept distinct from `zero`.

The distinction is the observable half of the equality ruling; see
`negZero_ne_zero`.
-/
def negZero : Float64 := ⟨0x8000000000000000⟩

/-- The pinned spelling of `nan`. -/
theorem toBits_nan : toBits nan = (0x7ff8000000000000 : UInt64) := rfl

/-- The pinned spelling of `posInfinity`. -/
theorem toBits_posInfinity : toBits posInfinity = (0x7ff0000000000000 : UInt64) := rfl

/-- The pinned spelling of `negInfinity`. -/
theorem toBits_negInfinity : toBits negInfinity = (0xfff0000000000000 : UInt64) := rfl

/-- The pinned spelling of `zero`. -/
theorem toBits_zero : toBits zero = (0x0000000000000000 : UInt64) := rfl

/-- The pinned spelling of `negZero`: `zero` with the sign bit set. -/
theorem toBits_negZero : toBits negZero = (0x8000000000000000 : UInt64) := rfl

/-- A NaN is not finite. -/
theorem isFinite_nan : isFinite nan = false := by decide

/-- Positive infinity is not finite. -/
theorem isFinite_posInfinity : isFinite posInfinity = false := by decide

/-- Negative infinity is not finite. -/
theorem isFinite_negInfinity : isFinite negInfinity = false := by decide

/-- Positive zero is finite. -/
theorem isFinite_zero : isFinite zero = true := by decide

/-- Negative zero is finite. Signed zero is a finite datum, not a special case. -/
theorem isFinite_negZero : isFinite negZero = true := by decide

/--
Signed zero is not normalized away.

This is the ENSURES row that makes the equality ruling observable: a carrier
that normalized `-0` to `0` at construction fails here, and `SC-WIRE-04` would
then have nothing to normalize. `E4-SCHEMA-CE-041`. It is a statement about the
stored datum only — the host's `===` equates these two, and rc.112's
`JSON.stringify` writes both as `0`.
-/
theorem negZero_ne_zero : negZero ≠ zero := by decide

/--
The format rule for every datum, not just the five named ones.

The pointwise `isFinite_*` equations pin five bit patterns and say nothing
about the other `2^64 - 5`. These two equations characterise the test itself:
finiteness is exactly the eleven-bit exponent field failing to be all ones.
Together with `toBits_ofBits` they fix `isFinite` on the whole carrier, which
is what `SC-REP-04`'s literal-leg finiteness clause has to rest on.

These two are the only `Float64` theorems that reach an axiom. Both sit at
`[propext, Quot.sound]`, the repository ceiling, and the dependency is
inherited from core's `bne_iff_ne` rather than introduced by the proof — a
term-mode proof reaches the same pair. The pointwise `isFinite_*` and
`toBits_*` equations remain axiom-free.
-/
theorem isFinite_ofBits_iff (bits : UInt64) :
    isFinite (ofBits bits) = true ↔
      bits.toNat / 0x10000000000000 % 0x800 ≠ 0x7ff := by
  simp [isFinite, ofBits]

/-- The complementary half of `isFinite_ofBits_iff`: the all-ones exponent
field is exactly the non-finite case, which is the wire's three escape
spellings plus every NaN payload. -/
theorem not_isFinite_ofBits_iff (bits : UInt64) :
    isFinite (ofBits bits) = false ↔
      bits.toNat / 0x10000000000000 % 0x800 = 0x7ff := by
  simp [isFinite, ofBits]

end Float64

/--
The raw JSON tree.

Object entries are an ordered `List`, never a map: duplicate keys must survive
until the profile rejects them. Nothing here decodes, encodes, normalizes, or
spells a persisted key.
-/
inductive Json where
  /-- The JSON `null` literal. Unrelated to `LiteralKind.null` and to the `Null` tag. -/
  | null
  /-- A JSON boolean. -/
  | bool (value : Bool)
  /-- A JSON number, carried as the raw binary64 datum. -/
  | number (value : Float64)
  /-- A JSON string. -/
  | str (value : String)
  /-- A JSON array, in source order. -/
  | arr (elements : List Json)
  /-- A JSON object: ordered entries, duplicate keys preserved. -/
  | obj (entries : List (String × Json))

namespace Json

/--
The single-motive induction principle for the nested inductive.

Structural companion. Lean's generated `Json.rec` carries one motive per nested
container instance; this collapses them into the membership form every proof
below actually uses.
-/
@[elab_as_elim]
private theorem ind {motive : Json → Prop}
    (null : motive .null)
    (bool : ∀ value, motive (.bool value))
    (number : ∀ value, motive (.number value))
    (str : ∀ value, motive (.str value))
    (arr : ∀ elements, (∀ element ∈ elements, motive element) → motive (.arr elements))
    (obj : ∀ entries, (∀ entry ∈ entries, motive entry.2) → motive (.obj entries)) :
    ∀ value : Json, motive value :=
  fun value =>
    Json.rec (motive_1 := motive)
      (motive_2 := fun elements => ∀ element ∈ elements, motive element)
      (motive_3 := fun entries => ∀ entry ∈ entries, motive entry.2)
      (motive_4 := fun entry => motive entry.2)
      null bool number str arr obj
      (by intro _ hmem; cases hmem)
      (fun _ _ ihHead ihTail => by
        intro _ hmem
        cases hmem with
        | head => exact ihHead
        | tail _ hmem' => exact ihTail _ hmem')
      (by intro _ hmem; cases hmem)
      (fun _ _ ihHead ihTail => by
        intro _ hmem
        cases hmem with
        | head => exact ihHead
        | tail _ hmem' => exact ihTail _ hmem')
      (fun _ _ ih => ih)
      value

/--
The constructor cap for the JSON carrier.

A seventh constructor makes this unprovable. It fixes the constructor set, not
the constructor order.
-/
theorem cases_census (value : Json) :
    value = Json.null ∨
    (∃ b : Bool, value = Json.bool b) ∨
    (∃ n : Float64, value = Json.number n) ∨
    (∃ s : String, value = Json.str s) ∨
    (∃ values : List Json, value = Json.arr values) ∨
    (∃ entries : List (String × Json), value = Json.obj entries) := by
  cases value with
  | null => exact Or.inl rfl
  | bool value => exact Or.inr (Or.inl ⟨value, rfl⟩)
  | number value => exact Or.inr (Or.inr (Or.inl ⟨value, rfl⟩))
  | str value => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨value, rfl⟩)))
  | arr elements => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨elements, rfl⟩))))
  | obj entries => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨entries, rfl⟩))))

mutual

/--
Structural equality as a Boolean.

Structural companion: `deriving DecidableEq` does not apply to this nested
inductive on Lean 4.33.1, so the instance is built from this function and
`beq_iff`. Numbers are compared as stored data, so `beq (number nan)
(number nan)` is `true` and `beq (number negZero) (number zero)` is `false`.
-/
private def beq : Json → Json → Bool
  | .null, .null => true
  | .bool a, .bool b => decide (a = b)
  | .number a, .number b => decide (a = b)
  | .str a, .str b => decide (a = b)
  | .arr a, .arr b => beqList a b
  | .obj a, .obj b => beqEntries a b
  | _, _ => false

/-- Structural companion: element-wise `beq` on arrays. -/
private def beqList : List Json → List Json → Bool
  | [], [] => true
  | a :: as, b :: bs => beq a b && beqList as bs
  | _, _ => false

/-- Structural companion: entry-wise `beq` on objects, key and value in order. -/
private def beqEntries : List (String × Json) → List (String × Json) → Bool
  | [], [] => true
  | a :: as, b :: bs => (decide (a.1 = b.1) && beq a.2 b.2) && beqEntries as bs
  | _, _ => false
end

/-- Structural companion: `beqList` decides list equality, given the element case. -/
private theorem beqList_iff {as : List Json}
    (ih : ∀ a ∈ as, ∀ b : Json, beq a b = true ↔ a = b) :
    ∀ bs : List Json, beqList as bs = true ↔ as = bs := by
  induction as with
  | nil => intro bs; cases bs <;> simp [beqList]
  | cons a as iha =>
    intro bs
    cases bs with
    | nil => simp [beqList]
    | cons b bs =>
      have hhead := ih a (by simp) b
      have htail := iha (fun x hx => ih x (by simp [hx])) bs
      simp only [beqList, Bool.and_eq_true, List.cons.injEq, hhead, htail]

/-- Structural companion: `beqEntries` decides entry-list equality. -/
private theorem beqEntries_iff {as : List (String × Json)}
    (ih : ∀ a ∈ as, ∀ b : Json, beq a.2 b = true ↔ a.2 = b) :
    ∀ bs : List (String × Json), beqEntries as bs = true ↔ as = bs := by
  induction as with
  | nil => intro bs; cases bs <;> simp [beqEntries]
  | cons a as iha =>
    intro bs
    cases bs with
    | nil => simp [beqEntries]
    | cons b bs =>
      have hhead := ih a (by simp) b.2
      have htail := iha (fun x hx => ih x (by simp [hx])) bs
      simp only [beqEntries, Bool.and_eq_true, decide_eq_true_eq, List.cons.injEq,
        Prod.ext_iff, hhead, htail, and_assoc]

/--
`beq` decides structural equality.

Structural companion of the `DecidableEq Json` instance.
-/
private theorem beq_iff : ∀ a b : Json, beq a b = true ↔ a = b := by
  intro a
  induction a using Json.ind with
  | null => intro b; cases b <;> simp [beq]
  | bool value => intro b; cases b <;> simp [beq]
  | number value => intro b; cases b <;> simp [beq]
  | str value => intro b; cases b <;> simp [beq]
  | arr elements ih => intro b; cases b <;> simp [beq, beqList_iff ih]
  | obj entries ih => intro b; cases b <;> simp [beq, beqEntries_iff ih]

/--
Decidable structural equality on the raw JSON tree.

`SC-REP-03`, payload half. This is equality of the stored tree, including the
stored binary64 data at its number leaves and the order and multiplicity of
object keys. It is not wire equality and not denotational equality.
-/
instance instDecidableEqJson : DecidableEq Json := fun a b =>
  if h : beq a b = true then
    isTrue ((beq_iff a b).mp h)
  else
    isFalse fun hab => h ((beq_iff a b).mpr hab)

mutual

/--
Every number in the tree is finite, as a Boolean.

`isJsonLeaf` (`SchemaAST.ts:4271-4274`) requires `Number.isFinite`. This
decides that requirement over the whole tree; it inspects no key and no string.
-/
def numbersFinite : Json → Bool
  | .null => true
  | .bool _ => true
  | .number value => value.isFinite
  | .str _ => true
  | .arr elements => numbersFiniteList elements
  | .obj entries => numbersFiniteEntries entries

/-- Structural companion: `numbersFinite` over an array's elements. -/
private def numbersFiniteList : List Json → Bool
  | [] => true
  | element :: rest => numbersFinite element && numbersFiniteList rest

/-- Structural companion: `numbersFinite` over an object's entry values. -/
private def numbersFiniteEntries : List (String × Json) → Bool
  | [] => true
  | entry :: rest => numbersFinite entry.2 && numbersFiniteEntries rest
end

mutual

/--
Every number in the tree is finite, as a proposition.

Structural rather than well-founded, so no `Acc` recursion and no `Quot.sound`
enters the receipts. The definitional shape is not the readable statement of
the property; the six per-constructor laws below are, and they are what the
battery freezes. `numbersFinite_iff` is the agreement with the Boolean form.
-/
def NumbersFinite : Json → Prop
  | .null => True
  | .bool _ => True
  | .number value => value.isFinite = true
  | .str _ => True
  | .arr elements => NumbersFiniteList elements
  | .obj entries => NumbersFiniteEntries entries

/-- Structural companion: `NumbersFinite` over an array's elements. -/
private def NumbersFiniteList : List Json → Prop
  | [] => True
  | element :: rest => NumbersFinite element ∧ NumbersFiniteList rest

/-- Structural companion: `NumbersFinite` over an object's entry values. -/
private def NumbersFiniteEntries : List (String × Json) → Prop
  | [] => True
  | entry :: rest => NumbersFinite entry.2 ∧ NumbersFiniteEntries rest
end

/-- Structural companion: the conjunction form is the membership form. -/
private theorem numbersFiniteList_forall (elements : List Json) :
    NumbersFiniteList elements ↔ ∀ element ∈ elements, NumbersFinite element := by
  induction elements with
  | nil => exact ⟨fun _ _ hmem => (nomatch hmem), fun _ => True.intro⟩
  | cons head tail iht =>
    constructor
    · intro hall element hmem
      cases hmem with
      | head => exact hall.1
      | tail _ hmem' => exact iht.mp hall.2 element hmem'
    · intro hall
      exact ⟨hall head (.head _),
        iht.mpr fun element hmem => hall element (.tail _ hmem)⟩

/-- Structural companion: the conjunction form is the membership form. -/
private theorem numbersFiniteEntries_forall (entries : List (String × Json)) :
    NumbersFiniteEntries entries ↔ ∀ entry ∈ entries, NumbersFinite entry.2 := by
  induction entries with
  | nil => exact ⟨fun _ _ hmem => (nomatch hmem), fun _ => True.intro⟩
  | cons head tail iht =>
    constructor
    · intro hall entry hmem
      cases hmem with
      | head => exact hall.1
      | tail _ hmem' => exact iht.mp hall.2 entry hmem'
    · intro hall
      exact ⟨hall head (.head _),
        iht.mpr fun entry hmem => hall entry (.tail _ hmem)⟩

/-- `null` carries no number. -/
theorem numbersFinite_null : NumbersFinite Json.null := True.intro

/-- A boolean carries no number. -/
theorem numbersFinite_bool (value : Bool) : NumbersFinite (Json.bool value) := True.intro

/-- A string carries no number, and its characters are never inspected. -/
theorem numbersFinite_str (value : String) : NumbersFinite (Json.str value) := True.intro

/-- At a number leaf the predicate is exactly `Float64.isFinite`. -/
theorem numbersFinite_number_iff (value : Float64) :
    NumbersFinite (Json.number value) ↔ Float64.isFinite value = true := Iff.rfl

/-- An array is checked element-wise. -/
theorem numbersFinite_arr_iff (elements : List Json) :
    NumbersFinite (Json.arr elements) ↔ ∀ element ∈ elements, NumbersFinite element :=
  numbersFiniteList_forall elements

/-- An object is checked at its entry values; its keys are never inspected. -/
theorem numbersFinite_obj_iff (entries : List (String × Json)) :
    NumbersFinite (Json.obj entries) ↔ ∀ entry ∈ entries, NumbersFinite entry.2 :=
  numbersFiniteEntries_forall entries

/-- Structural companion: the array case of `numbersFinite_iff`. -/
private theorem numbersFiniteList_iff {elements : List Json}
    (ih : ∀ element ∈ elements, (numbersFinite element = true ↔ NumbersFinite element)) :
    numbersFiniteList elements = true ↔ NumbersFiniteList elements := by
  induction elements with
  | nil => exact ⟨fun _ => True.intro, fun _ => rfl⟩
  | cons head tail iht =>
    have hhead := ih head (by simp)
    have htail := iht (fun x hx => ih x (by simp [hx]))
    simp only [numbersFiniteList, NumbersFiniteList, Bool.and_eq_true, hhead, htail]

/-- Structural companion: the object case of `numbersFinite_iff`. -/
private theorem numbersFiniteEntries_iff {entries : List (String × Json)}
    (ih : ∀ entry ∈ entries, (numbersFinite entry.2 = true ↔ NumbersFinite entry.2)) :
    numbersFiniteEntries entries = true ↔ NumbersFiniteEntries entries := by
  induction entries with
  | nil => exact ⟨fun _ => True.intro, fun _ => rfl⟩
  | cons head tail iht =>
    have hhead := ih head (by simp)
    have htail := iht (fun x hx => ih x (by simp [hx]))
    simp only [numbersFiniteEntries, NumbersFiniteEntries, Bool.and_eq_true, hhead, htail]

/-- The Boolean decision and the proposition agree. -/
theorem numbersFinite_iff (value : Json) :
    numbersFinite value = true ↔ NumbersFinite value := by
  induction value using Json.ind with
  | null => exact ⟨fun _ => True.intro, fun _ => rfl⟩
  | bool value => exact ⟨fun _ => True.intro, fun _ => rfl⟩
  | str value => exact ⟨fun _ => True.intro, fun _ => rfl⟩
  | number value => exact Iff.rfl
  | arr elements ih => exact numbersFiniteList_iff ih
  | obj entries ih => exact numbersFiniteEntries_iff ih

/--
A NaN is not a JSON number at the pin.

The third of the contract's four numeric domains: a non-finite number is a
legal enum value and property key, and is not a legal annotation payload.
`E4-SCHEMA-CE-028`.
-/
theorem not_numbersFinite_nan : ¬ NumbersFinite (Json.number Float64.nan) := by
  rw [numbersFinite_number_iff, Float64.isFinite_nan]
  simp

/-- Positive zero is a JSON number. -/
theorem numbersFinite_zero : NumbersFinite (Json.number Float64.zero) :=
  (numbersFinite_number_iff Float64.zero).mpr Float64.isFinite_zero

/-- A finite number nested under both an object and an array is reached. -/
theorem numbersFinite_nested :
    NumbersFinite
      (Json.obj
        [("outer", Json.arr
          [Json.number Float64.zero,
           Json.obj [("leaf", Json.bool true)]])]) :=
  (numbersFinite_iff _).mp (by decide)

/-- A NaN nested under both an array and an object is reached. An implementation
that checked only the immediate number, or only one of the two container routes,
fails here. -/
theorem not_numbersFinite_nested_nan :
    ¬ NumbersFinite (Json.arr [Json.obj [("bad", Json.number Float64.nan)]]) :=
  fun h => absurd ((numbersFinite_iff _).mpr h) (by decide)

end Json

end Effect4
