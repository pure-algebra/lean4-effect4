import Cas.Lang.Defun

/-!
# BREAKER attack on `EC1-T005` (`workshop/s1/T005.lean`), slice `EC1-S1`

Skill stage: `.claude/skills/lean/workflows/lean-assurance-review` — the target
is a landed proof claiming `PROVED-STRONGER`, so this is an assurance review run
adversarially.

Run from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s1/attack-T005.lean
```

Every carrier below is a VERBATIM re-declaration of `T005.lean`'s scratch
carrier. Nothing is imported from `T005.lean` — it is not a Lake module — so the
target's definitions are re-derived here, not assumed.

## Verdict summary

WHAT SURVIVES: the file elaborates (exit 0, 33 receipts, no `sorryAx`, no
`Classical.choice`); every §3 theorem is non-vacuous at `f08` (§9); the checker's
first-error soundness and existential completeness re-derive; §2's decidability
claim survives and is here STRENGTHENED to a reduction (§4).

WHAT DOES NOT:

* §1 `row_survives_any_premise` is NOT "strictly stronger" than the DAG row.
  `SerializableField` is inhabited at EVERY field, so the two are LOGICALLY
  EQUIVALENT (`row_implies_row_survives_any_premise`). Ground (a) of the
  `PROVED-STRONGER` grade collapses to `PROVED-EQUIVALENT`.
* §2 `FunctionVal` is NOT forced to be empty. `ALGEBRA.md:242-244` lists
  "host-function payloads" as deliberately representable, SEPARATELY from
  "dangling references". At the reading that honours that line the DAG row is
  FALSE (`row_is_false_at_the_payload_reading`), so the row has no truth value
  until `EC1-D020` fixes the field universe. Both halves of the target's
  headline — "proved verbatim" and "necessarily vacuous" — are artifacts of
  predicates the prover supplied.
* §3 the §2 round-trip ARGUMENT is FALSE. A carrier WITH a function-valued
  field admits an invertible walk (`fnParse_fnFields`), so invertibility does
  not mechanize "contains only serializable first-order data".
* §5 `EC1-F03`/`EC1-F82`: `checkFirstOrder` accepts a duplicate `CodeId` table
  and is blind to permuting it, while the resolved body differs.
* §6 `EC1-F08` NESTED: a continuation slot inside a code definition body is
  invisible to `FirstOrderClosed`, which is not reachability-closed.
* §7 `EC1-K12`'s captures half is unchecked; the door accepts any captures.
* §8 the flagged `T005`/`T006` interaction is real: permuting slots changes the
  reported diagnostic.

## Receipts

Every theorem reports `#print axioms` at the foot. No `sorry`, no `axiom`, no
`native_decide`, no `#eval` carrying a claim.
-/

namespace EffectCoreV1.AttackT005

open Cas.Lang
open Cas (Bytes Addr32)

/-! ## §0 — the target's carrier, re-declared verbatim -/

inductive RawField where
  | u8 (b : UInt8)
  | payload (bs : Bytes)
  | operand (i : PIn)
  deriving DecidableEq

def refFields : List (UInt8 × PIn) → List RawField
  | [] => []
  | (b, i) :: rest => .u8 b :: .operand i :: refFields rest

def fieldsOf : PLine → List RawField
  | .put v t payload refs => .u8 v :: .u8 t :: .payload payload :: refFields refs
  | .load src => [.operand src]

def SerializableField (raw : PLine) (field : RawField) : Prop :=
  field ∈ fieldsOf raw

def FunctionVal : RawField → Prop
  | .u8 _ => False
  | .payload _ => False
  | .operand _ => False

theorem functionVal_is_empty (field : RawField) : ¬ FunctionVal field := by
  cases field <;> exact not_false

/-- The target's row, re-derived. -/
theorem serialized_fields_first_order (raw : PLine) (field : RawField)
    (_h : SerializableField raw field) : ¬ FunctionVal field :=
  functionVal_is_empty field

/-- The target's claimed strictly-stronger form, re-derived. -/
theorem row_survives_any_premise (P : PLine → RawField → Prop) :
    ∀ raw field, P raw field → ¬ FunctionVal field :=
  fun _ field _ => functionVal_is_empty field

/-! ## §1 — ATTACK: "strictly stronger" is FALSE; the two are EQUIVALENT

The target's ground (a) for `PROVED-STRONGER` is that
`row_survives_any_premise` "LOGICALLY IMPLIES the DAG row" and is therefore
"a theorem strictly stronger than the DAG signature".

The implication holds. STRICTNESS does not. `SerializableField` is inhabited at
every field of the universe, so the row RECOVERS the quantified-over-`P` form,
and the two statements are inter-derivable. -/

/-- **THE INHABITATION WITNESS.** Every field of the universe is serializable
from some `PLine`. This is what kills strictness: the premise is not merely
unused, it is universally satisfiable, so no instance of the schema is weaker
than any other. -/
theorem every_field_is_serializable (field : RawField) :
    ∃ raw : PLine, SerializableField raw field := by
  cases field with
  | u8 b => exact ⟨.put b 0 [] [], by simp [SerializableField, fieldsOf]⟩
  | payload bs => exact ⟨.put 0 0 bs [], by simp [SerializableField, fieldsOf]⟩
  | operand i => exact ⟨.load i, by simp [SerializableField, fieldsOf]⟩

/-- **THE COLLAPSE.** The DAG row implies the target's "strictly stronger"
theorem. Combined with `row_survives_any_premise_implies_the_row` (the target's
own theorem, re-derived below) the two are LOGICALLY EQUIVALENT. -/
theorem row_implies_row_survives_any_premise
    (h : ∀ (raw : PLine) (field : RawField),
        SerializableField raw field → ¬ FunctionVal field) :
    ∀ (P : PLine → RawField → Prop) (raw : PLine) (field : RawField),
      P raw field → ¬ FunctionVal field := by
  intro _ _ field _
  obtain ⟨raw', hraw'⟩ := every_field_is_serializable field
  exact h raw' field hraw'

/-- The target's own converse, re-derived. -/
theorem row_survives_any_premise_implies_the_row
    (h : ∀ (P : PLine → RawField → Prop) (raw : PLine) (field : RawField),
        P raw field → ¬ FunctionVal field) :
    ∀ (raw : PLine) (field : RawField),
      SerializableField raw field → ¬ FunctionVal field :=
  h SerializableField

/-- **GROUND (a) OF `PROVED-STRONGER` IS REFUTED.** The DAG row and the
claimed-stronger theorem are equivalent, not strictly ordered. -/
theorem strictly_stronger_is_actually_equivalent :
    (∀ (raw : PLine) (field : RawField),
        SerializableField raw field → ¬ FunctionVal field)
      ↔ (∀ (P : PLine → RawField → Prop) (raw : PLine) (field : RawField),
            P raw field → ¬ FunctionVal field) :=
  ⟨row_implies_row_survives_any_premise, row_survives_any_premise_implies_the_row⟩

/-! ## §2 — ATTACK: `FunctionVal` is NOT forced to be the empty predicate

The target asserts (`T005.lean:50-52`, and the report's clause 1) that
`FunctionVal` "cannot honestly be written as anything but the empty predicate
over a first-order field universe: no arm holds a function, so no arm can
satisfy it."

`ALGEBRA.md:242-244` says otherwise. It lists the deliberately representable
defects of the raw carrier as "Duplicate identifiers, dangling references,
forged region tokens, invalid rows, bad types, illegal back edges,
HOST-FUNCTION PAYLOADS, and incomplete handlers". "Dangling references" and
"host-function payloads" are SEPARATE entries. The target's §3 discharges the
dangling-reference reading and declares the host-function-payload reading
unwritable; the packet says it is representable.

`EC1-F08`'s expected control (`CONTRACT-PACKET.md:737`) is a "Non-first-order-
FIELD diagnostic" — a field verdict, not a slot-resolution verdict. -/

/-- A `Bytes` payload carrying a serialized host function is a `RawField` the
target's own universe already admits: `.payload` is opaque bytes. Marking that
arm is a MODELLING CHOICE, and it is the choice `ALGEBRA.md:242` describes. -/
def FunctionValPayload : RawField → Prop
  | .u8 _ => False
  | .payload bs => bs ≠ []
  | .operand _ => False

/-- The line carrying a host-function payload. Nothing exotic: one `put` whose
payload is a non-empty byte string. -/
def hostFnLine : PLine := .put 0 0 [0] []

theorem hostFnLine_serializes_the_payload :
    SerializableField hostFnLine (.payload [0]) := by
  simp [SerializableField, hostFnLine, fieldsOf]

/-- **THE ROW IS FALSE AT THIS READING.** Same field universe, same
`SerializableField`, a different — and packet-sanctioned — `FunctionVal`. -/
theorem row_is_false_at_the_payload_reading :
    ¬ ∀ (raw : PLine) (field : RawField),
        SerializableField raw field → ¬ FunctionValPayload field := by
  intro h
  exact h hostFnLine (.payload [0]) hostFnLine_serializes_the_payload (by
    simp [FunctionValPayload])

/-- **THE ROW HAS NO TRUTH VALUE.** Both principal predicates were supplied by
the prover. Over ONE fixed field universe and ONE fixed `SerializableField`
there are two readings of `FunctionVal`, one making the row true and one making
it false. "Proved verbatim" and "necessarily vacuous" are therefore both
artifacts of the prover's own definitions, not results about `EC1-D020`. -/
theorem the_row_is_undetermined_not_vacuous :
    ∃ FV₁ FV₂ : RawField → Prop,
      (∀ raw field, SerializableField raw field → ¬ FV₁ field)
        ∧ ¬ (∀ raw field, SerializableField raw field → ¬ FV₂ field) :=
  ⟨FunctionVal, FunctionValPayload,
   serialized_fields_first_order, row_is_false_at_the_payload_reading⟩

/-- The third horn the target's `t005_dichotomy` does not cover: at the
payload reading the row is not vacuous, it is FALSE — which still leaves it
un-provable at `D2`, but for a different reason than the target records. -/
theorem third_horn_is_falsity_not_vacuity :
    (∃ raw field, SerializableField raw field ∧ FunctionValPayload field)
      ∧ ¬ ∀ raw field, SerializableField raw field → ¬ FunctionValPayload field :=
  ⟨⟨hostFnLine, .payload [0], hostFnLine_serializes_the_payload, by
      simp [FunctionValPayload]⟩,
   row_is_false_at_the_payload_reading⟩

/-! ## §3 — ATTACK: the §2 round-trip ARGUMENT is FALSE

`T005.lean:257-260`: "A carrier with a host-function field admits no such pair
— it must either put the function in a field, breaking first-orderness, or drop
it, breaking this equation."

The target's own omissions call this "an argument about what such a carrier
would have to do, not a Lean theorem". It is worse than unproved: it is FALSE.
A carrier WITH a function-valued field admits a perfectly invertible walk. -/

/-- A line carrying an actual Lean function — the thing `EC1-K12` forbids. -/
inductive FnLine where
  | pure (n : Nat)
  | callback (f : Nat → Nat)

/-- A field universe with a FUNCTION-VALUED arm. -/
inductive FnField where
  | num (n : Nat)
  | fn (f : Nat → Nat)

def fnFields : FnLine → List FnField
  | .pure n => [.num n]
  | .callback f => [.fn f]

def fnParse : List FnField → Option FnLine
  | [.num n] => some (.pure n)
  | [.fn f] => some (.callback f)
  | _ => none

/-- **THE REFUTATION.** The walk over a function-valued carrier round-trips,
exactly as `parseFields_fieldsOf` does over the first-order one. Invertibility
therefore does NOT mechanize `ALGEBRA.md:224`'s "contains only serializable
first-order data"; §2 proves a round trip and nothing about first-orderness. -/
theorem fnParse_fnFields (l : FnLine) : fnParse (fnFields l) = some l := by
  cases l <;> rfl

/-- And injectivity follows for the function-valued carrier too, by the target's
own three-line argument. -/
theorem fnFields_injective {l l' : FnLine} (h : fnFields l = fnFields l') :
    l = l' := by
  have hl : fnParse (fnFields l) = some l := fnParse_fnFields l
  rw [h, fnParse_fnFields l'] at hl
  exact (Option.some.inj hl).symm

/-! ## §4 — FALSIFIER SURVIVED, and strengthened: decidability DOES separate them

The target's second §2 claim — that decidable equality "is what a host-function
field would destroy" — survives the attack above, and the target left it as an
elaboration observation ("failure to synthesize is not a proof of
non-existence"). It can be upgraded to a REDUCTION, which is a real theorem and
is the honest replacement for the refuted round-trip argument. -/

/-- **THE REDUCTION.** Decidable equality on a field universe with a
function-valued arm DECIDES extensional equality of `Nat → Nat`. That is the
mechanized content of "first-order", and it is the claim §2 should have carried
instead of the round trip. -/
theorem decEq_fnField_decides_function_equality
    (inst : DecidableEq FnField) (f g : Nat → Nat) : f = g ∨ f ≠ g := by
  have hiff : FnField.fn f = FnField.fn g ↔ f = g := by
    constructor
    · intro h; injection h
    · intro h; exact congrArg FnField.fn h
  rcases inst (FnField.fn f) (FnField.fn g) with h | h
  · exact Or.inr (fun hfg => h (hiff.mpr hfg))
  · exact Or.inl (hiff.mp h)

/-! ## §5 — `EC1-F03` / `EC1-F82`: the repaired row admits a duplicate code table

The target's §3 carrier and checker, re-declared verbatim. -/

abbrev CodeId := Nat

structure RawCodeDef where
  id : CodeId
  body : PProg
  deriving DecidableEq

structure Slot where
  code : CodeId
  captures : List PIn
  deriving DecidableEq

structure RawProg where
  codeTable : List RawCodeDef
  slots : List Slot
  deriving DecidableEq

def HostCallback (r : RawProg) (s : Slot) : Prop :=
  ∀ d ∈ r.codeTable, d.id ≠ s.code

def FirstOrderClosed (r : RawProg) : Prop :=
  ∀ s ∈ r.slots, ∃ d ∈ r.codeTable, d.id = s.code

def resolves (r : RawProg) (s : Slot) : Bool :=
  r.codeTable.any (fun d => d.id == s.code)

def checkFirstOrderB (r : RawProg) : Bool :=
  r.slots.all (fun s => resolves r s)

def checkFirstOrder (r : RawProg) : Except Slot Unit :=
  match r.slots.find? (fun s => !resolves r s) with
  | some s => .error s
  | none => .ok ()

def zeroAddr : Addr32 := ⟨List.replicate 32 0, by simp⟩

def bodyA : PProg := [PLine.load (.lit zeroAddr)]
def bodyB : PProg := [PLine.load (.ans 0)]

/-- `EC1-F03`: two code definitions share `CodeId` 7 with DIFFERENT bodies. -/
def dupProg : RawProg :=
  { codeTable := [⟨7, bodyA⟩, ⟨7, bodyB⟩], slots := [⟨7, []⟩] }

/-- `EC1-F82`: the same table, permuted. -/
def dupProgSwapped : RawProg :=
  { codeTable := [⟨7, bodyB⟩, ⟨7, bodyA⟩], slots := [⟨7, []⟩] }

theorem dupProg_bodies_differ : bodyA ≠ bodyB := by
  simp [bodyA, bodyB]

/-- **THE F03 HIT.** A code table that is not a function passes the repaired
row. `FirstOrderClosed` asserts SOME definition resolves each slot; it does not
assert a unique one, so "the code this slot names" is ambiguous in an accepted
program. -/
theorem dupProg_accepted : checkFirstOrder dupProg = .ok () := rfl

theorem dupProg_is_closed : FirstOrderClosed dupProg := by
  intro s hs
  simp only [dupProg, List.mem_singleton] at hs
  subst hs
  exact ⟨⟨7, bodyA⟩, by simp [dupProg], rfl⟩

/-- Two DISTINCT definitions both witness the closure clause for the same
slot — the ambiguity, exhibited. -/
theorem dupProg_resolution_is_ambiguous :
    (∃ d ∈ dupProg.codeTable, d.id = (7 : CodeId) ∧ d.body = bodyA)
      ∧ (∃ d ∈ dupProg.codeTable, d.id = (7 : CodeId) ∧ d.body = bodyB) := by
  constructor
  · exact ⟨⟨7, bodyA⟩, by simp [dupProg], rfl, rfl⟩
  · exact ⟨⟨7, bodyB⟩, by simp [dupProg], rfl, rfl⟩

/-- **THE F82 HIT.** Permuting the duplicate-key code table leaves the verdict
identical, while the definition a first-match resolver would select changes.
The repaired row is blind to the permutation it would need to condemn. -/
theorem dupProg_permutation_is_invisible :
    checkFirstOrder dupProgSwapped = checkFirstOrder dupProg
      ∧ dupProg.codeTable.head?.map (·.body)
          ≠ dupProgSwapped.codeTable.head?.map (·.body) := by
  refine ⟨rfl, ?_⟩
  simp [dupProg, dupProgSwapped, bodyA, bodyB]

/-! ## §6 — `EC1-F08` NESTED: `FirstOrderClosed` is not reachability-closed

`EC1-K12` names "every stored continuation, HANDLER BODY, finalizer, CHILD
BODY, error arm, and race arm". The target's `RawProg` puts every slot in ONE
flat top-level list, and its code bodies are `PProg`, which cannot hold a slot.
So the model cannot express a continuation slot reachable through a code
definition — and the checker built on it checks only depth 1. -/

/-- Minimal extension: a code definition that carries its own slots, which is
what a handler body with a nested resume is. -/
structure NestedCodeDef where
  id : CodeId
  inner : List Slot
  deriving DecidableEq

structure NestedProg where
  codeTable : List NestedCodeDef
  slots : List Slot
  deriving DecidableEq

/-- The target's predicate, transported: top-level slots only. -/
def TopLevelClosed (r : NestedProg) : Prop :=
  ∀ s ∈ r.slots, ∃ d ∈ r.codeTable, d.id = s.code

/-- The predicate `EC1-K12` actually asks for: closure through code bodies too. -/
def ReachablyClosed (r : NestedProg) : Prop :=
  TopLevelClosed r ∧
    ∀ d ∈ r.codeTable, ∀ s ∈ d.inner, ∃ d' ∈ r.codeTable, d'.id = s.code

/-- `EC1-F08`, planted one level down: code 7 is registered, but its body names
code 99, which is not. -/
def f08Nested : NestedProg :=
  { codeTable := [⟨7, [⟨99, []⟩]⟩], slots := [⟨7, []⟩] }

/-- **THE HIT.** The target's closure predicate ACCEPTS a program carrying an
unregistered host callback, because the callback is nested. -/
theorem f08Nested_passes_the_target_predicate : TopLevelClosed f08Nested := by
  intro s hs
  simp only [f08Nested, List.mem_singleton] at hs
  subst hs
  exact ⟨⟨7, [⟨99, []⟩]⟩, by simp [f08Nested], rfl⟩

theorem f08Nested_is_not_reachably_closed : ¬ ReachablyClosed f08Nested := by
  intro h
  obtain ⟨d', hd', hid⟩ := h.2 ⟨7, [⟨99, []⟩]⟩ (by simp [f08Nested]) ⟨99, []⟩
    (by simp)
  simp only [f08Nested, List.mem_singleton] at hd'
  subst hd'
  simp at hid

/-- **THE SEPARATION.** `TopLevelClosed` is strictly weaker than the property
`EC1-K12` states, so the §3 bundle is NOT safe to lift verbatim into
`EC1-D021 ProgramWF` as the report recommends. -/
theorem topLevelClosed_is_strictly_weaker :
    ¬ ∀ r : NestedProg, TopLevelClosed r → ReachablyClosed r :=
  fun h => f08Nested_is_not_reachably_closed
    (h f08Nested f08Nested_passes_the_target_predicate)

/-! ## §7 — `EC1-K12`'s captures half is unchecked

"Every free value of a source lambda admitted by the bridge is named in the
target block's parameter list." The target declares this omitted. The door is
not merely silent about captures: it is PROVABLY blind, accepting any two
programs that differ only there. -/

def capNone : RawProg :=
  { codeTable := [⟨7, bodyA⟩], slots := [⟨7, []⟩] }

def capTwo : RawProg :=
  { codeTable := [⟨7, bodyA⟩], slots := [⟨7, [PIn.lit zeroAddr, PIn.ans 3]⟩] }

/-- **CAPTURE BLINDNESS.** Two distinct raw programs whose slots carry
different captures for the same code are accepted identically. Whatever arity
or shape `bodyA` needs, the door cannot see it. -/
theorem checker_is_capture_blind :
    checkFirstOrder capNone = .ok ()
      ∧ checkFirstOrder capTwo = .ok ()
      ∧ capNone ≠ capTwo := by
  refine ⟨rfl, rfl, ?_⟩
  simp [capNone, capTwo]

/-! ## §8 — the flagged `T005`/`T006` interaction, made concrete

The target flags but does not formalize: "If `check` runs after `normalizeRaw`,
the FIRST condemning slot is first in NORMALIZED order, not source order."
Here is the witness that makes the flag load-bearing. -/

def twoBad : RawProg := { codeTable := [], slots := [⟨7, []⟩, ⟨9, []⟩] }
def twoBadPermuted : RawProg := { codeTable := [], slots := [⟨9, []⟩, ⟨7, []⟩] }

/-- **THE DIAGNOSTIC IS ORDER-DEPENDENT.** Two programs with the same slot SET
and the same code table produce DIFFERENT diagnostics. Any `EC1-T006`
`normalizeRaw` that reorders slots therefore changes `EC1-F08`'s red control,
and `EC1-T013 check_erase`'s byte-exact diagnostic promise (`EC1-F10`: "exact
byte equality and identical diagnostics") is at risk. -/
theorem diagnostic_depends_on_slot_order :
    checkFirstOrder twoBad = .error ⟨7, []⟩
      ∧ checkFirstOrder twoBadPermuted = .error ⟨9, []⟩
      ∧ checkFirstOrder twoBad ≠ checkFirstOrder twoBadPermuted := by
  refine ⟨rfl, rfl, ?_⟩
  simp [checkFirstOrder, twoBad, twoBadPermuted, resolves]

/-! ## §9 — FALSIFIERS THE TARGET SURVIVES

Recorded as evidence, per the breaker brief: a falsifier the proof survives is
evidence, not a finding. -/

def f08 : RawProg := { codeTable := [], slots := [⟨7, []⟩] }

def ok1 : RawProg :=
  { codeTable := [⟨7, [PLine.load (.lit zeroAddr)]⟩]
    slots := [⟨7, [PIn.lit zeroAddr]⟩] }

/-- `EC1-F01` (delete the target definition) as a RED CONTROL on the positive
control: removing `ok1`'s code definition turns the verdict red. The checker is
not trivially accepting. -/
theorem f01_red_control :
    checkFirstOrder ok1 = .ok ()
      ∧ checkFirstOrder { ok1 with codeTable := [] } = .error ⟨7, [PIn.lit zeroAddr]⟩ :=
  ⟨rfl, rfl⟩

/-- NON-VACUITY of `checkFirstOrder_error_condemns`: its hypothesis is
inhabited, so the theorem is not quantifying over nothing. -/
theorem error_condemns_hypothesis_is_inhabited :
    ∃ (r : RawProg) (s : Slot), checkFirstOrder r = .error s :=
  ⟨f08, ⟨7, []⟩, rfl⟩

/-- NON-VACUITY of `checkFirstOrder_rejects`: its hypothesis is inhabited. -/
theorem rejects_hypothesis_is_inhabited :
    ∃ r : RawProg, ¬ FirstOrderClosed r := by
  refine ⟨f08, ?_⟩
  intro h
  obtain ⟨d, hd, _⟩ := h ⟨7, []⟩ (by simp [f08])
  simp [f08] at hd

/-- NON-VACUITY of `checkFirstOrder_ok_iff`: both sides are inhabited, so the
`iff` is not `False ↔ False`. -/
theorem ok_iff_is_two_sided :
    (∃ r : RawProg, checkFirstOrder r = .ok ())
      ∧ (∃ r : RawProg, checkFirstOrder r ≠ .ok ()) :=
  ⟨⟨ok1, rfl⟩, ⟨f08, by simp [checkFirstOrder, f08, resolves]⟩⟩

/-- `EC1-F20` (a pure atom reads a mutable counter) / `R14a`: every carrier and
every checker above is effect-free first-order data OUTSIDE `Prog`. Recorded by
the type: `checkFirstOrder` inhabits `Except Slot Unit`, not any `Prog`. -/
theorem r14a_the_door_is_outside_prog :
    ∀ r : RawProg, (checkFirstOrder r = .ok ()) ∨ (∃ s, checkFirstOrder r = .error s) := by
  intro r
  cases h : checkFirstOrder r with
  | ok u => cases u; exact Or.inl rfl
  | error s => exact Or.inr ⟨s, rfl⟩

/-! ## §10 — receipts -/

#print axioms every_field_is_serializable
#print axioms row_implies_row_survives_any_premise
#print axioms row_survives_any_premise_implies_the_row
#print axioms strictly_stronger_is_actually_equivalent
#print axioms hostFnLine_serializes_the_payload
#print axioms row_is_false_at_the_payload_reading
#print axioms the_row_is_undetermined_not_vacuous
#print axioms third_horn_is_falsity_not_vacuity
#print axioms fnParse_fnFields
#print axioms fnFields_injective
#print axioms decEq_fnField_decides_function_equality
#print axioms dupProg_bodies_differ
#print axioms dupProg_accepted
#print axioms dupProg_is_closed
#print axioms dupProg_resolution_is_ambiguous
#print axioms dupProg_permutation_is_invisible
#print axioms f08Nested_passes_the_target_predicate
#print axioms f08Nested_is_not_reachably_closed
#print axioms topLevelClosed_is_strictly_weaker
#print axioms checker_is_capture_blind
#print axioms diagnostic_depends_on_slot_order
#print axioms f01_red_control
#print axioms error_condemns_hypothesis_is_inhabited
#print axioms rejects_hypothesis_is_inhabited
#print axioms ok_iff_is_two_sided
#print axioms r14a_the_door_is_outside_prog

end EffectCoreV1.AttackT005
