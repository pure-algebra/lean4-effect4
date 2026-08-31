import Cas.Lang.Defun

/-!
# Effect Core v1 — scout probe for `EC1-T005` (`serialized_fields_first_order`)

Run from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s1/scout-T005.lean
```

Scouting only. Nothing here is proposed for `library/` or for
`formal/effect-core-v1/EffectCore/Syntax/Raw.lean`, which is still an empty
reserved stub. `RawProgram` (`EC1-D020`), `SerializableField`, and
`FunctionVal` exist NOWHERE in the tree — `grep -rn 'SerializableField\|FunctionVal' .`
returns only `PROOF-DAG.md:197` itself and its two worktree copies. So §2–§3
below use a THROWAWAY scratch carrier whose only job is to decide the SHAPE of
the row's statement. It mints nothing that competes with an estate type: the
real serializable carrier used in §1 is the estate's own `PLine`/`PIn`
(`Cas/Lang/Defun.lean:167,180`), per `EC1-XT018` ("no second CAS serialization
is permitted").

The DAG's schematic signature is

    serialized_fields_first_order : SerializableField raw field -> not FunctionVal field

Three findings:

* §1 the estate's actual serializable carrier is first-order by CONSTRUCTION —
  `PIn`/`PLine` derive `DecidableEq`, which a carrier with a host-function
  field cannot;
* §2 therefore the row is a TAUTOLOGY in the exact sense `PROOF-DAG.md:207`
  already used to delete two rows: it is provable with `SerializableField`
  replaced by ANY relation whatsoever, including `fun _ _ => True`. The premise
  is dead weight, so the conclusion says nothing about `raw`;
* §3 the reading under which the row has content — the one `ALGEBRA.md:242`
  requires so that `EC1-F08` has an input at all — is not about function VALUES
  but about a `CodeId` slot that resolves to no registered code definition.
  Under that reading a raw witness IS representable, so the premise-free
  property is FALSE on raw programs and true only under a checker premise.
  §3.3 proves the repaired `iff` in the estate's own `checkRefs_ok_iff` shape.

Checks OMITTED: no claim is made here about `RawProgram`'s eventual field
universe, about the TypeScript source hoover's ability to detect a host
callback before decoding, or about `EC1-F08`'s executable form. §1 does not
prove that `Prog` has no `DecidableEq` — a non-existence-of-instance claim is
not a theorem; the elaboration observation is reported in prose only.
-/

namespace EffectCoreScoutT005

open Cas.Lang
open Cas (Bytes)

/-! ## §1 — the estate's real serializable carrier is first-order by construction

`Cas/Lang/Prog.lean:27` `Prog.vis` holds `k : S.Ans op → Prog S A` — a genuine
host function. `Cas/Lang/Defun.lean:167` `PIn` and `:180` `PLine` hold no such
field, and both `deriving DecidableEq`. That derived instance is the mechanized
content of "first-order": it is what decides `l = l'` without `Classical.choice`,
and it is exactly what a carrier with a function field over an infinite answer
domain cannot supply.

OBSERVATION, NOT A THEOREM: `example : DecidableEq (Prog CasSig Cas.Addr32) :=
inferInstance` fails to elaborate ("failed to synthesize"). Failure to
synthesize is not a proof of non-existence, so it is recorded here and used
nowhere below. -/

/-- Equality of the estate's serializable code points is decided, not assumed.
The `dite` below resolves the DERIVED `DecidableEq PLine`; the axiom receipt is
the evidence that no choice principle was needed. -/
theorem pline_equality_is_decided (l l' : PLine) : l = l' ∨ l ≠ l' :=
  if h : l = l' then Or.inl h else Or.inr h

/-- Same at the operand carrier. -/
theorem pin_equality_is_decided (i j : PIn) : i = j ∨ i ≠ j :=
  if h : i = j then Or.inl h else Or.inr h

/-! ## §2 — the tautology horn

The field universe a serialization walk over `PLine` can yield. Every arm is a
first-order estate type; there is no arm a `FunctionVal` predicate could be
true of, because there is no arm holding a function. -/

/-- THROWAWAY: what one step of a serialization walk over a real `PLine`
yields. Scratch only — it is not a proposal for `EC1-D020`'s field universe. -/
inductive RawField where
  | u8 (b : UInt8)
  | payload (bs : Bytes)
  | operand (i : PIn)
  deriving DecidableEq

/-- The walk itself, over the estate's real `PLine`. -/
def PLine.fields : PLine → List RawField
  | .put v t payload refs =>
      .u8 v :: .u8 t :: .payload payload ::
        refs.flatMap (fun r => [RawField.u8 r.1, RawField.operand r.2])
  | .load src => [.operand src]

/-- `SerializableField raw field`, spelled at the estate's carrier. -/
def SerializableField (raw : PLine) (field : RawField) : Prop :=
  field ∈ PLine.fields raw

/-- `FunctionVal`, in the only way it can honestly be written over a
first-order field universe: no constructor holds a function, so the predicate
is empty on every arm. Writing it any other way would be writing a DIFFERENT
predicate — see §3. -/
def FunctionVal : RawField → Prop
  | .u8 _ => False
  | .payload _ => False
  | .operand _ => False

/-- The DAG row, proved. -/
theorem serialized_fields_first_order (raw : PLine) (field : RawField)
    (_h : SerializableField raw field) : ¬ FunctionVal field := by
  cases field <;> exact not_false

/-- THE TAUTOLOGY WITNESS. The row is provable for EVERY choice of the
`SerializableField` relation — including `fun _ _ => True`, including one that
holds of no pair at all. The premise is never eliminated, so the row's
conclusion carries no information about `raw`. This is precisely the criterion
`PROOF-DAG.md:207` applied when it deleted `exists! v, evalPure e env = v` and
the same-input function-equality forms. -/
theorem row_survives_any_premise (P : PLine → RawField → Prop) :
    ∀ raw field, P raw field → ¬ FunctionVal field := by
  intro _ field _
  cases field <;> exact not_false

/-- Two instantiations, to make the point concrete: the row holds with the
premise replaced by `True` and with it replaced by `False`. -/
theorem row_holds_with_premise_True :
    ∀ raw field, (fun (_ : PLine) (_ : RawField) => True) raw field →
      ¬ FunctionVal field :=
  row_survives_any_premise _

theorem row_holds_with_premise_False :
    ∀ raw field, (fun (_ : PLine) (_ : RawField) => False) raw field →
      ¬ FunctionVal field :=
  row_survives_any_premise _

/-- And the same for the genuine walk — the intended reading is the `True`
instance up to logical strength. -/
theorem row_is_the_True_instance :
    (∀ raw field, SerializableField raw field → ¬ FunctionVal field)
      ↔ (∀ raw field, (fun (_ : PLine) (_ : RawField) => True) raw field →
            ¬ FunctionVal field) :=
  ⟨fun _ => row_holds_with_premise_True,
   fun _ raw field h => serialized_fields_first_order raw field h⟩

/-! ## §3 — the contentful horn, and why it is not the row as written

`ALGEBRA.md:224` says `EC1-A11 RawProgram` "contains only serializable
first-order data"; eighteen lines later, `ALGEBRA.md:242-244` says
"host-function payloads ... are deliberately representable". Both are true at
once only under `EC1-K12`'s spelling (`CONTRACT-PACKET.md:353`): a stored
continuation is "a `CodeId` plus explicit captures", so a raw program never
HOLDS a function — it can only NAME one that no `codeTable` row defines.

That is the property `EC1-F08` attacks ("put an unregistered host callback in
raw content"), and it is not `¬ FunctionVal field`. It is slot resolution. The
scratch carrier below is the minimal shape that can state it. -/

abbrev CodeId := Nat

/-- THROWAWAY: a registered first-order code definition, body reusing the
estate's `PProg` per `EC1-XT018`/`EC1-F76`. -/
structure RawCodeDef where
  id : CodeId
  body : PProg
  deriving DecidableEq

/-- THROWAWAY: `EC1-K12`'s continuation slot — a `CodeId` plus explicit
captures, never a function. -/
structure Slot where
  code : CodeId
  captures : List PIn
  deriving DecidableEq

/-- THROWAWAY: the two `EC1-A11` tables the property actually relates. -/
structure RawProg where
  codeTable : List RawCodeDef
  slots : List Slot
  deriving DecidableEq

/-- The property `EC1-F08` attacks: a slot naming no registered definition. -/
def HostCallback (r : RawProg) (s : Slot) : Prop :=
  ∀ d ∈ r.codeTable, d.id ≠ s.code

/-- `EC1-K12` as a property of a raw program. -/
def FirstOrderClosed (r : RawProg) : Prop :=
  ∀ s ∈ r.slots, ∃ d ∈ r.codeTable, d.id = s.code

/-! ### §3.1 — `EC1-F08`'s input is representable, so the premise-free property
is FALSE on raw programs -/

/-- One slot, empty code table: the unregistered host callback. -/
def f08 : RawProg := { codeTable := [], slots := [⟨7, []⟩] }

theorem f08_carries_an_unregistered_callback :
    ∃ s ∈ f08.slots, HostCallback f08 s := by
  refine ⟨⟨7, []⟩, by simp [f08], ?_⟩
  intro d hd
  simp [f08] at hd

/-- THE FALSIFICATION. Stated without a checker premise, `EC1-K12` is false on
raw content — by the packet's own design (`ALGEBRA.md:242`), because otherwise
`EC1-F08` would have no input to feed. -/
theorem firstOrderClosed_is_false_on_raw : ¬ FirstOrderClosed f08 := by
  intro h
  obtain ⟨d, hd, _⟩ := h ⟨7, []⟩ (by simp [f08])
  simp [f08] at hd

/-! ### §3.2 — a raw program that is NOT a counterexample, for contrast -/

def ok1 : RawProg :=
  { codeTable := [⟨7, [.load (.lit ⟨List.replicate 32 0, by simp⟩)]⟩]
    slots := [⟨7, []⟩] }

theorem ok1_is_closed : FirstOrderClosed ok1 := by
  intro s hs
  simp [ok1] at hs
  subst hs
  exact ⟨⟨7, [.load (.lit ⟨List.replicate 32 0, by simp⟩)]⟩, by simp [ok1], rfl⟩

/-! ### §3.3 — the repaired row, in the estate's own shape

`Cas/Core/Admission.lean:60` `checkRefs_ok_iff : checkRefs σ rs = .ok () ↔
RefsOk σ rs` is the estate's decidable-clause-plus-iff shape, and it is the
shape this row wants one level up. Both halves in one theorem; the decision
procedure is the content, and `EC1-F08` becomes runnable because the checker
returns the offending slot. -/

def resolves (r : RawProg) (s : Slot) : Bool :=
  r.codeTable.any (fun d => d.id == s.code)

def checkFirstOrder (r : RawProg) : Bool :=
  r.slots.all (fun s => resolves r s)

/-- THE STATEMENT THAT SHOULD BE PROVED. Decidable soundness AND completeness
for `EC1-K12`'s first-order-closure clause. -/
theorem checkFirstOrder_iff (r : RawProg) :
    checkFirstOrder r = true ↔ FirstOrderClosed r := by
  simp only [checkFirstOrder, resolves, FirstOrderClosed, List.all_eq_true,
    List.any_eq_true, beq_iff_eq]

/-- The diagnostic form `EC1-F08` names: the checker returns the slot. -/
def diagnose (r : RawProg) : Except Slot Unit :=
  match r.slots.find? (fun s => !resolves r s) with
  | some s => .error s
  | none => .ok ()

/-- `EC1-F08` observed: the non-first-order-field diagnostic, at the exact
slot. -/
theorem f08_diagnostic : diagnose f08 = .error ⟨7, []⟩ := rfl

theorem ok1_diagnostic : diagnose ok1 = .ok () := rfl

/-- And the checker agrees with §3.1/§3.2. -/
theorem f08_check_false : checkFirstOrder f08 = false := rfl

theorem ok1_check_true : checkFirstOrder ok1 = true := rfl

/-! ## §4 — receipts -/

#print axioms pline_equality_is_decided
#print axioms pin_equality_is_decided
#print axioms serialized_fields_first_order
#print axioms row_survives_any_premise
#print axioms row_holds_with_premise_True
#print axioms row_holds_with_premise_False
#print axioms row_is_the_True_instance
#print axioms f08_carries_an_unregistered_callback
#print axioms firstOrderClosed_is_false_on_raw
#print axioms ok1_is_closed
#print axioms checkFirstOrder_iff
#print axioms f08_diagnostic
#print axioms ok1_diagnostic
#print axioms f08_check_false
#print axioms ok1_check_true

end EffectCoreScoutT005
