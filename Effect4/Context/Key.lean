import Std

/-!
# First-order context keys

Owner: the environment slice's `L0` identity node, fence `F-KEY` in
`docs/ENVIRONMENT-DAG.md`. Its contract packet is
`test/contracts/environment-context-key.contract.md` and its red battery is
`Effect4Test/Environment/ContextKeyContract.lean`.

A context key is **first-order data**. `ServiceKey` is a `Type` at universe
zero: the ordered pair of a nominal `ServiceName` and a first-order
`ServiceTypeCode`, both single-field carriers over `Nat`, following the flow
slice's `BlockId`/`OperationId`/`AlphabetId`/`DecisionId` convention. No field
of a key is a Lean `Type` and no field is a Lean function, so a key satisfies
the `AGENTS.md` "Representation rules" requirement that canonical program
content be first-order data.

Reading a code as a Lean type is a separate supplied `ServiceUniverse`, in
exactly the position `Effect4.FlowAlphabet` occupies for the flow slice: a
trusted boundary object, never canonical content. This module enforces only
that the *key* carries no universe; keeping a universe out of a downstream
carrier is each downstream packet's own obligation.

What the first-order answer gives up is priced here rather than asserted:
`ServiceUniverse.exists_carrier_collision` proves that two distinct codes may
read as the same Lean type, so type identity never recovers code identity and
no inverse interpretation exists.

This module imports `Std` and nothing else. It states no requirement row law,
no environment admission rule, and no persisted or wire spelling of a key. A
key is an identity plus a code; it is not a service, not a value, and not a
requirement.

The edge `ENV-KEY-INTERP` is left open: every downstream typing statement about
a service value is relative to a supplied `ServiceUniverse`, and nothing here
consumes one. `Context/Service` and `Context/Environment` are the first nodes
that can state what agreement between two universes buys.
-/

namespace Effect4

/--
The nominal identity of a service key.

`Nat` rather than `String` is an ordering decision, not a spelling decision: a
`String` name would require irreflexivity, transitivity, and trichotomy for
`String.lt` from core alone, with no consumer at `L0`, and would import a
persisted spelling question this slice does not own. A wire profile owns tag
strings later.
-/
structure ServiceName where
  value : Nat
deriving DecidableEq, Repr

/--
The first-order code of a service's type.

Nominally distinct from `ServiceName`: a name is not a code, and the two are
never interchangeable at `ServiceKey.mk`. A code is a `Nat`, never a Lean
`Type`, and there is no `ServiceTypeCode.ofType` — codes are not minted from
Lean types.
-/
structure ServiceTypeCode where
  value : Nat
deriving DecidableEq, Repr

/--
A context key: a nominal name paired with a first-order service type code.

The identity is the **pair**, not the name. Two keys may share a name and
differ in code; `ServiceKey.Conflict` names that situation and decides it.
Effect's `Context.Tag` identity is the tag string alone and cannot express the
colliding pair, so no compatibility with it is claimed here.

Field order is `name` before `service` and is frozen by the battery's
`ServiceKey.rec` snapshot.
-/
structure ServiceKey where
  name : ServiceName
  service : ServiceTypeCode
deriving DecidableEq, Repr

namespace ServiceKey

/--
The underlying name-major lexicographic strict order relation on keys.

Name-major is chosen so that nominally equal keys are contiguous in an
ascending row, which is the shape `ServiceKey.Conflict` will be read against at
`Context/Environment`. That is the reason for the choice, not a theorem: no
adjacency result is stated at `L0`.

The order itself is load-bearing and not merely a convenience. `PORT-MANIFEST.md`,
"Canonical row extraction", freezes canonicality as strictly ascending
`List.Pairwise (· < ·)` and records that "Effect4 gains no second canonical
order notion", so a canonical row over keys must cite exactly this relation.
Three order laws alone would not fix it: a service-major or hash-derived order
satisfies them and spells a different ascending row for the same key set.
-/
protected def Lt (a b : ServiceKey) : Prop :=
  a.name.value < b.name.value ∨
    (a.name = b.name ∧ a.service.value < b.service.value)

end ServiceKey

instance : LT ServiceKey where
  lt := ServiceKey.Lt

/--
The key order is decided by structural comparison of two `Nat` fields.

The instance is built from `Nat.decLt` and the derived `DecidableEq
ServiceName`, so it reduces in the kernel; a classically obtained instance
would satisfy the `Decidable` signature while computing nothing.
-/
instance instDecidableLtServiceKey (a b : ServiceKey) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.name.value < b.name.value ∨
    (a.name = b.name ∧ a.service.value < b.service.value)))

namespace ServiceKey

/-- The key order is exactly name-major lexicographic on the two `Nat` fields. -/
theorem lt_iff (a b : ServiceKey) :
    a < b ↔ (a.name.value < b.name.value ∨
      (a.name = b.name ∧ a.service.value < b.service.value)) :=
  Iff.rfl

/-- The key order is irreflexive. -/
theorem lt_irrefl (a : ServiceKey) : ¬ a < a := by
  intro contra
  rcases (lt_iff a a).mp contra with nameLt | ⟨_, serviceLt⟩
  · exact Nat.lt_irrefl _ nameLt
  · exact Nat.lt_irrefl _ serviceLt

/-- The key order is transitive. -/
theorem lt_trans {a b c : ServiceKey} : a < b → b < c → a < c := by
  intro hab hbc
  refine (lt_iff a c).mpr ?_
  rcases (lt_iff a b).mp hab with nameLt | ⟨nameEq, serviceLt⟩ <;>
    rcases (lt_iff b c).mp hbc with nameLt' | ⟨nameEq', serviceLt'⟩
  · exact Or.inl (Nat.lt_trans nameLt nameLt')
  · have step : b.name.value = c.name.value := congrArg ServiceName.value nameEq'
    exact Or.inl (Nat.lt_of_lt_of_le nameLt (Nat.le_of_eq step))
  · have step : a.name.value = b.name.value := congrArg ServiceName.value nameEq
    exact Or.inl (Nat.lt_of_le_of_lt (Nat.le_of_eq step) nameLt')
  · exact Or.inr ⟨Eq.trans nameEq nameEq', Nat.lt_trans serviceLt serviceLt'⟩

/-- The key order is trichotomous, so it is a strict linear order. -/
theorem lt_trichotomy (a b : ServiceKey) : a < b ∨ a = b ∨ b < a := by
  obtain ⟨⟨aName⟩, ⟨aService⟩⟩ := a
  obtain ⟨⟨bName⟩, ⟨bService⟩⟩ := b
  rcases Nat.lt_trichotomy aName bName with nameLt | nameEq | nameGt
  · exact Or.inl (Or.inl nameLt)
  · subst nameEq
    rcases Nat.lt_trichotomy aService bService with serviceLt | serviceEq | serviceGt
    · exact Or.inl (Or.inr ⟨rfl, serviceLt⟩)
    · subst serviceEq
      exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, serviceGt⟩))
  · exact Or.inr (Or.inr (Or.inl nameGt))

/-!
### Standard non-strict order bridge

Everything in this section is derived from `ServiceKey.Lt` above and from
equality of keys. Nothing here introduces a second comparison.
-/

/--
The non-strict key order: strictly below, or equal.

`Std`'s order hierarchy is stated over `LE`, not over `LT`. `Std.IsPreorder`,
`Std.IsPartialOrder`, and `Std.IsLinearOrder` all quantify over `≤`, and
`Std.LawfulOrderLT` exists precisely to demand that a supplied `<` agrees with
that `≤`. `test/contracts/data-row.contract.md` quantifies every row operation
over `Std.IsLinearOrder` and `Std.LawfulOrderLT`, so a canonical row over keys
cannot be spelled from `DecidableEq` and `LT` alone. That packet assigns the
missing instances to this node rather than to the row.

This is **not** a second canonical order. `PORT-MANIFEST.md`, "Canonical row
extraction", records that Effect4 gains no second canonical order notion, so
`Le` is defined from `ServiceKey.Lt` and equality and from nothing else. The
agreement of the two is proved by `ServiceKey.lt_iff_le_not_le` and installed
as the `Std.LawfulOrderLT` instance; it is not asserted, and a consumer that
reads `≤` back through `Std.LawfulOrderLT.lt_iff` recovers exactly the
name-major relation of `lt_iff`.
-/
protected def Le (a b : ServiceKey) : Prop :=
  a < b ∨ a = b

/--
The `LE` instance the hierarchy above is stated over.

This and the five instances below are declared inside the `ServiceKey`
namespace, so every name this section allocates is prefixed by
`Effect4.ServiceKey`.
-/
instance instLE : LE ServiceKey where
  le := ServiceKey.Le

/-- The non-strict key order is exactly the strict key order or equality. -/
theorem le_iff (a b : ServiceKey) : a ≤ b ↔ (a < b ∨ a = b) :=
  Iff.rfl

/--
The non-strict key order is decided by the strict order and the derived
`DecidableEq ServiceKey`.

Built with `inferInstanceAs` over the spelled-out disjunction for the reason
`instDecidableLtServiceKey` gives: only an instance that resolves to computing
core instances reduces in the kernel, which is what lets a ground `≤`
comparison close under `decide`.
-/
instance instDecidableLE (a b : ServiceKey) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a < b ∨ a = b))

/-- The key order is asymmetric: `lt_irrefl` and `lt_trans` taken together. -/
theorem lt_asymm {a b : ServiceKey} (h : a < b) : ¬ b < a :=
  fun reverse => lt_irrefl a (lt_trans h reverse)

/-- The non-strict key order is reflexive. -/
theorem le_refl (a : ServiceKey) : a ≤ a :=
  (le_iff a a).mpr (Or.inr rfl)

/-- The non-strict key order is transitive. -/
theorem le_trans {a b c : ServiceKey} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  refine (le_iff a c).mpr ?_
  rcases (le_iff a b).mp hab with ltAB | eqAB
  · rcases (le_iff b c).mp hbc with ltBC | eqBC
    · exact Or.inl (lt_trans ltAB ltBC)
    · exact Or.inl (eqBC ▸ ltAB)
  · exact eqAB ▸ (le_iff b c).mp hbc

/-- The non-strict key order is antisymmetric. -/
theorem le_antisymm {a b : ServiceKey} (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  rcases (le_iff a b).mp hab with ltAB | eqAB
  · rcases (le_iff b a).mp hba with ltBA | eqBA
    · exact absurd ltBA (lt_asymm ltAB)
    · exact eqBA.symm
  · exact eqAB

/-- The non-strict key order is total; this is `lt_trichotomy` reread over `≤`. -/
theorem le_total (a b : ServiceKey) : a ≤ b ∨ b ≤ a := by
  rcases lt_trichotomy a b with ltAB | eqAB | ltBA
  · exact Or.inl ((le_iff a b).mpr (Or.inl ltAB))
  · exact Or.inl ((le_iff a b).mpr (Or.inr eqAB))
  · exact Or.inr ((le_iff b a).mpr (Or.inl ltBA))

/--
The strict and non-strict key orders agree in exactly `Std`'s sense.

This is the obligation `Std.LawfulOrderLT` states, and proving it is what makes
the added `≤` a reading of the frozen `<` rather than an independent notion.
-/
theorem lt_iff_le_not_le (a b : ServiceKey) : a < b ↔ a ≤ b ∧ ¬ b ≤ a := by
  constructor
  · intro ltAB
    refine ⟨(le_iff a b).mpr (Or.inl ltAB), ?_⟩
    intro hba
    rcases (le_iff b a).mp hba with ltBA | eqBA
    · exact lt_asymm ltAB ltBA
    · exact lt_irrefl a (eqBA ▸ ltAB)
  · intro both
    rcases (le_iff a b).mp both.left with ltAB | eqAB
    · exact ltAB
    · exact absurd ((le_iff b a).mpr (Or.inr eqAB.symm)) both.right

/-- Reflexivity and transitivity of `≤`, which is `Std.IsPreorder`. -/
instance instIsPreorder : Std.IsPreorder ServiceKey where
  le_refl := ServiceKey.le_refl
  le_trans _ _ _ := ServiceKey.le_trans

/-- Antisymmetry of `≤` on top of the preorder, which is `Std.IsPartialOrder`. -/
instance instIsPartialOrder : Std.IsPartialOrder ServiceKey where
  le_antisymm _ _ := ServiceKey.le_antisymm

/--
Totality of `≤` on top of the partial order, which is `Std.IsLinearOrder`.

`Std.IsLinearOrder` also lists `Std.IsLinearPreorder` as a parent, but its
constructor takes only the partial order and totality; the linear preorder is
recovered from those, so no further instance is owed.
-/
instance instIsLinearOrder : Std.IsLinearOrder ServiceKey where
  le_total := ServiceKey.le_total

/-- The frozen `<` is the strict order of the `≤` above. -/
instance instLawfulOrderLT : Std.LawfulOrderLT ServiceKey where
  lt_iff := ServiceKey.lt_iff_le_not_le

/--
Two keys are in nominal conflict when they share a name and differ in code.

This is representable and decidable at `L0` so `Context/Environment` has a
vocabulary it does not have to mint, and so a later admission clause stays
executable. Whether an environment may *hold* a conflicting pair is that
node's ruling, not this one's.
-/
def Conflict (a b : ServiceKey) : Prop :=
  a.name = b.name ∧ a.service ≠ b.service

/-- Nominal conflict is decided by the two derived `DecidableEq` instances. -/
instance instDecidableConflict (a b : ServiceKey) : Decidable (Conflict a b) :=
  inferInstanceAs (Decidable (a.name = b.name ∧ a.service ≠ b.service))

/-- Nominal conflict is exactly name agreement together with code disagreement. -/
theorem conflict_iff (a b : ServiceKey) :
    Conflict a b ↔ (a.name = b.name ∧ a.service ≠ b.service) :=
  Iff.rfl

end ServiceKey

/--
A supplied reading of first-order service type codes as Lean types.

This is a trusted boundary object of exactly the kind `Effect4.FlowAlphabet`
already is in `Effect4/Flow/Block.lean`, whose docstring records that executable
lookup stays in the trusted semantic environment "so no host function enters
canonical flow content". The same sentence applies here: a universe is a Lean
function, it is deliberately outside the first-order frame, and it may not be
stored as canonical content by any consumer.

There is no canonical universe. "The type of a service" is defined only
relative to a supplied `U`, and nothing here forces two callers to agree on
one; that agreement is the open `ENV-KEY-INTERP` edge. There is also no
`ServiceUniverse.code`: `ServiceUniverse.exists_carrier_collision` shows no
faithful inverse can exist.
-/
structure ServiceUniverse.{u} where
  Carrier : ServiceTypeCode → Type u

namespace ServiceKey

/--
The Lean type a key's service value inhabits, relative to a supplied universe.

Selection is by the **code**, never by the nominal name. A name-keyed
interpretation is the shape reached for when trying to make `ServiceName`
behave like Effect's tag, and it is excluded here and by `carrier_def`.
-/
def Carrier.{u} (U : ServiceUniverse.{u}) (k : ServiceKey) : Type u :=
  U.Carrier k.service

/-- A key's carrier is selected by its service code. -/
theorem carrier_def.{u} (U : ServiceUniverse.{u}) (k : ServiceKey) :
    Carrier U k = U.Carrier k.service :=
  rfl

/--
The only transport this node supplies between key carriers.

The equality of codes is an explicit argument, so no service value crosses
codes without a proof, and there is no `ServiceKey.cast`. The signature takes
no instance argument, so a default value cannot be produced in place of the
transported one.
-/
def transport.{u} (U : ServiceUniverse.{u}) {a b : ServiceKey}
    (h : a.service = b.service) (v : Carrier U a) : Carrier U b :=
  Eq.mp (congrArg U.Carrier h) v

/-- Transport along reflexivity is the identity. -/
theorem transport_rfl.{u} (U : ServiceUniverse.{u}) (k : ServiceKey)
    (v : Carrier U k) :
    transport U (rfl : k.service = k.service) v = v :=
  rfl

end ServiceKey

/--
Distinct service type codes may read as the same Lean type.

This is the price of the first-order answer, stated as a theorem rather than as
prose: type identity never recovers code identity, so no inverse interpretation
`Type → ServiceTypeCode` exists and every consumer must route through the code.
A `ServiceUniverse` constrained to an injective `Carrier` would refute this, and
that constrained design is exactly the one under which a consumer could recover
a code from a type.

The witness is deliberately trivial — a constant carrier — because triviality is
the point: nothing in the design constrains a universe to be injective.
-/
theorem ServiceUniverse.exists_carrier_collision :
    ∃ (U : ServiceUniverse.{0}) (a b : ServiceTypeCode),
      a ≠ b ∧ U.Carrier a = U.Carrier b :=
  ⟨⟨fun _ => Unit⟩, ⟨0⟩, ⟨1⟩, by decide, rfl⟩

end Effect4
