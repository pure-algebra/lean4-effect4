/-
Contract packet: `test/contracts/environment-context-key.contract.md`

Breaker-owned red battery for environment-slice node L0, fence `F-KEY`
(`Effect4/Context/Key.lean`). The implementation phase must not edit this file.
It is red until the frozen context-key declarations exist.

Every obligation is ascribed at its exact proposition and supplied by name with
`@`, so a declaration that carries the frozen name but a weaker statement does
not satisfy the battery. Names are written fully qualified rather than through
`open Effect4`, because during the red phase `Effect4/Context/Key.lean` is an
empty stub that opens no namespace, and `open` of an absent namespace would
produce a failure that is not an unresolved frozen name.

Every unresolved name costs one diagnostic while this battery is red, and Lean
stops a file at 100. An in-file `set_option maxErrors` does not lift that limit,
so the obligation set below is deliberately kept free of redundant ascriptions:
at 93 red diagnostics nothing is truncated, and a later revision that adds
checks must re-measure rather than assume.
-/

import Effect4.Machine.Key

namespace Test.Environment.ContextKeyContract

universe u

/-!
## D0 — nominal identities

`ServiceName` and `ServiceTypeCode` are first-order single-field carriers over
`Nat`, matching the flow slice's `BlockId`/`OperationId`/`AlphabetId`/
`DecisionId` convention. `mk` ascribed at `Nat → _` fixes the field count and
type, and the `value` projection fixes its name, so a carrier that gains a
second field or a `Type`-valued one fails here even when every theorem below
still holds. Only `ServiceKey` needs a recursor snapshot, because it is the only
one of the four structures frozen here with fields that can be permuted.

`Repr` is required of `ServiceKey` alone; the component instances exist so that
one derives, and are not separately frozen.
-/

section NominalIdentities

#check (@Effect4.ServiceName : Type)
#check (@Effect4.ServiceName.mk : Nat → Effect4.ServiceName)
#check (@Effect4.ServiceName.value : Effect4.ServiceName → Nat)
#synth DecidableEq Effect4.ServiceName

#check (@Effect4.ServiceTypeCode : Type)
#check (@Effect4.ServiceTypeCode.mk : Nat → Effect4.ServiceTypeCode)
#check (@Effect4.ServiceTypeCode.value : Effect4.ServiceTypeCode → Nat)
#synth DecidableEq Effect4.ServiceTypeCode

end NominalIdentities

/-!
## D1 — the key carrier (ENSURES 1, ENSURES 2)

`E4-ENV-CE-001`. The ascription `@Effect4.ServiceKey : Type` is the load-bearing
exclusion of the type-indexed answer: a `ServiceKey : Type u → Type` fails it
by arity, and a `ServiceKey.{u}` carrying a `Type u` field fails it because such
a structure lives in `Type (u + 1)`, which cannot unify with `Type 0`.

`DecidableEq` alone does **not** exclude the type-indexed answer — a family
`Key : Type u → Type` can have `DecidableEq (Key α)` at every index. It
excludes a key that stores a Lean function or a `Type` at all. The two
obligations are listed separately because they forbid different things, not
because either implies the other.
-/

section KeyCarrier

#check (@Effect4.ServiceKey : Type)
#check (@Effect4.ServiceKey.mk :
  Effect4.ServiceName → Effect4.ServiceTypeCode → Effect4.ServiceKey)
#check (@Effect4.ServiceKey.name : Effect4.ServiceKey → Effect4.ServiceName)
#check (@Effect4.ServiceKey.service :
  Effect4.ServiceKey → Effect4.ServiceTypeCode)
#synth DecidableEq Effect4.ServiceKey
#synth Repr Effect4.ServiceKey

#check (@Effect4.ServiceKey.rec.{u} :
  {motive : Effect4.ServiceKey → Sort u} →
  ((name : Effect4.ServiceName) → (service : Effect4.ServiceTypeCode) →
    motive (Effect4.ServiceKey.mk name service)) →
  (t : Effect4.ServiceKey) → motive t)

end KeyCarrier

/-!
## D2 — decidable strict order (ENSURES 3 through 7)

`E4-ENV-CE-004` and `E4-ENV-CE-005`. `lt_iff` pins the relation itself, so no
other strict linear order — service-major, reversed, or hash-derived —
satisfies this section. `lt_irrefl`, `lt_trans`, and `lt_trichotomy` are
derivable from `lt_iff` together with the corresponding `Nat` facts; they are
listed separately because they are the three statements a canonical ascending
row cites, and because they survive a later reformulation of `lt_iff`.

The four ground examples are decided in the kernel. They close the loophole a
`Decidable` instance obtained classically would leave open, and the second one
pins the name-major direction independently of `lt_iff`: under a service-major
order it is false.
-/

section Order

#synth LT Effect4.ServiceKey

example (a b : Effect4.ServiceKey) : Decidable (a < b) := inferInstance

#check (@Effect4.ServiceKey.lt_iff :
  forall a b : Effect4.ServiceKey,
    a < b ↔ (a.name.value < b.name.value ∨
      (a.name = b.name ∧ a.service.value < b.service.value)))

#check (@Effect4.ServiceKey.lt_irrefl :
  forall a : Effect4.ServiceKey, ¬ a < a)

#check (@Effect4.ServiceKey.lt_trans :
  forall {a b c : Effect4.ServiceKey}, a < b → b < c → a < c)

#check (@Effect4.ServiceKey.lt_trichotomy :
  forall a b : Effect4.ServiceKey, a < b ∨ a = b ∨ b < a)

example : (⟨⟨0⟩, ⟨0⟩⟩ : Effect4.ServiceKey) < ⟨⟨0⟩, ⟨1⟩⟩ := by decide
example : (⟨⟨0⟩, ⟨9⟩⟩ : Effect4.ServiceKey) < ⟨⟨1⟩, ⟨0⟩⟩ := by decide
example : ¬ ((⟨⟨1⟩, ⟨0⟩⟩ : Effect4.ServiceKey) < ⟨⟨0⟩, ⟨9⟩⟩) := by decide
example : ¬ ((⟨⟨0⟩, ⟨0⟩⟩ : Effect4.ServiceKey) < ⟨⟨0⟩, ⟨0⟩⟩) := by decide

end Order

/-!
## D3 — nominal collision (ENSURES 8, ENSURES 9)

`E4-ENV-CE-002`. The identity of a key is the whole pair, so two keys may share
a name and still differ. `conflict_iff` names that situation and decomposes it
onto the service code; the ground witnesses exhibit one conflicting pair and
two non-conflicting pairs, and the final example states the same fact without
`Conflict` at all, so a builder cannot satisfy this section by making
`Conflict` vacuous.

This section rules that nominal collision is **representable** at L0. It does
not rule on whether an environment may hold a colliding pair; that is the
`Context/Environment` node's obligation.
-/

section NominalCollision

#check (@Effect4.ServiceKey.Conflict :
  Effect4.ServiceKey → Effect4.ServiceKey → Prop)

example (a b : Effect4.ServiceKey) :
    Decidable (Effect4.ServiceKey.Conflict a b) := inferInstance

#check (@Effect4.ServiceKey.conflict_iff :
  forall a b : Effect4.ServiceKey,
    Effect4.ServiceKey.Conflict a b ↔
      (a.name = b.name ∧ a.service ≠ b.service))

example : Effect4.ServiceKey.Conflict ⟨⟨0⟩, ⟨0⟩⟩ ⟨⟨0⟩, ⟨1⟩⟩ := by decide
example : ¬ Effect4.ServiceKey.Conflict ⟨⟨0⟩, ⟨0⟩⟩ ⟨⟨1⟩, ⟨0⟩⟩ := by decide
example : ¬ Effect4.ServiceKey.Conflict ⟨⟨0⟩, ⟨0⟩⟩ ⟨⟨0⟩, ⟨0⟩⟩ := by decide
example : (⟨⟨0⟩, ⟨0⟩⟩ : Effect4.ServiceKey) ≠ ⟨⟨0⟩, ⟨1⟩⟩ := by decide

end NominalCollision

/-!
## D4 — the interpretation (ENSURES 10 through 13)

`E4-ENV-CE-003` and `E4-ENV-CE-006`. A `ServiceUniverse` is the trusted,
supplied reading of first-order service type codes as Lean types, in exactly
the position `FlowAlphabet` occupies for the flow slice. It is a boundary
object, not canonical content, and the `ServiceKey.rec` snapshot above is what
keeps it out of the key.

`carrier_def` pins that the carrier is selected by the **code**, so a name-keyed
interpretation fails. `transport` is the only transport this packet supplies
and its equality proof is an explicit argument, so no value crosses codes
without one; `transport_rfl` forces it to be the identity at reflexivity and
its ascribed signature forbids adding an instance argument that would let a
default value stand in for the transported one.

`exists_carrier_collision` is the price of the first-order answer, stated as a
theorem rather than as prose: distinct codes may read as the same Lean type, so
type identity never recovers code identity, and no inverse interpretation
exists to be relied on.
-/

section Interpretation

#check (@Effect4.ServiceUniverse.{u} : Type (u + 1))
#check (@Effect4.ServiceUniverse.mk.{u} :
  (Effect4.ServiceTypeCode → Type u) → Effect4.ServiceUniverse.{u})
#check (@Effect4.ServiceUniverse.Carrier.{u} :
  Effect4.ServiceUniverse.{u} → Effect4.ServiceTypeCode → Type u)

#check (@Effect4.ServiceKey.Carrier.{u} :
  Effect4.ServiceUniverse.{u} → Effect4.ServiceKey → Type u)

#check (@Effect4.ServiceKey.carrier_def.{u} :
  forall (U : Effect4.ServiceUniverse.{u}) (k : Effect4.ServiceKey),
    Effect4.ServiceKey.Carrier U k = U.Carrier k.service)

#check (@Effect4.ServiceKey.transport.{u} :
  (U : Effect4.ServiceUniverse.{u}) → {a b : Effect4.ServiceKey} →
    a.service = b.service →
    Effect4.ServiceKey.Carrier U a → Effect4.ServiceKey.Carrier U b)

#check (@Effect4.ServiceKey.transport_rfl.{u} :
  forall (U : Effect4.ServiceUniverse.{u}) (k : Effect4.ServiceKey)
    (v : Effect4.ServiceKey.Carrier U k),
    Effect4.ServiceKey.transport U (rfl : k.service = k.service) v = v)

#check (@Effect4.ServiceUniverse.exists_carrier_collision :
  ∃ (U : Effect4.ServiceUniverse.{0}) (a b : Effect4.ServiceTypeCode),
    a ≠ b ∧ U.Carrier a = U.Carrier b)

end Interpretation

/-!
## Enforcement by absence

Each guard below asserts only that the named member does not resolve. The
expected text is `Unknown` rather than `Unknown constant`, because Lean reports
an unresolved name two ways: `Unknown identifier` while no prefix of the name
exists, which is the red-phase state of this file, and `Unknown constant` once
the enclosing declaration exists and only the member is missing, which is the
implemented state. Both spellings contain `Unknown`; pinning either one alone
would make this section fail in one of the two phases for a reason that has
nothing to do with the attacked design.

These are name-level guards and are defense in depth. The load-bearing
exclusions are the ascriptions named beside each one.
-/

section EnforcementByAbsence

-- The key stores no Lean type. Carried by `@Effect4.ServiceKey : Type` and the
-- `ServiceKey.rec` snapshot.
/--
error: Unknown
-/
#guard_msgs(error, substring := true) in
#check (@Effect4.ServiceKey.Service)

-- The key does not embed its own interpretation. Carried by the same two.
/--
error: Unknown
-/
#guard_msgs(error, substring := true) in
#check (@Effect4.ServiceKey.universe)

-- No proof-free transport between service carriers. Carried by the ascribed
-- signature of `Effect4.ServiceKey.transport`.
/--
error: Unknown
-/
#guard_msgs(error, substring := true) in
#check (@Effect4.ServiceKey.cast)

-- A service type code is not minted from a Lean type. Carried by
-- `@Effect4.ServiceTypeCode.mk : Nat → Effect4.ServiceTypeCode` and the
-- `value` projection ascription.
/--
error: Unknown
-/
#guard_msgs(error, substring := true) in
#check (@Effect4.ServiceTypeCode.ofType)

-- There is no inverse interpretation. Carried by
-- `Effect4.ServiceUniverse.exists_carrier_collision`, which makes any such
-- function unimplementable as a faithful inverse.
/--
error: Unknown
-/
#guard_msgs(error, substring := true) in
#check (@Effect4.ServiceUniverse.code)

end EnforcementByAbsence

end Test.Environment.ContextKeyContract
