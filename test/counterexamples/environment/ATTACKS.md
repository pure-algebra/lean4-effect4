# Environment slice attacks

Packet: `test/contracts/environment-context-key.contract.md`

Battery: `Effect4Test/Environment/ContextKeyContract.lean`

These are durable semantic attacks on the environment slice. They are retained
after the implementation turns the breaker battery green.

Rows `E4-ENV-CE-001` through `E4-ENV-CE-006` belong to node `L0`
(`Effect4/Context/Key.lean`, fence `F-KEY`) in `docs/ENVIRONMENT-DAG.md`. Later
nodes take later IDs; none of these six is discharged by a later node without
being restated here.

## Type-indexed key — `E4-ENV-CE-001`

The attacked design makes the key a family, `Key : Type u → Type`, or a
structure with a `Type u` field, so that a key carries the Lean type of its
service and `Environment` becomes a dependent map.

It is superficially the stronger design: `get : Environment → Key α → Option α`
is well typed by construction. It fails for four reasons that are not about
taste.

- A key is canonical content. `docs/ENVIRONMENT-DAG.md` makes a requirement a
  row over keys, and a Lean `Type` inside canonical content is what `AGENTS.md`,
  "Representation rules", forbids.
- `PORT-MANIFEST.md`, "Canonical row extraction", freezes canonical row order as
  strictly ascending. Ordering keys across type indices means ordering Lean
  types, which is not available.
- Equality of environments reduces to equality of keys, which under a type index
  is equality of `Type`s. Lean does not decide it, so the design imports
  heterogeneous-equality machinery this repository does not have.
- Recovering the index of a stored entry needs an injectivity for type
  constructors that Lean does not provide, so the recovery is done by an added
  cast or axiom outside the allowlist.

The battery excludes it with the ascription `@Effect4.ServiceKey : Type` and the
exact `Effect4.ServiceKey.rec` snapshot. `DecidableEq` alone does **not** exclude
it — a family can have `DecidableEq (Key α)` at every index — and the packet
says so rather than letting the instance stand in for the argument.

Compile-negatives on `ServiceKey.Service` and `ServiceKey.universe` are
defense in depth on top of the ascription, not the exclusion itself.

## Name-determines-service — `E4-ENV-CE-002`

The attacked design treats a key's nominal name as its identity, so two keys
with the same name are the same key and the service type is a function of the
name. This is Effect's `Context.Tag` model, where the tag string is the whole
identity.

Under the first-order answer, the identity is the pair. Two keys may share a
name and differ in code, and that situation has to be nameable and decidable
before `Context/Environment` can rule on it. Collapsing onto the name instead
makes the situation unspellable, so the environment node would have no witness
to test its own rule against.

The retained witnesses are `ServiceKey.conflict_iff`, one conflicting ground
pair, two non-conflicting ground pairs, and the same-name disequality stated
without `Conflict` at all. That last one matters: without it a builder could
satisfy the row with a `Conflict` that is everywhere false.

This row asserts only that collision is **representable**. Whether an
environment may hold a colliding pair is the `Context/Environment` node's
ruling, and this row does not pre-empt it.

## Faithful code — `E4-ENV-CE-003`

The attacked design assumes a service type code names exactly one Lean type, so
that equal carriers imply equal codes and an inverse interpretation
`Type → ServiceTypeCode` could exist. Anything that looks up a service by
matching on the carrier type relies on this.

It is false, and the packet proves it false rather than warning about it:
`ServiceUniverse.exists_carrier_collision` exhibits a universe and two distinct
codes reading as the same type. The witness is deliberately trivial — a constant
carrier — because triviality is the point: nothing in the design constrains a
universe to be injective, so every consumer must route through the code.

The compile-negative on `ServiceUniverse.code` records the absent inverse.

## Order-free key — `E4-ENV-CE-004`

The attacked statement is the edge description in `docs/ENVIRONMENT-DAG.md`
itself: that the `Context/Key → Context/Requirement` edge carries "key identity
and `DecidableEq`".

`DecidableEq` is not enough. A requirement is a row over keys, and
`PORT-MANIFEST.md`, "Canonical row extraction", freezes canonicality as
`List.Pairwise (· < ·)` and records that "Effect4 gains no second canonical
order notion". With only `DecidableEq` available at `L0`, the requirement node
must either mint its own order — a second canonical-order notion — or fall back
to authored insertion order, which the same section condemns: order-preserving
dedup is not normalization.

The forced repair is to freeze the order at the key node, where it belongs. The
retained obligations are `ServiceKey.lt_iff`, `lt_irrefl`, `lt_trans`,
`lt_trichotomy`, a synthesized `Decidable (a < b)`, and four kernel-decided
ground comparisons. The last of those is what stops a classically obtained
`Decidable` instance from satisfying the row while computing nothing.

This row states no `DATA-ROW` law and closes no `DATA-ROW` edge. It says only
what a key must supply for such a law to be statable at all.

## Any-order — `E4-ENV-CE-005`

The attacked statement is that once irreflexivity, transitivity, and trichotomy
hold, the particular order does not matter.

It matters, because the order *is* the canonical spelling. A service-major, a
reversed, or a hash-derived order satisfies all three laws and spells a
different ascending row for the same key set, so two nodes that disagree about
the order disagree about canonical form while both look correct.

Name-major lexicographic is the frozen choice, and it is chosen so that
nominally equal keys are contiguous in an ascending row — the property
`E4-ENV-CE-002`'s collision rule will want. That is the reason for the choice,
not a theorem: no adjacency result is stated at `L0`.

`ServiceKey.lt_iff` pins the relation. The ground comparison
`⟨⟨0⟩, ⟨9⟩⟩ < ⟨⟨1⟩, ⟨0⟩⟩` pins the name-major direction independently of it: it
is false under a service-major order.

## Proof-free transport — `E4-ENV-CE-006`

The attacked design lets a service value cross service type codes without an
equality proof — a `cast`, an unchecked coercion, or a lookup that returns a
value at the requested carrier by construction.

This is the escape hatch the type-indexed design would have needed anyway, and
it reappears in the first-order design as soon as an environment tries to return
a value at a caller-chosen key. The packet supplies exactly one transport,
`ServiceKey.transport`, whose equality proof is an explicit argument and which
takes no instance argument, so a default value cannot stand in for the
transported one. `ServiceKey.transport_rfl` forces it to be the identity at
reflexivity.

The compile-negative on `ServiceKey.cast` records that no proof-free route is
offered. It is a name-level guard; the ascribed signature of `transport` is what
carries the exclusion.
