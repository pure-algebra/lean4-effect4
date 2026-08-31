# Environment slice — dependency DAG

Status: drafted 2026-08-31. Owns the build order for `PLAN.md` broad-sweep
item 4, "freeze one Context/Service/Layer/Scope/ManagedRuntime representative".

This document exists because the Schema payload slice was built without one.
Two builders were dispatched against a contract that grew mid-run; two `Float64`
obligations landed after the module's builder had finished, and no fence owned
them. The battery stayed red on a seam nobody was assigned. The rule that
follows is the point of this file: **every node names its fence, and every edge
names the declarations that cross it.**

## Node status

`Context/Key.lean` is implemented. Its frozen battery, absence guards, full
build, trust gate, and axiom receipt are green. Its exact generated 97-name
owned-declaration census, separate 25-name frozen API, owner/theorem/axiom
join, and five detector reactions close `ENV-LEAF-KEY-IDENTITY`. The separate
14-name Std bridge API has exact synthesis, relation, computation, and axiom
receipts, so its local `ENV-LEAF-KEY-ORDER-BRIDGE` receipt is also closed. The
authored manifest supplies only allocations and routes; the generated check
derives both local results. The bridge's parent link is route-only; Data.Row
alone owns the status of `DATA-PG-ROW/ORDER`. `ServiceUniverse` alone remains
attached to the open `ENV-KEY-INTERP` semantic edge of the shared Context
graph. Neither local receipt creates a proof graph. `Data/Row.lean` is
implemented and its generated join closes all ten `DATA-PG-ROW` edges from
the exact declaration, API,
hypothesis, theorem, axiom, counterexample, and mutation receipts. The other
thirteen environment, layer, and runtime modules remain empty breadth stubs.

## The DAG

Edges point from provider to consumer. A node may be built only when every
node it points from is green.

```text
   Data/Row.lean                         Context/Key.lean
   (IMPLEMENTED, DATA-PG-ROW CLOSED,     (IMPLEMENTED, local receipts CLOSED,
   contract frozen)                       delegated ORDER route +
                                            ENV-KEY-INTERP OPEN)
          │                              ┌───────┴───────┐
          │  row edge available          │               │
          └──────────────┐               │               │
                         ▼               ▼               ▼
                    Context/Requirement        Context/Service
                              │                      │
                              └──────────┬───────────┘
                                         ▼
                                Context/Environment
                                         │
                        ┌────────────────┴────────────────┐
                        ▼                                 ▼
                Layer/Description                   Runtime/Scope
                        │                                 │
                        ▼                                 ▼
                   Layer/Build                     Runtime/Resource
                        │                                 │
                 ┌──────┴──────┐                          ▼
                 ▼             ▼                   Runtime/Lifecycle
            Layer/Memo   Layer/Provision                  │
                 │             │                          │
                 └──────┬──────┘                          │
                        ▼                                 │
                   Layer/Laws                             │
                        │                                 │
                        └────────────────┬────────────────┘
                                         ▼
                                  Runtime/Runtime
                                         │
                                         ▼
                              Runtime/ManagedRuntime
```

## Layers, and what may be dispatched in parallel

A layer is a set of nodes with no edge between them. Everything in one layer
may be given to concurrent builders; nothing may cross a layer boundary until
the whole preceding layer is green.

| Layer | Nodes | Parallel builders |
| --- | --- | --- |
| L0 | `Context/Key`, `Data/Row` | 2 |
| L1 | `Context/Requirement`, `Context/Service` | 2 |
| L2 | `Context/Environment` | 1 |
| L3 | `Layer/Description`, `Runtime/Scope` | 2 |
| L4 | `Layer/Build`, `Runtime/Resource` | 2 |
| L5 | `Layer/Memo`, `Layer/Provision`, `Runtime/Lifecycle` | 3 |
| L6 | `Layer/Laws` | 1 |
| L7 | `Runtime/Runtime` | 1 |
| L8 | `Runtime/ManagedRuntime` | 1 |

## Edge contents

An edge is only real if it names what crosses it. These are the declarations a
consumer imports; anything not listed here is not an edge and must not be
assumed.

| Edge | What crosses |
| --- | --- |
| `Data/Row → Context/Requirement` | the row carrier and its normalization/union laws. **This edge is not available yet** — see the correction below. It does NOT touch `Context/Key`; a key needs no row. |
| `Context/Key → Context/Requirement` | key identity, `DecidableEq`, **and a decidable strict linear order**. `DecidableEq` alone is not enough: `PORT-MANIFEST.md` "Canonical row extraction" freezes canonicality as strictly ascending `List.Pairwise (· < ·)`, so spelling a canonical row over keys requires an order at the key node. |
| `Context/Key → Context/Service` | key identity, the order, **and the interpretation triple** `ServiceUniverse`, `ServiceKey.Carrier`, `ServiceKey.transport`. Narrower would leave the first-order ruling only half-frozen: an L1 builder could reintroduce a type index at `Service`. The consuming edge `ENV-KEY-INTERP` is open until `Context/Service` and `Context/Environment` close it. |
| `Requirement + Service → Environment` | discharge: an environment satisfies a requirement row |
| `Environment → Layer/Description` | the target environment a layer describes |
| `Environment → Runtime/Scope` | the environment a scope closes over |
| `Layer/Description → Layer/Build` | the description a build interprets |
| `Runtime/Scope → Runtime/Resource` | acquisition and finalization order |
| `Layer/Build → Memo`, `→ Provision` | the built environment and its identity |
| `Memo + Provision → Layer/Laws` | composition, identity, and memo agreement |
| `Runtime/Resource → Runtime/Lifecycle` | finalization observing pre-failure state |
| `Layer/Laws + Lifecycle → Runtime/Runtime` | a runtime is a built environment plus a lifecycle |
| `Runtime/Runtime → ManagedRuntime` | a managed runtime owns a runtime's lifetime |

## Non-edges

Recorded so a builder does not invent them.

- **Schema does not gate this slice.** No node here needs a codec. A service
  value is not a persisted value, and nothing in this slice serializes.
- **Flow does not gate this slice.** `Runtime/Runtime` executes a checked
  program, but the representative may execute a `Program` from the closed P3
  algebra. Wiring the P4 checked flow is a later edge, not this one.
- **`Layer/Memo` does not gate `Layer/Provision`.** They are siblings.
  Memoization is an optimization whose agreement with unmemoized provision is
  the obligation; making one depend on the other would make that obligation
  unstatable, exactly as the Schema document packet found for the guarded
  checker.
- **Concurrency does not gate this slice.** Scope finalization here is
  sequential. Interruption and fibers are P7.

## Fences

One fence per builder, disjoint by construction. A builder that needs a
declaration outside its fence must stop and report, never reach across.

| Fence | Files |
| --- | --- |
| F-KEY | `Effect4/Context/Key.lean` |
| F-ROW | `Effect4/Data/Row.lean` |
| F-REQ | `Effect4/Context/Requirement.lean` |
| F-SVC | `Effect4/Context/Service.lean` |
| F-ENV | `Effect4/Context/Environment.lean` |
| F-LAYER-D | `Effect4/Layer/Description.lean` |
| F-SCOPE | `Effect4/Runtime/Scope.lean` |
| F-LAYER-B | `Effect4/Layer/Build.lean` |
| F-RES | `Effect4/Runtime/Resource.lean` |
| F-MEMO | `Effect4/Layer/Memo.lean` |
| F-PROV | `Effect4/Layer/Provision.lean` |
| F-LIFE | `Effect4/Runtime/Lifecycle.lean` |
| F-LAWS | `Effect4/Layer/Laws.lean` |
| F-RT | `Effect4/Runtime/Runtime.lean` |
| F-MRT | `Effect4/Runtime/ManagedRuntime.lean` |

`Effect4Test/Environment/AxiomReport.lean` is shared. It is **not** in any
builder's fence; receipts are appended by the coordinator after each layer
closes. That is the direct fix for the seam that stalled the Schema slice.

## Contract freeze rule for this slice

The Schema slice's battery grew from 817 to 1295 lines while builders worked
against it. That must not recur.

**A layer's contract is frozen before any builder in that layer is
dispatched, and is not edited while that layer is in flight.** A defect found
mid-layer is recorded as a fired finding and repaired in the next layer's
freeze, not patched under a running builder.

## Axiom traps builders keep hitting

Three now, each found the expensive way. A builder in this slice should reach
for the right-hand column first.

| Pulls in an axiom | Axiom-free alternative |
| --- | --- |
| `simp` on a positive `String` disequality | `by decide` on the same goal |
| `decreasing_by` well-founded recursion | `termination_by structural <arg>` |
| `omega` on `Nat` inequality chains | explicit `Nat.lt_of_lt_of_le` / `Nat.lt_of_le_of_lt` with `Nat.le_of_eq` |

The third was found at L0: a first draft of `ServiceKey.lt_trans` used `omega`
and pulled `[propext, Quot.sound]`; the explicit steps removed both. None of
these is a trust violation — `[propext, Quot.sound]` is the allowlist ceiling —
but a slice whose declarations are all axiom-free is cheaper to audit than one
where every receipt has to be read to see whether the axiom was necessary.

A related L0 lesson about *instances* rather than proofs: build a `Decidable`
instance with `inferInstanceAs` over the spelled-out proposition so it resolves
to computing core instances, rather than producing it by tactic and wrapping it
in `Eq.mpr`. Only the former reduces in the kernel, which is what lets a ground
comparison close `by decide`.

## Corrections to this document

Recorded rather than silently edited, because a DAG that quietly repairs
itself teaches nothing.

**BROKE.** The first draft showed `Data/Row.lean` as an existing closed node
and claimed `DATA-ROW-01/02/03` were "already closed and this slice may not
restate them". All three parts are false. `Effect4/Data/Row.lean` is an empty
breadth stub declaring nothing, `Effect4/Schema/Getter.lean` records those
obligations as open, and no `DATA-ROW` contract exists in `test/contracts/`.

**LAW.** A DAG edge may name a provider only if that provider's obligations
are actually closed, or the edge must be marked unavailable. An inbound edge
asserted from an empty stub is the same defect class as a citation that does
not resolve.

**WITNESS.** The L0 breaker checked the claim while freezing against it, and
found `Effect4/Context/Key.lean` needs no row at all — it imports only `Std`.

**CLASS.** Unverified precondition in a planning artifact.

**FIXED-BY.** `Data/Row` is now a node in L0 with its own fence `F-ROW`, and
`Context/Requirement` in L1 is blocked on it. **L1 may not be dispatched until
a `DATA-ROW` breaker has frozen that contract.**

**Third correction — the same edge, under-specified again.** The
`Context/Key → Context/Requirement` edge was corrected once already, from
`DecidableEq` to "a decidable strict linear order". That was still not what
the consumer needs. The landed `DATA-ROW` packet quantifies rows over
`Std.IsLinearOrder` and `Std.LawfulOrderLT`, which require `LE α`, and
`#synth LE Effect4.ServiceKey` fails outright on the closed L0 module. The
edge is therefore not traversable as written, for the second time.

**LAW.** Naming the *mathematical content* an edge carries is not enough. An
edge must name the **instances the consumer will actually synthesize**, since
that is what fails at elaboration. "A decidable strict linear order" and
`Std.IsLinearOrder` are the same idea and different facts.

**WITNESS.** Two `DATA-ROW` breakers ran concurrently and produced mutually
exclusive packets — one over a local `RowOrder` mixin on `[LT α]` that works
against the frozen key today, one over Std's hierarchy that does not. The
collision is what exposed the gap; neither packet was wrong about rows.

**CLASS.** Edge specified by content rather than by resolvable instance.

**FIXED-BY.** The landed Std-based packet is kept. Minting a local `RowOrder`
class would introduce a second order API alongside Std's, and
`PORT-MANIFEST.md` "Canonical row extraction" forbids a second canonical-order
notion; Std is also the deeper abstraction the dependency policy prefers. The
gap is closed **additively at the key** — an `LE` instance and the
`Std.IsLinearOrder` / `Std.LawfulOrderLT` instances derived from the existing
`ServiceKey.Lt`, adding no new comparison. The frozen L0 contract's ENSURES
list is unchanged and its battery must stay green, so this is an extension of
a closed leaf rather than an amendment of it.

The extension owns exactly 14 authored declarations:
`ServiceKey.Le`, `ServiceKey.instLE`, `ServiceKey.le_iff`,
`ServiceKey.instDecidableLE`, `ServiceKey.lt_asymm`, `ServiceKey.le_refl`,
`ServiceKey.le_trans`, `ServiceKey.le_antisymm`, `ServiceKey.le_total`,
`ServiceKey.lt_iff_le_not_le`, `ServiceKey.instIsPreorder`,
`ServiceKey.instIsPartialOrder`, `ServiceKey.instIsLinearOrder`, and
`ServiceKey.instLawfulOrderLT`. The generated environment census separately
owns compiler-generated structural companions but keeps them outside the
authored API count. The 14 bridge names belong to local receipt
`ENV-LEAF-KEY-ORDER-BRIDGE`, whose delegated parent route is the now-closed
`DATA-PG-ROW/ORDER`; Data.Row alone owns that edge status. They do not attach
to or close `ENV-KEY-INTERP`.

**Second correction.** The `Context/Key → Context/Service` edge was written as
"key identity only". The frozen L0 packet puts the interpretation triple on it
as well, for the reason given in the edge table. The DAG understated its own
edge; the packet is right.

## Open questions

1. ~~Is a context key first-order or type-indexed?~~ **SETTLED at L0: first
   order.** `ServiceKey` is the pair of a nominal `ServiceName` and a
   first-order `ServiceTypeCode`; reading a code as a Lean type is a supplied
   `ServiceUniverse`, a trusted boundary object in the position
   `Effect4.FlowAlphabet` already occupies. What it gives up is frozen in
   `test/contracts/environment-context-key.contract.md`, including a proof —
   not an assertion — that distinct codes may read as the same type, so type
   identity never recovers code identity.
2. Does `Requirement` reuse `Effect4.Data.Row` directly, or a named view of it?
   The row carrier and graph are closed. A quotient or copied carrier would
   duplicate that role and is disallowed; the remaining choice is an alias or
   named view over the one canonical row.
3. Does a scope's finalization order need to be observable, or only its
   effect? `PLAN.md` requires that state produced before failure remains
   available to finalization, which constrains the carrier but not yet the
   order.
