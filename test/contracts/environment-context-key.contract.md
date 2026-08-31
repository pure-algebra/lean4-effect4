# Environment context key contract

Status: FROZEN breaker packet, 2026-08-31; its pre-implementation revision is
required to be RED, and fired findings are recorded below

Ruling input: `docs/ENVIRONMENT-DAG.md`, node `L0` and its open question 1,
"Is a context key a first-order identity with `DecidableEq`, or does it carry a
type index?"

Implementation fence: `F-KEY` = `Effect4/Context/Key.lean`

Battery: `Effect4Test/Environment/ContextKeyContract.lean`

Counterexamples: `test/counterexamples/REGISTER.md`, rows `E4-ENV-CE-001`
through `E4-ENV-CE-006`, with attack shapes in
`test/counterexamples/environment/ATTACKS.md`

## The ruling

**A context key is first-order data. It is not type-indexed.**

`Effect4.ServiceKey` is a `Type` — not a family `Type u → Type`, and not a
structure carrying a `Type`-valued field. It is the ordered pair of a nominal
`ServiceName` and a `ServiceTypeCode`, both single-field carriers over `Nat`,
and both the key and its two components have `DecidableEq`. The reading of a
code as a Lean type is a separate, supplied `ServiceUniverse`, in exactly the
position `Effect4.FlowAlphabet` occupies for the flow slice: a trusted boundary
object, never canonical content.

### Why

1. `AGENTS.md`, "Representation rules", requires that canonical program content
   be first-order data and that Lean functions not be stored program syntax. A
   key is canonical content: `docs/ENVIRONMENT-DAG.md` makes a requirement a row
   over keys, and a requirement row is authored, compared, and — at P10 — lowered
   to a target. A `Key : Type u → Type` puts a Lean `Type` inside that content.
2. The row lane needs more than `DecidableEq`. `PORT-MANIFEST.md`, "Canonical
   row extraction", freezes canonicality as *strictly ascending*, spelled
   `List.Pairwise (· < ·)`, and records that "Effect4 gains no second canonical
   order notion". A canonical row over keys therefore needs a decidable strict
   linear order on keys. No such order exists across the indices of a
   type-indexed family, because it would have to order Lean types.
3. Deciding equality of an environment requires deciding equality of its keys.
   Under a type index that is equality of `Type`s, which Lean does not decide,
   so the type-indexed answer forces heterogeneous-equality machinery this
   repository does not have and has not priced.
4. Lean gives no injectivity for type constructors, so a type-indexed key admits
   no honest recovery of its index from a stored entry without an added cast or
   axiom. `PLAN.md`, "Non-negotiable semantic boundaries", puts axioms and host
   escape hatches outside the model, and the repository allowlist is
   `[propext, Quot.sound]`.

### What the ruling gives up

Stated plainly, because each item is a real loss and three of them are visible
downstream.

- **Type safety at the key is no longer automatic.** With a type index,
  `get : Environment → Key α → Option α` is well typed by construction. Here the
  type of a service value is `ServiceKey.Carrier U k`, which depends on a
  supplied `U`. Universe agreement becomes an explicit hypothesis of every
  downstream statement instead of a consequence of the key's type. This node
  supplies the vocabulary for that hypothesis and discharges none of it.
- **A code is not a faithful name for a type.** Two distinct codes may read as
  the same Lean type, so type identity never recovers code identity and no
  inverse interpretation exists. This packet does not leave that as an
  assumption: `ServiceUniverse.exists_carrier_collision` (ENSURES 12) proves it,
  so a downstream design cannot quietly rely on the converse.
- **There is no canonical reading of a code.** `ServiceUniverse` is supplied at
  the boundary, so "the type of a service" is only defined relative to a
  universe. Nothing here forces two callers to agree on one.
- **The identity is the pair, not the nominal name.** Effect's `Context.Tag`
  identity is the tag string alone. `ServiceKey` admits two keys that share a
  name and differ in code, which that model cannot express. Any later
  compatibility statement must handle the colliding pair rather than assume it
  away; this packet only makes it representable and decidable.
- **`ServiceUniverse` is a Lean function.** It is a boundary object, and this
  node can enforce only that the *key* does not carry one. It cannot stop a
  downstream node from storing a universe in canonical content; that is each
  downstream packet's obligation.

## Claim boundary

This packet freezes the `L0` node and nothing else. It says what a key is, how
two keys compare, what nominal collision means, and how a code is read as a
type.

It does **not** freeze, and makes no claim about:

- requirement rows, their canonical spelling, normalization, or union laws —
  `DATA-ROW-01/02/03` are open (see "Upstream edge status") and this packet
  restates none of them;
- whether an environment may hold a nominally colliding pair, which is the
  `Context/Environment` node's ruling;
- adjacency of colliding keys inside an ascending row. Name-major ordering is
  chosen so that nominal groups are contiguous, but no adjacency theorem is
  stated or proved here, and the choice is an ordering ruling rather than a
  derived result;
- any persisted or wire spelling of a key. `ServiceName` is a `Nat`, and this
  slice serializes nothing — `docs/ENVIRONMENT-DAG.md`, "Non-edges", records
  that Schema does not gate it. A later wire profile owns tag strings, exactly
  as `E4-SCHEMA-CE-039` assigns persisted key spellings away from a carrier;
- compatibility with Effect's `Context.Tag`, in either direction;
- `Context/Service`, `Context/Requirement`, `Layer/*`, or `Runtime/*`.

A key is an identity plus a code. It is not a service, not a value, and not a
requirement.

## Upstream edge status

`docs/ENVIRONMENT-DAG.md` draws one inbound edge, `Data/Row → Context/Key`, and
describes `Data/Row.lean` as existing and closed with `DATA-ROW-01/02/03`
already closed.

That is not the state of the tree. `Effect4/Data/Row.lean` is an empty breadth
stub with no declaration, `Effect4/Schema/Getter.lean` records `DATA-ROW-01/02/03`
as open, and `PORT-MANIFEST.md`, "Canonical row extraction", says in its "Open"
paragraph that no declaration may enter the row module before a breaker freezes
the `DATA-ROW` contract.

This packet is therefore built with **no inbound edge**: `Effect4/Context/Key.lean`
imports nothing from `Effect4.Data.Row`, and the builder must not add such an
import. Nothing at `L0` needs one: a key is an identity, and every obligation
below is stated over key values alone. The row carrier is what
`Context/Requirement` needs at `L1`, and that node cannot be dispatched until
`DATA-ROW` is frozen by its own breaker. Reconciling
the DAG's edge description is the coordinator's, not this packet's — this
section records the observation rather than editing that document.

## Edge content this packet widens

`docs/ENVIRONMENT-DAG.md` says the `Context/Key → Context/Service` edge carries
"key identity only". This packet puts `ServiceUniverse`, `ServiceKey.Carrier`,
and `ServiceKey.transport` on that edge as well.

The reason is that the ruling above is only half-frozen without them. The cost
of the first-order answer *is* the interpretation function; if `L0` froze the
codes and left the reading of a code to `L1`, a service builder could reintroduce
a type index by making `Service` type-indexed, and the decision this packet
exists to settle would not in fact be settled. Putting the interpretation in
`F-KEY` also matches the flow slice, where `FlowAlphabet` lives beside `BlockId`
in one module rather than at the consumer.

The widening is confined to `F-KEY` and adds no new file. The coordinator owns
whether the DAG's edge row is updated to match.

## Assurance route

This node closes with local signature and theorem receipts plus an axiom
receipt, not with its own proof graph. It declares no admission judgment, no
denotation, no handler, no recursion, and no composition invariant; it is a
finite identity carrier, a decidable order over `Nat` pairs, and one supplied
reading.

One edge is named and left **open** by this packet:

- `ENV-KEY-INTERP` — every downstream typing statement about a service value is
  relative to a supplied `ServiceUniverse`, and nothing at `L0` consumes one.
  The edge is closed by `Context/Service` and `Context/Environment`, which are
  the first nodes that can state what agreement between universes buys.

Packet-local obligation IDs, used by the ENSURES list below, are `ENV-KEY-01`
through `ENV-KEY-04` mapping to declaration groups D1 through D4. They are
packet-local on purpose: this slice has no cutover document of its own yet, and
minting slice-wide IDs here would put a fact in this file that
`docs/ENVIRONMENT-DAG.md` or a later environment cutover ruling should own.

The axiom receipt for this node belongs in `Effect4Test/Environment/AxiomReport.lean`,
which `docs/ENVIRONMENT-DAG.md` places outside every builder's fence. The
builder does not create or edit it; the coordinator appends the receipt when
`L0` closes.

## CATEGORIES

- `inductive-data` — the key and its components are finite first-order
  structures with no `Type`-valued field;
- `specification-design` — identity, ordering, nominal collision, and
  interpretation are four separate obligations rather than one;
- `algebraic-laws` — the order is a decidable strict linear order, stated as an
  exact relation and not merely as three axioms;
- `claim-scope` — a code is not a faithful name for a type, and a key is not a
  service.

## REQUIRES

1. Lean core and Std at the repository's pinned Lean 4.33.1 toolchain. No
   Mathlib, so no `Fintype` and no order typeclass hierarchy; the order laws are
   proved directly over `Nat`.
2. No dependency on `Effect4.Data.Row`, `Effect4.Algebra`, `Effect4.Flow`, or
   `Effect4.Schema`. `Effect4/Context/Key.lean` is free-standing; `import Std`
   is permitted and nothing else.
3. Every declaration is safe and total. The repository trust gate rejects
   `unsafe`, `partial`, and `sorry`.
4. No new axiom. The exported closure stays inside `[propext, Quot.sound]`.

## Public declaration DAG

Binder names may differ. Names, field identity and order, result types, universe
arities, and theorem propositions are frozen by the Lean battery. All names are
in the flat `Effect4` namespace, matching `Effect4.BlockId` and
`Effect4.RepresentationTag`.

### D0 — nominal identities

```lean
structure ServiceName where
  value : Nat
deriving DecidableEq, Repr

structure ServiceTypeCode where
  value : Nat
deriving DecidableEq, Repr
```

Two single-field carriers over `Nat`, following the flow slice's `BlockId`,
`OperationId`, `AlphabetId`, and `DecisionId`. They are **nominally distinct**:
a name is not a code, and a design that uses one type for both fails the
`ServiceKey.mk` ascription in D1.

`Nat` rather than `String` is deliberate and is an ordering decision, not a
spelling decision. A `String` name would require proving irreflexivity,
transitivity, and trichotomy for `String.lt` from core alone, which is a
sizeable obligation with no consumer at `L0`, and it would import a persisted
spelling question this slice explicitly does not own.

### D1 — the key (`ENV-KEY-01`)

```lean
structure ServiceKey where
  name : ServiceName
  service : ServiceTypeCode
deriving DecidableEq, Repr
```

`ServiceKey : Type`, at universe zero, with exactly these two fields in this
order. The exact `ServiceKey.rec` is frozen by the battery, so a third field, a
`Type`-valued field, or a permutation of `name` and `service` fails even when
every theorem below still holds.

### D2 — decidable strict order (`ENV-KEY-02`)

```lean
instance : LT ServiceKey
instance (a b : ServiceKey) : Decidable (a < b)

theorem ServiceKey.lt_iff (a b : ServiceKey) :
    a < b ↔ (a.name.value < b.name.value ∨
      (a.name = b.name ∧ a.service.value < b.service.value))
theorem ServiceKey.lt_irrefl (a : ServiceKey) : ¬ a < a
theorem ServiceKey.lt_trans {a b c : ServiceKey} : a < b → b < c → a < c
theorem ServiceKey.lt_trichotomy (a b : ServiceKey) : a < b ∨ a = b ∨ b < a
```

The order is **name-major lexicographic**. The battery does not freeze a name
for the underlying relation, so the builder may spell it as a `def`, an
`instance` body, or a `Bool` helper; what is frozen is `<` and its law.

Name-major is chosen so that nominally equal keys are contiguous in an ascending
row. That is the reason for the choice; it is not a claim, and no adjacency
theorem is stated here.

### D3 — nominal collision (`ENV-KEY-03`)

```lean
def ServiceKey.Conflict (a b : ServiceKey) : Prop
instance (a b : ServiceKey) : Decidable (ServiceKey.Conflict a b)

theorem ServiceKey.conflict_iff (a b : ServiceKey) :
    ServiceKey.Conflict a b ↔ (a.name = b.name ∧ a.service ≠ b.service)
```

`Conflict` names the situation two keys are in when they share a nominal
identity and are still different keys. Freezing it at `L0` gives
`Context/Environment` a vocabulary it does not have to mint, and freezing it as
a *decidable* relation keeps a later admission clause executable.

`Conflict` is representable here. Whether an environment may hold a conflicting
pair is not decided by this packet.

### D4 — the interpretation (`ENV-KEY-04`)

```lean
structure ServiceUniverse.{u} where
  Carrier : ServiceTypeCode → Type u

def ServiceKey.Carrier.{u} (U : ServiceUniverse.{u}) (k : ServiceKey) : Type u

theorem ServiceKey.carrier_def.{u} (U : ServiceUniverse.{u}) (k : ServiceKey) :
    ServiceKey.Carrier U k = U.Carrier k.service

def ServiceKey.transport.{u} (U : ServiceUniverse.{u}) {a b : ServiceKey}
    (h : a.service = b.service) (v : ServiceKey.Carrier U a) :
    ServiceKey.Carrier U b

theorem ServiceKey.transport_rfl.{u} (U : ServiceUniverse.{u}) (k : ServiceKey)
    (v : ServiceKey.Carrier U k) :
    ServiceKey.transport U (rfl : k.service = k.service) v = v

theorem ServiceUniverse.exists_carrier_collision :
    ∃ (U : ServiceUniverse.{0}) (a b : ServiceTypeCode),
      a ≠ b ∧ U.Carrier a = U.Carrier b
```

`ServiceUniverse` is the trusted supplied reading of codes. It is a boundary
object of exactly the kind `Effect4.FlowAlphabet` already is in
`Effect4/Flow/Block.lean`, whose docstring calls it a "trusted semantic
environment" so that "no host function enters canonical flow content". The same
sentence applies here, and the `ServiceKey.rec` snapshot is what mechanically
keeps the universe out of the key.

`transport` is the only transport this packet supplies, and its equality proof
is an explicit argument. It takes no instance argument, so it cannot be
implemented by producing a default value in place of the transported one.

## ENSURES

The builder must prove these exact edges without `sorry`, `admit`, custom
axioms, unsafe declarations, partial declarations, or `Classical.choice`.

1. **Key carrier** — `ServiceKey` elaborates at `Type`; `ServiceKey.mk` has type
   `ServiceName → ServiceTypeCode → ServiceKey`; `ServiceKey.name` and
   `ServiceKey.service` have the two frozen projection types; and
   `ServiceKey.rec` has the exact dependent type with `name` before `service`.
   `ServiceName.mk : Nat → ServiceName` and `ServiceTypeCode.mk : Nat →
   ServiceTypeCode`, with their `value` projections, fix the two components.
2. **Decidable equality** — `DecidableEq ServiceName`, `DecidableEq
   ServiceTypeCode`, `DecidableEq ServiceKey`, and `Repr ServiceKey` synthesize.
   The component `Repr` instances are not separately frozen; they exist so that
   `Repr ServiceKey` derives.
3. `ServiceKey.lt_iff` — the exact name-major lexicographic law.
4. `ServiceKey.lt_irrefl`.
5. `ServiceKey.lt_trans`.
6. `ServiceKey.lt_trichotomy`.
7. **Decidable order** — `LT ServiceKey` synthesizes, `Decidable (a < b)`
   synthesizes for arbitrary `a` and `b`, and four ground comparisons reduce in
   the kernel under `decide`.
8. `ServiceKey.conflict_iff`.
9. **Decidable collision** — `Decidable (ServiceKey.Conflict a b)` synthesizes
   for arbitrary `a` and `b`, and four ground statements reduce under `decide`:
   one conflicting pair, a same-code different-name pair that does not conflict,
   a reflexive pair that does not conflict, and the same-name pair's
   disequality stated without `Conflict` at all.
10. `ServiceKey.carrier_def` — the carrier is selected by the **code**.
11. `ServiceKey.transport` at the exact ascribed signature, and
    `ServiceKey.transport_rfl`.
12. `ServiceUniverse.exists_carrier_collision`.

### What each row excludes, and what it does not

Obligation 1 is the load-bearing exclusion of the type-indexed answer. A
`ServiceKey : Type u → Type` fails the ascription by arity, and a
`ServiceKey.{u}` carrying a `Type u` field fails it because such a structure
lives in `Type (u + 1)`, which cannot unify with `Type 0`.

Obligation 2 does **not** exclude the type-indexed answer, and is not listed as
if it did. A family `Key : Type u → Type` can carry `DecidableEq (Key α)` at
every index. What obligation 2 excludes is a key that stores a Lean function or
a `Type` at all, which no decidable-equality instance can survive. The two rows
forbid different things.

Obligations 4, 5, and 6 are **not** independent of obligation 3. Each follows
from `lt_iff` together with the corresponding `Nat` fact — `Nat.lt_irrefl`,
`Nat.lt_trans`, and `Nat.lt_trichotomy` — in a few lines. They are listed
separately because they are the three statements a canonical ascending row cites,
and because they survive a later reformulation of `lt_iff`; not because they
carry content `lt_iff` lacks. Conversely, obligation 3 is not implied by 4, 5,
and 6 together: those three admit any decidable strict linear order, including a
service-major or hash-derived one, and every such order spells a different
canonical row for the same key set.

Obligation 7's four ground comparisons are not decoration. `Decidable (a < b)`
alone can be satisfied by a classically obtained instance that computes nothing;
the kernel reductions rule that out. One of the four also pins the name-major
direction independently of `lt_iff`: `⟨⟨0⟩, ⟨9⟩⟩ < ⟨⟨1⟩, ⟨0⟩⟩` is false under a
service-major order.

Obligation 9's conflicting witness follows from obligation 8 together with
`ServiceTypeCode.mk 0 ≠ ServiceTypeCode.mk 1`, which obligation 1 supplies. It
is listed because it is what actually fails if a builder collapses the key onto
its name: under a name-only identity there is no conflicting pair to exhibit,
and `conflict_iff` would be vacuously satisfied by a `Conflict` that is
everywhere false.

Obligation 10 excludes a name-keyed interpretation, which is the shape a builder
reaches for when trying to make the nominal name behave like Effect's tag.

Obligation 11's `transport_rfl` on its own is weak; its force comes from the
ascribed signature beside it. Together they say the transport is definitionally
the identity at reflexivity and takes nothing but the equality proof.

Obligation 12 is the only row that is *false* of a plausible alternative design
rather than true of it. A `ServiceUniverse` constrained to an injective
`Carrier` would refute it, and that constrained design is exactly the one under
which a consumer could recover a code from a type. Proving the collision is how
this packet prices the ruling instead of asserting the price.

## Enforcement by absence

Five members are required not to resolve. Each is a name-level guard and is
defense in depth; the load-bearing exclusion is named beside it in the battery.

| Absent member | What it would reintroduce | Carried by |
| --- | --- | --- |
| `ServiceKey.Service` | a Lean type stored on the key | ENSURES 1 |
| `ServiceKey.universe` | the key carrying its own interpretation | ENSURES 1 |
| `ServiceKey.cast` | transport with no equality proof | ENSURES 11 |
| `ServiceTypeCode.ofType` | a code minted from a Lean type | ENSURES 1 |
| `ServiceUniverse.code` | an inverse interpretation | ENSURES 12 |

The battery spells the expected diagnostic as `Unknown` rather than
`Unknown constant`. Lean reports an unresolved name two ways — `Unknown
identifier` while no prefix of the name exists, which is this file's red-phase
state, and `Unknown constant` once the enclosing declaration exists and only the
member is missing, which is its implemented state. Pinning either spelling alone
would make the section fail in one of the two phases for a reason unrelated to
the attacked design.

## Falsification battery

- `E4-ENV-CE-001`: a context key carries its service type as a Lean type index.
- `E4-ENV-CE-002`: a key's nominal name determines its service, so name equality
  is key equality.
- `E4-ENV-CE-003`: a first-order service type code is a faithful name for a Lean
  type, so type equality recovers code equality.
- `E4-ENV-CE-004`: `DecidableEq` on keys is enough to spell a canonical
  requirement row.
- `E4-ENV-CE-005`: any decidable strict linear order on keys serves equally.
- `E4-ENV-CE-006`: a service value may cross service type codes without an
  equality proof.

Attack shapes are in `test/counterexamples/environment/ATTACKS.md`. No
`E4-ENV-CE-*` row is discharged by a later node without being restated there;
these six are this node's.

## Decrease, frame, and trust

Every function is a finite projection or a comparison of two `Nat` fields.
Nothing recurses, mutates state, invokes a handler, executes a host callback, or
allocates a resource. The frame is the two key values and, for D4, the supplied
universe.

`ServiceUniverse` is a Lean function and is deliberately outside the first-order
frame. It is a boundary object, exactly as `FlowAlphabet` is, and it may not be
stored as canonical content by any consumer. This packet enforces only that the
key does not carry one.

The public proof ceiling is Lean's kernel plus the repository allowlist
`[propext, Quot.sound]`. No custom axiom and no `Classical.choice` is permitted.
Against a reference implementation written by this breaker to check that the
battery is satisfiable, `lt_trans` and `conflict_iff` elaborated through
`propext` and the other six exported theorems depended on no axiom; `Quot.sound`
was not reached. That is one implementation's receipt and it is not binding on
the builder's — the binding constraint is the allowlist, and the builder records
the actual receipt for every exported declaration.

## Battery reaction evidence

Each ENSURES row above was checked against a design that commits the defect it
is meant to forbid, rather than being assumed to bite. The reference
implementation and six mutants were elaborated by this breaker outside the
repository tree; no mutant is retained here, and none of them is an Effect4
declaration.

Two mutants matter most, because both are *self-consistent*: each compiles on
its own with all of its own proofs discharged, so only the battery can reject
them.

- **Service-major order.** A key order that compares codes before names, with
  `lt_iff` restated in its own direction and correct irreflexivity,
  transitivity, and trichotomy proofs. It compiles alone. Against the battery it
  produces three errors: a type mismatch at the `ServiceKey.lt_iff` ascription
  and two ground comparisons that `decide` refutes. This is the evidence for
  `E4-ENV-CE-005`: the three order laws alone do not settle the spelling.
- **Name-keyed interpretation.** A `ServiceKey.Carrier` that selects by
  `k.name` instead of `k.service`, with `carrier_def` and `transport` restated
  over name equality and proved. It compiles alone. Against the battery it
  produces three errors, at `carrier_def`, `transport`, and `transport_rfl`.

Four further designs were rejected: a type-indexed family, a key with its two
fields permuted, a `ServiceUniverse` carrying an injectivity field, and a
name-only key with the code derived from the name. The first was additionally
checked in isolation — `@_ : Type` rejects `KeyA : Type → Type` by arity and
rejects a `KeyB.{u}` with a `Type u` field because such a structure elaborates
at `Type (u + 1)`.

This is detector-reaction evidence over six specified designs. It is not a
theorem that every defective key design is rejected, and it closes no
obligation.

## Battery sizing

Every unresolved name costs one diagnostic while the battery is red, and Lean
stops a file at 100. An in-file `set_option maxErrors` does not lift that limit
for this build path, so a truncated red run would silently under-report what is
frozen. The obligation set is kept free of redundant ascriptions for that
reason: the frozen revision produces 93 red diagnostics and nothing is
truncated. A later revision that adds checks must re-measure rather than assume.

This is also why `ServiceName.rec`, `ServiceTypeCode.rec`, and
`ServiceUniverse.rec` are not snapshotted. Each of those three is a
single-field structure whose `mk` ascription already fixes the field count and
type and whose projection ascription already fixes the field name. Only
`ServiceKey` has fields that can be permuted, so only `ServiceKey.rec` earns its
diagnostics.

## RED and acceptance commands

The breaker records the intended red state with:

```text
lake env lean Effect4Test/Environment/ContextKeyContract.lean
```

It must fail only because the frozen declarations do not yet exist: every
diagnostic is `error(lean.unknownIdentifier)` naming one of the twenty-five
frozen names. While that is true, `Effect4Test.Environment.ContextKeyContract`
is listed in `test/fixtures/trust-gate/known-red.txt` so
`./scripts/test-trust-gate.sh` can excise it and still exercise its planted
declarations against a green tree.

After implementation, acceptance additionally requires:

```text
lake env lean Effect4Test/Environment/ContextKeyContract.lean
lake clean && lake build
./scripts/test-trust-gate.sh
```

and the removal of the `known-red.txt` entry, which the gate itself demands: a
declared-red module that has become green fails the gate until the stale entry
is cleared.

The builder then records the axiom receipt without editing this contract or its
Lean battery.

## Fired findings

### Numbering slip in the D4 section prose

**BROKE.** The battery's D4 section docstring says "ENSURES 10 through 13".
The ENSURES list in this contract ends at 12, and this contract's own D4
discussion cites only 10, 11, and 12. There is no ENSURES 13.

**LAW.** A frozen packet's prose must not name an obligation the packet does
not contain. A reader cannot tell a numbering slip from a dropped obligation
without re-deriving the list.

**WITNESS.** The L0 builder found it while discharging D4 and correctly did
not touch either file — the slice's contract-freeze rule forbids editing a
packet under a running builder.

**CLASS.** Prose/obligation-count mismatch. No obligation changed; nothing was
under- or over-specified.

**FIXED-BY.** Recorded here by the coordinator after L0 closed. The D4
docstring should read "ENSURES 10 through 12" at the next freeze of this
packet. Left unedited for now because the battery is the frozen artifact and
this is the recorded-finding channel for it.

### Reference implementation was weaker on axioms than the delivered one

**BROKE.** Nothing, but it is worth the record. This packet's satisfiability
check used a reference implementation whose `lt_trans` and `conflict_iff`
reached `propext`. The contract's trust paragraph was written against that
observation.

**WITNESS.** The delivered implementation reaches neither `propext` nor
`Quot.sound`; all 23 exported constants are axiom-free, receipted in
`Effect4Test/Environment/AxiomReport.lean`.

**CLASS.** Trust-paragraph scope written from one implementation rather than
from the obligation.

**FIXED-BY.** The trust paragraph should state the ceiling the obligations
*permit* (`[propext, Quot.sound]`) and record separately what the delivered
implementation *reaches* (nothing). A packet must not imply an axiom is
required when it is merely allowed.
