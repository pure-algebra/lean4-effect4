# Data row contract packet

Status: **Pass-B FROZEN; implementation REQUIRED-BLOCKED**. The production
fence `F-ROW` is solely `src/Effect4/Data/Row.lean`, which remains an empty breadth
stub at freeze. The breaker-owned Lean battery is
`Test/Data/RowContract.lean`. Its proof graph is `DATA-PG-ROW`.

This packet freezes one reusable data structure: a finite row with exactly one
canonical list spelling. It does not interpret a requirement, analyze a
program, encode bytes, or claim preservation of any effectful meaning.

## Ownership and duplicate prevention

| Stable type row | Exact owner | Role | Existing-type disposition | Duplicate prevention | Assurance |
| --- | --- | --- | --- | --- | --- |
| `E4-TYPE-DATA-ROW` | `Effect4.Row`; `Effect4.Data.Row` | the sole checked finite canonical row | native Effect4 type; Foldlab `T016.lean` is `evidenceOnly`, not a port source | Context `Requirement` must be an alias or named view of this row; Schema, Layer, Runtime, and targets may not mint another checked row | `proofGraphId = DATA-PG-ROW`; `required-open` |
| `E4-TYPE-DATA-ASCENDING` | `Effect4.Ascending`; `Effect4.Data.Row` | the strict-list canonicality predicate used by `Row` | native abbreviation over `List.Pairwise (· < ·)`; adopted proof shape from Foldlab evidence | no `Nodup`-only, non-strict, comparator-relative, or area-local canonicality predicate | attached to `DATA-PG-ROW/identity`; `required-open` |

There is no `Effect4.RowOrder`, comparator record, ordering witness stored in a
row, or second checked row. The ambient element type supplies Lean's standard
instances:

```text
LE α
LT α
DecidableEq α
DecidableLT α
Std.IsLinearOrder α
Std.LawfulOrderLT α
```

The logical `Row` carrier itself depends only on the ambient `LT`; operations
that compare elements request the remaining standard instances. This is a
consumer of Lean's order API, not an Effect4 order API.

The choice is anchored to Lean 4.33.1's
`Init/Data/Order/Classes.lean`: `Std.IsLinearOrder` owns reflexivity,
transitivity, antisymmetry, and totality of `≤`, while
`Std.LawfulOrderLT` relates `<` to that order. Lean's own
`Init/Data/Order/PackageFactories.lean` says the aggregate order packages are
for constructing instances and “should not be used as hypotheses”; therefore
the frozen declarations quantify over the individual standard classes.

`Effect4.ServiceKey` already owns the exact name-major relation. Its row bridge
must supply `LE ServiceKey`, `Std.IsLinearOrder ServiceKey`, and
`Std.LawfulOrderLT ServiceKey` for that same relation. That work belongs to the
key leaf. `Data.Row` must not define, reverse, or shadow the key order.

## Raw and checked boundary

The raw carrier is exactly `List α`. The checked carrier is exactly
`Effect4.Row α`:

```lean
structure Row (α : Type u) [LT α] where
  elems : List α
  ascending : Ascending elems
```

The public constructor is acceptable because its proof argument prevents a
noncanonical value. A private constructor would also prevent forging, but it
would remove the useful checked-list boundary; this packet freezes the
proof-carrying constructor instead. There is no unchecked `Row.ofList`.

`normalize : List α → Row α` is the only proof-free raw admission route.
Insertion accepts an already checked row and returns the same checked carrier.
No `RawRow`, `CheckedRow`, tree-set carrier, or comparator-indexed row is
introduced.

## ENSURES

The builder owes exactly these public facts and operations. The Lean battery
ascribes their complete signatures.

1. `Ascending xs ↔ xs.Pairwise (· < ·)`.
2. `Row.mk` requires `Ascending elems`.
3. `Row.elems` returns the raw `List` spelling.
4. `Row.ascending` retains its canonicality proof.
5. `Row` membership is underlying-list membership.
6. Membership and row equality are decidable when element equality is.
7. `Row.insert x r` returns the sole `Row` carrier.
8. `a ∈ insert x r ↔ a = x ∨ a ∈ r`.
9. The elements of `insert x r` are strictly ascending.
10. `Row.normalize` accepts exactly a raw `List`.
11. `a ∈ normalize xs ↔ a ∈ xs`.
12. The elements of `normalize xs` are strictly ascending.
13. Two rows with the same members are equal.
14. Normalization fixes every already ascending list.
15. Normalization is idempotent.
16. `normalize [a, a] = normalize [a]`, explicitly recording multiplicity
    erasure.
17. `Row.empty` has no member.
18. `b ∈ Row.singleton a ↔ b = a`.
19. `a ∈ union r s ↔ a ∈ r ∨ a ∈ s`.
20. Union is associative.
21. Union is commutative.
22. Union is idempotent.
23. Empty is a left union identity.
24. Empty is a right union identity.
25. `Row.Subset r s` means every member of `r` belongs to `s`.
26. Subset is decidable when element equality is.
27. Subset is reflexive and transitive.
28. Both operands are subsets of their union.

Nothing in this list is a denotational-preservation theorem. In particular,
ENSURES 16 proves the precondition for a possible semantic loss: raw authored
multiplicity is erased. A later calculus may prove that its observation is
multiplicity-insensitive; `Data.Row` cannot.

## Algebra and dependency spine

For `⟦r⟧ a := a ∈ r`, the contracted equations are:

```text
⟦insert x r⟧ a = (a = x) ∨ ⟦r⟧ a
⟦normalize xs⟧ a = a ∈ xs
⟦empty⟧ a = False
⟦singleton x⟧ a = (a = x)
⟦r ∪ s⟧ a = ⟦r⟧ a ∨ ⟦s⟧ a
Subset r s = ∀ a, ⟦r⟧ a → ⟦s⟧ a
```

Canonical extensionality lifts those membership equations back to equality of
rows. The proof dependency is frozen as:

```text
standard order laws + strict-list constructor
  -> insert membership + insert ascending
  -> normalize membership + normalize ascending
  -> canonical extensionality
  -> normalize fixes canonical + normalize idempotent
  -> union membership
  -> union associativity/commutativity/idempotence/identities
  -> subset reflexivity/transitivity
  -> left/right union weakening
```

Insertion and normalization are structural recursion on the finite input list.
No fuel, well-founded recursion, partial definition, scheduler assumption, or
external state enters this graph.

## `DATA-PG-ROW`

This type receives a proof graph because canonicalization is a nontrivial
recursive invariant and the row directly gates Context/Requirement cutover.
Trivial private recursion helpers receive no child graphs.

| Edge | Evidence required | Status at freeze |
| --- | --- | --- |
| `DATA-ROW-IDENTITY` | one `Row`, one `Ascending`, raw boundary `List`, proof-carrying constructor, no duplicate carrier/order | frozen-open |
| `DATA-ROW-ORDER` | exact standard instance binders; no `Effect4.RowOrder`; ServiceKey bridge uses its existing relation | frozen-open; key bridge external dependency |
| `DATA-ROW-INSERT` | insert membership and strict-ascent preservation | frozen-open |
| `DATA-ROW-NORMALIZE` | normalization membership, strict ascent, canonical fixed point, idempotence, duplicate erasure | frozen-open |
| `DATA-ROW-EXTENSIONALITY` | membership equivalence implies equality of canonical rows | frozen-open |
| `DATA-ROW-UNION` | membership plus associative, commutative, idempotent, and two identity laws | frozen-open |
| `DATA-ROW-WEAKENING` | subset definition, decidability, reflexivity, transitivity, both union inclusions | frozen-open |
| `DATA-ROW-COUNTEREXAMPLES` | all `E4-DATA-CE-*` witnesses retained and attacked designs rejected | frozen-open |
| `DATA-ROW-TRUST` | axiom receipt for every exported theorem; no `Classical.choice` or custom axiom | frozen-open |
| `DATA-ROW-COVERAGE` | frozen battery, clean build, reaction gate, and generated declaration/owner/graph join | frozen-open |

No Context, Layer, Runtime, or TypeScript cutover may close from a green local
row battery alone. The graph closes only when all ten edges are joined
mechanically.

## Counterexamples and rejected designs

The stable rows are `E4-DATA-CE-001` through `E4-DATA-CE-009` in
`Test/Counterexamples/REGISTER.md`; full attack shapes are in
`Test/Counterexamples/Data/ATTACKS.md`.

- A raw list is not a checked row: equal membership does not imply raw-list
  equality, canonicality and agreement are independent, and unchecked
  construction would forge `[2, 1]`.
- Order-preserving duplicate removal produces `[2, 1]` from `[2, 1, 2]`; the
  contracted normal form is `[1, 2]`.
- `[1, 2]` and `[2, 1]` have the same members and are unequal raw lists.
  Membership extensionality becomes equality only after both spellings are
  canonical.
- Canonicality and agreement are independent: `[1]` is ascending but does not
  agree with `[1, 2]`; `[2, 1]` agrees with `[1, 2]` but is not ascending.
- A public unchecked raw constructor can forge `[2, 1]`; the proof-carrying
  constructor and absent `ofList` close that route.
- `normalize [1, 1] = normalize [1]` while the two raw lists differ. This is
  the executable reason no denotational preservation claim appears here.
- Reversing the lawful ambient order spells the same two numeric identities as
  `[2, 1]` instead of `[1, 2]`. The order therefore is part of canonical
  spelling and must remain the element owner's frozen relation.
- Concatenation and left-favouring merge are not union; both violate the
  membership/commutativity spine.
- A containment test beside `elems` can drift from the row observation;
  `mem_def` therefore binds every law to one membership face.
- Raw prefix/sublist containment does not model weakening; conventional
  member inclusion does, with both operands included in their union.
- A classical `Decidable` inhabitant can satisfy a proposition-level type and
  still fail every kernel reduction while adding `Classical.choice`; explicit
  computational instances and the axiom ceiling reject that route.

The battery contains raw executable witnesses for agreement/canonicality
independence, positive Nat reductions for sort/dedup/union/weakening, and a
local reverse-order type using the same standard Lean law classes. The local
type is a counterexample only and introduces no Effect4 carrier.

## Satisfiability receipt

Before freezing, the breaker built a scratch reference using only `Std`, the
standard order classes above, one proof-carrying `Row`, and structural list
recursion. The reference was copied over the empty stub in a throwaway Lake
project and the fixed battery was run unchanged:

```text
lake build Effect4.Data.Row
lake env lean -DmaxErrors=100 Test/Data/RowContract.lean
```

Both commands exited 0. The scratch source itself is deliberately not part of
the packet and was not copied into the production fence. Its exported theorem
receipt reached only `[propext, Quot.sound]`; it did not reach
`Classical.choice`. This proves the signatures are jointly satisfiable and
sets the allowed ceiling; it does not constrain the builder to that private
implementation.

## Decrease, frame, and trust

Insertion recurses on the checked row's finite `elems`; normalization recurses
on the raw finite list. Every recursive call consumes a tail. Union delegates
to normalization of a finite append. The state frame is empty: operations are
pure and observe only their arguments and the standard order instances.

The public theorem ceiling is Lean's kernel plus `[propext, Quot.sound]`.
`Classical.choice`, custom axioms, `sorry`, `partial`, `unsafe`, external code,
and native decision shortcuts are forbidden. The builder must add an axiom
report covering every exported theorem in ENSURES, not merely the graph's
headline lemmas.

## RED and acceptance commands

The frozen empty-stub command is:

```text
lake env lean -DmaxErrors=10000 --json Test/Data/RowContract.lean
```

The frozen battery SHA-256 is
`862bbc904c0c9150c5e9d722015797e5dcdaaa3a98baabccb9f2bb76a29d67ff`.
This supersedes the breaker-phase hash
`e94fa648ddd981c6df2ad22724a49e519d5058f57762aee13f0fa1f57435cb10`:
the coordinator replaced only the test-local reverse-order instance's appeal
to a class-projected law with the axiom-free equivalent
`Nat.lt_iff_le_and_not_ge`. No public declaration, proposition, reduction, or
error census changed.
It exits 1 with 118 errors, all
`lean.unknownIdentifier._namedError`, zero other error kinds, naming 34 distinct
frozen declarations through the final positive reduction. The standard order
checks and all implementation-independent counterexamples elaborate in that
same run.

While the battery is red,
`Effect4Test.Data.RowContract` is listed in
`test/fixtures/trust-gate/known-red.txt`. The trust gate removes exactly that
module in its throwaway control tree and rejects a stale entry once the
implementation turns green.

After implementation, acceptance requires all of:

```text
lake env lean Test/Data/RowContract.lean
lake clean && lake build
git:c407ab7:scripts/test-data-row-contract-reactions.sh
scripts/test-trust-gate.sh
```

plus the exported-theorem axiom report, independent assurance, and the
generated `DATA-PG-ROW` declaration/owner/evidence join. The builder may not
edit this packet, its Lean battery, the counterexample rows, or the reaction
fixtures.

The reaction script is explicitly bounded. In the red phase it checks the
118/118 clean-red census, then verifies that four planted forbidden public
routes are detected: a custom `Effect4.RowOrder`, unchecked `Row.ofList`,
`Row.append`, and a row-level denotation-preservation declaration. After the
implementation turns green, the same script must be updated by the breaker or
coordinator to exercise semantic implementation mutants; name-level reactions
do not claim exhaustive rejection.
