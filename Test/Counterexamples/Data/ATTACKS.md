# Data row attacks

This is the durable narrative companion to
`Test/Data/RowContract.lean`. Stable IDs are allocated in
`Test/Counterexamples/REGISTER.md`. The production fence is solely
`src/Effect4/Data/Row.lean`; no attack here defines another public row or order.

## Raw-list carrier and forged canonicality — `E4-DATA-CE-001`

**ATTACKED.** A row may be a raw list with canonicality checked beside it; or
equal raw membership is enough to equate raw lists.

**WITNESSES.** `[1, 2]` and `[2, 1]` have the same Nat members and are unequal
lists. The second is not strictly ascending. Canonicality and agreement are
also independent: `[2, 1]` agrees with `[1, 2]` but is noncanonical, while
`[1]` is canonical and does not agree with `[1, 2]`.

An unchecked `Row.ofList [2, 1]` would forge a checked value. A carrier with a
hidden provenance or ghost constructor could also contain two values with the
same members, defeating canonical extensionality.

**FORCED REPAIR.** Use one proof-carrying `Row`: its constructor receives
`Ascending elems`, its raw projection is `List`, and its extensionality theorem
applies only to checked rows. Keep `Row.ofList` absent; `normalize` is the only
proof-free raw-list route.

Foldlab provenance: late `s2/T016.lean` supplies the adopted `ascending_ext`
proof shape and the independent agreement/canonicality examples. Its digest is
in `git:c407ab7:vendor/foldlab/LATE-MANIFEST.tsv`; it is `evidenceOnly`.

## Order-preserving dedup is not normalization — `E4-DATA-CE-002`

**ATTACKED.** Removing repeated elements while retaining authored order is an
acceptable normalizer.

**WITNESS.** Order-preserving dedup maps `[2, 1, 2]` to `[2, 1]`. The frozen
reduction requires `Row.normalize [2, 1, 2]` to have elements `[1, 2]`; the
former output is not `List.Pairwise (· < ·)`.

**FORCED REPAIR.** Normalize by structurally recursive sorted insertion against
the ambient standard order. Prove exact membership and strict ascent.

Foldlab provenance: late `s2/attack-EC1-T012.lean` supplies the same failure
shape; its digest and `evidenceOnly` disposition are in the late manifest.

## Multiplicity is erased — `E4-DATA-CE-003`

**ATTACKED.** Normalization is injective, or the checked row retains authored
multiplicity.

**WITNESS.** `[1, 1] ≠ [1]`, but the contract requires both the general theorem
`Row.normalize_duplicate` and the ground equality
`normalize [1, 1] = normalize [1]`.

**FORCED REPAIR.** Make membership presence the row observation and state the
collision positively. Never offer a converse to `mem_normalize`.

## A private Effect4 order creates a second spelling — `E4-DATA-CE-004`

**ATTACKED.** `Data.Row` should bundle a comparator or define
`Effect4.RowOrder` so consumers can choose orders locally.

**WITNESS.** The battery's test-only `ReverseNat` satisfies the same standard
Lean law classes as Nat. Normalizing identities 1 and 2 spells projected values
`[2, 1]`, while ordinary Nat spells `[1, 2]`. A changed lawful order therefore
changes canonical content.

`Effect4.ServiceKey` already freezes name-major lexicographic `<`. A row-local
comparator could reverse it and silently create a second canonical spelling of
the same requirement keys.

**FORCED REPAIR.** Every comparing operation quantifies over `LE`, `LT`,
`DecidableEq`, `DecidableLT`, `Std.IsLinearOrder`, and
`Std.LawfulOrderLT`. The element owner supplies those instances for its frozen
relation. Keep `Effect4.RowOrder` and `Row.Comparator` absent.

## Concatenation and left-favouring merge are not union — `E4-DATA-CE-005`

**ATTACKED.** Union may append raw spellings or return the left operand whenever
it is non-empty.

**WITNESS.** Both
`union (normalize [1, 2]) (normalize [2, 3])` and the reversed operand order
must spell `[1, 2, 3]`. Append retains a duplicate 2 and is noncanonical;
left-favouring merge drops 3 and violates `mem_union`.

**FORCED REPAIR.** Prove union membership, then lift it through canonical
extensionality to associativity, commutativity, idempotence, and both empty
identities. Keep `Row.append` absent.

## Membership cannot drift from elements — `E4-DATA-CE-006`

**ATTACKED.** A row may carry one canonical list while a separate containment
test reports a different set.

**WITNESS.** Such a carrier can make `a ∈ r` false while `a ∈ r.elems` is true.
Every normalization and union equation could then look correct at one face and
fail at the other.

**FORCED REPAIR.** Freeze one `Membership` instance and prove
`Row.mem_def : a ∈ r ↔ a ∈ r.elems`. State insert, normalize, union, subset,
and counterexamples through that same membership face.

## Subset direction and weakening — `E4-DATA-CE-007`

**ATTACKED.** Weakening is raw prefix/sublist containment, or the direction of
the inclusion relation may be chosen later by Context.

**WITNESS.** A normalized row built from `[3, 1]` is a subset of the normalized
row built from `[1, 2, 3]`, despite neither raw input being a prefix of the
other. Reversing `Subset` would also reverse both union weakening statements.

**FORCED REPAIR.** Use the conventional direction
`Subset r s := ∀ a, a ∈ r → a ∈ s`. Prove decidability, reflexivity,
transitivity, `Subset r (r ∪ s)`, and `Subset s (r ∪ s)`. Program or environment
provision direction belongs to Context and is not baked into this data name.

## Opaque decision is not executable evidence — `E4-DATA-CE-008`

**ATTACKED.** Any inhabitant of `Decidable (a < b)` suffices, even when it is
classical and does not reduce.

**WITNESS.** A classical comparison can satisfy proposition-level signatures
while `by decide` fails to normalize insert, sort, duplicate erasure, union, or
subset. It also adds `Classical.choice` to theorem receipts. The frozen battery
contains reductions at every one of those operations.

**FORCED REPAIR.** Require explicit `DecidableEq` and `DecidableLT` instances,
use structural recursion, and keep exported theorem receipts within
`[propext, Quot.sound]`. No `Classical.choice` is admitted.

## Idempotence is not denotational preservation — `E4-DATA-CE-009`

**ATTACKED.** `normalize_idempotent` or `mem_normalize` proves normalization
preserves every meaning later assigned to a raw row.

**WITNESS.** `[1, 1]` and `[1]` collapse to one checked row while a denotation
that counts authored occurrences distinguishes them. Foldlab late
`s2/attack-EC1-T011.lean`, `synthAER_hides_the_duplicate`, has the same loss
shape.

**FORCED REPAIR.** Export row equalities only and keep
`Row.normalization_preserves_denotation` absent. A later calculus may bridge
normalization to its observation only after proving that observation is
multiplicity-insensitive.

## Evidence scope

The raw witnesses are logical counterexamples at their stated types. The Nat
and reverse-order reductions are finite executable probes pinning computation.
The forbidden-name reaction gate is a bounded public-surface test. None is a
host observation, program denotation, or exhaustive search of all faulty
implementations.

`DATA-PG-ROW/COUNTEREXAMPLES` closes only when all nine stable rows remain, the
production implementation makes the positive battery green, the reaction gate
kills its named mutants, and the generated evidence join links every ID to its
repair theorem or absence guard.
