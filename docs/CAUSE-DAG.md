# Cause and Exit proof DAG

Status: breaker-frozen, RED, 2026-09-01

This document is the bounded ownership and proof graph for `Effect4.Cause` and
`Effect4.Exit` as first-order data. It is not an Effect compatibility claim, a
continuation machine, or a cutover approval. `Effect4/Semantics/Cause.lean` and
`Effect4/Semantics/Exit.lean` remain annotation-only stubs until the red
contract in `test/contracts/cause-exit.contract.md` has an independently
implemented green proof graph.

The pinned source is `effect@4.0.0-rc.112` as vendored under
`vendor/effect-4.0.0-rc.112/src/`. Its reading is
`docs/effect-rc112-fiber-runtime.html` section 8.

## Scope

The packet contains only the polynomial information needed to state the eleven
Effect runtime census rows named below, relative to four externally admitted
alphabets:

- `ε` — the typed error;
- `δ` — the defect (rc.112 `unknown`);
- `ι` — the interruptor identity (rc.112 `fiberId: number | undefined` becomes
  `Option ι`);
- `α` — the annotation value (rc.112 `ReadonlyMap<string, unknown>` values).

It adds no effect syntax, primitive, continuation frame, fiber, scope, scheduler,
host `Error`, stack trace, span, JSON rendering, hash, or pretty printer. It
supplies:

- a finite insertion-ordered annotation map with unique `String` keys;
- a closed three-value reason tag alphabet;
- three reason constructors carrying payload and annotations, and nothing else;
- a cause that is exactly one ordered reason list;
- first-occurrence deduplication and the `Arr.union` combine;
- the four-armed squash;
- exits, the finalizer-cause merge, and the `exitAsVoidAll` join.

Fixing `ι := Effect4.FiberId` is a later packet's instantiation. Nothing here
imports or mentions `Effect4/Concurrency/`.

## Required semantic separations

1. **Semantics does not depend on Concurrency.** `Effect4/Semantics/*` must not
   import `Effect4/Concurrency/*` or anything above Semantics in
   `docs/ARCHITECTURE.md` "Dependency direction". The interruptor is the
   admitted alphabet `ι`, never `FiberId`. The concurrency representative's own
   contract already states that a later `Semantics.Exit` instantiation owes the
   result-arm separation proof; this packet supplies the carrier that
   instantiation will use, and it discharges none of that obligation here.
2. **A cause is not a set and not a tree.** `causeCombine` retains operand
   order, so `Effect4.Data.Row` — the repository's one canonical finite-set
   carrier, which is order-erasing and multiplicity-erasing — cannot carry a
   cause. `E4-SEM-CE-007` proves the separation; `E4-SEM-CE-001` proves that a
   sequential/parallel tree node is unobservable in rc.112.
3. **An annotation map is not a row.** `Effect4.ReasonAnnotations α` is a finite
   key-to-value map that retains insertion order. `Row α` stores no values, is
   parameterized by the element owner's lawful order rather than a key order,
   and erases both order and duplicates. The two roles are disjoint; neither is
   a view of the other, and no conversion is claimed.
   The name carries the `Reason` prefix because `Effect4.Annotations` is already
   taken: `Effect4/Schema/Payload.lean` owns
   `abbrev Annotations := Option (List AnnotationEntry)`, the persisted Schema
   annotation bag, whose surface is frozen by `E4-SCHEMA-CE-026` and
   `E4-SCHEMA-CE-027`. That carrier has a different key domain, a different
   payload type, an optional-versus-empty distinction this packet does not need,
   and a different owner. Reusing the name would be a hard duplicate-declaration
   failure in `Effect4.lean`; reusing the *carrier* would merge two unrelated
   alphabets. Neither is done.
4. **Refusal, frontier, and cause remain distinct.** This packet mints no
   refusal and no frontier carrier. A cause is a failure observation, never a
   scheduler-domain refusal and never fuel exhaustion.
5. **`Squashed` is not `Cause`.** Squashing is a lossy projection into a
   four-value observation used only by rc.112's throwing entry points
   (`runPromise`, `runSync`). It is not an alternative cause carrier and has no
   inverse.
6. **The WeakMap annotation memory is refused, not modelled.** See the boundary
   row below.

## Census rows this packet targets

Row summaries are the clauses that must become theorems. Take the exact text
from `generated/effect-runtime-census.tsv`; the table names the row ids and the
Effect4 obligation family that closes each.

| Census row | Closing obligations | State after this packet |
| --- | --- | --- |
| `cause.flat-reasons` | `Cause.ext`, `Cause.eq_iff`, `Cause.eq_iff_pointwise`, `Cause.empty_reasons` | green-able |
| `cause.reason-fail` | `Reason.tag_fail`, `Reason.annotations_fail`, `Reason.error_fail`, `Reason.fail_inj`, `Cause.fail_reasons` | green-able |
| `cause.reason-die` | `Reason.tag_die`, `Reason.annotations_die`, `Reason.defect_die`, `Reason.die_inj`, `Cause.die_reasons` | green-able |
| `cause.reason-interrupt` | `Reason.tag_interrupt`, `Reason.annotations_interrupt`, `Reason.interrupt_inj`, `Cause.interrupt_reasons` | green-able |
| `cause.combine-union` | `Cause.combine_empty_left/right`, `Cause.combine_reasons`, `Cause.mem_combine`, `Cause.combine_order`, `Cause.combine_nodup`, `Cause.combine_self` | green-able |
| `cause.finalizer-merge` | `Exit.mergeFinalizer_success_failure`, `Exit.mergeFinalizer_failure_failure`, plus the two remaining exact arms | green-able |
| `cause.squash` | `Cause.squash_error`, `Cause.squash_defect`, `Cause.squash_interrupted`, `Cause.squash_empty`, `Cause.squash_emptyCause_iff`, `Cause.squash_fail_over_die` | green-able, with the census-summary note below |
| `cause.annotations` | `ReasonAnnotations.*` receipts plus `Reason.host_memory_refused` | boundary closure only; see the refusal row |
| `exit.success-failure` | `Exit.cases_receipt`, `Exit.success_ne_failure`, `Exit.cause_*`, `Exit.causeReasons_*` | **partial** — the "is itself a primitive that can be stepped" clause is not modelled here |
| `exit.reason-alphabet` | `ReasonTag.all_nodup`, `ReasonTag.mem_all`, `ReasonTag.cases_receipt`, `Reason.cases_receipt`, `Reason.tag_mem_all` | green-able |
| `rule.cause-has-no-structure` | `Cause.ext`, `Cause.combine_no_new_reason`, `Cause.mem_combine` | green-able |

Two adjacent rows are also served, and are recorded here so a later joiner does
not mistake them for new work:

| Adjacent row | Served by | Note |
| --- | --- | --- |
| `scope.exit-as-void-all` | `Exit.asVoidAll_reasons`, `Exit.asVoidAll_nil`, `Exit.asVoidAll_all_success`, `Exit.asVoidAll_failure`, `Exit.asVoidAll_empty_cause` | outside the eleven assigned rows; the join decision belongs to the coverage owner |
| `scope.close-merge` | not served | this packet models only the merge function, not the parallel finalizer fibers |

**Census-summary note.** `causeSquash` at
`vendor/effect-4.0.0-rc.112/src/internal/effect.ts:298-309` has four arms: the
first `Fail` error, else the first `Die` defect, else
`Error("All fibers interrupted without error")`, else `Error("Empty cause")`.
The census row summary for `cause.squash` names only three. This packet models
all four. Whether the row summary is re-pinned to name the fourth arm is a
decision for the census generator's owner; the extra theorem is harmless to the
join either way, and no clause of the current summary is left without a
theorem.

## Existing-type rows

Every row is native to this contract. None renames or copies an Effect
TypeScript or Foldlab carrier. The `PORT-MANIFEST.md` "Effect TypeScript family
defaults" table disposes of `Cause and Exit` as *pure first-order data outside
`Program`*, with the required distinction "rc.112 Cause is an ordered reason
list; richer trees lower through a named lossy quotient"; the same table
disposes of `Effect success/failure` as `owned` core operations with typed
failure, defect, interruption, refusal, and live frontier kept distinct. Every
row below inherits those dispositions. `CAUSE-PG` abbreviates the
`CAUSE-PG-FLAT` graph defined further down.

| Stable public type | Owning module | Kind | Relationship | Pin | Assurance route |
| --- | --- | --- | --- | --- | --- |
| `Effect4.ReasonAnnotations` | `Semantics/Cause.lean` | canonical carrier | canonical finite key-to-value map for reason annotations; **not** a view, adapter, or second spelling of `Effect4.Data.Row`, which is the canonical finite *set* and stores no values | `internal/core.ts:178-239` (`annotationsMap`, `ReasonBase`, `annotate`) | leaf receipts linked to `CAUSE-PG.construction` |
| `Effect4.ReasonTag` | `Semantics/Cause.lean` | canonical finite alphabet | the closed rc.112 reason discriminator; no other tag alphabet claims this role | `Cause.ts:144` (`Reason<E> = Fail<E> \| Die \| Interrupt`) | leaf receipts linked to `CAUSE-PG.construction` |
| `Effect4.Reason` | `Semantics/Cause.lean` | canonical carrier | canonical failure-reason carrier; the concurrency representative's `τ` terminal alphabet is a *parameter* it may later be instantiated at, not a duplicate of it | `internal/core.ts:245-275` (Fail), `288-319` (Die), `internal/effect.ts:107-145` (Interrupt) | `CAUSE-PG` |
| `Effect4.Cause` | `Semantics/Cause.lean` | canonical carrier | canonical flat cause; explicitly *separate* from `Effect4.Data.Row` (order-retaining, duplicate-retaining) and from any tree-shaped cause, which `E4-SEM-CE-001` rejects | `internal/core.ts:138-176` (`CauseImpl`) | `CAUSE-PG` |
| `Effect4.Squashed` | `Semantics/Cause.lean` | derived observation alphabet | lossy projection of `Cause`; no inverse is claimed and it carries no annotations | `internal/effect.ts:298-309` (`causeSquash`) | leaf receipts linked to `CAUSE-PG.semantics` |
| `Effect4.Exit` | `Semantics/Exit.lean` | canonical carrier | canonical success/failure observation; separate calculus from `Effect4.Flow` diagnostics, from `SchedulerRefusal`, and from any frontier arm | `Exit.ts:118-157` | `CAUSE-PG` |

No public declaration in this packet duplicates an existing Effect4 carrier.
The duplicate-prevention check run before freezing was

```sh
grep -rhE '^[[:space:]]*(inductive|structure|abbrev|def)[[:space:]]+[A-Za-z]' \
  Effect4 --include='*.lean' \
  | grep -oE '(inductive|structure|abbrev|def) [A-Za-z0-9_.?]+' \
  | grep -iE 'cause|exit|reason|squash|annotat' | sort -u
grep -rnE '^\s*namespace\s+(Cause|Exit|Reason|ReasonTag|Squashed)\b' \
  Effect4 --include='*.lean'
```

It found no `Cause`, `Exit`, `Reason`, `ReasonTag`, or `Squashed` declaration or
namespace anywhere under `Effect4/`, and exactly one annotation collision:
`Effect4.Annotations` in `Effect4/Schema/Payload.lean`, resolved by the naming
ruling in separation 3 above. `Effect4/Schema/Annotations.lean` owns Schema
*document* annotation traversal — a different alphabet, key domain, and owner.
The Schema modules and this one must not be merged; neither is a view of the
other, and no conversion between them is claimed.

## Named boundary and refusal

| Boundary | Row | What is refused | Evidence |
| --- | --- | --- | --- |
| `CAUSE-FB-WEAKMAP` | `cause.annotations` (`foreignBoundary`) | rc.112 remembers annotations per *original host error object* in a `WeakMap` keyed by JavaScript object identity (`internal/core.ts:178`, used at `internal/core.ts:197-204`). Two structurally equal errors can be distinct objects with different remembered annotations. | `Reason.host_memory_refused`: any Effect4 recall function `ε -> ReasonAnnotations α` is a function of the *value*, so the identity distinction is not representable. This is a theorem-shaped refusal, not a model of the WeakMap. |
| `CAUSE-FB-REFERENCE-EQ` | `cause.reason-interrupt`, `cause.combine-union` | rc.112 compares annotation maps by reference (`this.annotations === that.annotations` for `Interrupt` at `internal/effect.ts:124-131`; `Equal.equals` falls back to reference equality for a plain `Map` in `Fail`/`Die`), and `causeCombine` returns the *original object* when the union is structurally equal. | Authored refusal row. Effect4 equality on `ReasonAnnotations` is structural over the ordered entry list, which is strictly coarser than reference equality and strictly finer than key-to-value content equality. `ReasonAnnotations.order_retained` proves the second inequality. Reference identity is not observable in the Effect4 model, and no theorem in this packet claims it is. |
| `CAUSE-FB-ERROR-MESSAGE` | `cause.squash` | rc.112's third and fourth squash arms construct host `Error` objects carrying the strings `"All fibers interrupted without error"` and `"Empty cause"`. | Authored refusal row. `Squashed.interruptedWithoutError` and `Squashed.emptyCause` are nominal constructors; this packet claims no host `Error`, no message bytes, and no stack. A later target profile may pin the strings. |

## Declaration and proof graph

```text
CAUSE-L0-ANNOTATIONS ----.
CAUSE-L0-REASON-TAG -----|
                          v
                   CAUSE-L1-REASON
                          |
                          v
                   CAUSE-L2-CAUSE
                    /            \
                   v              v
        CAUSE-L3-COMBINE     CAUSE-L3-SQUASH
                   \              /
                    v            v
                     CAUSE-L4-EXIT
                          |
                          v
                CAUSE-L5-COUNTEREXAMPLES
                          |
                          v
          CAUSE-L6-COVERAGE-JOIN (later obligation)
                          |
                          v
          CAUSE-L7-HOST-EVIDENCE (later obligation)
```

`CAUSE-L0-ANNOTATIONS` and `CAUSE-L0-REASON-TAG` close with local receipts and
link to one named parent edge each; they do not receive invented graphs.
`CAUSE-L1` through `CAUSE-L5` form one graph, `CAUSE-PG-FLAT`, because changing
any of them changes what a failure observation *is*.

## Node ownership

| Node | Production owner after dispatch | Required receipt |
| --- | --- | --- |
| `CAUSE-L0-ANNOTATIONS` | `Effect4/Semantics/Cause.lean` | unique-key invariant, `lookup`/`keys` equations, the exact `annotate_entries` merge shape, the four `lookup_annotate_*` laws, `annotate_empty`, and `order_retained` |
| `CAUSE-L0-REASON-TAG` | `Effect4/Semantics/Cause.lean` | constructor census, `Nodup`, `mem_all`, exhaustive cases, `DecidableEq`, `Repr` |
| `CAUSE-L1-REASON` | `Effect4/Semantics/Cause.lean` | three constructors with payload and annotations; `tag`, `annotations`, `error?`, `defect?` equations; per-constructor injectivity; exhaustive cases; `annotate` commutation; `DecidableEq` derived from the four alphabets |
| `CAUSE-L2-CAUSE` | `Effect4/Semantics/Cause.lean` | one field; `ext`; `eq_iff`; rc.112 pointwise equality; the three single-reason constructors; `annotate_reasons` |
| `CAUSE-L3-COMBINE` | `Effect4/Semantics/Cause.lean` | `dedup` equations and its `Nodup`/idempotence receipts; both empty identities; the definition-level union law; membership; `Arr.union` order; `Nodup` preservation; the structural short circuit |
| `CAUSE-L3-SQUASH` | `Effect4/Semantics/Cause.lean` | all four arms, the first-occurrence order receipt, and the `emptyCause` characterisation |
| `CAUSE-L4-EXIT` | `Effect4/Semantics/Exit.lean` | two constructors, separation, projections, the four exact `mergeFinalizer` arms, the three `restoreAfterFinalizer` arms, and the exact `asVoidAll` concatenation |
| `CAUSE-L5-COUNTEREXAMPLES` | `Effect4Test/Counterexamples/Semantics/CauseExit.lean` | seven registered witnesses, all proved, all within the axiom ceiling |
| `CAUSE-L6-COVERAGE-JOIN` | `Effect4Test/Audit/RuntimeCoverage.lean` (not this packet) | later obligation; see below |
| `CAUSE-L7-HOST-EVIDENCE` | a later Effect TypeScript conformance packet | later obligation; direct runtime and type receipts |

## Graph-edge ledger

The graph-bearing owner is `CAUSE-PG-FLAT`. Passive leaves link to it; they do
not receive duplicate graphs.

| Edge | Breaker state | Reason and closure evidence |
| --- | --- | --- |
| identity | `required-open` | exact public declaration snapshot plus the six existing-type rows above; closed when the frozen battery's ascriptions elaborate |
| construction | `required-open` | constructors, the `ReasonAnnotations` unique-key invariant, `ReasonTag` census and `Nodup`, and the derived `DecidableEq` instances |
| semantics | `required-open` | the observations this packet exposes: `Reason.tag`/`error?`/`defect?`, `Cause.reasons`, `Cause.squash`, `Exit.cause?`/`causeReasons`. No transition system is claimed |
| laws | `required-open` | the combine, squash, annotate, finalizer-merge, and join theorem spine |
| representation | `required-open` | `Cause.eq_iff_pointwise` and `Cause.ext` are the claimed normalization facts; `dedup_of_nodup` and `combine_self` are the claimed canonicality facts. No serialization or wire round trip is claimed by this packet |
| counterexamples | `required-open` | all seven `E4-SEM-CE-*` witnesses exist and are proved, but their repairs cannot close before implementation |
| bridges | `required-open` | the three `CAUSE-FB-*` boundary rows are the declared loss to the pinned host. `Reason.host_memory_refused` is the only theorem-shaped one; the other two are authored refusals and stay open until a later packet either states or retires them |
| targets | `not-applicable` | no TypeScript lowering, byte stability, or runtime observation is claimed here. The rc.112 squash message strings are explicitly refused under `CAUSE-FB-ERROR-MESSAGE`; refusing a target spelling does not erase the semantic obligations above |
| trust | `required-open` | `#print axioms` receipts for every public theorem, in `Effect4Test/Semantics/CauseExitAxiomReport.lean`, within `propext`/`Quot.sound` |
| coverage | `required-open` | the frozen contract must join every exported declaration to one owner route, and the generated declaration snapshot must show no unannotated exported type |

No edge is omitted. `targets` is the only `not-applicable` row and it carries
its reason.

## The generated assurance join is a later obligation

This packet writes no generated projection and edits no file under
`generated/`, `Effect4Test/Audit/`, or `Effect4Test/Concurrency/`. Three joins
therefore remain open after the builder turns the battery green:

1. **The Effect runtime coverage join.** A theorem in `Effect4/` moves no
   coverage number by itself. Each witness must be added to the matching row in
   `Effect4Test/Audit/RuntimeCoverage.lean` with its axiom receipt and its
   exact `#check (@name : proposition)` ascription, `snapshotWitnesses` must be
   extended in the same order, and `./scripts/check-effect-runtime-census.sh`
   must pass. `docs/RUNTIME-COVERAGE.md` owns the rules; that edit is a
   separate packet with a separate claim.
2. **The declaration and assurance snapshot.** The generated per-declaration
   assurance join must show every exported declaration of
   `Effect4/Semantics/Cause.lean` and `Effect4/Semantics/Exit.lean` resolving
   to exactly one of the routes in the existing-type table. No such generator
   exists for `Effect4/Semantics/` today; standing one up, or extending an
   existing one, is the coverage edge's real closure condition.
3. **Host evidence.** `CAUSE-L7` needs direct rc.112 runtime and type
   observations. A Lean theorem about this model closes no host edge, and a
   language-service diagnostic is auxiliary.

Until those land, this graph may be reported as *breaker-frozen with an open
coverage edge*, never as a closed category and never as a coverage number.

## Determinism, totality, and claim boundary

Every operation in this packet is a total first-order function over finite
data. There is no relation, no fuel, no choice, and therefore no determinism
theorem to state — that is a property of the carrier, not a result. Nothing
here claims that Effect4's `Cause` is *equivalent* to rc.112's `Cause`: the
claim is that each named clause of each named census row has an exact theorem
over the Effect4 model, with the three `CAUSE-FB-*` rows naming what was
deliberately dropped.

`exit.success-failure` is explicitly **partial**: its second clause, that an
`Exit` is itself a steppable primitive, needs the continuation-machine calculus
that `docs/RUNTIME-COVERAGE.md` "Path to full coverage" assigns to a later
model. Reporting that row green on the strength of this packet would be a
false green.
