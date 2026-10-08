# The host boundary: host answers, handle declarations, and the external-reply contract

The authority for how a host answers a program's calls: what the runtime does today, what is
known to be wrong, the contract the external lane must meet, the interim profile, and the order
of work. Written 2026-09-30 at `be15b062`. Decisions rows 95–100 own its open choices. The
derivations and probes are research records:
- [the external runtime contract](../research/2026-09-30-external-runtime-contract.md) (Codex,
  the full lane);
- [host answers and the typed guarantee](../research/2026-09-30-host-answers-and-typed-guarantee.md);
- [the plan review](../research/2026-09-30-origin-plan-review.md) and its
  [ratification conditions](../research/2026-09-30-origin-plan-review/RemediationReview.md);
- the probes in `docs/research/2026-09-30-host-answers-evidence/` and
  `docs/research/2026-09-30-external-runtime-contract/`.

**Status (owner, 2026-09-30).** The near-term work here is the interim rule (§5), with the M6
in-scope repair (row 95) and the value membership fix (row 96). The full contract (§4) and its
order (§6) are parked until host services need them. They stay written down so the path is known
(`system-map.md` §3).

## 1. Scope and completion

"Complete" has two named scopes.

1. **The current admitted core.** Every permitted row, value, completion and session case has
   semantics, an executable admission check, a proof that the prepared answer is typed, and a
   table-aware agreement with the reference machine. A case outside the published profile is
   refused, with a located reason, before execution.
2. **Module and target expansion.** Each new host binding, stored-behavior API, transaction
   profile, runtime container and compiler target brings its own obligations. Nothing about all
   of Effect, arbitrary foreign objects, or an unproved whole compiler follows from scope 1.

The typed-state guarantee (M5–M7) on runs without host answers is a first, provisional result.
The public promise, that typed programs using host services stay typed, is claimed only when this
lane lands (row 99).

## 2. How host answers flow today

- **The live session is the canonical route.** `advance` refuses an answer given as a plain
  decision (`advance`, `src/Effect4/Api/HostSession.lean`). A reply enters only by `submit`
  through `preflight`, and `applyReply` checks it again when it applies it.
- **The admission check** (`Program/Admit.lean`). `admit` (`:77`) requires the fiber to be parked
  at that token on an external row. `admitAnswer` then checks the answer:
  - a success value goes through `externalValue` (`src/Effect4/Program/Compile.lean`). At a
    handle-typed row a number is an allocation request that becomes a new external handle; any
    other value must pass `Val.hasTy` and carry no external handle;
  - every handle must exist (`mintedIn`, `src/Effect4/Program/Admit.lean`);
  - typed failures must fit the row's error type;
  - a delayed cell read (`ofRefGet`) is checked by what the cell holds at that moment.
- **The check at the call's instance** (decisions row 323). An external registration keeps the
  address of its call. Where the row's own columns refuse a completion, the session checks it
  again at the checker's instance at that address (`acceptAtInstance`,
  `src/Effect4/Program/Admit.lean`; `HostSession.instanceAt`). A success admitted there is a
  member of the instance's answer column with no handle, and it reaches the program unchanged
  (`instance_prepared_success`). The checked replay does not take this path yet.
- **Preparation.** `prepareExternalAnswer` (`src/Effect4/Program/Compile.lean`) turns an accepted reply into the
  code the fiber resumes with, allocating any new external handle.
- **Tape replays.**
  - `Api.replayChecked` runs `admit` before each decision, but compiles with the execution
    budget.
  - `Api.replay`, `Typed.replay` and `replayAdmitted` do not admit decisions; by their
    documentation the caller does.
- **The reference machine takes the row table** (decisions rows 313 and 314). The frame
  machine and the reference machine agree at every row table when no answer is preloaded
  (`run_eq_ref_table_noPreload`, `src/Effect4/Laws/Program/Table/Agreement.lean`). The case
  with preloaded answers waits on their deletion (DI-23).

## 3. Known holes, with evidence

| Hole | Evidence | Row |
| --- | --- | --- |
| The runtime check accepts a live handle of the wrong declared type. A program checked at `nat` finishes with a string on the certified live session (start, bind, submit, apply) and on the checked replay. `Val.hasTy` checks a handle by kind only (`src/Effect4/Program/Typed.lean`); `mintedIn` checks only that it exists. Fiber handles are exploitable now; native cells and deferreds hold numbers only, and generic cells would open the same gap. | `host-answers-evidence/Probe.lean` §2 (proposed `E4-HOST-CE-007`); the contract's `Probe.lean` | 97 |
| The proof's value predicate checks nothing inside products, Results or successful exits, and a union can take shape from one branch and handle evidence from another (`Laws/Program/Typed/Admission.lean:39-62`). A closed program with no host stores a fiber handle in a pair, projects it and awaits it; it checks at `nat` and runs to 7. | the contract's `PredicateProbe.lean`; `host-answers-evidence/PathProbes.lean` §D | 96 |
| M6's capstone counts every decision tape: a `sleep` answered with `42` finishes with `42`. | `origin-plan-review/Probe.lean`, `current_m6_capstone_false` (proposed `E4-SCHED-CE-015`) | 95 |
| The certificate-first `Typed.replay` runs unchecked answers. | `origin-plan-review/RemediationProbe.lean` | 98 |
| `replayChecked` uses the execution budget for compilation; swapping it in changes an unfinished run into a finished one. | `RemediationProbe.lean` | 98 |
| An allocation reply is tied to the allocation count when it is applied; two replies checked against one snapshot need not both apply. | the contract's `Probe.lean` | 100 |
| **Repaired 2026-10-03.** The runtime check accepted a host failure carrying `badName` or `notImplemented`, the machine's own markers for malformed code, which the typed exit judgment refuses (`NoShapeDefect`, row 152); so `admit = none` did not imply `AnswerOk` on failures. Admission now refuses them on both paths (`Refusal.reservedDefect`). | `docs/research/2026-10-03-session-work/t4-audit.lean` (Codex); `Test/Counterexamples/Machine/Runtime/HostReservedDefect.lean` (`E4-HOST-CE-008`) | 191 |

## 4. The contract (proposed; rows 96–100)

### 4.1 The interfaces owed

| Interface | Meaning |
| --- | --- |
| `RequestFits` | The live (fiber, token) identifies the exact external row and evaluated request; request values and required services fit their declared types. |
| `HostProgress` / `HostComplete` | A binding may take observable host steps before completing; a completed success or failure keeps its resulting host state. |
| `ReplyEnvelope` | Version, session, binding, the exact raw table, call id, key, row, request and category match the recorded call. |
| `ReplyFits` | The received data and capability claims are valid for this call. Checking runs nothing, allocates nothing, consumes nothing. |
| `PrepareReply` | For a currently applicable reply: the prepared completion, the new store, the capability and ownership correspondence and the extended typing world, or a located refusal. |
| `PreparedFits` | The prepared completion fits the parked continuation's intermediate type in the resulting world. |
| `ApplyReply` | Select one key, prepare and resume it, consume its guard at most once, keep all committed state across a later failure or frontier. |
| `RegistryAgrees` | The executable handle declarations agree with actual allocations, checked creation sites and the proof world. |

Envelope matching alone is not answer typing, and answer typing alone is not evidence that a real
host binding did the specified work.

### 4.2 Lifecycle

`issued → host pending → acquired, unprepared → received → prepared, machine-owned → cleanup
pending → released`, with `compensation pending` for an unprepared acquisition that is cancelled
or refused.

- Receiving a reply stores it once for its key and runs nothing.
- Applying it prepares atomically: the whole candidate update is validated before any part
  commits.
- Exhausting fuel after preparation keeps the prepared state and never prepares again.
- Interruption before application retires the association. An unprepared acquisition is
  compensated only when no other valid claimant remains.
- Recovery replays recorded commands and replies. It never repeats host work, transfers a
  resource twice or repeats compensation.
- At-most-once consumption is not exactly-once network side effects; that needs durable journal
  and idempotency obligations of its own.

### 4.3 Handle declarations come from creation evidence

The runtime keeps no types in values, and a host reply cannot create, replace or widen the
declaration of an existing internal handle. Declarations are derived:

- **A fiber.** From its creation record, read by the checker: the fork ledger's site and the
  creating construct's kind (`machine-state.md` §7; row 91), with the checker's static
  environment at that site. A probe derives `string` for a forged fiber and `nat` for an honest
  one (`PathProbes.lean`, path B).
- **Forks the runtime makes without a source point** record the empty site: finalizer forks, and
  races without a source site. They carry their construct's kind, which fixes their type.
- **The root fiber** has the program's certified type.
- **Cells and deferreds.** Today's native ones hold numbers only. Generic cells (rows 42–44) need
  creation evidence in the same pattern.
- **External resources** have a stable host key scoped to the binding and session, separate from
  the machine's allocation index. The machine allocates only when a selected reply is applied.

A reply carries a reply-local capability environment. Every handle in it resolves through that
environment with an exact kind check; aliases reuse one entry. A union branch is chosen by the
whole shape-and-capability judgment. If several branches fit, their prepared effects must agree;
otherwise the reply is refused as ambiguous. Under `unknown`, ordinary data is kept and every
embedded capability is still checked.

### 4.4 Membership: one judgment over the actual encoding

Shape and handle evidence are checked in one derivation over the value encoding that `Val.hasTy`
reads (row 96). One executable check and its proof-side mirror are joined by a connecting lemma;
no other value-type check is added. Every `Ty` constructor has its clause:

| `Ty` constructor | At the boundary |
| --- | --- |
| `never` | no successful inhabitant (a row answering `never` may still fail, defect, be interrupted or pend) |
| `unit`, `bool`, `string` | the exact image |
| `nat` | the exact natural number in the semantic core; a target's bound is explicit and covers intermediate values (`lcnf-route.md` §8) |
| `int` | no inhabitant today; an explicit unsupported profile entry |
| `handle` | the exact reserved internal kind, or external target correspondence; contexts by their static service types |
| `option` | absent or present, the payload recursively |
| `list` | one decoded element view for ordinary lists and fiber snapshots, every element recursively |
| `prod` | the actual two-element list encoding, both columns recursively |
| `except` | the exact constructor, the selected arm recursively |
| `exitOf` | decoded once; a success recursively; a failure by its cause image |
| `causeOf` | every typed failure fits its error column; defects and interruptions keep their categories |
| `fiberOf` | an existing fiber whose declaration is a subtype of the answer and error |
| `union` | at least one complete branch, under §4.3's agreement rule |
| `lit` | the exact string literal |
| `refOf` | an existing cell with the declared type up to equal normal forms (row 137), not the type of its current contents |
| `deferredOf` | an existing deferred with the declared answer and error up to equal normal forms (row 137) |
| `var` | refused: templates are instantiated before admission |
| `unknown` | ordinary data plus capability validation |

For completions:
- `ofExit (success v)` is prepared, then must be a member at the row's answer type in the new world;
- `ofExit (failure c)` is checked against the supported error image, with order and annotations
  kept;
- `ofRefGet cell` checks the cell's declared type against the answer type and keeps the read
  delayed.

### 4.5 Theorem shapes

**Receipt.** Under the typed-state invariant, `RegistryAgrees`, a lawful table and a live call,
accepting a reply establishes the envelope and the boundary judgment at the receipt state. It
promises nothing about applying it later.

**Application.** At application time, under the same invariants, a still-live key, the retained
reply, the binding's current correspondence and a successful recheck give three things:
- preparation yields a valid state and world extension;
- ownership is accounted for exactly;
- the completion fits the token's intermediate type in the new state.

Unrelated allocation alone cannot invalidate a claim.

The converse is owed on the admitted profile: every semantically valid, representable reply is
accepted.

### 4.6 Entry paths

| Route | Disposition |
| --- | --- |
| `HostSession`, `Runner`, `Run` | the canonical checked keyed route |
| `Typed.replay` | consumes a session header and a `Runner.Command` journal through the checked keyed session, with both budgets and phases that can refuse (row 98) |
| `Api.replayChecked` | low-level evidence; budgets separated; no claim of host-envelope conformance |
| raw `Api.replay`, `replayAdmitted` | low-level; the caller admits decisions |
| the preloaded external answer list | migrated with its provenance and removed from production paths (DI-23, DI-58) |
| timers, yields, deferred deliveries | typed through their own delivery paths, never through external admission |
| the OCaml engine | needs a table-aware keyed entry path of its own |

### 4.7 Required controls

**Positive.** These must pass:
- scalar and structured answers for every inhabited constructor;
- fresh, existing, nested and aliased resources;
- typed failures and mixed causes;
- delayed cell reads with legal writes in between;
- two acquisitions in both receipt and application orders;
- cancellation before receipt, after receipt and after preparation;
- zero execution budget with a positive compile budget, and the reverse;
- a resource stored in a Ref, read, used by a second call, then released.

**Negative.** Each must be refused, independently:
- every envelope field mismatched in turn;
- duplicate, stale and retired replies;
- forged resource identity;
- unallocated handles, and handles of the wrong target or wrong declaration;
- internal targets minted as external;
- each structural gap of §3;
- a delayed read whose current value fits but whose declared type is too wide;
- missing, conflicting or unused capability entries;
- a partial preparation followed by refusal;
- lost cleanup responsibility.

## 5. The interim profile (row 97)

Until declarations for a handle kind land, host rows whose answer or error types carry that
internal kind (fiber, cell, deferred, scope, context) are refused when a table is admitted, with a
located refusal. All fifteen host rows in the tree pass this rule
(`PathProbes.lean`, path A). The rule is stricter than row 7's open recommendation, which admits
handles arriving in-process. It is lifted kind by kind as declarations land.

The reply check enforces the same rule on values: a success value carries no handle except a fresh
external allocation.
- **Why it is needed.** Today the check refuses only external handles (`externalValue`,
  `src/Effect4/Program/Compile.lean`). So a row answering `unknown` could carry a live internal handle
  even with the table rule in place.
- **Typed failures need no new check.** The error alphabet is closed, and every decoded error is
  handle-free (`valOfErr_keys`, `causeImage_handleFree`).
- **Reserved defects are refused (row 191).** A failure whose cause dies with `badName` or
  `notImplemented` is refused before its error column is read (`reservedDie`, `Program/Typed.lean`),
  on the decision path and the oracle path alike. Every other defect and every interrupt stays
  admitted at every error column. An accepted failure therefore satisfies the typed judgment's
  defect exclusion (`preflight_failure_noShapeDefect`, `Laws/Api/HostSession.lean`).
- **One test fixture falls under the rule:** the row `"cell"` of `Test/Api/ExternalContract.lean`,
  which answers a cell. Host-returned internal cells wait for the registry (row 7).

This is item A of the [slice 6 brief](../research/2026-09-30-codex-brief-slice6-and-fixes.md), as
amended by its [addendum 1](../research/2026-09-30-codex-brief-slice6-addendum-1.md).

## 6. Order (parked until needed, except X0's rows 95–96 and the interim rule)

These are the contract's X-steps (its §9), with the fiber slice first:

1. **X0.** Record the rulings (rows 95–100) and reconcile the frozen packets. The M6 in-scope
   repair and the membership amendment go before M6 proof work.
2. **The fiber slice.** The fork ledger's site and kind, the static environment at a path, the
   one-recursion membership check, admission against derived fiber declarations, and the
   typed-replay route. It closes the live hole for fibers without generic cells.
3. **X1.** Declared capabilities and preparation in general: the registry, recursive preparation,
   aliases, ownership.
4. **X2.** The keyed lifecycle, both budgets, disposition of the legacy paths, the image codec.
5. **X3.** The reference connection: a table-aware reference and the DI-57 statement. The
   empty-table theorem becomes its corollary.
6. **X4.** The checked application guarantee over all valid execution prefixes, and the public
   typed entry paths.
7. **The Ref slice** (acquisition, a handle in a Ref, a second call, release) after the
   generic-cell work of rows 42–43.

## 7. Decision 12 and the boundary rule (2026-09-10; written here 2026-10-01, row 122)

Two owner rulings of 2026-09-10 govern every boundary in this document. Until 2026-10-01 they
lived only in research notes, now force-added
([Decision 12](../research/2026-09-10-schema-at-boundaries.md),
[the boundary decisions](../research/2026-09-10-boundary-decisions.md)); decisions row 122 writes
them here. Cite the first as "Decision 12", never "D12": in tracked files "D12" also names other
things.

**Decision 12: every boundary value carries an Effect Schema.**
`Ty.schema` writes a persisted description in `src/Effect4/Schema/Bridge.lean`.
`EffTy.document` publishes the exit description and requirement keys.
`Row.document` publishes request, answer and error descriptions.
The Schema language describes data; effectful behavior remains program content.

`Bridge.ofSchema_schema` states retraction for closed, reserved-free raw types.
`Bridge.ofSchema_exact` states exactness under `Bridge.normS` after successful Schema reading.
Both declarations live in `src/Effect4/Schema/Bridge.lean`.
The public type face normalizes record fields and the two-item tuple/product alias.
Raw Schema reading separately retains property order and optional flags.
Formation separately refuses repeated declaration names.

`Schema.encode` and `Schema.decode` live in `src/Effect4/Schema/Codec.lean`.
They include records, string maps and fixed-size tuples, composed with the existing supported leaves.
The decoder refuses duplicate JSON keys before sorting, undeclared record fields and missing required fields.
An absent optional field differs from a present value containing an option.
Opaque handles and unsupported leaves have no new JSON image.
Type support does not establish value-level codec admission.

`Schema.decode_iff` states exactness under `Codec.normJ` in `src/Effect4/Laws/Schema/Codec.lean`.
It covers every type; both public operations normalize the type first.
The normalizer retains duplicate keys and sorts object entries recursively.
A host JSON text parser may discard duplicates before supplying the Lean JSON value.
That parser behavior remains outside the Lean theorem.

The finite comparisons in `harness/truth/schema-codec/check.ts` cover the new data shapes against rc.112.
The strict comparison uses `onExcessProperty: "error"` for host decoding.
The default host decoder discards extra record fields; the Lean decoder refuses them.
The controls retain these differences and the duplicate-key text parsing difference explicitly.
The [Schema host receipt](../research/2026-10-03-data-language/schema-host-receipt.md) records their scope and commands.

S-5 remains the requested finite host check of recorded exits against their published `Schema.Exit`, under decision row 5.
The Lean codec laws alone establish no rc.112 execution or external host progress.
Decision 12 answers DI-08 for the persisted description plane.

**The boundary rule.** The owner's rule for every boundary: "fidelity to a normal Effect TS
project where possible; never break host code because a type at a boundary was declared narrower
or differently than the host sees it; be comprehensive and overload rather than refuse"
(`2026-09-10-boundary-decisions.md` §1). There are four boundaries where a type is declared on
one side and observed on the other:

| boundary | declared by | observed by | what "not breaking" means |
| --- | --- | --- | --- |
| B-print | the checker's type, printed as `Effect.Effect<A, E, R>` on the module | the pinned TypeScript compiler | mutually assignable, both directions |
| B-accept | Lean's typing rules | a program rc.112 accepts | Lean accepts it too, or refuses it by a named refusal, never by a wrong type |
| B-row | a row's request, answer and error columns | the real package through the adapter | the adapter's projection inhabits the column exactly |
| B-tape | the row's answer and error columns | a recorded host answer on replay | admitted whenever the host's value is a member, at any subtype of the column |

"Overload" means: at B-accept and B-tape, widen what Lean admits; at B-print, declare what the
compiler would infer; at B-row, project at the adapter, never in the program.

**Route A, the one boundary decode route** (row 122). Host data enters a program as a typed host
answer, checked by membership at the reply (§4.4). Every reply the session accepts at a call is a
member at the call's answer type in the new world. At a row with no type parameter that type is
the row's answer column. At a template row it is the call's checked instance (decisions row 323).
So a row from `List<A>` to `Option<A>`, called at a list of numbers, takes `some 1`. So the host adapter decodes with the call's instantiated schema, not the row's template;
the session checks a `Val`, and nothing in the program parses. A reply that is not a
member is refused with a located `envelope` refusal; an internal handle is refused by §5's rule.
