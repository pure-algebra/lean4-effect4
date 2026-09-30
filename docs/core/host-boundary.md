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
  decision (`Api/HostSession.lean:239-243`). A reply enters only by `submit` through `preflight`,
  and `applyReply` checks it again when it applies it (`:204-215`).
- **The admission check** (`Program/Admit.lean`). `admit` (`:77`) requires the fiber to be parked
  at that token on an external row. `admitAnswer` then checks the answer:
  - a success value goes through `externalValue` (`Program/Compile.lean:1354`). At a
    handle-typed row a number is an allocation request that becomes a new external handle; any
    other value must pass `Val.hasTy` and carry no external handle;
  - every handle must exist (`mintedIn`, `Admit.lean:25`);
  - typed failures must fit the row's error type;
  - a delayed cell read (`ofRefGet`) is checked by what the cell holds at that moment.
- **Preparation.** `prepareExternalAnswer` (`Compile.lean:1369`) turns an accepted reply into the
  code the fiber resumes with, allocating any new external handle.
- **Tape replays.**
  - `Api.replayChecked` runs `admit` before each decision, but compiles with the execution
    budget.
  - `Api.replay`, `Typed.replay` and `replayAdmitted` do not admit decisions; by their
    documentation the caller does.
- **The reference machine ignores the host table.** It has no external registration, no
  conversion or allocation, no prepared answer, and no way to take a table-aware interpreter.
  These are the four gaps filed with DI-57 (`Test/contracts/machine-scheduler-core.contract.md`,
  "Table-aware agreement"). `run_eq_ref` therefore holds at the empty table only
  (`Laws/Program/RuntimeR.lean:203-210`).

## 3. Known holes, with evidence

| Hole | Evidence | Row |
| --- | --- | --- |
| The runtime check accepts a live handle of the wrong declared type. A program checked at `nat` finishes with a string on the certified live session (start, bind, submit, apply) and on the checked replay. `Val.hasTy` checks a handle by kind only (`Program/Typed.lean:34`); `mintedIn` checks only that it exists. Fiber handles are exploitable now; native cells and deferreds hold numbers only, and generic cells would open the same gap. | `host-answers-evidence/Probe.lean` §2 (proposed `E4-HOST-CE-007`); the contract's `Probe.lean` | 97 |
| The proof's value predicate checks nothing inside products, Results or successful exits, and a union can take shape from one branch and handle evidence from another (`Laws/Program/Typed/Admission.lean:39-62`). A closed program with no host stores a fiber handle in a pair, projects it and awaits it; it checks at `nat` and runs to 7. | the contract's `PredicateProbe.lean`; `host-answers-evidence/PathProbes.lean` §D | 96 |
| M6's capstone counts every decision tape: a `sleep` answered with `42` finishes with `42`. | `origin-plan-review/Probe.lean`, `current_m6_capstone_false` (proposed `E4-SCHED-CE-015`) | 95 |
| The certificate-first `Typed.replay` runs unchecked answers. | `origin-plan-review/RemediationProbe.lean` | 98 |
| `replayChecked` uses the execution budget for compilation; swapping it in changes an unfinished run into a finished one. | `RemediationProbe.lean` | 98 |
| An allocation reply is tied to the allocation count when it is applied; two replies checked against one snapshot need not both apply. | the contract's `Probe.lean` | 100 |

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
| `refOf` | an existing cell with exactly the declared type, not the type of its current contents |
| `deferredOf` | an existing deferred with exactly the declared answer and error |
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

## 6. Order

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
