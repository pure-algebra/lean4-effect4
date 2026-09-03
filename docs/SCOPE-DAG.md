# Scope runtime proof DAG

Status: base implementation present; generated assurance and host connections
remain open. The original frozen requirements below are retained, with the
separate close-stepping continuation recorded at the end (2026-09-03).

This document owns the bounded Scope state machine and its independently
stepping close interpreter. `Effect4/Runtime/Scope.lean` implements the base
contract; `Effect4/Runtime/ScopeMachine.lean` implements the later request and
response contract. These local implementations do not close the generated
assurance, fiber, region-compilation or host connections, and do not approve
cutover.

The pinned source is `effect@4.0.0-rc.112` as vendored under
`vendor/effect-4.0.0-rc.112/src/`. Its reading is
`docs/effect-rc112-fiber-runtime.html` section 6.

## Scope

The packet contains only the polynomial information needed to state the
fifteen Effect runtime census rows named below, relative to the four cause
alphabets already owned by `Effect4/Semantics/Cause.lean` and two new
externally admitted alphabets:

- `κ` — the finalizer key. rc.112 keys a finalizer by a fresh JavaScript object
  (`const key = {}`, `internal/effect.ts:3840`) and compares keys by reference.
  Effect4 admits `κ` with `DecidableEq` and compares by value; the freshness of
  `{}` is refused, not modelled, under `SCOPE-FB-KEY-IDENTITY`.
- `φ` — the finalizer name. rc.112 stores
  `(exit: Exit<any, any>) => Effect<void>`. DB-02 forbids a Lean closure in
  canonical program content, so the scope stores a nominal `φ` and nothing
  else. What a finalizer *does* is supplied to the closing operations as the
  argument
  `run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α`.

**Why `run` is a function argument and not a stored field, a relation, or a
constructor.** Three shapes were considered.

1. *Stored closure.* `ScopeState.openInline (key : κ) (finalizer : Exit -> Exit)`
   is exactly what DB-02 excludes: the finalizer would be Lean function data
   inside canonical scope content, so a scope would have no decidable equality,
   no serialisable spelling, and no first-order identity. Rejected.
2. *Relation.* `Run : φ -> Exit -> Exit -> Prop` supplied as a parameter would
   let a later packet model a nondeterministic finalizer. Nothing in the pinned
   scope code is nondeterministic: `scopeCloseUnsafe` calls each finalizer once
   and reads back one exit. A relation would force every close law to become
   an existential over an unconstrained witness, would delete every ground
   `decide` receipt, and would state *less* about rc.112 than a function does.
   Rejected for this packet, and recoverable later: relaxing a function
   parameter to a relation is an additive change with its own breaker packet,
   the same way `docs/DESIGN-BASIS.md` DB-03 keeps open nondeterminism
   relational only where a decision source actually exists. The decision source
   for scheduling *finalizer fibers* is the fiber machine, not the scope.
3. *Function argument, chosen.* `run` is passed to `closeExits`, `closeResult`,
   `close`, `addExit`, `runScoped`, and `acquireRelease`. It never enters
   `Scope`, so `Scope` keeps `DecidableEq`, `Repr`-able first-order content, and
   kernel-reducible ground receipts, while exit-aware finalization stays
   observable: `run` takes the closing exit, which is the whole point of
   rc.112's `(exit) => …` finalizer signature.

The packet adds no effect syntax, primitive, continuation frame, fiber,
scheduler, fiber context, interruption mask, host `Error`, or `Map` object. It
supplies:

- a two-value finalizer-strategy label;
- a five-constructor scope state machine whose three `open*` arms are exactly
  the three inhabited shapes of rc.112's `Open` record;
- an insertion-ordered keyed finalizer table with `Map.set`/`Map.delete`
  semantics;
- registration, registration-after-close, and removal;
- the state-first, LIFO, idempotent close with its three result arms;
- fork linkage at the shape level; and
- the scope-side clauses of `scoped` and `acquireRelease`.

It reuses `Effect4.Exit` and `Effect4.Cause` unchanged and mints no second exit
or cause carrier. Nothing here imports or mentions `Effect4/Concurrency/`.

## Required semantic separations

1. **Scope is its own calculus.** `docs/DESIGN-BASIS.md` DB-05 keeps `Scope` a
   separate signature summand because acquisition, registration, delimitation,
   exit-aware finalization, and closing order are observable. This packet
   supplies exactly those five observations and no operation family beyond
   them. It does not merge Scope with Layer, with service lookup, or with the
   fiber machine.
2. **No dependency on Concurrency.** `Effect4/Runtime/Scope.lean` imports
   `Effect4.Semantics.Exit` (hence `Effect4.Semantics.Cause`) and nothing else
   from Effect4. `docs/ARCHITECTURE.md` "Dependency direction" puts Runtime
   above Semantics and beside Fiber; the concurrency lane is a sibling, and no
   edge is created in either direction. The finalizer key `κ` is an admitted
   alphabet, never `Effect4.FiberId`.
3. **A finalizer is a name, not a computation.** DB-02 closes the pure fragment
   at the reification boundary: a host function, thunk, or raw closure becomes a
   named registered boundary. `φ` is that name. DB-05's no-`HHandler` ruling is
   conditional on exactly this: a scoped operation stores stable first-order
   references, not actual subcomputations. `Effect4.Scope.key_freshness_refused`
   is the theorem-shaped half of the boundary.
4. **The finalizer table is not `Effect4.Data.Row` and not
   `Effect4.ReasonAnnotations`.** `Row` is the canonical finite *set*: it stores
   no values, needs a lawful order on its element type, and erases both order
   and duplicates — all three fatal here, because registration order decides
   close order (`E4-RUN-CE-002`). `ReasonAnnotations` is the canonical
   `String`-keyed annotation map owned by `Effect4/Semantics/Cause.lean`: its key
   domain is `String`, its role is failure annotation, and its `annotate` merge
   is a different operation from `Map.set`. The finalizer table is therefore an
   ordinary `List (κ × φ)` with named `Scope.tableInsert` / `Scope.tableRemove`
   operations and a `Nodup`-preservation receipt, not a third map carrier and
   not a view of either existing one. No conversion between them is claimed.
5. **Refusal, frontier, and finalizer failure remain distinct.** A finalizer
   exit is an `Effect4.Exit`; it is never a scheduler-domain refusal and never
   fuel exhaustion. This packet mints no refusal and no frontier carrier.
6. **`Empty`, `Open`-with-nothing, and `Open`-with-an-empty-map are three
   states, not one.** rc.112 reaches all three, and they differ at the very
   next add: `Empty` and a cleared inline slot take the next finalizer into the
   inline slot, an emptied `Map` takes it into the map, and only `Empty` is
   still pre-`Open`. `E4-RUN-CE-005` proves the distinction.
7. **The strategy label is not a scheduler policy.** rc.112's "parallel" is
   immediate daemon forks that inherit the closing fiber's mask, awaited
   together. This packet models no fiber, so
   `Effect4.Scope.close_strategy_irrelevant` states plainly that the label
   changes nothing this model observes. Two census rows stay `partial` because
   of it; see the per-row table.

## Census rows this packet targets

Row summaries are the clauses that must become theorems. Take the exact text
from `generated/effect-runtime-census.tsv`. The "after the join" column is the
coverage state `Effect4Test/Audit/RuntimeCoverage.lean` should carry once a
later packet joins these witnesses, under the clause-by-clause rule in
`docs/RUNTIME-COVERAGE.md`. This packet writes no coverage row.

| Census row | Clauses this packet closes | Clauses left to another packet | After the join |
| --- | --- | --- | --- |
| `scope.states` | Empty; Open with one inline finalizer; Open with a keyed insertion-ordered map; Closed carrying the closing `Exit` — `ScopeState.cases_receipt`, the five `entries_*`, the five `isOpen_*`, `isClosed_eq`, `closingExit_closed`, `openEmpty_ne_openMap_nil` | none | **green** |
| `scope.make` | starts at `Empty`; sequential strategy by default — `Scope.make_state`, `make_strategy`, `make_finalizers`, `makeDefault_eq`, `makeDefault_strategy` | none. The word "shared constant" describes rc.112's allocation of one `constScopeEmpty` object, refused under `SCOPE-FB-STATE-IDENTITY` exactly as `cause.combine-union` refuses reference preservation under `CAUSE-FB-REFERENCE-EQ` | **green** |
| `scope.add-finalizer` | the first add stores an inline finalizer and its key; the second promotes both into a map preserving insertion order — `Scope.addUnsafe_empty`, `addUnsafe_openEmpty`, `addUnsafe_openInline`, `addUnsafe_openMap`, `addUnsafe_promotes`, `addUnsafe_finalizers`, `tableInsert_new`, `tableInsert_existing`, `tableInsert_keys_of_mem` | none | **green** |
| `scope.add-after-closed` | adding to a Closed scope runs the finalizer immediately with the stored closing exit instead of registering it — `Scope.addExit_closed`, `addExit_closed_registers_nothing`, `addUnsafe_closed`, `addExit_open` | none | **green** |
| `scope.remove-finalizer` | clears the inline slot on a key match; otherwise deletes from the map; leaves a non-Open scope untouched — `Scope.removeUnsafe_inline_hit`, `removeUnsafe_inline_miss`, `removeUnsafe_openMap`, `removeUnsafe_not_open`, `removeUnsafe_keys`, `tableRemove_eq`, `tableRemove_keys` | none | **green** |
| `scope.close-state-first` | close is idempotent; it returns on an already-Closed scope; it writes the Closed state before any finalizer runs — `Scope.close_idempotent`, `close_twice`, `closeState_idempotent`, `close_state_independent_of_run`, `closeState_state`, `closeState_finalizers`, `close_reentrant_add` | none | **green** |
| `scope.close-lifo` | many finalizers are materialised in insertion order and iterated backwards, so the last registered runs first — `Scope.closeOrder_eq`, `closeOrder_last_first`, `closeExits_eq`, `closeExits_reverse` | none | **green** |
| `scope.close-sequential` | failures are captured rather than thrown: every registered finalizer contributes an exit and none aborts the loop — `Scope.closeExits_length`, `closeResult_reasons` | "awaits each finalizer through `exit()`": the temporal sequencing of one finalizer effect after another. This model has no notion of time, so it cannot distinguish sequential from parallel; that needs the fiber machine | **partial** |
| `scope.close-parallel` | "not a separate scheduler policy": `FinalizerStrategy` is a two-value label carrying no scheduler payload, and `Scope.close_strategy_irrelevant` shows it selects nothing this model observes | "immediate daemon forks that inherit the closing fiber mask": the fork mode, the daemon flag, and mask inheritance are fiber-machine facts | **partial** |
| `scope.close-merge` | "every exit is merged by `exitAsVoidAll`" — `Scope.closeResult_many`, `closeResult_reasons`, together with the already-green `Exit.asVoidAll_*` receipts | "parallel finalizer fibers are awaited together": `fiberAwaitAll` and the fiber array are fiber-machine facts | **partial** |
| `scope.exit-as-void-all` | already `green` from the Cause/Exit packet | — | unchanged; **do not re-witness** |
| `scope.fork-linkage` | a child of a Closed parent is born Closed with the parent's exit; otherwise **one** shared key registers a parent-side finalizer and a child-side finalizer, and removing that key restores the parent exactly — `Scope.fork_closed_parent`, `fork_closed_parent_child_exit`, `fork_open_parent`, `fork_parent_finalizers`, `fork_child_finalizers`, `fork_shared_key`, `fork_detach`, `fork_child_strategy` | that the parent-side name *is* `scopeClose(child, exit)` and the child-side name *is* `scopeRemoveFinalizerUnsafe(parent, key)`. Interpreting a finalizer name as an operation on another scope needs a scope store, which belongs to the fork/supervision packet | **partial** |
| `scope.scoped` | installs a fresh scope, at the default strategy, and closes it with the body's exit — `Scope.runScoped_fresh_scope`, `runScoped_eq`, `runScoped_state`, `runScoped_strategy`, `runScoped_empty`, `runScoped_lifo` | "in the fiber context", "through an OnExit frame", "restoring the previous context first": three continuation-machine and context facts | **partial** |
| `scope.acquire-release` | "registers the release against the ambient scope" — `Scope.acquireRelease_success`, `acquireRelease_failure`, `acquireRelease_registers`, `acquireRelease_closed_ambient` | "runs under `uninterruptibleMask`", "restores interruptibility for the acquire only when asked", "with the captured context": interruption masking and `Context`/`provideContext` | **partial** |
| `rule.scope-close-lifo-state-first` | close flips the state to Closed before running anything, and only then runs finalizers in reverse registration order — `Scope.close_state_independent_of_run`, `close_reentrant_add`, `closeState_finalizers`, `closeOrder_last_first`, `closeExits_reverse` | none | **green** |

Eight rows are green-able, six stay `partial`, and one is already green and is
not touched. No row is claimed green on a clause this packet does not have a
theorem for.

## Existing-type rows

Every row is native to this contract. None renames or copies an Effect
TypeScript or Foldlab carrier. `PORT-MANIFEST.md` "Effect TypeScript family
defaults" disposes of `Scope and Resource` as lifetime delimiters and
exit-aware finalization owning their own calculus; every row below inherits
that disposition. `SCOPE-PG` abbreviates the `SCOPE-PG-STATE` graph defined
further down.

| Stable public type | Owning module | Kind | Relationship | Pin | Assurance route |
| --- | --- | --- | --- | --- | --- |
| `Effect4.FinalizerStrategy` | `Runtime/Scope.lean` | canonical finite alphabet | the closed rc.112 close-strategy label; no other alphabet claims this role, and it is **not** a scheduler policy carrier — `Effect4.SchedulerDecision` in `Effect4/Concurrency/Scheduler.lean` owns scheduling choices and is a separate calculus | `internal/effect.ts:3915` (`scopeMakeUnsafe` default), `Scope.ts:99-187` | leaf receipts linked to `SCOPE-PG.construction` |
| `Effect4.ScopeState` | `Runtime/Scope.lean` | canonical carrier | canonical scope-state machine; the three `open*` constructors are the three inhabited shapes of rc.112's one `Open` record under its own XOR invariant, made unconstructible-otherwise rather than checked | `Scope.ts:99-187` (`State.Empty`, `State.Open`, `State.Closed`) | `SCOPE-PG` |
| `Effect4.Scope` | `Runtime/Scope.lean` | canonical carrier | canonical scope; separate calculus from `Effect4.Exit` (a result observation, reused here unchanged), from `Effect4.Data.Row` (a finite set, order-erasing), and from `Effect4.ReasonAnnotations` (a `String`-keyed annotation map owned by Semantics) | `Scope.ts:99-187`, `internal/effect.ts:3769-3922` | `SCOPE-PG` |
| `Effect4.Exit` | `Semantics/Exit.lean` | **reused, not re-declared** | already canonical, owned by `docs/CAUSE-DAG.md` `CAUSE-L4-EXIT`; this packet adds no arm, no view, and no adapter | `Exit.ts:118-157` | `CAUSE-PG-FLAT` (unchanged) |
| `Effect4.Cause` | `Semantics/Cause.lean` | **reused, not re-declared** | already canonical, owned by `docs/CAUSE-DAG.md` `CAUSE-L2-CAUSE`; the closing cause of a scope is exactly `Exit.asVoidAll`'s flat cause | `internal/core.ts:138-176` | `CAUSE-PG-FLAT` (unchanged) |

The duplicate-prevention check run before freezing was

```sh
grep -rhE '^[[:space:]]*(inductive|structure|abbrev|def)[[:space:]]+[A-Za-z]' \
  Effect4 --include='*.lean' \
  | grep -oE '(inductive|structure|abbrev|def) [A-Za-z0-9_.?]+' \
  | grep -iE 'scope|finali|resource|strategy|acquire|release|lifetime|close' | sort -u
grep -rnE '^\s*namespace\s+(Scope|Finalizer|FinalizerKey|FinalizerStrategy|ScopeState|Resource)\b' \
  Effect4 --include='*.lean'
```

It found no `Scope`, `ScopeState`, `FinalizerStrategy`, or `Resource`
declaration or namespace anywhere under `Effect4/`, and exactly two
finalizer-named declarations, both in `Effect4/Semantics/Exit.lean`:
`Exit.mergeFinalizer` and `Exit.restoreAfterFinalizer`. Those are the
`combineFinalizerCause` and `OnExit`-restore operations on *exits*; this packet
reuses them conceptually through `Exit.asVoidAll` and declares neither again.
`Effect4/Runtime/Resource.lean` and `Effect4/Runtime/Lifecycle.lean` are
annotation-only stubs and remain so.

### Public declaration records

138 public declarations are frozen: three types, eight constructors, two
structure projections, twenty-seven definitions, and ninety-eight theorems. Two
derived `DecidableEq` instances are checked by `inferInstance` in the battery
rather than named. Per `docs/AGENT-ROUTING.md` "Public declaration records",
the routine constructors, projections, and theorems inherit their owner,
disposition, duplicate-prevention relationship, and assurance route from the
type row above them; the table below records the ones that do not inherit
cleanly, which is every definition plus the refusal theorem.

| Declaration | Module | Role | Origin / disposition | Relationship | Assurance route |
| --- | --- | --- | --- | --- | --- |
| `Effect4.FinalizerStrategy.all` | `Runtime/Scope.lean` | constructor census of the strategy alphabet | native; contract `test/contracts/scope.contract.md` | `derived` from `Effect4.FinalizerStrategy` | leaf receipts under `SCOPE-PG.construction` |
| `Effect4.ScopeState.entries` | `Runtime/Scope.lean` | the materialised registration order of a state | native | `canonical` observation of `Effect4.ScopeState` | `SCOPE-PG.semantics` |
| `Effect4.ScopeState.isOpen`, `.isClosed`, `.closingExit?` | `Runtime/Scope.lean` | state discriminators and the stored closing exit | native | `derived` from `Effect4.ScopeState` | `SCOPE-PG.semantics` |
| `Effect4.Scope.tableInsert`, `.tableRemove` | `Runtime/Scope.lean` | `Map.set` / `Map.delete` on the keyed insertion-ordered finalizer table | native; models `internal/effect.ts:3877-3888` and `:3894-3901` | `separate-calculus` from `Effect4.Data.Row` (finite set, order-erasing) and from `Effect4.ReasonAnnotations` (`String`-keyed annotation map); no conversion claimed | `SCOPE-PG.construction` |
| `Effect4.Scope.make`, `.makeDefault` | `Runtime/Scope.lean` | `scopeMakeUnsafe`, with and without the default strategy | native | `canonical` constructor of `Effect4.Scope` | `SCOPE-PG.construction` |
| `Effect4.Scope.finalizers`, `.finalizerKeys`, `.finalizerCount`, `.isOpen`, `.isClosed`, `.closingExit?` | `Runtime/Scope.lean` | the observations a scope exposes; `finalizerCount` is `scopeFinalizerCountUnsafe` | native | `derived` from `Effect4.ScopeState`'s observations | `SCOPE-PG.semantics` |
| `Effect4.Scope.addUnsafe`, `.addExit`, `.removeUnsafe` | `Runtime/Scope.lean` | `scopeAddFinalizerUnsafe`, `scopeAddFinalizerExit`, `scopeRemoveFinalizerUnsafe` | native | `canonical` transitions of `Effect4.Scope` | `SCOPE-PG.semantics`, `SCOPE-PG.laws` |
| `Effect4.Scope.closeState`, `.closeOrder`, `.closeExits`, `.closeResult`, `.close` | `Runtime/Scope.lean` | the four phases of `scopeCloseUnsafe` and their pairing | native | `canonical`; `close` is the pair, the other four are its named phases and exist so "state before finalizers" is a statement rather than a comment | `SCOPE-PG.laws` |
| `Effect4.Scope.fork` | `Runtime/Scope.lean` | `scopeForkUnsafe`, shape only | native | `canonical` | `SCOPE-PG.laws` |
| `Effect4.Scope.addAll` | `Runtime/Scope.lean` | the registration trace a delimited body leaves in its scope | native | `helper` for `Effect4.Scope.runScoped` | `SCOPE-PG.laws` |
| `Effect4.Scope.runScoped` | `Runtime/Scope.lean` | rc.112 `scoped`, scope side only. Named `runScoped` because `scoped` is a Lean keyword and `Effect4.Scope.scoped` would need `«scoped»` at roughly ten ascription sites | native | `canonical` for the scope-side clauses; the fiber-context and `OnExit` clauses are unowned here | `SCOPE-PG.laws` |
| `Effect4.Scope.acquireRelease` | `Runtime/Scope.lean` | rc.112 `acquireRelease`, scope side only | native | `canonical` for the registration clause; the mask and context clauses are unowned here | `SCOPE-PG.laws` |
| `Effect4.Scope.key_freshness_refused` | `Runtime/Scope.lean` | the theorem-shaped refusal of rc.112 key freshness | native | `separate-calculus` boundary receipt, sibling of `Effect4.Reason.host_memory_refused` | `SCOPE-PG.bridges` |

Auxiliary lemmas beyond the frozen list are permitted in the implementation but
must be `private`, so the generated declaration snapshot has no unannotated
public export.

## Named boundary and refusal

| Boundary | Row | What is refused | Evidence |
| --- | --- | --- | --- |
| `SCOPE-FB-KEY-IDENTITY` | `scope.add-finalizer`, `scope.remove-finalizer`, `scope.fork-linkage` | rc.112 mints a finalizer key as a fresh empty object, `const key = {}` (`internal/effect.ts:3840`) and `scopeAddFinalizerUnsafe(scope, {}, finalizer)` (`:3855`), and a JavaScript `Map` compares those keys by reference. Two evaluations of the same expression produce distinct keys. | `Effect4.Scope.key_freshness_refused`: any Effect4 key-minting function `γ -> κ` is a function of its argument, so equal inputs give equal keys and the host freshness distinction is not representable. Keys are supplied externally and their distinctness is the caller's obligation, discharged in this packet's laws by explicit `key ∉ self.finalizerKeys` hypotheses. This is a theorem-shaped refusal, not a model of object identity. |
| `SCOPE-FB-STATE-IDENTITY` | `scope.states`, `scope.make`, `scope.fork-linkage` | rc.112 allocates one shared `constScopeEmpty` object for every new scope (`internal/effect.ts:3919-3922`), and `scopeForkUnsafe` assigns the parent's *same* `Closed` state object to the child (`:3837`). Object identity of a state record is therefore observable to a host that compares by reference. | Authored refusal row. Effect4 equality on `ScopeState` is structural, which is strictly coarser than reference equality; sharing is not observable through any operation this packet declares, and no theorem claims it is. The same shape as `CAUSE-FB-REFERENCE-EQ`. |
| `SCOPE-FB-FINALIZER-MEANING` | `scope.fork-linkage`, `scope.scoped`, `scope.acquire-release` | rc.112 finalizers are closures: `(exit) => scopeClose(newScope, exit)`, `(_) => scopeRemoveFinalizerUnsafe(scope, key)` (`internal/effect.ts:3841-3842`), and `(exit) => provideContext(release(a, exit), context)` (`:3983`). Each names an operation on another scope or on a captured context. | Authored refusal row. DB-02 forbids storing those closures. `φ` is their nominal name and `run` interprets it, but nothing in this packet ties a particular name to a particular operation on another scope: that needs a scope store and belongs to the fork/supervision packet. The three census rows above are `partial` for exactly this reason. |
| `SCOPE-FB-FIBER` | `scope.close-sequential`, `scope.close-parallel`, `scope.close-merge`, `scope.scoped`, `scope.acquire-release` | `scopeCloseFinalizers` yields through `exit(...)`, forks with `forkUnsafe(parent, …, true, true, "inherit")`, and awaits with `fiberAwaitAll` (`internal/effect.ts:3818-3824`); `scoped` runs inside `withFiber` and an `onExitPrimitive` frame (`:3937-3947`); `acquireRelease` runs under `uninterruptibleMask` (`:3970-3987`). | Authored refusal row. No fiber, frame, mask, or scheduler is modelled. `Effect4.Scope.close_strategy_irrelevant` states the consequence positively rather than hiding it: in this model the strategy label selects nothing. |

## Declaration and proof graph

```text
SCOPE-L0-STRATEGY ------.
SCOPE-L0-TABLE ---------|
                         v
                  SCOPE-L1-STATE
                         |
                         v
                  SCOPE-L2-SCOPE
                    /         \
                   v           v
        SCOPE-L3-REGISTER  SCOPE-L3-CLOSE
                   \           /
                    v         v
                   SCOPE-L4-FORK
                         |
                         v
                  SCOPE-L5-BRACKETS
                         |
                         v
              SCOPE-L6-COUNTEREXAMPLES
                         |
                         v
        SCOPE-L7-COVERAGE-JOIN (later obligation)
                         |
                         v
        SCOPE-L8-HOST-EVIDENCE (later obligation)
```

`SCOPE-L0-STRATEGY` and `SCOPE-L0-TABLE` close with local receipts and link to
one named parent edge each; they do not receive invented graphs.
`SCOPE-L1` through `SCOPE-L6` form one graph, `SCOPE-PG-STATE`, because
changing any of them changes what a scope lifetime *is*. The graph route is
required, not optional: this owner carries protocol-state invariants
(`Nodup` preservation, the Open XOR shape), an ordering law, and an
idempotence law, all of which `docs/AGENT-ROUTING.md` "Assurance threshold"
lists as graph triggers.

`Effect4.Exit` and `Effect4.Cause` are **not** nodes of this graph. They are
closed by `CAUSE-PG-FLAT` and are consumed here unchanged; the only edge
between the graphs is that `Scope.closeResult_many` and
`Scope.closeResult_reasons` are stated over `Exit.asVoidAll` and its already
green `Exit.asVoidAll_reasons` receipt.

## Node ownership

| Node | Production owner after dispatch | Required receipt |
| --- | --- | --- |
| `SCOPE-L0-STRATEGY` | `Effect4/Runtime/Scope.lean` | constructor census, `Nodup`, `mem_all`, exhaustive cases, `DecidableEq`, `Repr` |
| `SCOPE-L0-TABLE` | `Effect4/Runtime/Scope.lean` | the `Map.set` split into new-key append and existing-key in-place replacement, key-list preservation, `Nodup` preservation, the `Map.delete` filter equation, and post-removal key absence |
| `SCOPE-L1-STATE` | `Effect4/Runtime/Scope.lean` | five constructors; exhaustive cases; the five `entries` equations; the five `isOpen` equations; the `isClosed` characterisation; the stored closing exit; `openEmpty ≠ openMap []`; `DecidableEq` derived from the seven alphabets |
| `SCOPE-L2-SCOPE` | `Effect4/Runtime/Scope.lean` | two fields; `make` at `Empty` with the given strategy; the sequential default; the four observations and their definitional equations; the non-Open finalizer count; the key-freshness refusal |
| `SCOPE-L3-REGISTER` | `Effect4/Runtime/Scope.lean` | the four `addUnsafe` state arms and the absent `Closed` arm; the promotion order; the append law; `Nodup` preservation; the two `addExit` arms; the three `removeUnsafe` arms; the non-Open no-op; post-removal key absence |
| `SCOPE-L3-CLOSE` | `Effect4/Runtime/Scope.lean` | the pairing law; independence of the written state from `run`; the state, strategy, and emptied registration list; idempotence and the double close; the re-entrant add; the LIFO order in three spellings; the length law; the three result arms; the flat reason law; the strategy-irrelevance statement |
| `SCOPE-L4-FORK` | `Effect4/Runtime/Scope.lean` | the Closed-parent arm with the inherited exit; the open arm; both registration lists; the shared key on both sides; the detach law; the child strategy |
| `SCOPE-L5-BRACKETS` | `Effect4/Runtime/Scope.lean` | `addAll`'s two equations and its ordered-append law under `Nodup` keys; the fresh scope, its default strategy, and its close with the body exit; the LIFO trace of a delimited body; the four `acquireRelease` arms |
| `SCOPE-L6-COUNTEREXAMPLES` | `Effect4Test/Counterexamples/Runtime/Scope.lean` | nine registered witnesses, all proved, all within the axiom ceiling |
| `SCOPE-L7-COVERAGE-JOIN` | `Effect4Test/Audit/RuntimeCoverage.lean` (not this packet) | later obligation; see below |
| `SCOPE-L8-HOST-EVIDENCE` | a later Effect TypeScript conformance packet | later obligation; direct rc.112 runtime and type receipts |

## Graph-edge ledger

The graph-bearing owner is `SCOPE-PG-STATE`. Passive leaves link to it; they do
not receive duplicate graphs.

| Edge | Breaker state | Reason and closure evidence |
| --- | --- | --- |
| identity | `required-open` | exact public declaration snapshot plus the five existing-type rows above, two of which are reuse rows for carriers this packet does not own; closed when the frozen battery's 138 ascriptions elaborate |
| construction | `required-open` | the three carriers, the strategy census and `Nodup`, the `Map.set`/`Map.delete` table laws with their `Nodup` preservation, and the derived `DecidableEq` instances |
| semantics | `required-open` | the observations this packet exposes: `ScopeState.entries`/`isOpen`/`isClosed`/`closingExit?`, `Scope.finalizers`/`finalizerKeys`/`finalizerCount`, `Scope.closeOrder`/`closeExits`/`closeResult`. The three transitions `addUnsafe`, `removeUnsafe`, `closeState` are total functions on states; no relation and no fuel is claimed |
| laws | `required-open` | the registration, removal, close-order, idempotence, merge, fork-linkage, and bracket theorem spine |
| representation | `required-open` | `Scope.finalizers_eq`, `finalizerKeys_eq`, and `finalizerCount_eq` are the claimed normalization facts; the `Nodup`-preservation receipts are the claimed canonicality facts. No serialization or wire round trip is claimed by this packet |
| counterexamples | `required-open` | all nine `E4-RUN-CE-*` witnesses exist and are proved, but their repairs cannot close before implementation |
| bridges | `required-open` | the four `SCOPE-FB-*` rows are the declared loss to the pinned host. `Effect4.Scope.key_freshness_refused` is the only theorem-shaped one; the other three are authored refusals and stay open until a later packet either states or retires them. The `Exit`/`Cause` reuse is a consumption, not a bridge: no conversion, embedding, or erasure is claimed between `Scope` and either carrier |
| targets | `not-applicable` | no TypeScript lowering, byte stability, or runtime observation is claimed here. Refusing the host's key and state identities under `SCOPE-FB-KEY-IDENTITY` and `SCOPE-FB-STATE-IDENTITY` does not erase the semantic obligations above |
| trust | `required-open` | `#print axioms` receipts for all ninety-eight public theorems, in `Effect4Test/Runtime/ScopeAxiomReport.lean`, within `propext`/`Quot.sound` |
| coverage | `required-open` | the frozen contract must join every exported declaration to one owner route, and the generated declaration snapshot must show no unannotated exported type |

No edge is omitted. `targets` is the only `not-applicable` row and it carries
its reason.

## The generated assurance join is a later obligation

This packet writes no generated projection and edits no file under
`generated/`, `Effect4Test/Audit/`, or `Effect4Test/Concurrency/`, except that
appending rows to `test/counterexamples/REGISTER.md` changes an input digest
pinned by `generated/fiber-assurance.tsv`, which is regenerated with its
recorded command in the same commit. Three joins remain open after the builder
turns the battery green:

1. **The Effect runtime coverage join.** A theorem in `Effect4/` moves no
   coverage number by itself. Each witness must be added to the matching row in
   `Effect4Test/Audit/RuntimeCoverage.lean` with its axiom receipt and its exact
   `#check (@name : proposition)` ascription, `snapshotWitnesses` must be
   extended in the same order, and `./scripts/check-effect-runtime-census.sh`
   must pass. `docs/RUNTIME-COVERAGE.md` owns the rules; that edit is a separate
   packet with a separate claim. The per-row table above states the expected
   states, not the achieved ones, and `scope.exit-as-void-all` must **not** be
   re-witnessed: it is already green.
2. **The declaration and assurance snapshot.** The generated per-declaration
   assurance join must show every exported declaration of
   `Effect4/Runtime/Scope.lean` resolving to exactly one of the routes in the
   existing-type and declaration-record tables. No such generator exists for
   `Effect4/Runtime/` today; standing one up, or extending an existing one, is
   the coverage edge's real closure condition.
3. **Host evidence.** `SCOPE-L8` needs direct rc.112 runtime and type
   observations — in particular for the one-finalizer short circuit, which is a
   behaviour this model claims and no Lean theorem can confirm about
   JavaScript.

Until those land, this graph may be reported as *breaker-frozen with an open
coverage edge*, never as a closed category and never as a coverage number.

## Determinism, totality, and claim boundary

Every operation in this packet is a total first-order function over finite
data, parameterised by one externally supplied total function `run`. There is
no relation, no fuel, no choice, and therefore no determinism theorem to state:
determinism is a property of the carrier here, not a result. Where rc.112 *is*
nondeterministic — the interleaving of parallel finalizer fibers — this packet
does not model the behaviour at all rather than silently determinising it, and
`Effect4.Scope.close_strategy_irrelevant` says so in the frozen surface.

Nothing here claims that `Effect4.Scope` is *equivalent* to rc.112's `Scope`.
The claim is that each named clause of each named census row in the per-row
table has an exact theorem over the Effect4 model, and that the four
`SCOPE-FB-*` rows name what was deliberately dropped: host key freshness, host
state-object identity, the meaning of a finalizer name, and the whole fiber
machine.

Six of the fifteen assigned rows are explicitly **partial**. Reporting any of
them green on the strength of this packet would be a false green.


## Scope close stepping continuation, 2026-09-03

The independently frozen packet is `test/contracts/scope-machine.contract.md`
at `e5a2bdb835b414ef329c1067ef95bec467dceae6`. Its production owner is
`Effect4/Runtime/ScopeMachine.lean`, importing only existing Scope. This extends
`SCOPE-L3-CLOSE` with an execution residual; it does not replace the canonical
Scope, Exit, Cause or finalizer-operation alphabets. The same local edge feeds
`docs/TRACE-DAG.md`'s D4 `frame-simulation` obligation, which remains open.

| Stable public type | Owner | Native origin and relationship | Assurance route |
| --- | --- | --- | --- |
| `Effect4.ScopeMachine.Phase` | `Runtime/ScopeMachine.lean` | The three administrative phases of one close, frozen by the scope-machine packet; distinct from Scope's lifetime states and from fiber or scheduler status. | Local construction receipts under `SCOPE-PG-STATE.close-stepping` |
| `Effect4.ScopeMachine.State` | `Runtime/ScopeMachine.lean` | Residual execution data: retained closed Scope, original exit, pending operation names, actual operation/exit pairs, and phase. Its completed view is related to existing `Scope.closeExitsM` by `runState_complete`; it is not another Scope or stored program syntax. | Required `SCOPE-PG-STATE.close-stepping` semantic edge |

The nine operation roots are `start`, `advance`, `request?`, `respond`,
`result?`, `journal`, `restore?`, `bound`, and `runState`, all in
`Effect4.ScopeMachine`. The packet owns their exact declarations and
observations. Constructors, projections and derived equality inherit their
corresponding type row. The ten public theorem roots below inherit the same
native origin and owner. All other implementation helpers are private; the
new namespace's sole production owner is `Runtime/ScopeMachine.lean`.

| Local obligation | Named evidence and current boundary |
| --- | --- |
| construction and interface | The unchanged frozen battery checks both types, constructor/field order, independent body-value universe, all nine operation signatures, equality instances and all ten exact theorem statements. |
| request identity | `request_uses_original`, `respond_rejects_wrong_id`, `respond_rejects_wrong_phase`; finite controls reject stale, future, repeated and wrong-phase replies. Response routing between different close instances remains caller-owned. |
| pause and resume | `runState_zero`, `runState_add`; the equality retains both machine and service state for every budget, with no fabricated failure at a pause. This is a microstep law for this independent machine, not a general fixed-source-fuel bind law. |
| scope and prefix semantics | `runState_scope`, `runState_prefix`; exact captured/waiting/pending operation partition, fixed original exit and closed Scope, and actual captured replies plus service-state equality at every prefix. |
| completed fold and restoration | `runState_complete` gives the complete machine/service pair at `2 * closeOrder.length + 1`; `runState_result` agrees with existing pure `Scope.closeResult`; `runState_restore` agrees with stateful `closeExitsM`, the exact zero/one/many exit fold and existing `restoreAfterFinalizer`. |
| counterexamples | The packet reuses `E4-RUN-CE-001`, `002`, `003`, `008`, `009` and `E4-TARGET-CE-019`/`020`; all 27 existing-owner controls and 72 machine guards pass, including failures, duplicate reasons and singleton empty failure. The old region/frame counterexamples stay unchanged. |
| trust | All ten saved public receipts pass: the first six use `propext`; prefix, completion, result and restoration use `propext` and `Quot.sound`. No added axiom is admitted. |
| representation and coverage | First-order fields and derived equality are checked. No serialization theorem is claimed. A generated declaration-assurance join covering this extension remains owed; no runtime census row or percentage changes here. |
| external connections | Required-open: the general region compiler and residual simulation, arbitrary-program finalizer evaluation, generic frame relation, host behavior, interruption and parallel scheduling. The state retains either strategy label, while this driver executes the existing sequential fold for both labels. |

Narrow verification is `lake build Effect4.Runtime.ScopeMachine`,
`lake env lean Effect4Test/Runtime/ScopeMachineContract.lean` and
`lake env lean Effect4Test/Runtime/ScopeMachineAxiomReport.lean`; all pass on
the saved implementation. Independent review accepted SHA-256
`1189173bca2b6b76e114bc178d1945463e0e862e0faca3d0ed91cf04ddb95979`,
including a fresh scratch-olean check. The production commit is `abefdb1`.
Broader package and trust results are recorded in `COORDINATION.md`'s local
proof integration receipt. Neither successful local tests nor
these local universal equations close the external connections above.

## Scope cleanup restoration continuation, 2026-09-03

The independently frozen packet is `test/contracts/scope-restoration.contract.md`
at `945f729`. `Effect4/Runtime/ScopeRestoration.lean` imports only ScopeMachine
and the existing Runtime. It adds no carrier: its sole executable root,
`Effect4.ScopeRestoration.resumeClosedScope`, maps a completed existing
`ScopeMachine.restore?` exit through the real existing `FrameFiber.step` after
replacing only the current primitive with `Prim.ofExit`.

The nine public theorem roots are `resumeClosedScope_unfinished`,
`resumeClosedScope_complete`, `resumeClosedScope_success_pending`,
`resumeClosedScope_failure_pending`, `resumeClosedScope_success_no_pending`,
`resumeClosedScope_already_masked`, `resumeClosedScope_masked_continuation`,
`resumeClosedScope_failure_cleanup` and
`resumeClosedScope_success_cleanup_failure`. They inherit the native derived
owner, duplicate-prevention record and required local composition route from
the executable root. All implementation helpers are private.

| Local edge | Evidence and exact boundary |
| --- | --- |
| completion composition | `resumeClosedScope_complete` preserves the whole actual service-state pair and equates the adapter at ScopeMachine's bound with existing `closeExitsM`, the exact zero/one/many fold, existing `restoreAfterFinalizer` and the real frame step. Unfinished phases return no step. |
| success restoration | Under the precise top `setInterruptible true` frame and false deferred latch, successful cleanup with a pending full cause immediately becomes that failure primitive, with the arbitrary tail and exact popped, ran-continuation and substituted events. No pending cause follows the actual tail success step. |
| failure restoration | A pre-existing restored failure skips the pending replacement in the real failure evaluator and enters the actual arbitrary tail step; the substituted event remains visible. No unrestricted terminal-cause stability is claimed for arbitrary tail handlers. |
| nested masks | Existing `uninterruptible` is unchanged on an already masked fiber, and the actual success continuation under an outer mask retains that mask, optional pending cause and arbitrary tail. |
| cleanup causes | Existing `Cause.combine` joins failed original and cleanup causes. A cleanup failure under an originally successful exit follows the failure-restoration equation and is not overwritten by a pending interrupt. ScopeMachine remains owner of actual ordered callback replies, duplicate journal and service state. |
| counterexamples and finite host evidence | `E4-RUN-CE-025` and `026` reject replacing existing failure at restoration and dropping outer cleanup after delivered interruption. The independent boundary has 27 controls and five named witnesses. The explicit-path host probe runs 20 cases at two scheduling thresholds, verifies the four source/runtime hashes before import and distinguishes JavaScript-only fallible releases from legally typed cleanup defects. Host observations do not prove the Lean equations. |
| trust and generated coverage | The unchanged 56-guard battery and all nine public axiom receipts pass within `propext`/`Quot.sound`; independent saved-source review is recorded with the integration receipt. The generated declaration-assurance join for Scope remains open. |
| external connections | Required-open: the general region compiler and source/target residual relation, arbitrary finalizer programs, actual first-order mask lowering and host-tail request delivery, parallel scheduling and host equivalence. This adapter closes only the local completed ScopeMachine-to-FrameFiber step. |

This local composition contributes to `SCOPE-PG-STATE.close-restoration` and
the Scope/Frame sides of TRACE-DAG D4 and M2. It moves no runtime-coverage
count and does not alter the existing Scope, Runtime, Exit or Cause owners.
