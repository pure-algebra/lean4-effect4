# STM design audit — 2026-09-19

Read-only audit for the ongoing architecture synthesis. No source edits, Git mutations, builds, or runtime experiments. Read the completed original scout transcript (agent-a428f7455c49c54b1.jsonl), its final note, `docs/core/machine-state.md`, and the cited pinned vendor/machine sources. The transcript says its citation pass finished; its lost-wakeup claim and reduction argument remain inferences, not reproduced or proved facts.

## Recommendation

Keep the proposed atomic transaction design as a candidate, specified first as a transaction relation over logical cells and explicit wake actions. Do not yet freeze the particular global-buffer representation, number-only first cut, or an unrestricted claim of Effect agreement. Prove the single-owner/isolation condition on the admitted fragment before deleting versions from an implementation. Lowered implementations can use a buffer, a lock, or version validation provided they satisfy that same relation. Single-threaded cooperative execution is an assumption of the proposed version-free implementation, not a property provided automatically by LLVM, C, OCaml, or Wasm.

## Confirmed from pinned source

- `vendor/effect-4.0.0-rc.112/src/Effect.ts:24274-24311`: nesting reuses the existing Transaction context; failure/retry handling and commit decision are explicit. There is no nested rollback boundary.
- `Effect.ts:24313-24320`: versions validate every journal entry.
- `Effect.ts:24322-24341`: retry registers one callback identity across every accessed cell, and both callback/cancel remove that identity from every cell before resume.
- `Effect.ts:24343-24354`: successful commit visits cells in journal insertion order; every accessed cell wakes all its pending callbacks, including cells whose values were unchanged. Wakes are scheduled on the committing fiber's dispatcher at priority zero. Do not substitute changed-cells-only, read-set-only, one-waiter, or coalesced batch waking.
- `Effect.ts:24397-24403`: retry sets a sticky flag and signals interruption. Swallowing the cause does not clear the flag.
- `vendor/effect-4.0.0-rc.112/src/TxRef.ts:101,128-136,225-242`: allocation occurs outside the journal; accesses share one modify path and outside accesses are wrapped in a transaction. Failed/repeated attempts can allocate additional cells.
- `src/Effect4/Machine/Fibers.lean:1754-1789`: inline nested commands run before the original fiber continues; scheduled owed resumes post tasks instead. The guard protocol already blocks stale resumes (`:1814-1827`).
- `src/Effect4/Laws/Machine/Behaviour.lean:29-50`: the present Obs includes the entire Stores record, not merely user-visible cell contents.

## Findings requiring correction or an explicit proof condition

1. **Transitive admission.** The scout's lexical-only argument (`stm-scout.md:375-385,642-662`) depends on fully expanded programs with no stored program application. `machine-state.md:102-105` simultaneously plans program values for six modules. Admission therefore needs a reusable effect summary/certificate that composes through named programs, stored programs, handlers/finalizers, and service implementations. Unknown/foreign callees are refused without such evidence. A Boolean over only the visible outer Eff syntax is insufficient once those features land. Nested transaction flattening must respect dynamic calls and ownership, not merely text nesting.

2. **No-park does not establish atomicity.** The scout already correctly notices Deferred completion reentrancy, but its proposed defensive guard lists only park/yield/fork (`stm-scout.md:427-436,580-581`). Guard every route that can execute a different fiber before close, including inline resumes, observer delivery, interrupt delivery, injected commands, and protected-context changes. Prefer one checked command-effect classification/owner invariant over a second hand-maintained forbidden-row list. The proof, not the guard, licenses version elimination.

3. **Observation must be abstracted before buffer layout is frozen.** Placing TxOpen in Stores makes buffer, retry flags, registrations, and any future backend internals appear in current Obs equality. Use an explicit logical-state projection plus a representation relation. Specify which stable/quiescent boundaries permit observations and what a live transaction frontier exposes. Otherwise a list buffer and a map buffer fail equality for representation reasons even if transactions act identically.

4. **Rollback is selective.** The proposed admitted fragment includes ordinary synchronous Ref effects (`stm-scout.md:497-505`). They survive transaction failure/retry in rc.112. Allocation also survives. A denotation called "atomic/all-or-nothing" must scope rollback to transactional buffered writes; it cannot restore the entire Stores world. Finalizers see the transaction's interrupt-like retry cause. A pure TxRef-only first admitted profile is simpler, but broadening to other sync effects needs this explicit separation and evidence.

5. **Do not promote the serializability paragraph to a general behavior theorem.** `stm-scout.md:310-318` discusses committed attempts but then suggests only the lost wakeup remains observable for TxRef/pure bodies. Termination/frontier behavior needs a stronger condition. Candidate falsifier: two cells start equal; T reads the first, U commits both to a new equal value, T reads the second, and T loops on unequal values. A preempted inconsistent attempt can diverge before reaching validation; an atomic attempt cannot enter that branch. This is an unexecuted counterexample design, not a recorded failure. Restrict any reduction theorem to terminating validated attempts or prove a separate divergence-sensitive observation claim. Scope allocation and fairness too.

6. **A static footprint is a proof aid, not a dynamic wake set or a complete optimization certificate.** The scout correctly distinguishes this at `:359-390,667-684`, but its suggestion that comparing footprints mechanically checks a specialized implementation (`:631-640`) is insufficient. Equal sets do not establish values, branching, access order, multiplicity, commit atomicity, dispatcher choice, cancellation, or operation-budget behavior. Require a simulation against the selected observation.

7. **Fuel must preserve ownership and pending work.** `Fibers.lean:1941-1954` returns command residue; replay stops on an insufficient command receipt (`:2145-2147`). A transaction stopped by fuel must remain an unfinished attempt with buffer and ownership intact. It cannot release ownership, roll back as a typed failure, or let an unrelated host decision start another attempt when refuel resumes. The proposed global one-open-record invariant is conditional on this API discipline.

8. **Target agreement needs its actual configuration.** The scout proposes printing plain `Effect.tx(...)` (`:693-697`) while describing the model as Effect under PreventSchedulerYield (`:306-308`). These are different target profiles. Either emit/prove the protected wrapper with restrictions against rebinding its control references, or explicitly claim only an admitted/scheduling-restricted relation. Operation count, custom scheduler behavior, replay observation and callback cleanup placement require named obligations; an unqualified lockstep claim is premature.

## Exact decisions to record before implementation

- Atomic admitted transactions or general preemptible transactions; define the observable relation to ordinary rc.112 separately from a configured protected profile.
- First admitted fragment: TxRef-only and pure computation, or selected nontransactional sync effects with persistent side effects; decide allocation visibility/rollback explicitly.
- Retry policy: cause-catching refusal, lexical outside-tx refusal, empty access-set permanent wait, flat dynamic nesting, and no public Transaction service manipulation.
- Preserve rc.112's wake-on-access and per-waiter scheduling, with cleanup-before-resume; choose the internal task representation only after this contract is fixed.
- Logical observation/projection for transactional state and frontier behavior; do not expose backend buffer layouts through semantic equality.
- Lowering execution assumptions: single cooperative owner, or a proved synchronization/validation implementation for concurrent hosts.
- Generic typed TxRef rows from the outset, aligned with approved per-cell world tables, rather than rebuilding a number-only API which cannot represent most surveyed modules.

## Useful proof-graph nodes and red controls

Admission completeness/refusal locations; transitive non-reentrancy; owner uniqueness; own-writes reads; dynamic access-order tracking; selective rollback including allocation; all-cell commit atomicity; flat nesting; retry registration/cancel all-cell cleanup; stale/duplicate wake inertness; cleanup-before-resume; scheduled dispatcher/priority/order; fuel resumption; representation refinement; target-profile simulation.

Red controls should cover hidden program/finalizer reentrancy, changing the protected scheduler reference, swallowed retry, empty access set, read-only wake, two-cell duplicate wake, cancellation before task fires, allocation followed by failure, ordinary Ref write followed by retry, inconsistent-read divergence, and fuel exhaustion while the record is open. These are proposed tests; none was run in this read-only review.
