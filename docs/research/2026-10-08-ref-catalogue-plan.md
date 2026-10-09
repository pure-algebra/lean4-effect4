# Ref catalogue slice

The slice reuses the native Ref rows. Its new shared part connects typed steps to native callbacks without changing captured inputs.

Base: `b8b4099eb6516f59d4380f8a8bdcb488332adeee`. The catalogue brief names this slice before PartitionedSemaphore.
Claude owns cutover C3, C4, and S1 in the primary checkout. This slice uses isolated worktrees.

## Design

Ref holds one value. The independent model transcribes the thirteen effectful operations in `vendor/effect-4.0.1/src/Ref.ts`.
It stores no program syntax and imports no step or machine implementation.
The existing native rows remain the operations. Their existing authoring forms remain the public calls.
A new `Step.callback` supplies a typed step to those forms. It freezes captured sources before the current-value binder enters scope.
It relocates each captured term's internal binders by one slot. Freezing without relocation can change a captured fold's value.
The connector returns existing `Src` data through the existing native form. It introduces no operation family or cell record.

`Ref.set` retains the existing cell-identity result. Effect 4.0.1's implementation returns its backing MutableRef, although its declaration says void.
A declared-void observation must discard that result explicitly. The slice does not amend DI-98 or equate backing and outer JavaScript objects.
The model observes the next cell value and reply. It distinguishes optional write behavior in the native operation laws when needed.
Callbacks are pure first-order steps. Arbitrary JavaScript closures, exceptions, reentrant mutation, and host object aliasing are outside the profile.
The direct host functions `makeUnsafe` and `getUnsafe` are outside the effectful surface.

## Proof placement

| Obligation | Concept and question | Reach and premises | Limits | Consumer and requirement |
| --- | --- | --- | --- | --- |
| Capture translation reads the original value | `translation-simulation`; helper of `step-language-sound` | One inserted binder; successful source reading; aligned caller scope | No arbitrary host callback claim | `Step.callback` reading; Ref callback agreement; R10 |
| Capture translation keeps its type | `store-typing`; helper of `step-language-typed` | One inserted binder; typed source; aligned caller scope | No source admission or allocation claim | Callback typing and checked Ref callers; R4 |
| Ref native operations agree with the model | `translation-simulation`; proposed `ref-steps-agree`, role simulation | One allocated cell; encoded inputs; successful callback evaluation in the required shape | No scheduling, whole-run, or JavaScript semantics theorem | Ref callers, then SynchronizedRef and keyed cells; R10 |
| Typed step callback reaches one Ref update | `translation-simulation` and `store-typing`; connector of the preceding claims | Step reading and typing premises, normal formed types, typed captures and prior cell membership | Membership does not establish allocation; safety does not establish progress | Real captured Ref caller and later module wrappers; R10 and R4 |

The receipt proposes the semantics registry addition. Claude owns the semantics registry move during this slice.
Helpers name their consuming obligation. No theorem changes a frozen statement.

## Verification

- Build each new module and its direct consumers with `LEAN_NUM_THREADS=3`, one Lake process per worktree.
- Apply shared laws to actual numeric and handle callers.
- Reject wrong captured types, wrong callback shapes, and unallocated-cell premises.
- Check captures that inspect caller depth and captures containing an internal fold.
- Check each optional operation on both branches, and check reply plus final cell value.
- Emit checked TypeScript from real callers and compile the exact output with pinned tsgo 7.
- Compare finite callers with Effect 4.0.1, including a mutation that changes the stored value without changing the reply.
- Regenerate engine fixtures after step changes and inspect every diff. Recheck affected Faces consumers.
- Audit transitive axioms on new declarations, source trust rules, and root reachability without a full sweep.
- Report `#load_report` as its measured direct-citation view, with known traversal limits.

The slice finishes with a checked commit and a receipt. It does not push or change the primary checkout during Claude's work.
The next catalogue module needs a keyed reservation model. Existing Semaphore steps do not implement PartitionedSemaphore's behavior.
