# 23:16 D4 closed-row amendment — bounded static review

**Verdict:** no concrete defect found in the row117 amendment at `7690c6d2b3c740aa3a4169f5bacae902c4b09462`, compared with its exact parent `1819fc1632b376f25f7333857eebf6984f6dfd73`. The only narrowing is the authorized empty requirement row. M7 retains its empty host-table restriction and all three existing conclusions. Earlier placement/comparison wording corrections are committed. One minor new wording slip remains in the coordinator's historical count description, below.

## Authority and exact statement trace

Authority read at main `296ad9faff85376679582a558c2ef9d123de9353`: `docs/core/decisions.md:210` (row117) rules the empty requirement row on M5, M6c, and M7's fragment, with the per-position presence design and H2 part two still open. `brief-D4.md:86–96` prescribes the extra premise immediately after `ClosedEff rootTy`, unchanged `DecisionKeeps`, and no proof using the presence fact yet.

All following Assembly references are at the reviewed D4 commit:

- `LoadsTyped`, `Typed/Assembly.lean:1051–1054`, checks `root.program` with **that root's signature** to obtain **the same rootTy** whose `requires` must equal `Env.Requirement.empty`; its conclusion is unchanged `∃ w, MachineTyped root rootTy w (loadR root.program fuel compileFuel)`.
- `ReachableTyped:1067–1070` adds exactly the same premise to the same checked root/type, before `RReachable root fuel m`. Its machine/type conclusion is unchanged. `DecisionKeeps:1057–1062` is unchanged; it still starts from an already typed machine and an admitted host answer.
- `M7Fragment:1477–1484` adds `closedRow` at the same `rootTy`; `lawful`, `root.table = []`, the checker verdict under `root.signature`, `ClosedEff`, and `answerFree` are retained. Requirement-row emptiness is not substituted for host-table emptiness. `M7Exits:1499–1502`, `M7Stores:1505–1508`, and `M7NoHalt:1511–1513` still require this fragment and keep their existing observations/conclusions.

## Connector and control trace

- `reachable_of_ledger:1250–1261` names `row` and passes it to `load lawful checked closed row` before the unchanged replay lift.
- `m7_of_capstone:1550–1575` passes `fragment.closedRow` to its reachable-state premise at `1560–1561`, alongside the same lawful/checked/closed facts and answer-free tape. It then uses the unchanged observation/stuck bridge. `m7_of_ledger:1579–1584` composes these same named propositions, so the premise remains inside each M7 result's fragment even though its own displayed binder list did not grow.
- `loadsTyped_of_denotesTyped:1185–1198` introduces but does not inspect the row premise. This matches the explicit authorization: the stronger conditional denotation/code-typing premise already supplies the current load proof, while the presence contract is not landed. It does **not** export a `LoadsTyped` theorem with the new premise removed. The unchanged lower-level code-typing builder is not a new checked-source theorem with an open-row guarantee.
- The three test-file diffs are only the required extra argument/introduction: `FitsOrder.Reviewed.loadsTyped_false` uses `rfl`; its `capstone_implies_load` forwards the new hypothesis. `FitsOrder.loadsTyped` and `AwaitLoad.loadsTyped` introduce it; their `capstone_at_load` facts forward it. `RawOrderLoad.capstone_false` supplies `rfl` for its concrete root. No historical refusal conclusion is replaced or removed, and no M5/M6/M7 proof is newly claimed complete.
- `M7Fragment.emptyTable` remains an explicit caller obligation even though the unchanged bridge proof does not inspect it; the observed replays are the same existing default-table frame/reference replays. This commit does not widen that fragment to a table-aware execution theorem.

## Earlier corrections and one small coordinator wording fix

Confirmed by the two exact commits requested:

- Main `296ad9fa` adds `brief-D4.md:140–148`, explicitly superseding the original unsafe-close edit location with the public close, and records that amendment in decision row151.
- Seat `1819fc16` changes `voidedClose_typed`'s docstring to `closeScopeR` and changes the evidence README to exactly the measured Effect3 cases (`zero`, `inline`, `two`, explicitly excluding `mapOne`/`loneDie`). Its ProtocolPosts history text is also labeled before/after the ruling.
- **Minor correction:** main `296ad9fa`, `docs/core/decisions.md` row151's appended site amendment, says the `seqOne` count `19 → 21` was measured “for the public path.” The retained step-one commit message says this was the attempted **unsafe-close placement**, affecting **scoped exits**; that is the reason the final change moved to the public close. Replace “for the public path” with “when voiding the unsafe close used by scoped exits.” This is a historical-evidence wording issue, not a source-semantic issue.

## Limits

Only committed diffs/statements, the named authority excerpts, and direct connectors were inspected. No dirty/later runtime work, compiler, build, generator, or runtime probe was read or executed; no repository was modified. This is independent static confirmation, not a fresh compilation or an independent repetition of the seat's reported counts. No conclusion is drawn about the pending presence contract, H2 part two, or other ongoing D4 work.
