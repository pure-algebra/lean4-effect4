# Review of the Codex landing, 15cb510e → ac4a0fe5

Reviewed 2026-09-20 by reading the twenty commits, the two receipts
(`2026-09-20-skeleton-first-receipt.md`, `2026-09-20-m1-receipt.md`), the landed modules and
the working tree. No build was run (Codex holds the compiler; a worker is open on
`Laws/Machine/Refinement.lean`, whose uncommitted diff is Phase C work in flight).

## 0. Verdict

The redirect landed in order and honestly reported: Phase A (`8b64039f`), placement
(`05417cc6`), the Phase B skeleton (`3f893074`), and Phase C fills through the arena and the
reference kernel. The data changes are the ones asked for and nothing was hidden: the
regeneration count is stated as three, not one; the 334-line legacy file was untracked so
its removal is a file deletion, not a git deletion; the proof-search tool's two defects
were found by Codex itself and fixed before any count was published. Nothing was pushed.

Four things need a steer before Phase C continues, in this order: stop the `rfl` → `by aesop`
rewrites (§2 F1); move the store definitions out of the bank's `norm simp` set (F2); close
the memo question by an invariant, not by keeping a write (F3); confirm the exact clock was
your call (F4).

## 1. The redirect, item by item

| Redirect item | Landed | Where | Note |
|---|---|---|---|
| A1 payload parameter on `DeferredCell`/`DeferredStore`; LegacyStores deleted | yes | `Machine/Stores.lean:1077,1087`; `Laws/Machine/Refinement.lean` keeps `Projects`/`Refines` only | ten op bodies unchanged |
| A2 `RunFiber.origin : Origin := root \| forked parent daemon site`; site from `Point.path` | yes | `Machine/Fibers.lean:224-231`, `spawn` at `:924`; `Program/Compile.lean:987,991,1030,1056,1455` | `raceAll` carries `Option (List Nat)` with a cursor `nextSite` advanced by `[1]` |
| A2 `statusOf` reads origin; `forkedOf`/`forkedIds`/`forkedEvents` leave the API | yes | `Api/Supervision.lean:224-227`; `Laws/Api/Supervision.lean:53` keeps `TraceFacts.forkedOf` as the control | `reachable_agrees : forkedOf m.trace = originForks m` stated, open |
| A3 row 61 deleted; refs/cells rows become indexed columns | yes | `Typed/Sources.lean:58-59` (`.column "HeapCell" (some RefKey.mk)`, `.column "PromiseCell" (some DeferredKey.mk)`) | |
| A4 one regeneration | no: three | receipt | two generation-manifest gaps found only by OCaml compile: `Origin` pruned as a placeholder; prelude annotations for the parameterized store |
| A5 placement as one import-only commit | yes | `05417cc6`, 47 files | architecture map 26 → 0 wrong-direction imports; `make check` green at the boundary |
| B6 `#typed_state` column quantifier from the field's carrier | yes | `Typed/TypedStateDecl.lean:146,327`; 17 predicates, 12 carrier, 2 refusals | World reuses `Columns.Stores_refs` and `Columns.DeferredStore_cells` |
| B7 `World`, order, leaves, `CompletionOk` reads `Ρ cell` only, `HeapNat_iff`, `heapNotMonotone` control, extension at fork/refMake/deferredMake/memoBuild, `Expect` pruned | yes, all statements | `Typed/World.lean`; `Typed/State.lean:15-18` | 24 open (19 + 5 controls) |
| B8 `Arena`, `LawfulArena` ten laws, list instance, `toList` + five theorems, `refStepOfA`, `refStepOfA_list`, `Projects` instance, two red controls | yes | `Laws/Machine/Arena.lean`, `RefKernel.lean:150-`, `Refinement.lean:378` | red controls stated at ceiling 2, not yet closed (they are `decide`) |
| B9 connector statements: `map`, naturality, `map_id`/`map_comp`, `completionPrim_injective`, `deferredOk_iff_image`, `memoEntry_keys` | yes | `Refinement.lean:44-160` proved; injectivity/image/Projects/Factors being proved in the uncommitted diff | `memoEntry_keys` lives in Handles |
| B10 `ParkHandshake` stated, held to M4 | yes | `Laws/Machine/Handshake.lean:40`; consumer `Guard/Handshake.lean` at ceiling 1 | packet's `wakeList` replaced by a read-only `pendingWaiters` projection, since `wakeList` dispatches; `Inert` = `obs (drive … [resume]) = obs m` for every fuel and answer |
| B11 every changed M1 statement as Obligation + `#proof_wanted`; ceilings pinned | yes | 36 new gate sites; 311 statements accounted for | the receipt records four statements whose pre-proof snapshot is missing; it does not backfill them |
| C12 banks first with red controls | partly | `Effect4.Stores` declared, 92 registrations; `TypedState` 4 | see F2 |
| C13 fills in order | in progress | deferred map 14/14, arena 13/13, refkernel 5/5, `CompletionSupport` 0; World 0/24; origin/clock/simulation seats open | 130 live `#proof_wanted` markers remain of 172 at Phase C start |
| C14 `make check`, coverage 133/135 | at Phase B | receipt | Phase C's full check pending |

Not in the redirect and landed anyway: the exact clock (`Data/ClockMillis.lean`, `Store/Domain/Clock.lean`,
`Laws/Machine/Clock.lean`, `OCaml5/Lcnf/ClockFlow.lean` 450 lines, Zarith in the switch,
keyed host protocol v3, TS recorder changes). The receipt says the owner chose it (§ "Clock
addition, authorized during Phase A"). See F4.

## 2. Findings, ranked

**F1. 104 existing proofs rewritten to `by aesop` for no gain.** Commits `60520379`,
`f92d05d9`, `d0af326b`, `da93c0a8`, `0091b2ba`, `1864dcbd`, `531b9c76`, `76f67589` replace
90 `:= rfl` and 14 short tactic proofs with `by aesop` ("use checked searched proofs").
The receipt itself says "this is proof-body cleanup, not new semantic coverage" and that the
before/after censuses "do not establish a causal effect of the rewrites". `#auto_census`
re-proves *statements*, so the metric is unchanged by the rewrite; what changes is that a
`rfl` becomes a search on every build and depends on whatever the default bank does next.
§6a's loop is for filling skeleton obligations, and its before/after numbers are for the
bank's power on statements, never a target to raise by editing bodies. Steer: stop; do not
revert (eight builds of churn for nothing); count only skeleton statements from here.

**F2. The `Effect4.Stores` bank registers definitions as `norm simp`.** `CompletionData.lean:7-10`
puts `DeferredStore.make/cellAt/setCell/isDone/poll/register/cancel/complete/drainDue/wakeBatch`
and `Owed.mapCode` in the bank as unfolding rules; `Arena.lean:113` adds the class
projections at the list instance. Every downstream search in the bank now unfolds the store
ops, which is why FrameOwned's census falls from 2/49 plain to 0/49 with the bank while the
arena and map modules close. A bank is equations and laws (`map_*`, `deferred_*`, the ten
arena laws, `refStepOfA_size`), and a definition is unfolded locally with `add norm unfold`
where a proof needs it. Move the definitions out before the World fill, which will otherwise
inherit the noise.

**F3. The memo identity write was kept on a counterexample that needs duplicate map ids.**
`syncOpStep`'s `memoComplete` arm keeps `memo := st.memo.updateEntry memoMap layer id`
(`Stores.lean:2020`). The evidence (`MemoDuplicateCounterexample.lean`) shows behaviour changes
only when two memo maps carry the same id, a state `MemoValid` (`StoresLaws.lean:208`) does not
exclude and allocation never produces. Codex's process reason is right (a field deletion does
not authorize a behaviour change), so the fix is its own commit: state `MemoKeysFresh` beside
`ScopeKeysFresh` (`Stores.lean:1743`), prove `memoEntry_keys` under it, then delete the write.
Validity by reachability (kickoff §3.5), not a no-op kept for bit-equality on unreachable states.

**F4. The exact clock is a scope decision to confirm.** It cost the protocol version bump
(v2 refused explicitly), Zarith, a 450-line LCNF flow analysis with 22 controls, three
auxiliary producer groups and the TS recorder repair. The design is sound (`ClockMillis`
as a two-constructor nominal over `Nat` so mono LCNF keeps it; `clockNow` narrows with
explicit refusal per DI-56; frontier deadlines stay exact). If you did not authorize it in
those words, say so now; it is not separable from Phase A's commit any more.

**F5. Regeneration was three, and the two extra cuts are producer gaps, not process.** Both
were found only by the OCaml compiler: a retained-type manifest that did not list `Origin`,
and hand-written prelude annotations that did not know the store is parameterized. Two
producer checks that read the environment would have caught them before generation: every
inductive reachable from the API cut's closure is retained or pruned by a stated rule; every
prelude annotation names a type at its current arity. Both fit the owner's rule (a check
reads the environment, not source text).

**F6. Instrument defects found and fixed, historical counts retired.** `ProofGraph.search`
set `maxHeartbeats` in options but not the cached `Core.Context` limit, so every earlier
"closed at cap N" ran at the default cap; and a searched proof could reference a temporary
helper discarded by rollback. Both fixed (`tools/ProofGraph/Search.lean`), with controls;
the fresh portable census is 648/4062 across 218 modules, 647 within `[propext, Quot.sound]`.
This is the loop working as intended.

**F7. Small items.** (a) The two Arena red controls are stated at ceiling 2 and are `decide`;
close them. (b) `docs/STATE.md` gained a 51-line status section; the rule is a pointer
paragraph, the receipt holds the status. (c) The generated `api_engine` carries blank-line
indentation that `git diff --check` flags; a producer fix, not a hand edit. (d) The
uncommitted `README.md` edit that stood at the start of the day is no longer in the
working tree, in no stash and in no commit; check it was you who dropped it.

## 3. Numbers

| Measure | Value |
|---|---|
| Commits since 15cb510e | 20, ahead of origin by 25, nothing pushed |
| Source diff | 145 files, +5,869 / −2,249 |
| Regenerations (LCNF / CAS / EFF) | 3 / 4 / 4 completed; partial attempts recorded separately |
| `Effect4.Stores` registrations | 92 (was 0); `TypedState` 4 |
| Live `#proof_wanted` markers | 130 (172 at Phase C start) |
| `#typed_state_obligations` sites | 64; ceiling sum 263, pinned at statement counts |
| Proof bodies rewritten to `by aesop` | 104 |
| `make check` | green at `05417cc6` and after Phase B; Phase C's pending |
| Coverage | 133/135, partial `op.Failure`, `layer.launch-holds-scope` |
| Trust audit | 469 modules, 66,145 declarations, `[propext, Quot.sound]`; 14 modules / 29 declarations on the exact-implementation exception |

## 4. What to hand Codex

1. Stop rewriting existing proof bodies; the census is a measurement, not a target.
2. Re-cut the `Effect4.Stores` bank: equations and laws in, definitions out; re-run the
   FrameOwned and Fibers censuses as the control (FrameOwned must not fall).
3. Memo: `MemoKeysFresh`, `memoEntry_keys`, then delete the identity write, one commit.
4. Close the two Arena red controls, then the World fill (24), then the origin/clock seats
   in dependency order (`M1OriginClauses` 10 → `Sched.M1Origin` 10 → `Api.M1Origin` 18 →
   `Api.M1Trace` 15), then the simulation seats. Full `make check` and the coverage line
   close Phase C.
