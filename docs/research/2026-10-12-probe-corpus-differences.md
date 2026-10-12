# Probe: the corpus's 18 registered disagreements (2026-10-12)

A read-only probe. It changes no tracked file. Each claim below names its evidence kind.

Evidence base:

- branch `land/typed-context` at `1cca2047`, the commit that moves the seven context rows;
- `land/release-merge` at `67d0cd06` holds the same `harness/truth/corpus-results.tsv` and
  `harness/truth/corpus-known-differences.md`;
- the fresh run in the worktree `/Users/pooks/Dev/lean4-effect4-land-context`
  (2026-10-12, 13:17 to 13:19) equals that committed file byte for byte (`cmp`);
- vendored sources: `vendor/effect-4.0.0-rc.112/src/…` and `vendor/effect-4.0.1/src/…`.

This checkout (`refactor/phase1-phase3` at `68856e77`) does not contain `1cca2047` yet. Here
the register still lists DI-76 (c) and `g309`, and the committed results hold 25 disagreement
triples, not 18.

## Know this first

1. The 18 triples are 12 programs and three causes. Only seven programs are distinct: five
   programs are the one program `Effect.fiberId`, and `g16` and `g55` are one program.
2. No exit kind differs, and no store differs. Six programs differ at run time, in fiber
   identity only. Six differ in a type only, and their runs agree on both entries.
3. **`g102` is registered under the wrong cause.** It is no fiber-numbering effect (DI-73).
   The machine forks one fiber per sibling of a layer merge. rc.112 builds a sibling whose
   build is already an exit inline, with no fork.
4. **DI-87's ruled repair of DI-77 (R4) breaks 20 agreeing rows.** `Ty.unit` rendered as
   `undefined` makes every `Effect.yieldNowWith` annotation fail under tsgo (`TS2375`).
5. Cheap and worth it now: two record repairs, with no code (queue items 1 and 2).
6. Not cheap: the five `getId` rows need DI-81's `Ty.fiberId` (the `Ty` series). The `g102`
   repair touches the merge arms of `src/Effect4/Program/Compile.lean` and about 108
   references in 12 law modules.
7. Optional and cheap: a named `undefined ≤ void` widening in the type oracle closes DI-77's
   six rows in TypeScript alone. It changes no run, so do it only with the ruling repair.

## The 18 triples

Class A is `getId`, class B is `g102`, class C is the unit spelling. The classes are below.

| # | program | dimension outcome | Lean | rc.112 or tsgo | class and cause | run outcome or type verdict | fix | cost | worth it? |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | `g81` | run differ | `success 0` | `success 8` | A: ruled divergence DI-73, repair DI-81 not landed | outcome: a fiber id as a number | DI-81 | large | no, not alone |
| 2 | `g81` | sync differs | `success 0` | `success 7` | A | outcome | DI-81 | large | no, not alone |
| 3 | `g144` | run differ | `success 0` | `success 8` | A, same program as `g81` | outcome | DI-81 | large | no, not alone |
| 4 | `g144` | sync differs | `success 0` | `success 7` | A | outcome | DI-81 | large | no, not alone |
| 5 | `g250` | run differ | `success 0` | `success 8` | A, same program | outcome | DI-81 | large | no, not alone |
| 6 | `g250` | sync differs | `success 0` | `success 7` | A | outcome | DI-81 | large | no, not alone |
| 7 | `g289` | run differ | `success 0` | `success 8` | A, same program | outcome | DI-81 | large | no, not alone |
| 8 | `g289` | sync differs | `success 0` | `success 7` | A | outcome | DI-81 | large | no, not alone |
| 9 | `g313` | run differ | `success 0` | `success 8` | A, same program | outcome | DI-81 | large | no, not alone |
| 10 | `g313` | sync differs | `success 0` | `success 7` | A | outcome | DI-81 | large | no, not alone |
| 11 | `g102` | run differ | `success {"fiber":5}` | `success {"fiber":2}` | B: machine model gap, `forEach`'s exit fast path | outcome: fiber handle and schedule; exit kind agrees | build an exited sibling inline | medium to large, Lean | later; rename the cause now |
| 12 | `g102` | sync differs | `{"fiber":5}` | `{"fiber":2}` | B | outcome, same | same | same | same |
| 13 | `g16` | types mismatch-A | A is `void` | infers `undefined` | C: printer spelling, DI-77 (ruled by DI-87, not landed) | verdict only; runs agree; `tsc clean` | oracle widening | small, TypeScript | optional |
| 14 | `g49` | types mismatch-A | `void` | `undefined` | C | verdict only | oracle widening | small | optional |
| 15 | `g55` | types mismatch-A | `void` | `undefined` | C, same program as `g16` | verdict only | oracle widening | small | optional |
| 16 | `g160` | types mismatch-A | `Fiber.Fiber<void, never>` | `Fiber<undefined, never>` | C | verdict only | oracle widening | small | optional |
| 17 | `g308` | types mismatch-A | `void` | `undefined` | C | verdict only | oracle widening | small | optional |
| 18 | `g363` | types mismatch-A | `void` | `undefined` | C | verdict only | oracle widening | small | optional |

No triple is a harness artifact in kind. The exact host number in class A is one, below.

## Class A: `getId` answers a number (10 triples)

The program. All five rows print the same module:
`export const main: Effect.Effect<number, never, never> = Effect.fiberId`.
Both faces type it `number`, so the type oracle agrees and the module compiles.

What each face answers:

- Lean answers `0`, the machine's index of the root fiber. The checker types `getId` at `nat`
  (the `getId` arm of `src/Effect4/Program/Checker.lean` answers `EffTy.pure .nat`).
- rc.112 answers its process-wide counter. `fiberIdStore` starts at `0`, and each new fiber
  takes `++fiberIdStore.id` (`vendor/effect-4.0.0-rc.112/src/internal/effect.ts:499`, `:512`).
  4.0.1 keeps this (`vendor/effect-4.0.1/src/internal/effect.ts:490`).
- The host number counts the runner's earlier fibers too. It is `8` on `runPromiseExit` and
  `7` on `runSyncExit`. The compatibility policy records its moves from `1` to `7` to `8`.

So the exact host number is a harness artifact. The disagreement is not one. rc.112's root
fiber never has id `0`, so no runner change can make the faces agree.

Cause: a ruled divergence. DI-73 is answered by DI-81 (ruled 2026-09-16): fiber identity is
the opaque `Ty.fiberId`, with no literal, compared up to one bijection by first appearance.
DI-81 has not landed: `Ty` has no `fiberId` constructor (`src/Effect4/Program/Ty.lean`).
R8 lists DI-81 as one of its parts (`docs/core/system-map.md`).

Fix and cost:

- **DI-81 as ruled.** Cost: large. A `Ty` constructor appended (wire tag, compatibility
  policy, generated folds, three decoders, the TypeScript reader). Then the checker,
  the printer's host value and the recorder. It reaches every behaviour gate.
- **An interim printer refusal of `getId`** (as `EmissionRefusal.outsideProfile` does for a
  literal, `src/Effect4/Codegen/Checked.lean`). Cost: small to medium, in Lean. Not
  recommended: it also refuses `g53` and `g238`, which agree today, and it moves no outcome.

Worth it: not for these rows. Land it with the `Ty` series, where R8 needs it. The five
copies are one program, so the register overstates the class five times.

Stale register text, to repair in queue item 1:

- DI-73 in `docs/DESIGN-ISSUES.md` says rc.112 answers `1` for `g81`. It answers `8` and `7`.
- `harness/truth/corpus-known-differences.md` cites `eq(getId, 0)`. No corpus row holds it.
  It is `pIdIsZero` in `Test/Api/ApiContract.lean`, a Lean-only battery program.

## Class B: `g102` forks three fibers more than rc.112 (2 triples)

The program (printed, shortened):

```ts
Effect.provide(
  Effect.forkChild(Effect.provideService(Effect.forkScoped(Effect.succeed(1), …), k8_4, 9), …),
  Layer.fresh(Layer.mergeAll(Layer.succeed(k6_4, 13),
                             Layer.merge(Layer.succeed(k4_4, 15), Layer.succeed(k4_4, 19)))),
  { local: true })
```

The two schedules, from the results file (fiber numbers by first sight, decisions row 274):

- Lean forks fibers `1`, `2`, `3` and `4` during the layer build: one per merge sibling.
- rc.112 forks fiber `1` alone during the build: the inner `Layer.merge`.
- After the build both faces fork the `forkChild` fiber, which dies, then the same six fibers.
  Lean numbers these seven `5` to `11`. rc.112 numbers them `2` to `8`.
- The answer is the `forkChild` handle: `{"fiber":5}` against `{"fiber":2}`.

So the numbering is not the cause. Row 274's renaming already applies. The cause is the
count of forks.

rc.112's mechanism:

- `Layer.mergeAll` builds through `forEach` with `concurrency: layers.length`
  (`vendor/effect-4.0.0-rc.112/src/Layer.ts:1596-1600`). `Layer.merge` is `mergeAll`.
- `forEach` with a concurrency above 1 runs `iterateEagerImpl`. Its "fast case (already an
  exit)" consumes an item whose effect is already an `Exit`, with no fork
  (`vendor/effect-4.0.0-rc.112/src/internal/effect.ts:4820-4821`). It forks the others
  (`vendor/effect-4.0.0-rc.112/src/internal/effect.ts:4851`).
- `Layer.succeed` is `succeedContext`, whose build is `constant(internalEffect.succeed(context))`
  (`vendor/effect-4.0.0-rc.112/src/Layer.ts:1129-1130`). `Effect.succeed` is `exitSucceed`
  (`vendor/effect-4.0.0-rc.112/src/internal/effect.ts:920`).
  So a `Layer.succeed` sibling is an exit, and no fiber runs it.
- A `fromBuild` layer (the inner `merge`) wraps its build in `onExit`, so it is forked.
- 4.0.1 keeps the fast path (`vendor/effect-4.0.1/src/internal/effect.ts:5089`).

The machine's mechanism: the arms `mergeForkOne` and `mergeAllForkOne` of the continuation
table in `src/Effect4/Program/Compile.lean` fork every sibling through `EffThunk.forkLayer`.
Their comment cites the fork at `internal/effect.ts:4851` and not the fast case before it.

Finite probe (bun 1.4.2, `effect` 4.0.0-rc.112 from `harness/truth/node_modules`). It counts
the fibers forked during `Layer.build`, by the ids of two marker fibers:

| layer | forks during the build on rc.112 |
| --- | --- |
| `Layer.succeed(a, 1)` | 0 |
| `Layer.mergeAll(succeed, succeed)` | 0 |
| `g102`'s layer | 1 |
| `Layer.mergeAll(succeed, effect)` | 1 |
| `Layer.mergeAll(effect, effect)` | 2 |

Lean's schedule for `g102` shows 4 forks during the same build.

Effect on outcomes: the exit kind, the values other than fiber handles, and the stores agree.
The fiber count differs, so a fiber handle's position differs, and the schedule differs.
`Layer.mergeAll(Layer.succeed(Config, …), …)` is a common application shape, so the gap is
not rare outside the corpus. In the corpus, `g102` is the only well-typed program with a merge.
The hand truth lane merges only `Layer.effect` layers (`pProvideMerge`, `pProvideTwice`,
`pMergeAll` in `harness/truth/Truth.lean`), which rc.112 forks too. So no truth fixture sees it.

The census: row `layer.merge-parallel-scopes` (`generated/effect-runtime-census.tsv`) says the
build runs "with concurrency equal to the layer count". It does not claim a fork per sibling.
No census row names `forEach`'s exit fast path.

Fix: in the two fork arms, build a sibling whose resolved layer is an immediate exit inline.
Keep the sequential child scope that rc.112 forks for every sibling. The immediate layers are
`LayerTerm.succeed`, and a `ref` or a `fresh` whose target is one. `fresh` calls the inner
build directly (`vendor/effect-4.0.0-rc.112/src/Layer.ts:3850-3851`). The await list then holds a fiber or a context per
sibling, in order, because `Context.mergeAll` reads the order.

Cost: medium to large, in Lean.

- `src/Effect4/Program/Compile.lean`: the two fork arms, `EffName.mergeForkOne` and
  `mergeAllForkOne` (their `forked` list), and `mergeContextsK`.
- Proof repair in 12 law modules under `src/Effect4/Laws/Program/`, about 108 references by
  `grep -c` of the arm names:

  | module | references |
  | --- | --- |
  | `Handles/Hooks.lean` | 28 |
  | `Agreement.lean` | 26 |
  | `Intro/Merge.lean` | 26 |
  | `Handles/Alphabet.lean` | 8 |
  | `DenoteR.lean`, `Typed/LayerArm.lean` | 5 each |
  | `NativeScope.lean` | 4 |
  | `EvaluateR.lean` | 2 |
  | `InterpR.lean`, `NativeActionScope.lean`, `SourceOpportunityActions.lean`, `ReleaseCustody/NativeActionDebit.lean` | 1 each |

- `Test/Audit/RuntimeCoverage.lean`: the witnesses of `layer.merge-parallel-scopes`.
- Gates: `check-corpus` moves `g102` to agree, and `verdict_moves` names it. Both entries leave.
- `check-truth` needs one new fixture with a `Layer.succeed` sibling.
- The machine change reaches the OCaml route: `check-compiler`, `check-native`, `check-ocaml`.

Worth it: later. It moves no exit and no store. It matters to R8's face comparison, whose
observation includes the schedule. No planned goal on the M5 → M6 → M7 spine needs it. Do it
when the merge arms are next opened. Name it now (queue item 3).

## Class C: the unit spelling (6 triples)

The programs print the unit value as `undefined`, and Lean renders `Ty.unit` as `void`
(`renderRaw` in `src/Effect4/Program/Ty.lean`):

| program | printed initializer | Lean A | tsgo infers A |
| --- | --- | --- | --- |
| `g16`, `g55` | `Effect.sync(() => undefined)` | `void` | `undefined` |
| `g49` | `Effect.flatMap(Effect.failCause(Cause.fail(12)), (a0) => Effect.succeed(undefined))` | `void` | `undefined` |
| `g160` | `Effect.forkChild(Effect.succeed(undefined), …)` | `Fiber.Fiber<void, never>` | `Fiber<undefined, never>` |
| `g308` | `Effect.succeed(undefined)` | `void` | `undefined` |
| `g363` | `Effect.uninterruptible(Effect.sync(() => undefined))` | `void` | `undefined` |

The oracle reads the unannotated module (`tools/target/corpus.ts`). `undefined` assigns to
`void`, and `void` does not assign to `undefined`. The column rule in `reportProject`
(`tools/target/checker.ts`) accepts that one-way case only on a program's `E` axis
(`strict-containment`). On the `A` axis it is a mismatch.

Effect on outcomes: none. Both entries agree on every row, and the shipped annotated module
compiles (`tsc clean`). This is a type verdict difference only.

The ruling and its trap:

- DI-87 (2026-09-16) rules DI-77 as R4 of `docs/research/2026-09-15-drift-release-plan.md`.
  `Ty.unit` renders `undefined` at every position, and the printer emits no `void` spelling.
- 20 well-typed corpus rows agree today with `void`. They are `g3`, `g66`, `g78`, `g105`, `g109`,
  `g117`, `g136`, `g148`, `g172`, `g175`, `g211`, `g235`, `g260`, `g274`, `g278`, `g300`,
  `g317`, `g368`, `g380`, `g384`. Each answers through `Effect.yieldNowWith`.
- rc.112 declares `yieldNowWith: (priority?: number) => Effect<void>`
  (`vendor/effect-4.0.0-rc.112/src/Effect.ts:2374`, and
  `vendor/effect-4.0.1/src/Effect.ts:2514`).
- Finite probe (tsgo 7.0.0-dev.20260629.1, `effect` 4.0.0-rc.112, the harness's strict
  options, a scratch module): `Effect.Effect<undefined, never, never> = Effect.yieldNowWith(0)`
  fails with `TS2375`. So does the `Exit` form. The `void` annotations compile.
- So R4 as written turns these 20 rows into `tsc errors` on well-typed programs, a worse class.
  The plan's slice 4 acceptance counts DI-77's six rows and not these.
- The same probe shows that `Effect.void` and `Effect.sync(() => {})` infer `void`.

Fix options:

- **(a) A named widening in the oracle.** Accept `A` when the actual assigns to the expected
  and the expected, with `void` read as `undefined`, is exactly the actual. Cost: small, about
  two hours. TypeScript only (`tools/target/checker.ts` or `tools/target/corpus.ts`, a test in
  `tools/target/oracle.test.ts`), one corpus promotion, the DI-77 entry removed. Gates:
  `check-corpus` (six `types` cells), `check-target`. DI-77's own text names this option.
- **(b) The printer spells unit as rc.112 does** (`Effect.void`, `Effect.sync(() => {})`),
  `Ty.unit` stays `void`. `Forms.lean` already reads `Effect.void` as `succeed (lit unit)`.
  Cost: medium, in Lean: the printer, `read_print` and `read_exact` in
  `src/Effect4/Codegen/Read.lean`, and `ts/eff/read.ts`. It contradicts R4's "emits none".
- **(c) R4 as written.** Not viable: it breaks the 20 rows above.

Worth it: the ruling repair, yes (queue item 2). The code, optional: it moves no run.

## The ranked fix queue

1. **Repair the register text** (record only, about 15 minutes, worth it).
   - In `harness/truth/corpus-known-differences.md`, give `g102` its own two rows under
     class B's cause, and keep the five `getId` rows under DI-73.
   - Replace `eq(getId, 0)` with `pIdIsZero` (`Test/Api/ApiContract.lean`).
   - The triples stay the same, so `check-corpus` passes unchanged.
   - In the receipt, propose two corrections to DI-73 (`docs/DESIGN-ISSUES.md`).
     The host answers `8` and `7`, and `g102` is class B. The owner writes the register.
2. **Ask the owner to amend DI-87's DI-77 part** (ruling only, worth it). Keep `Ty.unit` as
   `void`. Choose option (a) or (b) of class C. Cite the 20 `yieldNowWith` rows and the
   `TS2375` probe.
3. **Name class B** (record only, worth it). Seed a counterexample row in
   `Test/Counterexamples/REGISTER.md`: Lean forks a `Layer.succeed` sibling, rc.112 does not.
   Propose a census row for `forEach`'s exit fast path
   (`vendor/effect-4.0.0-rc.112/src/internal/effect.ts:4820-4821`).
4. **Option (a) for class C** (small, TypeScript, optional). Do it only after item 2 is ruled.
   It removes one register class and touches no proof.
5. **The class B machine repair** (medium to large, Lean, later). Open it with the next change
   to the merge arms. Open it earlier if a face claim about layer builds needs the schedule.
6. **DI-81 for class A** (large, later). Land it in the `Ty` series. Do not add an interim
   printer refusal.

What this probe does not establish:

- The class B repair's proof cost is an estimate from reference counts, not a worked repair.
- The probes are finite: four layer shapes on rc.112, and three annotations under one tsgo.
- No gate was run. The counts come from the committed results file.

## Commands and results

1. `git show land/typed-context:harness/truth/corpus-results.tsv`, then a Python copy of
   `disagreements_of` (`scripts/check-corpus.py`): 18 triples. On this checkout's file: 25.
2. `cmp` of the worktree's fresh `harness/truth/corpus-check/corpus-results.tsv` against
   `land/release-merge`'s committed file: equal.
3. `git branch --contains 1cca20472`: `land/release-merge` and `land/typed-context` only.
4. Read `harness/truth/corpus-check/generated/<name>.ts`, `inferred/<name>.ts` and
   `corpus.json` in the worktree for the 12 programs.
5. `bun run probe2.ts` (scratchpad; imports `effect` from `harness/truth/node_modules`): the
   fork counts of class B's table, `effect 4.0.0-rc.112`.
6. `harness/truth/node_modules/.bin/tsgo -p tsconfig.json` (scratchpad module, strict and
   `exactOptionalPropertyTypes`): two `TS2375` on the `undefined` annotations. No error on
   the `void` annotations or the `Effect.void` and `Effect.sync(() => {})` checks.
7. `grep -c` of the merge arm names over `src/Effect4/Laws/Program/`: the counts in class B.
