# Probe: counted operations against Effect's loop (2026-10-12)

Read-only probe. Base: `refactor/phase1-phase3` at `68856e778` (called HEAD below). The masked
provider entry is on `land/typed-context` at `dbb212937`, which contains `c2a1cdda4` (called the
branch below). HEAD does not contain `c2a1cdda4`.

## Know this first

- **The +5 is the masked provider entry.** `c2a1cdda4` adds five counted operations before a
  provide region's body: the `getInterruptible` bind (three), `provideMasked` (one) and
  `restoreRegion` (one). `budgeted k` in the traces is itself a provide region. So every budget
  window moves by exactly five.
- **The provider was already off before `c2a1cdda4`.** Effect enters a provide region in 2
  operations (rc.112) or 1 (4.0.1). HEAD takes 7, the branch takes 12. Effect leaves the region
  in 1 operation. Both of ours take 4, because the restore runs as a finalizer program.
- **The other constructs mostly agree.** `scoped`, `onExit`, `ensuring`, `uninterruptible` and
  the printed mask form match rc.112 operation for operation. `acquireRelease` costs +2 at entry
  and −1 at registration. Its release costs +10, or +13 when the release is an exit value.
- **Yield points move.** A fiber yields when its counted operations reach the budget. Every
  extra operation before a program point moves that point's yield window. Checked programs meet
  this only at the default budget 2048, because the checker refuses a budget provision. Raw
  programs (the Semaphore, Pool and Queue traces) meet it at every budget.
- **Recommendation.** Align the provide region first: one stateful entry action, as
  `enterScoped` is for `scoped`, and an inline restore at the pop, as `exitScoped` does. Land it
  after the typed-context merge, so the trace windows are re-pinned once. Record the rest.

Evidence kinds. Effect's counts are measured: a host probe under bun 1.4.2, on the vendored
sources (appendix). Our counts are read from the Lean definitions. No `lake` ran. The predictions
for our machine are finite readings, not runs and not theorems.

## The counter on each side

Effect rc.112 counts one operation per loop iteration. `runLoop`
(`vendor/effect-4.0.0-rc.112/src/internal/effect.ts:629-679`) resets `currentOpCount` at each
entry (`:636`), increments it at the loop top (`:643`), and asks `shouldYield` before it
evaluates the current primitive (`:644-652`). `shouldYield` is `currentOpCount >=
maxOpsBeforeYield` (`Scheduler.ts:174-176`); the default is 2048 (`Scheduler.ts:269-272`). The
verdict wraps the current primitive in `flatMap(yieldNow, …)` (`:651`). So a fiber yields before
its operation `k` of an entry, where `k` is the budget in force at that loop top.

Effect 4.0.1 keeps the same loop (`vendor/effect-4.0.1/src/internal/effect.ts:622-674`,
`:629`, `:636`, `:642`). It adds `succeedWith` (`:697-707`): `map`, `tap`, `exit` and `match`
continuations pass a value to the next continuation inline and count it (`++currentOpCount`).
No yield check runs at an inline step. So 4.0.1's count equals rc.112's count on these shapes,
but 4.0.1 has fewer loop tops, and a yield that rc.112 places at an inline step lands one or
more operations later in 4.0.1. Every 32nd inline step returns to the loop (`maxInlineSteps`,
`:769`).

Our frame machine counts at `countOp`, called by `iteration` after `runloopTop`
(`src/Effect4/Machine/Fibers.lean`). `yieldVerdict` and `injectYield` transcribe `:644-652`.
`driveStep` resets the count at `Cmd.evaluate`. `Cmd.deliver` evaluates a `sync` thunk's answer
without a count, as rc.112's `Sync[evaluate]` pops in the same iteration (`:929-936`). The term
machine (`src/Effect4/Laws/Program/EvaluateR.lean`) is the second `FiberEvaluator` instance of
the same `iteration`. Its denotations (`updateContextR`, `contextEntryR`, `onExitR`,
`acquireInR`, `denoteFin` in `src/Effect4/Laws/Program/DenoteR.lean` and
`src/Effect4/Laws/Program/InterpR.lean`) take one counted operation per frame step. So one count
covers both machines.

## The table

A count is the operations a construct adds to its body, as the probe measures it: entry is the
operations between the region's first primitive and the body's first, exit is the operations
between the body's last primitive and the caller's next. "HEAD" and "branch" differ only in the
provider entry.

| Construct | rc.112 (measured) | 4.0.1 (measured) | Ours (read) | Difference vs rc.112 |
| --- | --- | --- | --- | --- |
| `provideService`, `provideContext`, `updateContext`: entry | 2: `withFiber` reads, switches and returns `onExitPrimitive` (`:2073-2096`, switch at `:2091`); `OnExit[evaluate]` pushes (`:4009-4012`) | 1: `withFiber` switches and pushes `OnExitImpl` in the same step (`:2175-2201`, `onExitUnsafe` `:4219-4224`) | HEAD 7, branch 12; steps below | HEAD +5, branch +10 (vs 4.0.1: +6, +11) |
| the same: exit | 1: the body's last step pops `OnExit`, `contAll` masks, the callback restores and returns `undefined`, `contA` returns the exit (`:4013-4023`); the next step pops the mask frame and the caller | 1: `OnExitImpl` `contA` (`:4164-4205`) | 4: `evaluatePrim.finalizerOr` builds `finalizerCode` over `Prim.withFiber (EffThunk.setCtx previous)` (`interpOf.finalizerProgram`, `.restoreCtx`); push, `setCtx`, pop to `EffName.restore`, the exit | +3; the outer budget returns 2 loop tops later |
| the same, when the update keeps the context object | 1 (`:2090` returns `self`) | 1 | HEAD 3, branch 8 (`updateThenK`, `updateKeepsIdentity`) | +2, +7 |
| `provideContext(exitValue, ctx)` | 0: `effectIsExit` (`:2196`) | 0 (`:2301`) | 0: `compileEff`'s `.provideContext` and `provideLayerBodyK` test `asExit?` | 0 |
| `scoped`: entry | 2 (`:3938-3948`) | 1 (`:4100-4111`) | 2: `enterScoped`, then `Prim.onExit` push (`src/Effect4/Program/Compile.lean`) | 0 (vs 4.0.1: +1) |
| `scoped`: exit, empty scope | 1 | 1 | 1: `exitScoped` restores inline and continues with `Prim.ofExit` | 0 |
| `onExit`, `ensuring`: entry | 1 (`:4002-4030`, `:4043-4057`) | 1 | 1: `Prim.onExit` push (`compileEff` `.onExit`) | 0 |
| `onExit`, `ensuring`: exit, one-step finalizer | 3: `flatMap(eff, _ => exit)` push, `eff`, the exit (`:4019-4023`) | 3 | 3: `finalizerCode` push, the program, the exit | 0 |
| `uninterruptible` | entry 1, exit 0 (`:4302-4310`; `setInterruptible` acts in `getCont`, `:4312-4322`) | 1, 0 | 1, 0 (`actionAt`, `WithFiberAction.setInterruptible`) | 0 |
| `uninterruptibleMask(f)` native | entry 1 (`:4340-4351`); `restore(x)` +1 | 1; +1 | not expressible; the derived form `Authoring.uninterruptibleMask` (`src/Effect4/Program/Authoring/Mask.lean`) | — |
| the printed mask form `flatMap(uninterruptibleMask(r => succeed(r)), r => uninterruptible(x))` | entry 4 | 4 | 4: bind push, `getInterruptible`, pop, `uninterruptible` | 0 (+3 vs native, decisions row 246) |
| `acquireRelease`: acquire entry | 6 (`:3971-3987`): `contextWith`, the mask, `flatMap` push, `Scope` service (`Context.ts:420-425`), its exit, `tap` push | 6 | 8: bind push, `EffThunk.getCtx`, pop to `EffName.acquireCtx`, `EffThunk.acquireMasked`, push, `ambientScope`, pop to `EffName.acquireIn`, push | +2 |
| `acquireRelease`: registration, after the acquire | 4: `as` push, `scopeAddFinalizerExit`'s `suspend` (`:3847-3858`), `void_`, `succeed(a)` | 4 counted (3 loop tops and one `succeedWith`, `tapCont` `:1522`) | 3: push, `SyncOp.scopeAdd` answered by `Cmd.deliver`, `EffName.afterScopeAdd`'s value | −1 |
| release at `scoped` exit, one finalizer, release not an exit | 6 from the closing step to the caller: push, `updateContext` switch, `OnExit` push, the release, its exit, the exit | 5 | 16: push, `finProgram` `.foreign`'s `Prim.suspend`, `getCtx` (3), `setCtx` (3, `EffName.releaseUnder`), `EffThunk.releaseMasked`, `Prim.onExit` push, the release, the restore (3), the release's exit, the exit | +10 |
| the same, release an exit value (`Effect.void`) | 3: `provideContext` returns the exit (`:2196`) | 3 | 16: ours always switches | +13 |

The probe's composite rows confirm the last four. `scoped(acquireRelease(x, rel))` against
`scoped(x)` adds 6 at entry in both versions, and at exit 9 (rc.112) or 8 (4.0.1) for a
non-exit release, 6 for `Effect.void`. Ours reads +8 at entry and +18 at exit for both.

### The provider entry, step by step

The branch, from `updateContextAt` (`src/Effect4/Program/Compile.lean`, `land/typed-context`).
HEAD takes steps 5 to 11 only, with `updateThenK` and `bodyThen` answering
`Prim.onExit (regionCode body) (restoreCtx previous)` directly.

```mermaid
flowchart LR
  s1["1 push"] --> s2["2 captureMask: getInterruptible"]
  s2 --> s3["3 pop to provideMask"]
  s3 --> s4["4 provideMasked: mask"]
  s4 --> s5["5 push"] --> s6["6 getCtx"] --> s7["7 pop to updateThenK"]
  s7 --> s8["8 push"] --> s9["9 setCtx: budget k from here"]
  s9 --> s10["10 pop to bodyThen"] --> s11["11 onExit push"]
  s11 --> s12["12 restoreRegion: caller's mask"] --> b["13 body"]
```

rc.112 does steps 6, 7 and 9 inside one `withFiber` callback, and step 11 is its second
operation. 4.0.1 does 6, 7, 9 and 11 inside one. The term mirror is `updateContextR`
(`getInterruptible` under `guardR`, three; the `.mask false (.contextEntry …)` action, one),
`contextEntryR` (`getContext`, three; `setContext`, three; `onExitR` push, one) and
`restoreRegionR` (one): twelve.

### Measured yield windows

The probe forks a child that sets a flag, then runs twelve marks under
`provideService(body, MaxOpsBeforeYield, k)`. The yield first lands between mark 1 and mark 2 at
`k` = 8 and 9 on rc.112 (mark 1 at operation 7), and at `k` = 7 and 8 on 4.0.1 (mark 1 at
operation 6). Our fork prefix is the same three steps (bind push, the `fork` action, the pop).
So by reading, the same window is at `k` = 13 and 14 on HEAD and 18 and 19 on the branch.

## Does each difference move a yield point, and what can it change?

A yield point moves when the difference lies between the fiber's entry and the point, in the
same entry. The count resets at every park and resume. A yield is no interruption; it lets
every other runnable fiber run first.

- **Provider entry (+5 HEAD, +10 branch).** It moves every later point of the entry. Every
  `Effect.provide(layer)` holds at least two such regions: `buildWithMemoMap`'s
  `provideService(CurrentMemoMap)` (`Layer.ts:756-765`) and the final `provideContext`. A
  changed outcome: fiber A loops, one provide region and one `Ref.update` per round; fiber B,
  forked before, reads the Ref when it first runs. B first runs at A's yield, after 2048
  operations. A round costs 13 more operations in our branch, so B reads a smaller count than on
  Effect. Any exit that carries B's reading differs. The traces' raw budgets show the same move
  as a renumbering: the scenario at `k` in our machine is the scenario at `k − 10` on rc.112
  (branch). The protected-permit windows move with it. Semaphore trace 4 loses its permit at
  budgets 13 to 27 on HEAD (`Test/Program/SemaphoreTraces.lean`). So whether a pinned budget
  puts the yield inside the take's mask is a fact about our machine, not about Effect.
- **The switch window.** rc.112 can yield between the switch and the `OnExit` push (one loop
  top). HEAD can yield at two loop tops there, both interruptible. The branch masks the switch,
  so the window is closed, as in 4.0.1. An interrupt at that yield leaves the switched context
  current for the rest of the fiber: outer handlers and finalizers read the inner services and
  budget.
- **Provider exit (+3, budget lag).** It moves every point after the region in the same entry.
  The inner budget governs two loop tops that rc.112 checks against the outer budget. Under a
  small inner budget our fiber can yield at the exit where Effect does not, and another fiber
  runs before the caller's continuation.
- **`scoped`, `onExit`, `ensuring`, masks.** No move against rc.112. Against 4.0.1, `scoped`
  entry is one operation longer, and rc.112's scoped switch window remains (the restore-slot
  scout's open question).
- **`acquireRelease`.** The acquire's +2 −1 moves points inside and after the acquisition by one
  or two. The release's +10 or +13 moves every point after a scope close in the same entry. The
  release runs masked, so its extra loop tops are yield points inside a finalizer that Effect
  does not have.
- **4.0.1's inline steps.** Not ours. 4.0.1 can carry a yield past a mask's pop that rc.112
  makes inside the mask (the `tap` tail of `acquireRelease`). Our machine follows the pin.

None of these differences changes a run's set of reachable schedules when the budget is free.
Each changes which budget, or which default-budget program, selects a schedule. The traces pin
budgets, so their windows are statements about our machine only. They are not host claims.

## Ranked recommendation

1. **Align the provide region (entry and exit) — high value, medium cost.** Replace
   `updateContextAt`'s chain with one stateful action, as `enterScoped` is: read, switch, push
   `Prim.onExit body (restoreCtx previous) false` onto the stack, continue with the body. Pop it
   natively, as `exitScoped` does: restore the context inline and continue with `Prim.ofExit`.
   That is 4.0.1's shape: entry 1, exit 1, and no switch window without a provider mask.
   Against rc.112 it is −1 at entry and closes the pin's window; record that as a signed
   divergence (the owner rules the shape: rc.112's 2 with the window, or 4.0.1's 1 without it).
   Move `scoped` to the same shape in the same slice, so one rule covers both regions.
   Cost: `updateContextAt`, `updateThenK`, `contAOf` arms, `interpOf.withFiberOf` and
   `evaluateNative` (`src/Effect4/Program/Compile.lean`); `updateContextR`, `contextEntryR`,
   `restoreRegionR` and `Body.contextEntry` in the term (`DenoteR.lean`, `Sched.lean`,
   `EvaluateR.lean`, `InterpR.lean`, `Folds/Region.lean`); the region steps of `run_eq_ref` and
   of the typed-context clauses on the branch (`src/Effect4/Laws/Program/Typed/`); the lockstep
   shapes of `Test/Program/RuntimeRContract.lean`; the windows of the Semaphore, Pool and Queue
   traces; step-term pins in the Faces and Engine batteries; regenerate `lcnf`; the gates
   `check-compiler`, `check-native`, `check-ocaml`, `check-truth`, `check-host-protocol`. Land it
   after the typed-context merge, before the windows are re-pinned for `c2a1cdda4`.
2. **Align the release — medium value, small cost after 1.** Route `EffName.releaseUnder` and
   `EffThunk.releaseMasked` through the same atomic region, and test the release's code with
   `asExit?` as `provideLayerBodyK` does (`:2196`). That removes +9 (+12 for an exit release).
   The merge-versus-replace question of the restore-slot scout belongs to the same slice.
   `finProgram`'s counted `Prim.suspend` (+1) stays unless the close can resolve the capture.
3. **Align the acquire's context read — low value, small cost.** Read the context inside the
   masked action, so `contextWith` is one step (−2), and register with `suspend` then the value,
   as `scopeAddFinalizerExit` does (+1).
4. **Record — no code.** Propose a decisions row and a census line for: the printed mask form's
   +3 against the native callback (already decisions row 246); 4.0.1's inline `succeedWith`
   counts; and, until 1 and 2 land, the region differences above. State in the trace batteries
   that a pinned budget is a statement about our machine.

## What this note does not establish

- No Lean run. Our counts are read from the definitions; a probe under `lake env lean` should
  confirm the twelve-step entry and the four-step exit before a slice starts.
- The host probe runs the vendored TypeScript sources under bun, not the npm build. The harness's
  installed `effect` is 4.0.0-rc.112 and its `internal/effect.ts` equals the pin's.
- The multi-finalizer close (`scopeCloseFinalizers`, `ProgName.closeWalk`) and the parallel
  close were not counted.
- No proof obligation is placed. A slice from recommendation 1 places its own.

## Appendix: the probe

Files in the session scratchpad, not tracked. Command and versions:

```sh
bun --version   # 1.4.2
bun run opcount.ts /Users/pooks/Dev/lean4-effect4/vendor/effect-4.0.0-rc.112/src
bun run opcount.ts /Users/pooks/Dev/lean4-effect4/vendor/effect-4.0.1/src
bun run y2.ts      <same two roots>
```

The probe prints `succeedWith=undefined cache=false` on rc.112 and `succeedWith=function
cache=true` on 4.0.1, so each run loaded the runtime it names. The core of `opcount.ts`:

```ts
const cur = () => (F.getCurrent() as any).currentOpCount
const mark = (n) => E.sync(() => { log.push([n, cur()]) })
// entry = (b - a) - (b0 - a0), exit = (c - b) - (c0 - b0), baseline mk = x => x
E.runSync(E.flatMap(mark("a"), () => E.flatMap(mk(mark("b")), () => mark("c"))))
```

`y2.ts` runs, for each `k`, `flatMap(forkChild(sync(() => ran = true)),
() => provideService(m1 → … → m12, MaxOpsBeforeYield, k))` under `runPromise`, and reports the
first mark that sees `ran`.
