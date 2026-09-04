# Spike S3: Flow names a concurrent child through an operation

Status: spike complete, third pass, 2026-09-03. Row S3 of
`docs/research/2026-09-03-deep-plan.md:98`. Deliverables: `workshop/Deep/ForkFlow.lean`
(module `Deep.ForkFlow`, 1733 lines, builds), `workshop/Deep/fork-lowering.md`, and this
report. Rulings 3, 6, 7 of the plan's §0; review findings 1, 2, 3, 12, 13, 14 of
`docs/research/2026-09-03-deep-plan-review.md`.

The second pass rebased the spike onto the fiber machine that folded in spike S1's `Prim`
constructors and **both of this spike's first-pass machine findings**; §5 records which are
closed and how they are witnessed. The third pass rebases it onto **spike S4's rewritten
region compile** (`docs/research/2026-09-03-spike-s4-compile.md`): §3 and §6 are rewritten
for P1, P2 and P3, and the port is now by *delegation* — `compileFork` calls the new
`compileRegion` on every arm it does not change, so this module cannot go stale on
`compileRegion`'s bodies again.

No file under `Effect4/`, `Effect4Test/`, `.lake/packages/`, `workshop/Deep/Fibers.lean`,
any other `Deep.*` module or `lakefile.toml` was edited.

---

## Summary

The operation route works, end to end, and it is cheaper than the review priced it.

* **The profile is twelve `OpSpec` rows** and nothing else: `tableAlphabet` builds the
  `FlowAlphabet` from them, `admitRegions` admits the five witness flows with no clause
  changed, and the *existing* `SkeletonRender` printer already spells all twelve calls with
  no printer change — the fork's four request fields destructure at the call site through
  `Lowering.tupleArgs` into `fibers.fork(root, args, daemon, region)`.
* **The compile is one arm, and it now *calls* `compileRegion` for everything else.**
  `compileFork` writes out five arms — the two `perform` arms and the three recursion sites
  — and delegates the rest, so `compileFork_eq_compileRegion` **proves** that a flow with no
  profile operation compiles to the identical program, in three real cases. Nothing in
  `RegionSimulation.lean` moves: `Config`, `RegionName` (all five constructors), `Code`,
  `Table`, `performOp`, `performCont`, `catchCont`, `closeExit`, `regionSuspendBody`,
  `isFailure`, `statelessOracle` (including S4's new `registrations`) and `regionBound` are
  reused unchanged, and `regionInterp` is reused under a record update — which is how S1's
  `cancelThenFail` and S4's `finalizerExit`/`contE` repairs arrive without a line of work.
* **S4's P2 law extends to the profile.** `compileFork_not_failure` proves the fork compile
  emits `Prim.failure` nowhere either: a refused `join`/`await`/`yieldNow` compiles to
  `Prim.suspend point` and the interp's `suspendBody` raises the defect, so the refusal is
  raised by the **interp** on all twelve rows rather than half by the compile.
* **Eight executable witnesses run**, by `#guard`: a deferred fork joined after one
  `RunDecision.fire`; a child that fails and fails its parent through `join`; the same
  child answered as a value through `await`; a *caught* `join` whose failure edge binds the
  child's typed error; a fork naming an undeclared root **refused visibly and never stuck**;
  a **masked child** whose interrupt is recorded under the mask and delivered at the
  unmask; a stranded join that **halts the machine with its reason**; and a refused
  `direct` row that **dies rather than suspending for ever** on S4's frontier constructor.
* **`WellSourced` is proved for every program-carrying `withFiber` action** — the three fork
  shapes, a masked body, and every `raceAll` entrant. It is provable exactly because the
  request carries a block reference, which is DB-05's conditional discharged by the machine.
  `ConfigWellSourced` restates the invariant over the fiber's **whole configuration**
  (`current` plus `stack`), as the first pass recommended, and its **fork arm is proved**.
* **The decision partition is proved**, all three clauses, including "`RunDecision` names
  no `DecisionId` at all" — which survived the carrier's change to `interruptFrom`, now
  carrying `ReasonAnnotations α` and still naming no site.
* **Both first-pass machine findings are closed by the carrier and witnessed here**: a join
  on a fiber the machine does not hold is `Outcome.stuck (Stuck.unknownFiber …)` visible as
  `ReplayResult.stuck`, and `WithFiberAction.refuse` carries a refusal's cause. The spike
  routes nine of the twelve rows through `refuse`, and after S4 the other three through
  the interp's `suspendBody`; §3 says why.
* **Nothing is deferred and there is no `sorry`.** Two things are owed and are stated as
  `Prop`-valued definitions rather than assumed: `WellSourcedClosed` (closure of the
  configuration invariant under `stepDecision`) and `ForkFuelBound` (the sum-over-live-fibers
  bound). A third, `runnerFuel`, is an arithmetic spelling that stands in for the
  un-imported `Effect4.Flow.regionFuelFor`.
* **Two structural costs the review did not name** are recorded in §8: a flow has one
  `resultTy` for every declared root, so a child whose result type differs from its
  parent's cannot live in the same flow; and `join`'s failure arrives as a machine-level
  `Prim.failure`, not as an oracle `.error`, so a *caught* `join` needs packet P3's
  `onSuccessAndFailure` repair — implemented here for the profile arm.

Every theorem sits at `propext`/`Quot.sound`; `FiberOp.ofIndex_index` needs no axiom at
all. The `#print axioms` block is `ForkFlow.lean:1716-1731`.

---

## 1. What builds

```
lake build Deep.ForkFlow      -> Build completed successfully (48 jobs)
```

`workshop/Deep/ForkFlow.lean`, module `Deep.ForkFlow` of the non-default `Deep` library
(`lakefile.toml:98-101`). Imports: `Deep.Fibers`, `Effect4.Semantics.RegionSimulation`,
`Effect4.Target.TypeScript.ScriptFlow`, and — one beyond the plan's S3 row —
`Effect4.Flow.Interrupt`, which the decision-partition section of ruling 7 needs for
`Point.site`, `Point.site_ge`, `Point.site_ne_choose` and `sitesSeparated`. That import is
already in the built closure of `Effect4.Target.TypeScript.Skeleton`, so it costs nothing;
if the landing wants S3's import list literally as the plan wrote it, §7's three theorems
move to whichever module owns the partition instead.

Everything asserted is asserted by `#guard`, which is evaluation, not a `native_decide`
axiom. The counts:

| Kind | Count | Where |
| --- | --- | --- |
| `theorem` | 18 | proved, no `sorry` |
| `#guard` | 51 | all pass |
| `example` (separation-4 gates) | 6 | `ForkFlow.lean:1702-1707` |
| `Prop`-valued obligations | 2 | `WellSourcedClosed`, `ForkFuelBound` |
| `sorry` | 0 | |

Axiom report (`ForkFlow.lean:1716-1731`, printed at every build):

```
compileFork_eq_compileRegion        [propext]
compileFork_perform_off_profile     [propext]
compileFork_not_failure             [propext]
wellSourced_actions                 [propext, Quot.sound]
wellSourced_fork                    [propext, Quot.sound]
wellSourced_compileForkAt           [propext]
configWellSourced_make              [propext]
configWellSourced_forkChild         [propext, Quot.sound]
sitesSeparated_holds                [propext, Quot.sound]
interrupt_ne_choose                 [propext, Quot.sound]
choose_site_lt_base                 [propext, Quot.sound]
forkRequestOf_value                 [propext]
rootRequestOf_value                 [propext]
handleOf_handleValue                [propext]
listOf_listValue                    [propext]
FiberOp.ofIndex_index               (none)
```

---

## 2. The profile's rows

`fiberProfile answerTy errorTy : List OpSpec` (`ForkFlow.lean:239-274`), twelve rows, in
`FiberOp.index` order (`:139-152`). `A` is the child's answer spelling and `E` its error
spelling; `H = Fiber.Fiber<A, E>`, `X = Result.Result<A, E>`, and
`R = readonly [number, ReadonlyArray<unknown>]` is a plain root reference.

| # | Name | Request | Answer | `errorTy` | rc.112 |
| --- | --- | --- | --- | --- | --- |
| 0 | `fork` | `readonly [number, readonly [ReadonlyArray<unknown>, readonly [boolean, Option.Option<number>]]]` | `H` | `never` | `forkUnsafe` `:5264-5284`; `forkIn` `:5364-5378` when `region` is `some` |
| 1 | `forkScoped` | as `fork` | `H` | `never` | `forkScoped` `:5400-5406` |
| 2 | `join` | `H` | `A` | **`E`** | `fiberJoin` `:5291` |
| 3 | `awaitFiber` | `H` | `X` | `never` | `fiberAwait` `:5304` |
| 4 | `interruptFiber` | `H` | `void` | `never` | `fiberInterrupt` `:859` |
| 5 | `interruptAll` | `ReadonlyArray<H>` | `void` | `never` | `fiberInterruptAll` `:895` |
| 6 | `childrenSnapshot` | `void` | `ReadonlyArray<H>` | `never` | `awaitAllChildren`'s snapshot `:5318` |
| 7 | `awaitChildren` | `ReadonlyArray<H>` | `void` | `never` | the exit half of `awaitAllChildren` |
| 8 | `raceAll` | `ReadonlyArray<R>` | `A` | **`E`** | `raceAll` |
| 9 | `uninterruptibleIn` | `R` | `A` | **`E`** | `Effect.uninterruptible` `:4302-4310` |
| 10 | `interruptibleIn` | `R` | `A` | **`E`** | `Effect.interruptible` `:4331-4352` |
| 11 | `yieldNow` | `number` | `void` | `never` | `yieldNowWith` `:982-994` |

Rows 9 to 11 are **new in the second pass**, and they exist because the carrier now
supports them: `WithFiberAction.setInterruptible body flag`
(`workshop/Deep/Fibers.lean:282-284`) lets a program mask its own fiber, and
`Prim.yieldNowWith` is a constructor since spike S1. Without them the profile could not
express a masked child at all, so witness F (§4) would have no subject. `uninterruptibleIn`
and `interruptibleIn` take a plain root reference, which is the same "name a declared root"
shape the fork takes minus `daemon` and `region`; `yieldNow` takes the dispatcher priority.

The error channel, exactly as ruling 8 words it: **`join` carries the child's typed error in
`errorTy`** so a `performCatch` on it binds a value of that type; **`await` never fails**
(`errorTy = never`) and answers the exit as a value; **`interrupt` never fails**.

`daemon` and `region` are *request fields*, not formers (finding 14). `region = some n`
means `forkIn n`, which forks a daemon in rc.112 anyway, so `daemon` is only consulted when
`region` is `none`. `forkScoped` is nevertheless a **row of its own**, because the ambient
`Scope` is a fact of the fiber's context (`RunInterp.ambientScope`), not something a request
can name; a `forkScoped` whose request names a region is refused
(`ForkRefusal.scopedNamesRegion`). Immediacy is *not* a field: `forkActionOf` always builds
`⟨startImmediately := false, …⟩`, and when the child runs is `RunDecision.fire` / `flush`
(finding 3).

`Exit` on the two faces: `Result.Result<A, E>` on the host (`EffectV4.lean:49-52` already
fixes that spelling — rc.112 has no `Either`), and on the wire the `Val` of
`Effects.Trace.ToVal (Except ε α)` (`Effects/Trace.lean:69-70`), i.e.
`pair (bool true) value` / `pair (bool false) error`. `exitAsValue`
(`ForkFlow.lean:359-368`) is that coding; a cause with no `fail` reason (a `die`, an
interrupt) has no `Val` preimage and reads as `unit`, which is the same projection
`Exit.toOutcome` takes and is recorded as a loss, not hidden.

**The value alphabet.** A handle is `pair (str "Fiber") (nat id)`, and
`handleOf : Val → Option FiberId` (`ForkFlow.lean:318-320`) is **where a request's `fiber`
argument becomes a `FiberId`** — on the profile's value alphabet, not in the machine.
`RunInterp.fiberValue` mints one (`Fibers.lean:433-434`) and `handleOf` reads one back;
`handleOf_handleValue` proves they are inverse. `forkRequestOf_value` and
`rootRequestOf_value` prove the same for the four-field fork request and the two-field root
reference, and `listOf_listValue` for the wire's list spine.

Row names pass `EffectV4.bindingName` — pinned by `#guard` (`ForkFlow.lean:285-286`), along
with the three arities the printer's three call shapes turn on. `await` is reserved in the
generated-binding profile, the same refusal `Effect4/Concurrency/FiberFamily.lean:68-71`
already records, so the rows are `awaitFiber` and `interruptFiber`.

---

## 3. The compile's arms, and the rc.112 primitive each corresponds to

Spike S4 (`docs/research/2026-09-03-spike-s4-compile.md`) rewrote `compileRegion` under this
module between the second and third passes. The third pass **re-ported by delegation**:
`compileFork` (`ForkFlow.lean:585-634`) now *calls* the new `compileRegion` on every arm it
does not change, and only five arms are written out — the two `perform` arms and the three
recursion sites (`jump`, `choose`, the `enter` body) where the recursive call has to be
`compileFork` so a nested block's profile operation is still seen. `compileForkAt`
(`:636-639`) sits beside `RegionSimulation.compileAt` (`RegionSimulation.lean:645-647`).

What that buys: `compileFork_eq_compileRegion` (`:656-694`) is now three real cases and six
delegations rather than a mirrored case analysis, so this module does not go stale the next
time `compileRegion`'s arms change. Three of S4's changes are visible here.

* **P1, one frame per region.** The `enter` arm emits
  `Prim.onSuccessAndFailure body (RegionName.regionCont region enterPoint)
  (RegionName.close region enterPoint)`, and `forkTable` carries the five-way `RegionName`
  match, `regionCont`'s close check (`closeExit oracle (oracle.registrations point)`) and
  `close`'s reason concatenation.
* **P2, the compile emits `Prim.failure` nowhere.** Every frontier is `Prim.suspend point`.
  The refusal of the three `direct` rows moved with it (below), so
  `compileFork_not_failure` (`:696-757`) holds for the profile compile too — a strictly
  better answer than the second pass's compile-time `Prim.failure (Cause.die ())`.
* **P3 is upstream.** A caught operation compiles to `onSuccessAndFailure …
  (RegionName.cont point) (RegionName.caught point)`, and `contE (caught point)` reads the
  error off the cause. The `firstError` helper the second pass hand-rolled is deleted;
  `catchesMachineFailure` (`:573-580`) now only decides *which* profile rows need the
  failure arm at all.

| Profile row | Compiled program | Interp arm | rc.112 |
| --- | --- | --- | --- |
| `fork` | `onSuccess (withFiber point) (RegionName.cont point)` | `withFiberOf point = some (WithFiberAction.fork (compileFork … ⟨fuel, root, args, tape⟩) ⟨false, daemon, inherit⟩)` | `forkUnsafe` `:5264-5284` |
| `fork` with `region = some n` | as above | `… = some (WithFiberAction.forkIn program options n key)` | `forkIn` `:5364-5378` |
| `forkScoped` | as above | `… = some (WithFiberAction.forkScoped program options key)` | `:5400-5406` |
| `join` | `onSuccess (sync point) (cont point)` | `parkOf = some (ParkKind.join target joinEffect)`, `exitValue exit joinEffect = Prim.ofExit exit` | `:5291`, resumed by `:561-562` |
| `awaitFiber` | `onSuccess (sync point) (cont point)` | `parkOf = some (ParkKind.join target awaitValue)`, `exitValue exit awaitValue = Prim.success (exitAsValue exit)` | `:5304` |
| `interruptFiber` | `onSuccess (withFiber point) (cont point)` | `WithFiberAction.interrupt target` | `:859` |
| `interruptAll` | as above | `WithFiberAction.interruptAll targets none` | `:895` |
| `childrenSnapshot` | as above | `WithFiberAction.snapshotChildren` | `:5318` |
| `awaitChildren` | as above | `WithFiberAction.awaitNewChildren snapshot` | `awaitAllChildren`'s exit half |
| `raceAll` | as above | `WithFiberAction.raceAll (entrants.map compileFork …)` | `raceAll` |
| `uninterruptibleIn` | as above | `WithFiberAction.setInterruptible (compileFork … root args) false` | `:4302-4310` |
| `interruptibleIn` | as above | `WithFiberAction.setInterruptible (compileFork … root args) true` | `:4331-4352` |
| `yieldNow` | `onSuccess (yieldNowWith priority) (cont point)` | none — the machine reads the constructor before it consults `parkOf` (`Fibers.lean:701-709`) | `:982-994` |
| a refused row with an action channel | as its row above | `WithFiberAction.refuse (Cause.die ())` | — |
| a refused `join` / `await` / `yieldNow` | `Prim.suspend point` | `suspendBody point = Prim.failure (Cause.die ())` | — |
| a *caught* `join`, `raceAll` or mask row | `onSuccessAndFailure (…) (cont point) (**caught** point)` | `contE (caught point)` routes to `catchCont`'s failure successor with the cause's first `fail` error | S4's P3 |
| any operation **not** in the profile | one delegation to `compileRegion` at the same point | `regionInterp`'s own `contA` | unchanged |
| `ret`, `jump`, `choose`, the six frontier arms, `enter`, `acquire`, `leave` | `jump`/`choose`/`enter`-body recurse into `compileFork`; everything else is one delegation | unchanged | unchanged |

Three facts about this table are theorems, not claims:

* `compileFork_perform_off_profile` (`ForkFlow.lean:643-654`): the `perform` arm off the
  profile is exactly `compileRegion` at that point — by delegation, so it stays true
  whatever `compileRegion`'s arm becomes.
* `compileFork_eq_compileRegion` (`:656-694`): with `opOf = fun _ => none`, `compileFork`
  **is** `compileRegion`, for every fuel, block, environment and tape. This is what lets
  the landing add the arm to `compileRegion` without re-proving `E4-TARGET-CE-019..021`,
  the five region receipts in `Effect4Test/Semantics/RegionSimulationContract.lean`, or
  the harness's `frame-trace` output.
* `compileFork_not_failure` (`:696-757`): the profile compile emits `Prim.failure` nowhere
  either — S4's P2 law, extended to the fork profile.

### The run-time refusal, and where it is raised

Finding 2, cost (a): the named block is inside a request value, so `danglingSuccessor`,
`reachSet` and `CyclesWF` never see it, and "the request names a declared root of this flow
with a matching parameter count" is a decidable check *at the operation*, on the run's own
configuration. `checkRoot` / `checkFork` / `refusal?` (`ForkFlow.lean:455-520`) is that
check, with six constructors: `requestMalformed`, `rootUndeclared`, `rootUnknown`,
`rootArity`, `handleMalformed`, `scopedNamesRegion`.

**Which channel it is raised through — the coordinator's question (4), re-answered after
S4.** The spike routes the refusal through **`WithFiberAction.refuse`** wherever there is an
action to carry it, which is nine of the twelve rows. That is the honest place: a run-time
refusal should be a *machine event with a cause*, not a constant the compile folded in, and
`refuse` (`Fibers.lean:295-296`, applied at `:896-898`) is exactly the arm the first pass
asked for.

The other three — `join`, `await`, `yieldNow` — have no action channel, because they compile
to a primitive the machine reads directly: `parkOf : Prim → Option ParkKind` has no cause
slot (a `none` would fall through to the `Prim.sync` arm and answer from the oracle as if
the join had succeeded), and `Prim.yieldNowWith` is read before `parkOf` is consulted. The
second pass raised their refusal in the compile, as `Prim.failure (Cause.die ())`. **S4's P2
made that unnecessary and slightly wrong**: the compile is supposed to emit `Prim.failure`
nowhere. So the third pass moved them onto S4's own frontier constructor — a refused
`direct` row compiles to `Prim.suspend point` (`compileRefusal?`, `ForkFlow.lean:522-527`,
gated on `FiberOp.direct`, `:199-204`), and `forkTable.suspendBody` raises the defect at
that point (`directRefusalAt`, `:529-539`). The refusal is therefore raised by the **interp**
on all twelve rows, and `compileFork_not_failure` holds.

Either way the refusal is a **defect**, `Cause.die ()`, not a typed failure: nothing in the
flow declared it, so a `performCatch` must not catch it (`docs/DESIGN-BASIS.md:121-125`) —
and it cannot, because `contE (caught point)` needs a `fail` reason and a `die` has none.
Witness E (§4) shows the `refuse` path end to end; the receipts at `:1600-1621` show the
`suspend`/`suspendBody` path, including that a fiber stepping it **dies rather than
suspending for ever** and that the machine is not stuck.

### The interp

`forkTable` (`ForkFlow.lean:787-841`) is `regionInterp` under a record update, now three
fields: `contA` and `contE` because the compile they call is `compileFork`, and
`suspendBody` because it is where the three `direct` rows' refusal is raised. Both
continuation fields carry S4's five-way `RegionName` match — `cont`, `caught`, `regionCont`,
`close`, `fin` — in S4's shape. Everything else is inherited by the update: S1's
`cancelThenFail`, S4's constantly-`Exit.success ()` `finalizerExit` (P1's discharged `hfin`),
`syncValue`, and the six loop fillers. That is the whole point of the record update: two
upstream spikes changed `regionInterp` and this module needed one field's worth of work.

`forkParkOf` (`:843-869`), `forkActionOf` (`:871-935`) and `forkWithFiberOf` (`:937-949`)
are the two `RunInterp` fields that carry the profile; everything else in `forkInterp`
(`:951-999`) is the inert filler this instantiation needs, chosen to be *visible* rather
than silent: `cancelName`/`abortName` exist because `Prim.async` gained a cancel name and no
compiled program ever emits an `async`, so they are the identity and a `RegionName.fin`;
`restoreName`/`mergeName` answer that same `fin`, whose `contA` is now `Prim.suspend` — a
live frontier, so a use by the middleware exit path or a settled race would show up as one
rather than compute something plausible. `scopeLinkFiber`, `dropFinalizer` and `closeScope`
return `Option` (the fiber machine's M7), and this interp answers `some` for every scope,
which is correct for a profile that never opens one.

`forkOracle` (`:1001-1004`) is `statelessOracle` **unchanged** — including S4's new
`registrations` field, which `statelessOracle` computes with `regionRegistrations` and which
this spike therefore gets for free (no witness flow has a region, so it is never demanded).
`forkAnswerOf` answers `ok unit` at every profile point: the profile's value is minted by the
machine and `contA` continues with the machine's value, never the oracle's
(`RegionSimulation.lean:884-892`).

---

## 4. The witnesses, with their tapes and results

Five `RegionFlow String` over one table (`profileTable "number" "number" userRows`,
`ForkFlow.lean:1346`), all five **admitted by `Effects.admitRegions`** (`#guard`s at
`:1441-1445`) — the point of ruling 3: no clause of the eighteen v3 clauses or the fourteen
region clauses changed.

The start is
`runFork interp 512 (RunMachine.empty ()) (compileForkAt … ⟨runnerFuel, entry, [input], []⟩) ()`
— rc.112's `runForkWith` (`:5410-5430`), the root evaluated synchronously on the caller's
stack — then `replayEval` on the tape.

| Witness | Flow | Input | Tape | Result |
| --- | --- | --- | --- | --- |
| deferred start | `flowJoin` | `fork(3, [7], daemon=false, region=none)` | `[]` | `frontier`; fibers `[(0,false),(1,false)]`; parent's exit `none` |
| **A** join | `flowJoin` | as above | `[fire ⟨0⟩]` | `finished`; fibers `[(0,true),(1,true)]`; child ⟨1⟩ `Exit.success (nat 7)`; parent ⟨0⟩ `Exit.success (nat 7)` |
| **B** join fails | `flowJoinFails` | `fork(3, [1], false, none)` | `[fire ⟨0⟩]` | child ⟨1⟩ `Exit.failure (Cause.fail (nat 9))`; parent ⟨0⟩ **the same cause** |
| **C** await | `flowAwait` | `fork(3, [1], false, none)` | `[fire ⟨0⟩]` | parent ⟨0⟩ `Exit.success (pair (bool false) (nat 9))` |
| **D** caught join | `flowJoinCaught` | `fork(3, [1], false, none)` | `[fire ⟨0⟩]` | parent ⟨0⟩ `Exit.success (nat 9)` |
| **E** refusal | `flowJoin` | `fork(2, …)` — block 2 is not a root | `[fire ⟨0⟩]` | parent ⟨0⟩ `Exit.failure (Cause.die ())`; `stuckOf = none`; `finished`; fibers `[(0,true)]` |
| **F** masked child | `flowMaskedChild` | `nat 0` | `[fire ⟨0⟩]` | child ⟨1⟩ **masked**, interrupt **pending**, **no exit**; `stuckOf = none` |
| **F** (continued) | `flowMaskedChild` | `nat 0` | `[fire ⟨0⟩, fire ⟨1⟩]` | `finished`; child ⟨1⟩ and parent ⟨0⟩ both exit with an **interrupt-bearing** cause |
| **G** stranded join | hand-built machine | a handle naming fiber `99` | `[evaluate ⟨0⟩]` | `ReplayResult.stuck (Stuck.unknownFiber ⟨99⟩)` |
| **H** refused `direct` row (new, third pass) | hand-built machine | a `join` whose request slot holds `nat 7` | `[evaluate ⟨0⟩]` | compiles to `Prim.suspend`, `isFailure = false`, `suspendBody` answers `Prim.failure (Cause.die ())`, the fiber exits with it, `stuckOf = none` |

### A to D, arm by arm (`Fibers.lean` line numbers)

1. The parent's entry block compiles to `onSuccess (withFiber p0) (cont p0)`; the frame is
   pushed (`Runtime.lean:1682-1685`), then `iteration` reaches `Prim.withFiber` (`:746-749`),
   `withFiberOf` answers `WithFiberAction.fork`, `spawn` (`:616-634`) creates fiber ⟨1⟩ with
   an `untrackChild` observer, and `start … false` (`:638-644`) enqueues `Task.start ⟨1⟩` on
   the **parent's** dispatcher at priority 0 (`:5277`). The parent answers
   `Prim.success (handleValue ⟨1⟩)`.
2. `contA` at `RegionName.cont p0` continues at block 1 with `[] ++ [handle]`.
3. Block 1's `join` compiles to `onSuccess (sync p1) (cont p1)`; the frame is pushed, then
   `parkOf` (`:728`) classifies `sync p1` as `ParkKind.join ⟨1⟩ joinEffect`, the target has
   no exit, so an `Observer.resumeAwait` is appended to ⟨1⟩ and the parent parks
   (`:729-743`). `runFork`'s `drive` runs out of commands. **This is the frontier the empty
   tape reports.**
4. `RunDecision.fire ⟨0⟩` drains the parent's dispatcher once (`:1115-1127`,
   `Scheduler.ts:225-233`), runs `Task.start ⟨1⟩` as `Cmd.evaluate ⟨1⟩`, and the child runs
   to its exit.
5. `exitFiber` (`:983-1012`) stores the exit and fires ⟨1⟩'s observers **in index order**:
   `untrackChild` first, then `resumeAwait`, which comes back as
   `Cmd.resume ⟨0⟩ token (interp.exitValue exit joinEffect)` (`:919-920`).
6. The parent unparks with that primitive. For `join` it is `Prim.ofExit exit`: a success
   flows through the pushed `onSuccess` frame into `cont p1` and on to block 2; a failure
   finds no `contE` on an `onSuccess` frame, unwinds, and the parent exits with the child's
   cause — **witness B**. For `await` it is `Prim.success (exitAsValue exit)`, so the same
   frame answers with the exit *as a value* — **witness C**.
7. Witness D's block 1 is a `performCatch`, so the compile emitted S4's shape,
   `onSuccessAndFailure (sync p1) (RegionName.cont p1) (RegionName.caught p1)`, and
   `forkTable.contE` at the `caught` name reads `(failuresOfCause cause).head? = some (nat 9)`
   and continues at the failure successor with `errorEnv ++ [nat 9]`.

### E — a refused fork is visible and not stuck (new)

`ForkFlow.lean:1587-1598`. Three assertions in sequence, so the path is pinned and not just
the outcome:

* `forkActionOf … FiberOp.fork (forkInput 2 …)` — the action builder *would* build a
  `WithFiberAction.fork` over `compileFork … ⟨2⟩ [nat 7] []`, i.e. the refusal is not an
  accident of decoding;
* `forkWithFiberOf …` at the entry point answers
  `some (WithFiberAction.refuse (Cause.die ()))` — the refusal takes the `refuse` channel;
* end to end: the parent exits `Exit.failure (Cause.die ())`, `stuckOf = none`,
  `isFinished`, and `fiberSummary = [(0, true)]` — **no child fiber was ever created**.

That last clause is the content of the coordinator's request (a): a refusal is a fiber's
failure, never a state the machine cannot leave.

### F — a masked child, interrupted under the mask, delivered at the unmask (new)

`flowMaskedChild` (`ForkFlow.lean:1425-1439`), ten blocks, three declared roots
(`[⟨0⟩, ⟨6⟩, ⟨8⟩]`). The parent mints its fork request from a number in scope (a `forkRequest`
row of the flow's own service), forks child root `6`, **yields**, then interrupts the child
and joins it. Child root `6` runs root `8` under `uninterruptibleIn`; root `8`'s body parks
on its own `yieldNow`.

The sequence:

1. `runFork`'s drive: parent mints the request, forks ⟨1⟩ (deferred → `Task.start ⟨1⟩` on
   the parent's dispatcher), then `yieldNow 0` → `Prim.yieldNowWith` (`Fibers.lean:701-709`)
   parks the parent and enqueues `Task.resume ⟨0⟩` on the **parent's** dispatcher, behind
   the start task in the same priority bucket.
2. `fire ⟨0⟩` drains both in FIFO order:
   * `Task.start ⟨1⟩` → child ⟨1⟩ runs `uninterruptibleIn` → `WithFiberAction.setInterruptible
     body false` (`Fibers.lean:874-876`) → `FrameFiber.uninterruptible`
     (`Runtime.lean:2823-2829`) pushes `Prim.setInterruptible true` and masks; the body then
     parks on its own `yieldNow`, enqueuing on the **child's** dispatcher, which nothing has
     fired.
   * `Task.resume ⟨0⟩` → the parent resumes, performs `interruptFiber(handle ⟨1⟩)` →
     `interruptThenJoin` → `interruptRecord` (`Fibers.lean:544-565`) finds ⟨1⟩ not running
     and **not interruptible**, so it records the cause and returns `applyNow = false`; the
     parent then countdown-parks awaiting ⟨1⟩.
   * Asserted at this point: `fiberSummary = [(0,false),(1,false)]`, `maskedOf ⟨1⟩`,
     `interruptPendingOf ⟨1⟩`, `exitOf ⟨1⟩ = none`, `stuckOf = none`. **The mask held.**
3. `fire ⟨1⟩` drains the child's dispatcher: the yield's resume runs, the masked body
   finishes, and popping the `Prim.setInterruptible true` frame reaches
   `Prim.ensure` (`Runtime.lean:649-655`), which — because `interruptedCause` is set and the
   flag is `true` — returns the replacement `Prim.failure cause`. **The interrupt is
   delivered at the unmask.** The child unwinds and exits interrupted; its countdown
   observer resumes the parent; the parent's `join` carries the same cause up.
   * Asserted: `isFinished`, and `exitInterrupted` on both ⟨1⟩ and ⟨0⟩.

This is the first thing in the spike that exercises the interrupt half, and it is the
witness `WithFiberAction.setInterruptible` was added for.

### H — a refused `direct` row, on S4's frontier constructor (new, third pass)

`ForkFlow.lean:1600-1621`. Four assertions plus an end-to-end run, because this is the
channel the third pass moved:

* `compileForkAt … refusedJoinPoint = Prim.suspend refusedJoinPoint` — a refused `join`
  compiles to S4's frontier constructor, not to a failure;
* `isFailure (compileForkAt … refusedJoinPoint) = false` — the instance of
  `compileFork_not_failure` at the arm that used to break it;
* `forkTable.suspendBody refusedJoinPoint = Prim.failure (Cause.die ())` — the interp raises
  the defect at that point;
* end to end on a hand-built machine: the fiber exits `Exit.failure (Cause.die ())` and
  `stuckOf = none`. A refused `direct` row **dies**; it does not suspend for ever, which is
  the thing to check when a refusal moves onto a frontier constructor.

A fifth receipt pins P3's shape at the profile arm: a caught `join` compiles to
`onSuccessAndFailure (sync point) (RegionName.cont point) (RegionName.caught point)`.

### G — the stranded join halts (replaces the first pass's spin witness)

`ForkFlow.lean:1656-1694`. `forkParkOf` classifies a handle naming fiber `99` as
`ParkKind.join ⟨99⟩ joinEffect`; one `iteration` on a machine that does not hold ⟨99⟩ now
returns `Outcome.stuck (Stuck.unknownFiber ⟨99⟩)`, and a whole `replayEval` reports
`ReplayResult.stuck (Stuck.unknownFiber ⟨99⟩)` rather than exhausting fuel in silence.

---

## 5. What `Fibers.lean` lacks or gets wrong — both first-pass findings closed

### 5.1 `join` on an unheld fiber — **closed**

*First pass:* the arm returned the fiber **unchanged** with `Outcome.continue_`, and
`drive`'s `Cmd.loop` re-enqueued `Cmd.loop id it.yielding` on that same unchanged fiber, so
the iteration repeated identically until `drive`'s fuel was gone with nothing in the trace.
A silent spin, not a live frontier. The exact change asked for was to make the state
observable.

*Now:* `Fibers.lean:731` answers `Outcome.stuck (Stuck.unknownFiber target)`; `drive`
halts on it and records the reason (`:1050-1051`), refuses to run further commands
(`:1022`), and `replayEval` reports `ReplayResult.stuck why m` (`:1151-1158`). The carrier
went further than the repair this spike proposed — a dedicated `Stuck` alphabet
(`:326-331`) rather than a `notImplemented` defect — which is the better answer, because a
defect would have been indistinguishable from a program that legitimately dies.

*Witnessed here:* `strandedJoinOutcome` and the `replayEval` `#guard`
(`ForkFlow.lean:1681-1694`).

The justifying line stands: rc.112 cannot reach the state, because `fiberJoin` (`:5291`)
and `fiberAwait` (`:5304`) take a `Fiber` *object* that holds its own exit. In the Lean
machine a handle is a `Val` and `handleOf` decodes any well-shaped one, so the arm **is**
reachable, and DB-04 (`docs/DESIGN-BASIS.md:154`) requires a state the machine cannot leave
to be an observable frontier.

### 5.2 `WithFiberAction` had no refusal arm — **closed**

*First pass:* `withFiberOf` returning `none` fell through to `stepFrame`, and
`FrameFiber.step` on `Prim.withFiber` sets `current := interp.suspendBody thunk`
(`Runtime.lean:1672-1673`), which in the `regionInterp` of the day was
`Prim.failure Cause.empty` — the **empty** cause, then the compile's own frontier marker. A
refusal was therefore indistinguishable from a compile-time frontier, and the spike had to
put every refusal in the compile as a workaround. (S4's P2 has since replaced that
`suspendBody` with `regionSuspendBody`, a real live suspension, so the same fall-through
would today be a silent *frontier* rather than a silent failure — different symptom, same
defect: a refusal with no channel.)

*Now:* `WithFiberAction.refuse (cause)` exists (`Fibers.lean:295-296`) and `iteration`
answers it by failing the fiber with that cause (`:896-898`). The spike routes nine of the
twelve rows' refusals through it (§3), and witness E pins the path.

*The other three, resolved in the third pass:* `join`, `await` and `yieldNow` compile to
primitives the machine reads without consulting an interp function that could carry a
cause — `parkOf : Prim → Option ParkKind` in particular has no refusal channel, so a
malformed handle would otherwise be answered from the oracle as if the join had succeeded.
The second pass raised those three in the compile as `Prim.failure (Cause.die ())`; S4's P2
made that the one shape a compile must not emit. They now compile to `Prim.suspend point`
and `forkTable.suspendBody` raises the defect there, so **every** row's refusal is the
interp's, `compileFork_not_failure` holds, and witness H pins the path end to end. The
carrier request below is therefore now a tidiness item rather than a gap: if the landing
wants one *field* rather than one *place*, the minimal change is
`parkOf : Prim ν σ β ε δ ι α → Option (Except (Cause ε δ ι α) ParkKind)` — one field's type,
one arm of `iteration` — and this report records it as the only carrier request S3 still
has.

### 5.3 Three notes that need no change

* **`ι := Unit` loses the interruptor.** `RunInterp.encodeFiber : FiberId → ι` cannot carry
  an id when `ι = Unit`, which is `RegionSimulation`'s carrier
  (`RegionSimulation.lean:175-178`), not `Fibers.lean`'s. Witness F now *depends* on this
  being harmless: it asserts `Cause.hasInterrupts`, which is true whatever `ι` is, rather
  than the interruptor's identity. The landing must instantiate `ι` at a fiber-id carrier
  before any `interrupt.*` clause is claimed over a compiled flow, and witness F is the
  test that would then sharpen from "an interrupt" to "an interrupt by ⟨0⟩".
* **`exitValue` is a `RunInterp` field, and that is right.** The `join`/`await` distinction
  is a *profile* fact, carried on the observer as `Supervision.ObserverMode`.
* **`budgetOf ctx = (0, true)`** turns yield injection off wholesale (`Fibers.lean:690`), so
  witness F's parks are the program's own `yieldNow` and not an injected one. That is the
  right knob for a witness, and the same knob `E4-SEM-CE-011` says the host cannot hold
  stable at rc.112's yield floor.

---

## 6. What `RegionSimulation.lean` needs at the landing

**Two edits now, both additive, in one module.** The first pass listed four and the second
three; S4 landed two of them upstream on its own account.

1. **`compileRegion`'s `perform`/`performCatch` arm** (`RegionSimulation.lean:612-618`) gains
   the profile branch. Transplant `compileFork.performShape` (`ForkFlow.lean:620-634`) and
   give `compileRegion` the extra parameter `opOf : alphabet.Op → Option FiberOp`.
   `compileFork_eq_compileRegion` is the theorem that says this changes no existing program
   when `opOf` is constantly `none`, so the default instantiation keeps every receipt —
   including S4's five T5/T6 instances and its `RegionOracleAgrees` obligation, none of which
   this arm touches.
2. **`regionInterp`'s `suspendBody`** (`:924`) gains the refusal guard: today it is
   `regionSuspendBody alphabet flow oracle`, and a refused `direct` row needs it to answer
   `Prim.failure (Cause.die ())` first. `forkTable.suspendBody` (`ForkFlow.lean:838-841`) is
   the replacement, three lines. Nothing else in `regionInterp` moves: its **`contA`** and
   **`contE`** already call `compileRegion`, which is the function that gains the arm, so
   when the arm lands the two are the same functions again.

Already landed upstream, and no longer this spike's ask:

* **`cancelThenFail`** (`:878`, spike S1) — a record update inherits it.
* **`contE` routing a caught failure** (`:906-918`, S4's P3). The second pass listed this as
  edit 2 and hand-rolled it; S4 implemented it, with a dedicated `RegionName.caught`
  constructor rather than reusing `cont`, which is the better shape.
* **`finalizerExit` constantly `Exit.success ()`** (`:923`, S4's P1) and the one-frame-per-region
  `enter` arm, which this spike now simply carries.

Unchanged and reused verbatim: `regionBound` (`:1022`) stays the per-fiber bound, with the
machine bound a sum over live fibers (§7.3); `RegionOracle` — **including S4's new
`registrations` field** — and `statelessOracle` need nothing, because `forkOracle` wraps the
answer function and not the oracle; and `Config`, `RegionName`, `Err`, `Res`, `Cleanup`,
`Code`, `Machine`, `Table`, `traceOfRun`, `finalizerAndOutcomeMask`, `performOp`,
`performCont`, `catchCont`, `releaseOp`, `closeExit`, `isFailure`, `regionSuspendBody`,
`compileRegion_not_failure`, `causeOfFailures` and `failuresOfCause` are all used as they
stand.

**A note the landing should carry.** S4's open obligation is
`RegionOracleAgrees.registrations` — `closeWalk` agrees with `compileRegion` but not with the
runner when a region body consumes decision tape (`tapeAfterRegion_diverges`). The fork
profile does not make that worse and does not help it: a forked child is compiled at the
*fork's* configuration, and its tape is the parent's tape at that point, so the same
`leaveConfig` question would be asked of a forked region body. Whichever of S4's two options
the coordinator takes, the fork arm inherits it unchanged.

---

## 7. The obligations, and every `sorry`

**There is no `sorry` in `workshop/Deep/ForkFlow.lean`.** What is owed is stated as a
`Prop`-valued definition — a real Lean statement with no proof and no assumption.

### 7.1 `WellSourced`, ruling 6 / finding 12 — proved on `current`, and on the whole configuration for the fork arm

`WellSourced alphabet flow opOf program := ∃ point, program = compileForkAt alphabet flow opOf point`
(`ForkFlow.lean:1015-1017`).

**Proved:** `wellSourced_actions` (`:1041-1161`) — for every `withFiber` action
`forkWithFiberOf` returns, every program the action carries is `WellSourced`. That now
covers `fork`, `forkIn`, `forkScoped`, **`setInterruptible`'s masked body** and every
`raceAll` entrant; `actionPrograms` (`:1027-1034`) is the projection, and the other twelve
`WithFiberAction` constructors — `refuse` included — carry no program, so the statement is
exhaustive. `wellSourced_fork` (`:1163-1170`) is the ruling-6 wording as a corollary.

It is provable because finding 2's cost (c) is discharged: the request carries a **block
reference**, so the child's program is *computed* by the same `compileFork` from data the
flow already owns. DB-05's conditional (`docs/DESIGN-BASIS.md:216-219`) is satisfied by the
block reference, and the defunctionalization is discharged by the machine.

**New this pass, at the coordinator's request (c):** the invariant is restated over the
fiber's **whole configuration**, as the first pass recommended.
`ConfigWellSourced` (`:1182-1188`) says `current` is sourced *and every frame on the stack
is*, and its **fork arm is proved**:

* `configWellSourced_make` (`:1191-1201`) — a fiber the machine creates over a sourced
  program is sourced in its whole configuration, because `RunFiber.make` builds its frame
  with `FrameFiber.start`, whose stack is empty. `spawn` (`Fibers.lean:616-634`) builds its
  child by exactly this call.
* `configWellSourced_forkChild` (`:1203-1215`) — the same at the fork itself, composing with
  `wellSourced_fork`.

**Still owed:** `WellSourcedClosed` (`:1217-1223`), now stated over `ConfigWellSourced`:

```lean
∀ fuel before decision,
  (∀ f ∈ before.fibers, f.exit.isNone → ConfigWellSourced … f) →
    ∀ f ∈ (stepDecision interp fuel before decision).fibers, f.exit.isNone →
      ConfigWellSourced … f
```

What still blocks the general case, now that the stack is in the statement: the machine's
`current` between a resume and a `contA` is a `Prim.success value` or a `Prim.failure
cause`, which is not a compile image, and the stack acquires the machine's own bookkeeping
frames — `Prim.setInterruptible true` pushed by `uninterruptible`
(`Runtime.lean:2823-2829`), `Prim.asyncFinalizer` pushed by an `async` park
(`Fibers.lean:720-724`). The landing must widen `WellSourced` on both sides: an inductive
`Sourced` closing the compile's image under `success`/`failure` for `current`, and under
the two bookkeeping frames for the stack. That is a mechanical widening, not a design
question, and the fork arm above is the base case it will be proved from. It is the same
shape `docs/FRAMES-DAG.md:120-132` separation 1 asks for.

### 7.2 The decision partition, ruling 7 / finding 13 — **proved**

`SitesSeparated` (`ForkFlow.lean:1260-1270`) with three clauses, and `sitesSeparated_holds`
(`:1272-1280`) proves all three from `Effect4.Flow.sitesSeparated flow = true`:

* `chooseBelowBase` — `choose_site_lt_base` (`:1249-1258`) reads it off
  `Effect4/Flow/Interrupt.lean:117-122`;
* `interruptAtOrAboveBase` — `Effect4.Flow.Point.site_ge` (`Interrupt.lean:81-82`);
* `runDecisionNamesNoSite` — `runDecisionSite` is constantly `none` (`:1243-1247`), because
  `RunDecision`'s five constructors carry fiber ids, tokens, primitives, **annotations** and
  booleans (`Fibers.lean:358-376`) and no `DecisionId`. The carrier's change to
  `interruptFrom`, which gained a `ReasonAnnotations α`, did not touch this: an annotation
  map is not a site.

`interrupt_ne_choose` (`:1282-1289`) is the corollary: a Flow interrupt site and a Flow
`choose` site are never the same site, and no `RunDecision` names either.

### 7.3 The fuel bound, finding 3 — **stated, not proved**

`ForkFuelBound` (`ForkFlow.lean:1313-1322`), now hypothesised over `ConfigWellSourced`:

```lean
∀ machine tape fuel,
  (∀ f ∈ machine.fibers, f.exit.isNone → ConfigWellSourced … f) →
    (machine.fibers.filter (·.exit.isNone)).length * (regionBound (runnerFuel flow []) + 2) ≤ fuel →
      ∃ after, replayEval interp fuel tape machine = ReplayResult.finished after
```

Read: the machine's fuel is a **sum over live fibers** of the per-fiber bound
(`regionBound (regionFuelFor flow tape)`), plus a constant two commands per fiber for its
start and its resume. The per-fiber factor is `regionBound` (`RegionSimulation.lean:440`,
`4 * runnerFuel + 1`) over `regionFuelFor` (`Effect4/Semantics/Approximation.lean:2139`,
`2143`). `runnerFuel` (`ForkFlow.lean:1303-1305`) is that function's arithmetic spelling,
written out so this spike keeps the plan's S3 import list; at the landing it is the imported
function and this `def` goes.

Two things the landing must add to make it provable. First, the number of live fibers must
be bounded by the tape — finding 3's amendment, that *starting* a fork is a machine decision
and never a term field, which this spike honours (`startImmediately := false` always;
witnesses A and F both need an explicit `fire` before any child runs). Second, the
conclusion has to admit `ReplayResult.stuck` as a legitimate end, or the hypothesis has to
exclude it: a stuck machine finishes in bounded fuel but is not `finished`. Witness G is
exactly such a machine.

---

## 8. What the operation route cannot express, and what the terminator route would cost

Nothing in this spike was deferred. Three things the operation route genuinely cannot do,
each with the terminator route's price beside it.

### 8.1 The flow has one `resultTy`, so every declared root returns the same type

`Effects/Flow/Admission.lean:895-896`: a `ret`'s value type must equal `raw.resultTy`. A
`RegionFlow` carries one `resultTy` (`Effects/Flow/Region.lean:88`), so **every** declared
root of a flow — the entry, every fork target, and every masked body — returns that one
type, and the profile's `join`, `raceAll` and two mask rows all answer the flow's
`resultTy`. Witness C had to give its child root the `Result.Result<number, number>`
spelling for exactly this reason, and witness F had to route its fork request through a
service row so that its entry could take a number while its fork target took a root
reference.

**Terminator route's price for this: none, and none for the operation route either.** A Flow
v4 fork *terminator*'s body would be a block of the same flow, so it inherits the same
`resultTy`. Fixing it is a `RawFlow` change (a per-root result type, i.e.
`roots : List (BlockId × Ty)`), a carrier change in the pinned `effects` package on
**either** route. Recorded because it is a real limit on what a forking flow can express and
no review finding names it.

### 8.2 A caught `join` needs P3's `onSuccessAndFailure` — **now upstream**

`join`'s failure arrives as a machine-level `Prim.failure` on the resume, not as an oracle
`.error`. Before S4, `compileRegion`'s `performCatch` arm emitted `onSuccess`, whose frame
has no `contE`, so the child's cause would have unwound straight past the catch; the first
two passes emitted `onSuccessAndFailure … (cont point) (cont point)` and hand-rolled the
routing in `forkTable.contE`.

**S4 implemented P3 upstream**, and better: a caught operation compiles to
`onSuccessAndFailure … (RegionName.cont point) (RegionName.caught point)` with a dedicated
cause constructor, and `regionInterp.contE` reads the error off the cause. The third pass
deleted its `firstError` helper and adopted that shape. What remains this spike's is
`catchesMachineFailure` (`ForkFlow.lean:573-580`): *which* profile rows need the failure arm
at all — `join`, `raceAll` and the two mask rows, whose failure is machine-level rather than
an oracle `.error`. Every non-profile `performCatch` is `compileRegion`'s, by delegation,
which is what `compileFork_eq_compileRegion` proves. **Witness D** is the behavioural
receipt and the `caught`-shape `#guard` at `:1631-1636` is the syntactic one.

**Terminator route's price: identical.**

### 8.3 The three losses the review named, confirmed

* **(a) The named root is not a graph successor.** Confirmed: the five witness flows are
  admitted with the fork target invisible to `danglingSuccessor`, `reachSet` and
  `CyclesWF`, and the check is a *run-time* refusal. Terminator route: the target becomes a
  graph successor, and `CyclesWF` then refuses a supervisor loop that forks — the exact
  program Effect users write (finding 3's consequence), so the term route trades one loss
  for a worse one unless `CyclesWF` changes too.
* **(b) The lowering emits a service call.** Confirmed and priced in
  `workshop/Deep/fork-lowering.md` §(d), with the refusal row's text. Terminator route: a
  new nested-generator former in `TypeScript.Stmt`
  (`.lake/packages/typescript/TypeScript/Syntax.lean:106,129,133` has only `scopedGen` and
  `scopedGenMasked`), i.e. a bump of the pinned `typescript` package, plus a `Skeleton`
  constructor, a `Rule` tag and a ledger row.
* **(c) The defunctionalization moves from admission to the machine.** Confirmed and
  **discharged**: `wellSourced_actions` is that proof, and `configWellSourced_forkChild`
  carries it to the child's whole configuration.

### 8.4 The terminator route's full price, for the record

From review finding 2 (`deep-plan-review.md:80-101`), unchanged by anything this spike
found: a new `RegionTerm` constructor breaks **28** exhaustive matches in `Effect4/` and
**9** upstream (counting the `.leave` arm; 21 and 7 counting `.plain`); a new `RawTerm`
constructor breaks ~15 and ~16. `RegionClause` gains clauses and `regionWF_iff_check`
(`Effects/Flow/Region.lean:571-629`) is re-proved. `ScopeName` gains a fifth constructor and
`runRegions_eq_interpret`, `RegionTotal`, `RegionSafety` and the region half of
`Approximation` are all re-proved. Both pinned packages bump.

Against that, this spike's total cost to `Effect4/` is: **one arm of `compileRegion`, one
field of `regionInterp` (`contE`), and one lowering former pair plus one appended `Rule`
tag.** That is the answer to plan decision 11.

---

## 9. The one carrier request S3 still has — now optional

`RunInterp.parkOf : Prim ν σ β ε δ ι α → Option ParkKind` cannot carry a refusal, so the
three `direct` profile rows (`join`, `await`, `yieldNow`) raise theirs through
`suspendBody` rather than through `WithFiberAction.refuse` (§5.2). After the third pass that
is a **tidiness item, not a gap**: the refusal is raised by the interp on all twelve rows,
it is a defect that a `performCatch` cannot catch, it is witnessed end to end (witness H),
and `compileFork_not_failure` holds. Two channels rather than one is the only cost.

If the landing wants one *field* as well as one *place*, the minimal change is

```lean
  parkOf : Prim ν σ β ε δ ι α → Option (Except (Cause ε δ ι α) ParkKind)
```

with `iteration`'s `parkOf` arm answering `.error cause` by
`{ f.frame with current := Prim.failure cause }` and `Outcome.continue_`. One field's type,
one arm. `compileRefusal?` (`ForkFlow.lean:522-527`) already computes the refusal and
`FiberOp.direct` (`:199-204`) names exactly the rows that need it, so the migration is
mechanical and `forkTable.suspendBody` would go back to being `regionSuspendBody`.

Everything else this spike asked the carrier for has landed, from spikes S1 and S4 both.

---

## 10. Files

| File | What |
| --- | --- |
| `workshop/Deep/ForkFlow.lean` | the spike; `lake build Deep.ForkFlow` green |
| `workshop/Deep/fork-lowering.md` | the emitted TypeScript per row, the one lowering change, the host service sketch, the refusal row |
| `docs/research/2026-09-03-spike-s3-fork-flow.md` | this report |




