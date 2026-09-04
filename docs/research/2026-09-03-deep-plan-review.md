# Adversarial review of the deep plan, 2026-09-03

Reviewer's remit: find every place where executing
`docs/research/2026-09-03-deep-plan.md` as written would force a carrier change
or a redesign before full reification of Effect v4 and checked lowering are
reached, and name the minimal amendment. Read at HEAD `6d83533`, clean tree.
Two shape claims were checked by elaboration (§What I checked by elaborating).

## Verdict

**Not on the path as written, because of two structural omissions and one
internal contradiction — but all three are repairable by amendment, not by
redesign.** The plan's destination is right and its packet decomposition is
mostly sound; what is missing is that (1) no packet gives `Flow` a way to name
a concurrent child, so R2 would run `Prim` programs that no `Flow` denotes and
the lowering could never emit `Effect.fork` — the plan lists twelve `fork.*`
rows as "statable" at R2 (`docs/research/2026-09-03-deep-plan.md:110`) with no
carrier that can state them; (2) R1's fence says
"`Runtime.lean` untouched" (`:109`) while `docs/FRAMES-DAG.md:200-211` requires
that exact packet to revisit `popFrom`, and `popFrom` is a recursion over
`List (Prim …)` (`Effect4/Runtime/Runtime.lean:1154-1155`) — the three park
primitives cannot be added without either a fifteenth `Prim` constructor or a
second copy of the whole frame vocabulary; and (3) plan ruling 3 refuses a state
slot while plan packet M4 adds a `context` field to the same frozen record
(`:41` versus `:100`), a contradiction inherited unnoticed from the two research
notes. None of these forces a *new* carrier — the fork can be an alphabet
operation with no change to `RawTerm`/`RegionTerm` at all, the state slot can be
a `RunInterp extends PrimInterp` beside the frozen one (checked: it elaborates
and `Prim`/`FrameFiber` keep `DecidableEq`), and the frames contract can be
re-frozen once at R1 instead of twice. Two further items are decisions the plan
records as settled but are not: retiring `Race.lean` abandons an eight-edge open
proof graph and four register rows, and ruling 2 has no end state, so twelve
`fork.*` rows would keep two owners indefinitely.

---

## Findings, by severity

### 1. Flow cannot name a concurrent child, and no packet in the plan gives it one

**Claim.** Plan packet R2 (`deep-plan.md:110`) promises a program-carrying
multi-fiber machine with "fork variants" and twelve `fork.*` census rows
"statable". Nothing in the plan gives `Flow` a fork, so the `Prim` programs R2
steps are outside the image of every compile, and the lowering has nothing to
emit `Effect.fork` from.

**Evidence.**
- `Effects/Flow/Block.lean:96-116` — `RawTerm` is exactly `ret`, `jump`,
  `perform`, `choose`, `performCatch`, `branch`.
- `Effects/Flow/Region.lean:52-63` — `RegionTerm` is exactly `plain`, `enter`,
  `acquire`, `leave`. No constructor carries a child `BlockId` to run
  concurrently.
- `Effect4/Concurrency/FiberFamily.lean:96-99` — `fork (body : Nat)`; the child
  is a *number*, and `:122-127` `bodyOutcome : Nat → Option (Except Nat Nat)` is
  a four-row hard-coded table.
- `Effect4/Concurrency/FiberFamily.lean:13-20` — "nothing in the Lean tree can
  step two fibers against each other."
- `harness/trace/Generate.lean:584-592` — the repository's own words: "`Fibers`
  has no former for a child that performs operations of its own (its bodies are
  numbers)."
- `docs/TRACE-DAG.md:63` — "Closing this row needs a two-fiber model — a new
  model, not an extension of `Machine`."

**Carrier change or additive.** Forces a carrier change *somewhere*; §2 shows
the cheapest place is the alphabet, where it is additive.

**Minimal amendment.** Insert packet **X1** before R2 (see §2 for which of the
two routes). Add it to §3 "The machine" and to the wave table; R2's
prerequisites gain `X1`.

**Packet.** New X1; R2 depends on it.

### 2. Term versus operation: the cost comparison the plan must make, and the answer

**Claim.** The term route (a Flow v4 `fork` terminator, DB-05-shaped) is
correct and expensive; the operation route (a `fork` operation of the *supplied
alphabet*, whose request value names a declared root) is correct, cheap, and
loses exactly three things that can be named as refusals.

**Evidence — the term route's price.**
- A new `RegionTerm` constructor breaks **21** exhaustive `RegionTerm` matches
  across nine `Effect4/` modules (`Interrupt.lean`, `Region.lean`,
  `Approximation.lean`, `RegionDenotation.lean`, `RegionSafety.lean`,
  `RegionSimulation.lean`, `RegionTotal.lean`, `RegionLower.lean`,
  `StructuredLower.lean`) plus **7** in the pinned `effects` package's own
  `Effects/Flow/Region.lean`; counted by the `.plain` arm. Counting the `.leave`
  arm instead gives 28 in `Effect4/` and 9 upstream. A new `RawTerm`
  constructor breaks ~15 in `Effect4/` and ~16 upstream.
- Admission: `RegionClause` has fourteen clauses (`Effects/Flow/Region.lean:127-158`)
  and `RegionWF` fourteen fields (`:399-414`); a fork body needs at least its own
  label and typing clauses, so `regionWF_iff_check` (`:571-629`) is re-proved.
- Denotation: `ScopeName` has four constructors (`Effect4/Semantics/RegionDenotation.lean:109-118`)
  and `ScopeSig` (`:144`) is what D2's `runRegions_eq_interpret`, `RegionTotal`,
  `RegionSafety` and the region half of `Approximation` are stated over. A fifth
  name re-proves all four (`docs/TRACE-DAG.md:51`, `:58`).
- Lowering: `TypeScript.Stmt` has `scopedGen` and `scopedGenMasked` and nothing
  else nested-generator-shaped
  (`.lake/packages/typescript/TypeScript/Syntax.lean:106,129,133`). Emitting
  `Effect.fork(Effect.gen(function*(){…}))` needs a new former, i.e. a bump of
  the pinned `typescript` package (`docs/ARCHITECTURE.md:21-27`), plus a
  `Skeleton` constructor, a `Rule` tag and a ledger row.

**Evidence — the operation route's price.**
- The alphabet is a *parameter*: `FlowAlphabet` carries `Op`, `requestTy`,
  `answerTy`, `errorTy` (`Effects/Flow/Block.lean:66-92`). A `fork` operation
  whose request is a block-name code and whose answer is a fiber handle changes
  **no** constructor, **no** admission clause, **no** denotation summand, and
  **no** exhaustive match. `Flow.denote` stays the sequential face for free —
  a fork is an ordinary `perform` answering a handle.
- Cost (a): the named block is inside a *request value*, so
  `danglingSuccessor`, `reachSet` and `CyclesWF` never see it. The child body
  must therefore be a declared **root** (`RawFlow.roots`, already checked by
  `danglingRoot`/`entryNotRoot`/`nonCanonicalRootOrder`), and "the request names
  a declared root" is a **run-time** refusal, not an admission clause — a
  strictly weaker guarantee that must be recorded.
- Cost (b): the lowering emits a *service call*, `const f = yield* fibers.fork(n)`
  (`Effect4/Target/TypeScript/Skeleton.lean:186-187`,
  `SkeletonRender.lean:96-97`), never `Effect.fork`. The reification claim must
  carry a P7-shaped refusal saying so.
- Cost (c): DB-05's conditional (`docs/DESIGN-BASIS.md:216-219`) — "If a future
  public operation stores an actual subcomputation rather than a stable block
  reference, its breaker packet must either prove an adequate
  defunctionalization or introduce a separately justified higher-order
  calculus" — is satisfied by the block reference, but the *defunctionalization*
  ("interpreted through the same defunctionalization used by every other block",
  `:206-208`) now has to be discharged by the machine rather than by admission.

**Carrier change or additive.** Operation route: additive. Term route: carrier
change in two pinned packages plus 28+9 match sites.

**Minimal amendment.** Take the operation route for X1/R2/R3. Schedule the term
route as a separate, later packet whose *only* justification is emitting
`Effect.fork` — and price it there, with the `typescript` bump named. Add both
to §5 as decision 11.

**Packet.** X1 (operation), and a later X2 (term) if and when the lowering must
emit `Effect.fork`.

### 3. The tape bound is per-fiber; a fork makes the number of live fibers unbounded

**Claim.** Admission's fuel argument bounds one control walk. With `k` fibers
the machine performs `k` walks, and a fork inside a loop makes `k` unbounded on
a fixed tape, so R2 has no termination measure.

**Evidence.**
- `Effect4/Semantics/Fuel.lean:166` — `LoopBudget.covers`:
  `(tape.length + 1) * raw.blocks.length + 1 ≤ fuel + visited.length`. This is
  one walk.
- `Effect4/Semantics/RegionSimulation.lean:437` — `regionBound runnerFuel =
  4 * runnerFuel + 1`, one fiber's worth.
- `Effects/Flow/Admission.lean:368-375` — `unchosenCycle` forbids a cycle of
  non-`choose` edges, which is what buys `LoopBudget.segment_lt`.
- Consequence, either way round: if a fork body edge is a *graph successor*,
  `CyclesWF` refuses a supervisor loop that forks — the exact program Effect
  users write. If it is not a successor (the operation route), nothing bounds
  the number of children.

**Carrier change or additive.** Additive under the operation route; a
`CyclesWF` change under the term route.

**Minimal amendment.** Make *starting* a fork a machine decision
(`RunDecision.fireDispatcher`/`flush`), never a term field, so the machine tape
bounds the number of live fibers exactly as the Flow tape bounds `choose`; state
the machine bound as a sum over live fibers and freeze it in R2's contract. This
is also DB-03-correct: scheduling is a decision kind
(`docs/DESIGN-BASIS.md:134-138`).

**Packet.** R2 breaker (the alphabet freeze), stated in `docs/FIBER-MACHINE-DAG.md`.

### 4. The state slot: the author's fix works, ruling 3 as worded blocks it, and it changes `Deferred.await`'s disposition

**Claim.** A `RunInterp` extending `PrimInterp` with a service-state slot is
sound and cheap; `Prim`, `FrameFiber` and their `DecidableEq` are untouched.
Plan ruling 3 (`deep-plan.md:41`) and decision 8 (`:175`) as worded ("no state
slot in `PrimInterp`") are compatible with it, but the plan never says so, so a
builder reading ruling 3 will conclude the machine must stay pure.

**Evidence (checked by elaboration, exit 0).**
```lean
structure RunInterp (St : Type u) (ν σ : Type u) (β : Type v) (ε δ ι α : Type u) :
    Type (max u v) extends PrimInterp ν σ β ε δ ι α where
  syncState   : σ → St → St × β
  asyncResume : σ → St → St × Option (Exit β ε δ ι α)
```
elaborates against the built library; `DecidableEq (Prim …)` and
`DecidableEq (FrameFiber …)` still `inferInstance`; and
`statelessRun interp` (`syncState := fun t st => (st, interp.syncValue t)`)
makes the pure case a `rfl` corollary. The oracle form (`answersOf`,
`Effect4/Semantics/FrameSimulation.lean:183`; `RegionOracle`,
`RegionSimulation.lean:222-226`) is then a corollary, exactly as the author
proposes.

**The limit the amendment must name.** `finalizerExit` and `contA` are consumed
*inside* `armA`/`armE` (`Effect4/Runtime/Runtime.lean:718-770`), which are
frozen. A release that writes a Ref, or a continuation that reads one, cannot be
stateful without re-stating `armA`/`armE` at `RunInterp`. So "reuse `armA`/`armE`
verbatim" is true only while finalizers and continuations are pure; the moment
the stores are real, R1/R2 re-state them.

**`Deferred.await` and `op.Async`.** With a store-driven `asyncResume`,
`await` is a machine-level park on a store key resumed by the Deferred store,
and needs **no** `op.Async`. Plan premise 5 (`deep-plan.md:57`) and M2's row
column (`:98`) are wrong under this design. `layer.launch-holds-scope` (rc.112
`never` = `Effect.callback`) genuinely does need `op.Async` and stays partial.

**DB-07.** `docs/DESIGN-BASIS.md:249-275` requires state produced before failure
to survive. `RunMachine.step` must therefore thread `St` *out* on the failure
arm — never restore it — and R2 owes the lemma "`St` after `resumeCause` is the
`St` the failing fiber had reached", the machine-level counterpart of
`EStateM.run_throw`.

**Cleaner alternatives, assessed.** Stores-as-fibers: rejected — rc.112 does not
do it, and it would put a `Prim` inside a Ref cell, making the heap a program
carrier. Stores as a handler summand in the algebra: this is what D2 already
does for `Scope` (`ScopeSig`, `RegionDenotation.lean:144`) and it works for the
*denotation*; it does not work for the machine, because `PrimInterp` has nowhere
to put a monad (`RegionSimulation.lean:212-217`). `RunInterp` is the right
answer.

**Carrier change or additive.** Additive. No change to `Prim`, `FrameFiber`,
`PrimInterp` or the 28 frames census rows.

**Minimal amendment.** Rewrite ruling 3 and decision 8 (see §Amendments).

**Packet.** R1 declares `RunInterp` and `statelessRun`; M1/M2/M3 supply the
components of `St`; R2 consumes it.

### 5. R1 cannot leave `Runtime.lean` untouched and reuse `popFrom`

**Claim.** The two halves of R1's fence contradict each other.

**Evidence.**
- `deep-plan.md:109` — R1's fence: "new `Effect4/Runtime/RunLoop.lean`, …;
  `Runtime.lean` untouched", and it inherits "the `popFrom` agreement obligation
  of `docs/FRAMES-DAG.md`".
- `docs/FRAMES-DAG.md:200-211` — "The first frame that is that shape is
  `AsyncFinalizer` … The later run-loop and parking packet that adds it **must**
  revisit `popFrom` and either prove the fusion still agrees or unfuse the
  loops."
- `Effect4/Runtime/Runtime.lean:1154-1155` — `popFrom (demand) (skip) :
  List (Prim ν σ β ε δ ι α) → FrameFiber … → FramePop …`; `:225` —
  `stack : List (Prim …)`; `:408`, `:558`, `:589`, `:718`, `:750` — `arms`,
  `ensure`, `answerOf`, `armA`, `armE` all `match` on `Prim`.
- So an `asyncFinalizer` frame is either a fifteenth `Prim` constructor —
  breaking `Prim.cases_receipt` (`:129-173`), **14** exhaustive `Prim` matches
  in `Runtime.lean`, 2 in `Effect4Test/Counterexamples/Runtime/Frames.lean`, and
  the frozen `test/contracts/frames.contract.md` — or the whole frame vocabulary
  (`ContAnswer`, `FramePop`, `FrameEvent`, `ensure`, `answerOf`, `armA`, `armE`,
  `popFrom`, `getCont`) is re-declared at `RunPrim`, in which case the 28 frames
  census rows are witnessed over a carrier the run loop never steps.

**Carrier change or additive.** Carrier change either way; the question is which.

**Minimal amendment.** R1 opens a `test/contracts/frames.contract.md` breaker:
three new `Prim` constructors (`yieldNowWith`, `async`, `asyncFinalizer`),
`Prim.cases_receipt` restated at seventeen, `arms`/`ensure`/`answerOf`/`armA`/
`armE`/`step` extended, and the `popFrom` fusion agreement proved or the loops
unfused. Move plan decision 7 (`:173`) from P6 to R1, so the contract is
re-frozen **once**, at the start of the machine lane, rather than twice.

**Packet.** R1, with a frames breaker; P6 then rides the same freeze.

### 6. M4's `context` field on `FrameFiber` is forbidden by the frozen contract, and `Runtime/Runtime.lean` already has two owners

**Claim.** Plan M4 (`deep-plan.md:100`) proposes "a `context` field or wrapper
on `FrameFiber`". The frozen frames contract forbids both the field and the
import; and the ENVIRONMENT-DAG claims the same file path for a different node.

**Evidence.**
- `test/contracts/frames.contract.md:70-76` — REQUIRES 2: `Effect4/Runtime/Runtime.lean`
  "must not import `Effect4/Concurrency/` … nor `Effect4/Layer/`,
  `Effect4/Channel/`, `Effect4/Context/`, or `Effect4/Runtime/Scope.lean`."
- `:221-232` freezes the five-field `FrameFiber` by `#check` ascription; `:77-84`
  fixes the parameter list to `ν σ β ε δ ι α` with the instance binders named
  exactly.
- `docs/ENVIRONMENT-DAG.md:90` puts node `Runtime/Runtime` at layer L7;
  `:151` gives its fence as `F-RT = Effect4/Runtime/Runtime.lean`; `:29` still
  says "the other thirteen environment, layer, and runtime modules remain empty
  breadth stubs" — while the file is 2549 lines of frame machine frozen by a
  different contract.

**Carrier change or additive.** As written, a re-freeze of `frames.contract.md`
*and* an unresolved fence collision. With the amendment, additive.

**Minimal amendment.** (a) M4 adds **no** field to `FrameFiber`; the context is
an opaque parameter `χ` on `RunFiber`, R2's own carrier, so `Runtime.lean` never
imports `Effect4/Context/`. `scope.scoped` and `scope.acquire-release` then
become R2 rows, not M4 rows — and the plan's M6 (`:102`) must be re-stated over
`RunFiber`. (b) F1 (the records split) also repairs `ENVIRONMENT-DAG.md`'s node
status and renames the L7 node's fence (`Effect4/Runtime/Interpretation.lean`,
say) *before* M4 is dispatched.

**Packet.** M4 (fence change), M6 (restated over `RunFiber`), F1 (DAG repair).

### 7. M4 collapses two ENVIRONMENT-DAG layers into one packet and omits the graph-bearing part

**Claim.** The plan's own §5 decision 9 calls M4 "the one packet here nobody has
scoped"; the scoping it needs already exists and M4 contradicts it.

**Evidence.**
- `docs/ENVIRONMENT-DAG.md:83-84` — `Context/Requirement` and `Context/Service`
  are layer **L1**; `Context/Environment` is layer **L2**, alone.
- `docs/ENVIRONMENT-DAG.md:158-` and `PLAN.md:260-268` — "a layer's contract is
  frozen before that layer is dispatched and is not edited while it is in
  flight", written down because the Schema slice paid for it.
- `PLAN.md:207` — "The graph-bearing part is `Program.UsesOnly`: prove its pure,
  visit, perform, bind-by-union, and weakening laws"; `:208` lists the eleven
  `Context.Environment` theorems and seven counterexample classes.
- `docs/ENVIRONMENT-DAG.md:23-25` — `ENV-KEY-INTERP` is the one open Context
  semantic edge.
- `deep-plan.md:100` — M4 is one packet, one breaker, three modules, "600,
  estimate", and mentions none of `Program.UsesOnly`, `ENV-PG-CONTEXT`,
  `ENV-KEY-INTERP` or the counterexample classes.

**Carrier change or additive.** Additive, but as written it repeats the exact
process failure `PLAN.md:260-268` records.

**Minimal amendment.** Split M4 into **M4a** (`Requirement` + `Service`, L1, one
frozen contract, `Program.UsesOnly` and its five laws, `ENV-KEY-INTERP` named)
and **M4b** (`Environment`, L2, `ENV-PG-CONTEXT`, the eleven laws, the seven
counterexample classes). M4b's contract is frozen only after M4a is green.
Dispatch M4a's breaker in wave 0, M4b's in wave 2; M5's five clauses and M6
depend on M4b.

**Packet.** M4a, M4b.

### 8. Retiring `Race.lean` is not "zero frozen-list cost"

**Claim.** Plan ruling 1 and decision 1 (`deep-plan.md:34-36`, `:161`) retire
`Race.lean` on the strength of "zero frozen-list cost". That measurement is
correct for the two lists it was taken over and wrong for the repository.

**Evidence.**
- `docs/RACE-DAG.md:102-115` — `RACE-PG-BINARY-FIRST-COMPLETION` has **eight**
  `required-open` edges (identity, construction, semantics, laws,
  counterexamples, bridges, trust, coverage).
- `PLAN.md:183-189` — broad-sweep item 6, "Frozen / RED … The builder must close
  `RACE-PG-BINARY-FIRST-COMPLETION`"; and `PLAN.md:63` lists "one
  fork/join/interruption lifecycle" among the ten broad-before-deep
  representatives, of which this is the race half.
- `test/counterexamples/REGISTER.md:114-117` — `E4-CONC-CE-008` … `-011`,
  SEEDED, witnessed in `Effect4Test/Counterexamples/Concurrency/RaceRepresentative.lean`.
- `scripts/check-live-stack.mjs:106` and `test/contracts/live-stack.contract.md:246`
  name `Effect4Test.Concurrency.RaceRepresentativeContract` in a frozen
  expected-failure list; `generated/live-stack-assurance.json` is derived from it.
- `scripts/check-race-representative-red.sh` is its own gate.
- `PORT-MANIFEST.md:378` uses "bounded binary first-completion Race" as the
  duplicate-prevention referent for `Effect4.Supervision.RaceAllState`.
- A grep for the module and its types reaches **29** files, not eight.

**Carrier change or additive.** Neither — it is a *ruling* that closes an open
proof graph and a broad-sweep item.

**Minimal amendment.** Either (a) leave `Race.lean` alone — it costs nothing to
keep, and the plan's benefit is 681 lines; or (b) make F6 a ruling packet: a
decision record retiring or re-disposing `RACE-PG-BINARY-FIRST-COMPLETION`, a
`PLAN.md` broad-sweep amendment closing item 6 as superseded by R2, the four
register rows moved with their attack file re-homed onto R2's model,
`live-stack.contract.md` re-frozen through its own breaker, and `PORT-MANIFEST.md`
re-pointed. Recommended: (a) until R2 lands, then (b) as part of R3.

**Packet.** F6, promoted from a deletion to a ruling; or deferred to R3.

### 9. Ruling 2 has no end state, so twelve `fork.*` rows keep two owners

**Claim.** "Keep `Scheduler.lean` and `Supervision.lean` beside the new machine,
with projection lemmas where a projection is cheaper than a re-proof"
(`deep-plan.md:36-38`) is debt only if the end state is written down. Without
it, it is the redesign trap.

**Evidence.**
- `docs/TRACE-DAG.md:63` — the `fibers` row "does not and will not close" at the
  current model; "Closing this row needs a two-fiber model — a new model, not an
  extension of `Machine`."
- The fiber note's projection table is entirely `[inferred]`, none proved, and it
  records that `Machine.WellFormed`'s cleanup clauses and `Supervision.Refusal`'s
  fifteen constructors do **not** project
  (`docs/research/2026-09-03-deep-fiber-runloop.md:565-584`).
- The gates note: twelve `fork.*` rows carry **181** witness references drawn
  from **131** distinct `Effect4.Supervision.*` theorems, and nothing in the gate
  stops a row going `partial → absent`
  (`docs/research/2026-09-03-deep-gates-and-surfaces.md:45-48`, §3.3).

**Carrier change or additive.** Additive, but only if the end state is stated
now.

**Minimal amendment.** Add decision 11 to §5: *after R3, `Scheduler.lean` and
`Supervision.lean` witness no `fork.*` or `interrupt.*` census row; they remain
`separateCalculus` owners of a relational scheduler with its own decision
alphabet. R3 re-disposes their 181 witness references under the
`frozenCoverageStates` guard, with one register row per retired witness family.
Projection lemmas are optional evidence and are never a closure route for a
census row.* Neither module is retired; both stop being coverage owners.

**Packet.** §5 decision 11; executed in R3.

### 10. The lowering path, seam by seam — and what a `Skeleton → Prim` compile buys

**Claim.** Three of the four seams are evidence-only today. A `Skeleton → Prim`
compile is statable and worth adding, but it does not close the seam the plan
implies it closes.

**Evidence, seam by seam.**

| Seam | Status today | Closable in Lean without a carrier change? |
| --- | --- | --- |
| `Flow → Skeleton` | **theorem** for ordinary flows with interrupts off (`skeletonDispatch_denote`, `skeletonStructured_denote_of_fuelFor_le`, `docs/TRACE-DAG.md:65`) | already closed for that fragment; **region nodes and `interruptPoint` have no denotation** (`Effect4/Target/TypeScript/SkeletonSemantics.lean:38-41`), so the region and interrupt rules are evidence-only |
| `Skeleton → Stmt` | **evidence** — "`Skeleton.render` … is a printer … Its faithfulness to Effect v4 generator semantics stays a host receipt, permanently" (`Effect4/Target/TypeScript/Skeleton.lean:36-40`) | only by relating a second `Skeleton` interpretation to it; see below |
| `Stmt → text` | **evidence** — byte identity via `harness/trace/check.sh` and `TypeScript.Render` | no; rendering is where `String` and `Classical.choice` enter (`Skeleton.lean:50-56`) |
| text → rc.112 | **evidence, permanently** — `docs/TRACE-DAG.md:55`, `bridges` `required-open` "by construction" | no |

- A `Skeleton → Prim` compile **is** statable — `compileSkeleton (skeletonDispatch flow) = compileAt alphabet flow` — turning "the lowering's `Prim` equals the flow's `Prim`" into a theorem and leaving rc.112's `Iterator`, service lookup and runtime as the only evidence.
- It does **not** need `Prim.iterator`: `Effect4/Runtime/Runtime.lean:1091-1106`
  `iterator_folds_inline` proves the arm depends only on the outcome that stopped
  the generator, so a generator that only `yield*`s effects is transparent.
- It does **not** close the render seam. `SkeletonRender.lean:104-134` is where
  `Effect.result`, `decisions.report`, `interrupts.point`, `Effect.scoped` /
  `Effect.onExit` (`scopedGen`) and `Effect.acquireRelease` are *chosen*. A
  `Skeleton → Prim` compile is a *second* choice of the same thing; the two are
  related only by a theorem someone must state, or the seam moves rather than
  closes.

**Carrier change or additive.** Additive — a new module
`Effect4/Target/TypeScript/SkeletonPrim.lean`.

**Minimal amendment.** Add packet **P8** after P4: the `Skeleton → Prim` compile
and its agreement with `compileAt`, plus a register row naming the render seam
it does not close. Add a line to §6 saying the render choice remains a receipt.

**Packet.** P8 (new), §6.

### 11. DB-09 item 1 has no Lean subject, and the plan neither creates one nor rules it out

**Claim.** "lowering preserves the admitted Effect4 typing judgment"
(`docs/DESIGN-BASIS.md:326`) is the one DB-09 claim with nothing on the Lean side.

**Evidence.**
- `Effect4/Target/TypeScript/Type.lean` and `Decode.lean` are six-line breadth
  stubs.
- The only typed artefact is `Effect4.Target.EffectV4.Spelling` / the answer
  profile (`docs/TRACE-DAG.md:54`, `test/contracts/answer-profile.contract.md`),
  which types *answers on the wire*, not the lowering.
- Every compile in the plan lands at `Val`
  (`Effect4/Semantics/RegionSimulation.lean:175-188`; `Skel.FullSig` answers
  `Val`, `SkeletonSemantics.lean:32-37`).

**Carrier change or additive.** Nothing in the plan makes it *impossible*; but
the natural later reading — "type the lowering at `Prim`" — is a carrier change,
because `Prim`'s `β` is one value alphabet and typing it means indexing `Prim`
by a type, i.e. a new inductive.

**Minimal amendment.** One line in §6: *the compile is untyped at `Val`; DB-09
item 1 will be a judgment over the flow's own `Ty` with `Val` as its erasure,
never an index on `Prim`.* Plus a P7 register row.

**Packet.** P7, §6.

### 12. `Prim` is sanctioned as an existing-type row, not as a program carrier; R2 crosses that line

**Claim.** The DESIGN-BASIS exclusion "a second free-program carrier beside
`Program`" (`docs/DESIGN-BASIS.md:432`) and DB-02's "`Flow` is the sole
reifiable program representation" (`:103`) are currently satisfied because
`Prim` is only ever the image of a compile. R2 makes `Prim` the thing the machine
actually runs, with fork programs no `Flow` admits.

**Evidence.**
- `docs/FRAMES-DAG.md:274` — `Effect4.Prim` is recorded as "canonical
  first-order primitive syntax; **not** `Effect4.Program` … and **not**
  `Effect4.CheckedFlow` … this is the pinned rc.112 op family only, **with no
  admission**." That is the sanction, and it is an existing-type row in a frozen
  packet, not a `DESIGN-BASIS` entry.
- `docs/FRAMES-DAG.md:120-132`, separation 1 — "A later packet that wants a
  fiber whose body is a frame machine must state that embedding explicitly;
  nothing here does."
- Nothing in the plan states the embedding.

**Carrier change or additive.** Additive if the invariant is stated; the excluded
design if it is not.

**Minimal amendment.** R2's breaker carries the invariant *every `Prim` the
machine steps is `compileAt` of an admitted `Flow`* — as a theorem where X1 makes
it provable, and otherwise as a `Prim.WellSourced` predicate with an explicit
refusal row. Add one paragraph under DB-02 in `docs/DESIGN-BASIS.md` naming
`Prim` a target-profile machine syntax with no admission of its own. Write it
before R2, not after.

**Packet.** R2 breaker; a DESIGN-BASIS amendment carried by F1 or F5.

### 13. Six decision kinds, two of which answer the same question

**Claim.** The multiplicity is DB-03's intent for four of them and an unforced
duplication for two.

**Evidence.**
- `docs/DESIGN-BASIS.md:134-138` — "Scheduling, race winners, wake-up order,
  external replies, and other choices have distinct decision kinds." Distinct is
  the design.
- Present tapes: the Flow decision tape (`Effect4/Flow/Decision.lean`); the
  interrupt tape on the *same wire* above `interruptBase = 1000000`
  (`Effect4/Flow/Interrupt.lean:63,78-79`, `sitesSeparated :117`, and
  `Point.site_ne_choose`); `SchedulerDecision` /`DecisionTape`
  (`Effect4/Concurrency/Scheduler.lean:22-33`); `Supervision.RaceAllDecision`;
  `Race.RaceDecision`; and the answer *oracle*, which is a function keyed by a
  `Config`, not a tape (`Effect4/Semantics/RegionSimulation.lean:222-226`,
  `FrameSimulation.answersOf` at `:183`).
- The plan adds `RunDecision` with `fireDispatcher`, `flush`, `yieldVerdict`,
  `answerAsync`, `interruptFrom`. Two overlaps: `RunDecision.interruptFrom` and
  `Flow.Interrupt.Point` both decide interrupt delivery; `RunDecision.yieldVerdict`
  and `SchedulerDecision.schedule` both decide who runs.

**Carrier change or additive.** Additive, provided the partition is frozen.

**Minimal amendment.** R2's contract states the partition: the Flow tape owns
`choose`/`branch`; the interrupt tape owns delivery at a Flow interrupt point;
`RunDecision` owns dispatcher firing, yield verdict, async answer and the
machine-level interrupt with its interruptor id. Add the lemma that a Flow
interrupt site and a `RunDecision.interruptFrom` never name the same site — the
`sitesSeparated` shape one level up. Restate plan decision 7 (`:173-174`) as
"one interrupt *model*, two decision kinds, with the separation proved",
otherwise P6 will be asked to unify two tapes and will not be able to.

**Packet.** R2 breaker; decision 7 reworded.

### 14. One fork former is not enough: `raceAll`, `forkIn`/`forkScoped`

**Claim.** The author's proposed single `fork (body) (args) (target)` cannot
express `raceAll`'s immediate daemons or the two scope-linked forks.

**Evidence.**
- rc.112 `forkIn` (`internal/effect.ts:5364-5378`) forks a **daemon**, then, if
  the scope is `Open`, registers a keyed finalizer and an observer that removes
  the key; on a `Closed` scope it interrupts immediately. `forkScoped` is
  `forkIn` on the ambient `Scope` (`:5400-5406`). Reported at
  `docs/research/2026-09-03-deep-fiber-runloop.md:174-186`.
- The tracked/detached split already exists as two operations in the current
  family (`Effect4/Concurrency/FiberFamily.lean:96-99`).
- `raceAll`'s "start entrants as immediate daemons until observed success" needs
  (i) daemon, (ii) *when* each is given the processor — which the current
  projection reads off a tape (`FiberFamily.lean:248-261`, `forkAt`), and (iii)
  a child that completes another child, refused at the current alphabet
  (`FiberFamily.lean:329-338`).

**Carrier change or additive.** Additive under the operation route: three fields
on the fork's *request*, not three formers.

**Minimal amendment.** The fork carries `daemon : Bool` and
`region : Option RegionId` (a region, not a computation — DB-05 covers it, and
`scope.fork-linkage` needs exactly this, per the state note §5.4). Immediacy is
a `RunDecision`, never a term field (finding 3). `race` and `raceAll` are
derived Flow programs, with a register row saying the tenth `runtime-check.ts`
assertion stays host-only until a child can complete a cell — which is what
finding 4's store-driven park buys.

**Packet.** X1 (the fork's request shape), R2 (immediacy as a decision), M3/M6
(the scope link).

### 15. The DSL binds one family per program, so the J packet's cross-family golden cannot be spelled

**Claim.** Plan packet J (`deep-plan.md:103`) turns goldens into checks of a
projection of the model, and M2's `deferred.await` row is exactly the one that
needs a forked child to complete a cell. No such program can be written.

**Evidence.**
- `Effect4/Meta/Derive.lean:112` — `effect_program <name> (<arg>) over <family> : <ty> := …`,
  one family.
- `harness/trace/Generate.lean:584-592` — "the packet asked for a program in
  which a forked child completes a cell the parent awaits. `effect_program` binds
  exactly one family per program … so the program cannot be spelled even now that
  both exist."

**Carrier change or additive.** Additive — a DSL form, or a register row.

**Minimal amendment.** J's fence gains either an `over [F, G]` form (a family
sum, which `Handler.sum` already supports) or a register row saying the
cross-family golden stays unspellable and the two-fiber fact is a Lean theorem
only. Add it to §5 as decision 12.

**Packet.** J.

### 16. Premise 5 and M2's row disposition are wrong under finding 4

**Claim.** `deep-plan.md:57` — "`Deferred.await`'s resume half is `op.Async`" —
and `:98` — `await` partial until R2 — both change once the stores drive
`asyncResume`.

**Evidence.** Finding 4. `op.Async` remains needed for rc.112's external
callback (`Effect.callback`, `Effect.never`), which is what
`layer.launch-holds-scope` rests on.

**Carrier change or additive.** Additive; a wording and row-column repair.

**Minimal amendment.** Restate premise 5 as: *four of the five park rows are
blocked on the run loop; `deferred.await`'s resume half is a machine-level park
on a store key, not `op.Async`. `op.Async` is rc.112's external callback and is
what `layer.launch-holds-scope` needs.*

**Packet.** §2 premise 5, M2's row column, R3's join.

### 17. Counts and sizes in the plan are non-blank-line counts

**Claim.** Minor, but the plan's F1 fence and several sizes are quoted in two
different units.

**Evidence.** Actual line counts: `COORDINATION.md` 2730 (the plan's
"160 to 2730" is right); `Effect4/Runtime/Runtime.lean` 2549;
`Effect4/Runtime/Scope.lean` 1424; `Effect4/Semantics/RegionSimulation.lean`
1068; `Effect4/Concurrency/Race.lean` 681 (the plan's "−681" is right);
`Effect4/Stateful/RefFamily.lean` 255; `Effect4/Layer/LayerFamily.lean` 324. The
smaller figures circulating (1250, 219, 277) are non-blank counts. The state
note's correction (`docs/research/2026-09-03-deep-state-models.md:1011-1014`) is
right.

**Minimal amendment.** Fix when F1 lands; state the unit.

### 18. Where the notes disagree with each other or with the plan

1. **State slot versus context field.** The flow note refuses a state slot
   because it "would re-freeze `test/contracts/frames.contract.md` and restate 28
   census rows" (`docs/research/2026-09-03-deep-flow-to-frames.md:306-311`); the
   state note asks for a `context` field on `FrameFiber`
   (`docs/research/2026-09-03-deep-state-models.md`, §5.5-§5.6), which is the
   *same* re-freeze. The plan adopts both (ruling 3 at `:41`, M4 at `:100`)
   without noticing. Findings 4 and 6 resolve it.
2. **`Runtime.lean` untouched versus `popFrom` revisited.** The fiber note's R1
   says `Runtime.lean` is not in the fence and that `popFrom`/`ensure`/`armA`/
   `armE` are reused verbatim, while quoting `FRAMES-DAG.md:200-211` at its own
   `:500-508` saying that packet must revisit `popFrom`. Finding 5 resolves it.
3. **Compile coverage.** Plan premise 1 (`:47-50`) says the compile "already
   covers every Flow v3 term". True for `RegionTerm`
   (`RegionSimulation.lean:312-350`); `FrameSimulation.compile` covers only the
   straight-line fragment (`inFragment`, `FrameSimulation.lean:249-272`). Say
   "every Flow v3 *region* term".
4. **Sizes.** The flow note's summary says "~2 100 Lean lines"; its own packet
   table sums to "≈2 350". The plan's P1..P7 sum to 2 400 plus 150 under a
   breaker. Cosmetic; pick one.
5. **The gates note is silent on everything in findings 1-5.** It contains no
   mention of `Prim`, `PrimInterp`, `FrameFiber`, `Race.lean`, `forkIn`,
   `forkScoped` or `raceAll`. The plan cites it for premises 6, 7 and 8 only,
   which is correct; it is not evidence for ruling 1 or ruling 3.

---

## Amendments to the plan

Diff-like, against the plan's own sections.

### §1 The decision

- **Add, after "Downward":** *Sideways-first, one prerequisite:* `Flow` gains a
  way to name a concurrent child. It is an operation of the supplied alphabet
  whose request names a declared root and whose answer is a fiber handle — not a
  new `RawTerm`/`RegionTerm` constructor — so the alphabet, admission, the four
  region denotation theorems and the twenty-one exhaustive `RegionTerm` matches
  are untouched, and `Flow.denote` stays the sequential face by construction.
  Emitting `Effect.fork` from the lowering is a *later* packet with its own price
  (a `TypeScript.Stmt` former and a pinned-package bump). [finding 1, 2]
- **Ruling 3, replace:** ~~"`PrimInterp` stays pure. … a state slot would
  re-freeze the frames contract and restate 28 census rows."~~ →
  **"`PrimInterp` stays pure and `Prim`/`FrameFiber` are untouched. The machine
  is parametric in a service state through `RunInterp extends PrimInterp`, adding
  `syncState : σ → St → St × β` and an `asyncResume` driven by the stores;
  `statelessRun` makes every existing `PrimInterp` theorem a `rfl` corollary, and
  the oracle form (`answersOf`, `RegionOracle`) is a corollary too. `armA`/`armE`
  are re-stated at `RunInterp` only when a finalizer or a continuation touches a
  store, because `finalizerExit` and `contA` are consumed inside them
  (`Runtime.lean:718-770`). Under DB-07 the machine step threads `St` out on the
  failure arm and never restores it; R2 owes that lemma."** [finding 4]
- **Add ruling 4:** *R1 opens a `test/contracts/frames.contract.md` breaker. The
  three park primitives are `Prim` constructors, `Prim.cases_receipt` is restated
  at seventeen, and the `popFrom` fusion agreement is proved or the loops are
  unfused. The contract is re-frozen once, at R1, not twice.* [finding 5]
- **Add ruling 5:** *`Prim` is a target-profile machine syntax with no admission
  of its own. R2 carries the invariant that every `Prim` the machine steps is
  `compileAt` of an admitted `Flow`, as a theorem where X1 makes it provable and
  otherwise as a predicate plus a refusal row. `docs/DESIGN-BASIS.md` gains one
  paragraph under DB-02 saying so.* [finding 12]
- **Ruling 1, replace:** ~~"`Race.lean` is retired … costs eight files"~~ →
  **"`Race.lean` is left in place for now. Retiring it is a ruling, not a
  refactor: `RACE-PG-BINARY-FIRST-COMPLETION` has eight `required-open` edges
  (`docs/RACE-DAG.md:102-115`), four SEEDED register rows depend on it
  (`REGISTER.md:114-117`), `scripts/check-live-stack.mjs:106` and
  `test/contracts/live-stack.contract.md:246` name its battery in a frozen
  expected-failure list, and `PORT-MANIFEST.md:378` uses it as a
  duplicate-prevention referent. Twenty-nine files reference it. Revisit at R3,
  as a ruling packet."** [finding 8]

### §2 Premises corrected by the research

- **Premise 5, replace:** ~~"`Deferred.await`'s resume half is `op.Async`"~~ →
  **"Four of the five park rows are blocked on the run loop. `deferred.await`'s
  resume half is a machine-level park on a Deferred-store key, not `op.Async`;
  `op.Async` is rc.112's external callback, which is what
  `layer.launch-holds-scope` needs."** [finding 16]
- **Premise 1, replace** "every Flow v3 term" with **"every Flow v3 *region*
  term; `FrameSimulation.compile` still covers only the straight-line
  fragment"**. [finding 18.3]
- **Add premise 12:** *`Effect4/Runtime/Runtime.lean` has two recorded owners:
  the frames contract, and `docs/ENVIRONMENT-DAG.md:151`'s `F-RT` fence for the
  L7 node `Runtime/Runtime`, whose node status at `:29` still calls it an empty
  stub. F1 repairs the DAG and renames the L7 fence before M4 is dispatched.*
  [finding 6]
- **Add premise 13:** *`effect_program` binds exactly one family
  (`Effect4/Meta/Derive.lean:112`), so no golden can exercise a forked child
  completing a cell the parent awaits (`harness/trace/Generate.lean:584-592`).*
  [finding 15]

### §3 Packets

- **Insert, at the head of "The machine":**

  | Id | Packet | Fence | Size | Prerequisites | Closes |
  | --- | --- | --- | --- | --- | --- |
  | X1 | Flow names a child: a `fork` operation of the supplied alphabet whose request names a declared root and whose answer is a fiber handle; the request carries `daemon : Bool` and `region : Option RegionId`; a run-time refusal "the request does not name a declared root"; the fork's *start* is a machine decision, not a term or an admission clause | a new profile module under `Effect4/Flow/`, the `OpSpec` row shape in `Effect4/Target/TypeScript/ScriptFlow.lean` (`tableAlphabet` at `:84-90` is where an alphabet is actually built, from `OpSpec.requestTy`/`answerTy` spellings — a fork is one more row, with a `Handle` answer spelling), `Effect4Test/Flow/`, contract, register rows; **no** edit to `.lake/packages/effects` and **no** edit to `.lake/packages/typescript` | 250-350 | breaker | the carrier R2's twelve `fork.*` rows are stated over |

- **R1, amend:** fence gains `Effect4/Runtime/Runtime.lean` **under a
  `frames.contract.md` breaker**; delete "`Runtime.lean` untouched"; statement
  list gains "`Prim.cases_receipt` at seventeen" and "the `popFrom` fusion
  agreement, proved or unfused"; declares `RunInterp` and `statelessRun`.
  Size 750-1000. [findings 4, 5]
- **R2, amend:** prerequisites gain `X1`; the alphabet freeze states the decision
  partition of finding 13 and the machine's per-fiber-sum termination bound of
  finding 3; the breaker carries ruling 5's invariant; `RunFiber` gains the
  opaque `context : χ` that M4 wanted on `FrameFiber`. [findings 3, 6, 12, 13]
- **M4, split into M4a and M4b:** M4a = `Context/Requirement` + `Context/Service`
  (L1), one frozen contract, `Program.UsesOnly` and its five laws,
  `ENV-KEY-INTERP` named; M4b = `Context/Environment` (L2), `ENV-PG-CONTEXT`, the
  eleven laws of `PLAN.md:208` and its seven counterexample classes. Neither
  touches `FrameFiber`. [findings 6, 7]
- **M6, amend:** `scoped_installs_and_restores` and
  `acquireRelease_captures_context` are stated over `RunFiber`, not `FrameFiber`;
  prerequisites become M3, M4b, R2. [finding 6]
- **Add P8, after P4:** `Skeleton → Prim` compile and
  `compileSkeleton (skeletonDispatch flow) = compileAt alphabet flow`; a register
  row for the render seam it does not close; ~400 lines; prerequisites P4. It
  needs no `Prim.iterator` — `iterator_folds_inline` makes a `yield*`-only
  generator transparent. [finding 10]
- **P7, amend:** add two register rows — the lowering emits a service call and
  never `Effect.fork` (under X1's operation route), and the compile is untyped at
  `Val` so DB-09 item 1 will be a judgment over the flow's `Ty`, never an index
  on `Prim`. [findings 2, 11]
- **J, amend:** fence gains either an `over [F, G]` DSL form or a register row
  for the unspellable cross-family golden. [finding 15]
- **F6, amend:** promoted from a deletion to a ruling packet, or deferred to R3.
  [finding 8]
- **F1, amend:** also repairs `docs/ENVIRONMENT-DAG.md`'s node status and the
  `F-RT` fence name, and carries the DESIGN-BASIS paragraph of ruling 5.
  [findings 6, 12]

### §4 Order

| Wave | Builders | Beside, no Lean build |
| --- | --- | --- |
| 0 | F5 with F6* (alone) | F1 (now also the ENVIRONMENT-DAG and DESIGN-BASIS repairs), F2, F3a; **X1 breaker; M4a breaker** |
| 1 | **X1** · M1 then M2 · P1 then P2 then P3 | R1 breaker (**now a frames re-freeze**) |
| 2 | **R1** · F3b then F4 · M3 then **M4a** · P4 | F7; **R2 breaker (alphabet, decision partition, termination bound, ruling-5 invariant)**; M4b breaker |
| 3 | **R2** · **M4b** then M5 · P5 | J |
| 4 | R3 (**including the Race ruling**) · M6 · P6 · P7 · **P8** with the doc repairs | the stale-premise repairs land with their files |

\* F6 only if §5 decision 1 is taken as a ruling; otherwise it is dropped.

Changes from the plan's table: R1 moves from wave 1 to wave 2 because it now
adds three `Prim` constructors, and P1-P3 rewrite proofs that `cases` over
`Prim`'s constructor list (`RegionSimulation.lean:877-958`, `:987-1066`) — the
two must not be in flight together; X1 takes R1's wave-1 slot;
M4 becomes M4a (wave 2) and M4b (wave 3); M6 moves behind R2; P8 is added at
wave 4.

### §5 Decisions the plan needs from the user

- **1, replace:** ~~Retire `Race.lean`. Recommended: yes.~~ →
  **Leave `Race.lean` in place through wave 3 and decide at R3 whether to retire
  `RACE-PG-BINARY-FIRST-COMPLETION` as a ruling (eight open edges, four register
  rows, a red gate, a generated assurance file, a `PORT-MANIFEST.md` referent).
  Recommended: leave, then rule at R3.**
- **7, replace:** ~~P6 re-freezes `frames.contract.md` through a breaker, after
  R2.~~ → **R1 re-freezes `frames.contract.md` once, before R2. P6 rides that
  freeze. "One interrupt model" means one *model*, two decision kinds — the Flow
  interrupt point and the machine's `interruptFrom` — with the separation
  proved, in the `sitesSeparated` shape.**
- **8, replace:** ~~`stateless` is a named hypothesis in T5/T6; no state slot in
  `PrimInterp`.~~ → **`stateless` stays a named hypothesis in T5/T6 and
  `PrimInterp` stays pure. The machine takes a `RunInterp extends PrimInterp`
  with `syncState` and `asyncResume`; `statelessRun` is the corollary. Elaborated
  and checked.**
- **9, replace:** ~~M4 needs an owner and a breaker; dispatch its breaker in wave
  1.~~ → **M4a's breaker in wave 0 and M4b's in wave 2, one per ENVIRONMENT-DAG
  layer, per `PLAN.md:260-268`. Neither adds a field to `FrameFiber`; the
  context lives on `RunFiber`.**
- **Add 11:** *After R3, `Scheduler.lean` and `Supervision.lean` witness no
  `fork.*` or `interrupt.*` census row; they remain `separateCalculus` owners of
  a relational scheduler with its own decision alphabet. R3 re-disposes their 181
  witness references under `frozenCoverageStates`, one register row per retired
  witness family. Projection lemmas are evidence, never a closure route.
  Recommended: yes.*
- **Add 12:** *`Flow`'s fork is an operation of the supplied alphabet, not a new
  terminator. The lowering therefore emits a service call and never
  `Effect.fork`; that is a P7 refusal row. A Flow v4 fork terminator is a later
  packet, priced with the `effects` and `typescript` bumps it needs.
  Recommended: yes.*
- **Add 13:** *`effect_program` gains an `over [F, G]` form, or J carries a
  register row for the unspellable cross-family golden. Recommended: the register
  row now, the DSL form when a two-fiber golden is actually wanted.*

---

## What I could not verify

- **I ran no gate, no sweep, and no coverage report.** All census counts quoted
  here are the plan's or the notes', not the sanctioned block from
  `scripts/report-effect-runtime-coverage.sh`. `AGENTS.md:104-107` governs.
- **The 21/28 `RegionTerm` and 14/15 `RawTerm` match counts are lower bounds**
  taken by grepping for constructor arms in match position (`.plain`, `.leave`,
  `.branch`, `whileLoop`). A match that names only `.enter` and `_` is not
  counted; a `.leave` that belongs to `Trace.Event`, `Interrupt.Point`,
  `Skeleton` or `RegionDenotation`'s own op type is over-counted. The `.plain`
  count (21 in `Effect4/`, 7 upstream) is the tighter one.
- **I did not attempt the `popFrom` fusion proof, nor a counterexample.**
  Finding 5 establishes only that the frame vocabulary is typed at `Prim`, hence
  that R1 must edit `Runtime.lean` or duplicate; whether the fusion still agrees
  with `asyncFinalizer` present is exactly the obligation `FRAMES-DAG.md:205-211`
  names, and the fiber note also lists it as its own single most likely break.
- **I did not read `docs/RACE-DAG.md` or
  `test/contracts/race-representative.contract.md` in full** — only the header,
  the reuse ruling and the edge ledger. Whether `RACE-PG-BINARY-FIRST-COMPLETION`
  is retirable on its merits is a ruling I priced but did not judge.
- **`vendor/effect-4.0.0-rc.112/src/` was not re-read.** Every rc.112 line
  citation here is relayed from the four research notes, which took them
  directly. The flow note records that `Context.ts` and `Result.ts` are not in
  the vendored tree at all.
- **Whether an `over [F, G]` DSL form is a small change** I did not check;
  `Effect4/Meta/Derive.lean` is a `MetaM` elaborator behind the axiom-gate
  exemption (`:91-93`) and I read only its header and syntax declarations.
- **The `Effect.fork` render shape.** I established that
  `TypeScript.Stmt` has no fork-shaped former beside `scopedGen`/`scopedGenMasked`
  (`Syntax.lean:106,129,133`), not that adding one is the *only* way — a fork
  might be spellable through `Expr.call` plus an existing former. I did not try.
- **The estimate that X1 is 250-350 lines** is calibrated on nothing; it is an
  ordering claim (X1 is much smaller than R2), not a measurement.

## What I checked by elaborating

One scratch file, `lake env lean`, exit 0, no repository file edited:

1. `RunInterp extends PrimInterp` with `syncState : σ → St → St × β` and
   `asyncResume : σ → St → St × Option (Exit β ε δ ι α)` elaborates against the
   built library, in the same `Type (max u v)`.
2. `DecidableEq (Prim Nat …)` and `DecidableEq (FrameFiber Nat …)` still resolve
   by `inferInstance` — the state slot touches neither.
3. `r.toPrimInterp` is the projection, so every theorem taking a `PrimInterp`
   applies to a `RunInterp` verbatim.
4. `statelessRun interp` satisfies
   `(statelessRun interp).syncState thunk st |>.2 = interp.syncValue thunk` by
   `rfl` — the pure case is a corollary, not a re-proof.
5. A `fork` constructor derives `DecidableEq` both when the child is a nominal
   `κ` (`fork (child : κ) (daemon : Bool) (onHandle : ν)`) and when it is a
   `Prim`-shaped subterm — so `DecidableEq` is *not* an argument against either
   fork route, and the argument has to be made on the match-site and
   re-proof cost of finding 2 instead.
