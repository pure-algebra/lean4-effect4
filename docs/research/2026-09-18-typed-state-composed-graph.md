# The typed-state proof graph, composed (2026-09-18)

An adversarial read of the "algebraically factored" proposal for row 41 against the tree at
HEAD (`1246d121`), and the refinement that survives it. Every claim below was checked at the
file and line named; the one new piece of Lean (§4, layer 0) was built and stamped. The
design authority stays `docs/research/2026-09-18-typed-state-plan.md`; this note amends its §6
and is pending the owner's read. The scout note is
`docs/research/2026-09-18-typed-state-proof-graph-scout.md`.

## 0. Verdict

The proposal is right about the *shape* of the fix and wrong about most of the *facts* it
rests on. Its three structural moves — a protocol (pre/post) on the fiber signature, a Kripke
world for the tables, and factoring the step by what a transition touches — are the correct
way to organise the graph, and they are what §4 adopts. Its headline reduction (5,300–8,600
lines to 2,600–3,800; 65 arms to 25 lemmas) does not survive: it comes almost entirely from an
"administrative frame lemma" over 17 of the 18 scheduler commands, and that lemma is false as
stated. Read at `Machine/Fibers.lean:1795-1943`, seven commands leave every program-carrying
position untouched, nine install or deliver code through interpreter hooks or a command
payload, and two run the fiber. The proposal also misses five obligations that neither it nor
the scout names (§3), one of which — the typing of an asynchronous completion — is exactly the
async-versus-sync surprise the owner asked not to have. It is not a wall (§5).

The honest numbers after composition are in §6: about 130 lemmas and 4,500–6,300 lines, a
20–30 % cut against the scout's estimate, with the substance moved from "65 arms, each its own
proof" to "one generic layer proved once, one delivery lemma over a typed stack, and small
per-arm goals".

## 1. The proposal's claims, checked

| # | claim | where | verdict |
| --- | --- | --- | --- |
| 1 | "Every command but `resume` is code-free" means 17 transitions do not touch fiber code | `Laws/Machine/Book.lean:202` | **misread.** The line is about what a `Cmd` *carries* (`CmdMeans` relates payloads; only `resume` has a `κ`). `driveStep` (`Machine/Fibers.lean:1795`) installs code in `resume` (payload), `registrationDone` (`raceSettle` hook, `:1879`), `afterInterrupt` (`asVoidCode`/`awaitCode` hooks, `:1893`), `closeParAwait` (`parkCode` + `pushIterator`, `:1924`), `finish` (`exitInterruptChildren`: `onSuccess (interruptAllCode …)`, `:1733`), fires observers in `observe`/`enrollRace`/`finish` (`fireObserver`, `:1609`: `resumeAwait` emits `Cmd.resume … (exitValue exit mode)`; `countdown` resumes with the collected exits; `raceCallback` buffers or resumes with `raceSettle`), records an interrupt that can set `current` to a failure in `interruptTarget` and `link` (`interruptRecord`, `:763-777`), and creates a fiber from `Race.programs` in `launch` (`launchEntrant`, `:938`). `loop` and `deliver` run the fiber. Frame-untouched: `evaluate`, `trackChild`, `raceCancel`, `wake`, `drainDue` (state only, but it emits `resume` commands carrying code), `exitDone` (on an exited fiber), `enrollRace`'s no-exit branch. **Seven, not seventeen.** |
| 2 | `PreservesCode` may conclude `dispatcher = dispatcher ∧ races = races` | same | **false**: `enrollRace`/`registrationDone`/`launch` update races; `start` (`:927`) and `drainOwed` (`:1780`) post dispatcher tasks; the conclusion also ignores the stack, which holds continuations (`ScopeFrame.resume`/`.answer`, `InterpR.lean:44-45`). |
| 3 | Sync cluster: 11 ops, one shared lemma, ~40 lines | `EvaluateR.lean:156-285` | **overstated.** Four inline (`suspend`, `foreignRelease`, `closeWalk`, `sync`), six through distinct `FiberAction` helpers (`getId`, `getContext`, `setContext`, `snapshotChildren`, `ambientScope`, `dropObservers`), `refuse` installs a failure, `frontier` does nothing. Each is trivial under §4's generic resume lemma, but they are not one code path. |
| 4 | Scoping cluster: 6 ops, "push/pop a ScopeFrame", ~80 lines | same | **wrong in kind.** `unguard` and `finishFinalizer` are `deliverR` (`:127`), i.e. the `popR` walk (`:66-121`) with mask restoration, deferred interrupts, and the `iter`/`loop` slot re-entries. That walk is the single hardest piece of S2, not the easy cluster. |
| 5 | Control cluster reuses "existing `loopEnter`/`iterNext` invariants" | `InterpR.lean:312-332` | **no such invariants exist.** These are interpreter hooks returning code from `walkR` (`:226`), `loopNextRAt`/`loopResumeRAt` (`:281`, `:291`), `closeSeqStepR` (`:152`) — definitions outside `denoteR`'s mutual block (`DenoteR.lean:780-794`) with no typing lemma. Typing them is new work (§3.4). |
| 6 | Concurrency cluster: `Simulation/Actions.lean` "already characterized" the helpers | `Simulation/Actions.lean:449-760` | **pattern reusable, lemmas not.** Every theorem there is binary (`fork_rel`, `join_rel`, … conclude an `IterRel`/`BMeans`). What carries over is the parameterisation by an answer function (`AnswerRel`, `:27`), which lets a helper's behaviour be stated once for any continuation. The scout's §A.3 item 5 already said this. |
| 7 | `AnswerOk (.getId) := ∃ id, ans = Val.fiber id` | `Program/Checker.lean:371`, `InterpR.lean:386` | **wrong**: `getId` types to `.nat` and answers `Val.nat fiber.value`. The table was not read from the checker. |
| 8 | `AnswerOk (.fork …) := ∃ id, v = Val.fiber id ∧ validIn` | `Machine/Fibers.lean:1403` | **incomplete**: the continuation must learn the child's type through the table, in `∀`-form over the world *after* the fork (scout E.2/E.3); the clause as written carries nothing a later `await` can use. |
| 9 | Kripke world `(Γ, s)` with `Later` — presented as new | scout §A.1, `P6_bind` | **half already there**: the scout's clauses quantify continuations over later stores (`∀ ex s', Later s s' → …`). The table half is the genuine addition — but the proposal's own `AnswerOk Γ s` is *not* world-quantified, so as written its `TypedProg` is not monotone under `Later` (a `validIn s` in hypothesis position is antitone). The repair is the `∀ w' ≥ w` continuation clause, §4 layer 0, probed. |
| 10 | "The store half is already proved sound via `StoreOk`/`Stores.WF`" | `LoopSound.lean:157-164`, `Progress.lean:408-506` | **as a lemma set, yes; as a predicate, no.** `SoundB` is a statement about `runP` and there is no run for `RSig` (scout §A.5). What is reused is `progress`, `answer_typed`, `step_heapNat`, `syncOpStep_wf`, the `storesOk_*` family. `Stores.WF` explicitly excludes deferred completions (`STORES-FB-COMPLETION`, `StoresLaws.lean:19-22`), which is §3.5. |
| 11 | `Pred(Σ₁ ⊕ Σ₂) ≅ Pred(Σ₁) × Pred(Σ₂)` | `Effects/Algebra/Signature.lean:35`, `Sum.lean:48` | **true as a definition**, with the caveat that both halves read one world. `Protocol.sum` and `Typed.inl` in the probe make it a one-induction lemma. |
| 12 | Four combinator lemmas (`bind`, `guardR`, `constructR`, `prepareR`) collapse S1's macro arms to 3–5 lines | `DenoteR.lean:43-100`, `:296-525` | **right in direction, wrong in count.** The scout already noted every composite arm is `guardR`/`bind`/`constructR` (§A.2). But `DenoteR` has about twenty-five named `R`-combinators (`seqR`, `finalizerR`, `onExitR`, `suspendR`, `storeR`, `fiberValR`, `updateContextR`, `scopeAddR`, `bindServiceR`, `memoizeR`, `provideWithR`, `forkLayerR`, `mergeForkR`, `mergeAllR`, `provideLayerR`, `acquireInR`, …) and each needs its lemma. S1 is ~55 lemmas either way; the combinator lemmas make each *arm* short, they do not make the *count* small. |
| 13 | S3 through `BMeans.exitOf` per fiber, 3 lemmas | `RuntimeR.lean:239` | **agrees with the scout.** |
| 14 | `TypedProg.bind` stamped in probe 6 | scout §B.5 | **true** (`[propext]`). |
| 15 | Totals: ~75 lemmas, 2,620–3,830 lines | — | **not credible**: built on 1–5 and blind to §3. See §6. |

## 2. What the proposal gets right, and the scout did not have

- **A protocol, not a clause list.** Stating the fiber signature's typing as a pair
  (what an operation demands of the world it is performed in; what the scheduler promises of
  the answer in the world it answers in) is de Vilhena–Pottier's Ψ and it is the right unit.
  The scout's shape B is the *post* half only. The *pre* half is missing from both (§3.1).
- **The world is the object the invariant is about.** Handles carry no type in this tree —
  fibers (`Program/Typed.lean:55`, DI-17), cells (`Progress.lean:130`), promises (`:135`),
  scopes (`:141`) are all coarse in `Val.hasTy` and always valid in `validIn`. So typing them
  is a property of a world (tables plus store), and every judgement is a presheaf over worlds.
  `HandlesFit` is then world satisfaction, not a fourth ad-hoc field, and the same device
  types deferred completions (§3.5, §5).
- **Factor the step by what a transition touches.** The wrong lemma (claim 1) is the wrong
  instance of a right idea: after the world-quantified predicate of §4, any step that only
  extends the world and leaves every program-carrying position alone is settled by one lemma.
  The honest list of such steps is seven scheduler commands plus the observer kinds that only
  update bookkeeping (`untrackChild`, `dropScopeFinalizer`).

## 3. What neither document names

**3.1 The protocol's precondition.** `TypedProg`'s `vis (.inr op) k` clause needs a fact about
`op`'s *payload*, not only about its answer: `sync v` (`v` valid), `setContext ctx`, `refuse
cause` (the cause admits the error column), `unguard ex` / `finishFinalizer ex` / `closeScope
scope ex` / `scopeExit prev scope ex` (the exit fits the type being delivered), `loop p cursor`
(the cursor fits the loop's carrier), `fork child` / `forkIn` / `forkScoped` / `scoped` / `mask
flag body` / `raceAll entrants` / `gen at_` / `suspend at_` (the addressed body is typed at the
type the checker gives that point). Without it S2 cannot show `AnswerOk` for `sync v` (the
answer *is* `v`) and cannot type a forked child. This is `OpOk : World → FiberOp → Prop`, forty
arms, one line each, beside `AnswerOk`.

**3.2 The typed stack.** `ScopeFrame.resume kind next` and `.answer next` hold continuations
that have *forgotten which operation saved them* (`saveAnswerR`, `EvaluateR.lean:144`).
An `.answer` slot is pushed by `scoped`, `gen`, `loop`, `mask`, `raceAll`, `closeScope`,
`await`, `async`, `yieldNow`, the interrupt family, and `closeIter` — with different delivered
exits each time. The uniform statement is the typed evaluation context of a CK machine:
`StackOk w (ty : answer × error) stack` says the stack accepts an exit of type `ty` and
delivers the fiber's final exit at its table type; `current` is typed at `ty`. Then
`popR` is **one** lemma (`popR_typed`: a typed exit into a typed stack yields a typed
configuration), with seven slot cases, and `deliverR`, `prepareScopedExitR`, `prepareIterR`
follow from it. For a parked fiber the "current" is the park, and the expected type of the top
slot is fixed by the park's kind and the world: `join target mode` → the table at `target`;
`awaitAll targets` → the targets' exits; `race` → the race's type; `async (registerAwait cell)`
→ the promise table at `cell` (§3.5); `async (registerSleep _)` → `unit`; `yieldNow` → `void`.
That is `ParkedOk`.

**3.3 The delivery sites.** The places that construct an answer for a waiting continuation are
few and enumerable, and each is one obligation "the program installed or sent is typed at the
type the receiver expects":

| site | where | what it delivers |
| --- | --- | --- |
| immediate answers in `evaluateFiberR` | `EvaluateR.lean:156-285` | `next v`, `next .unit`, `answerWith next` via a helper |
| `join` on an exited target | `Machine/Fibers.lean:1561` | `exitValue exit mode` |
| `fireObserver.resumeAwait` | `:1614` | `Cmd.resume waiter token (exitValue exit mode)` |
| `fireObserver.countdown` / `countdownPark` immediate | `:1622`, `:831` | `resumePrim resumeWith exits` |
| `fireObserver.raceCallback` → `registrationDone` | `:1655`, `:1859` | `raceSettle` (`denoteRaceSettle`, `InterpR.lean:199`) or a park |
| `registerAsync` immediate, `dueResumes`, `clockStep` → `drainOwed` | `InterpR.lean:344-360`, `Fibers.lean:1780` | `denoteStored` of a stored completion; `Prim.success unit` for a sleep |
| `afterInterrupt` | `:1893` | `asVoidCode (awaitCode kind)` |
| `closeParAwait` | `:1924` | `parkCode (awaitAll fibers)` under an iterator slot |
| `exitInterruptChildren` | `:1733` | `onSuccess (interruptAllCode children) (restoreName exit)` |
| `Cmd.resume` (the sink) | `:1816` | `answerWith t.frame answer`, then `evaluate` |

Nine producers and one sink. This table, not "18 arms of `driveStep`", is S2's command half.

**3.4 Hook typing.** `interpR root` (`InterpR.lean:301-391`) has about fourteen code-valued
fields: `suspendBody`, `iterNext`, `loopEnter`, `loopResume`, `cancelThenFail`, `parkCode`,
`interruptCode`, `interruptAsCode`, `interruptAllCode`, `answerCode`, `registerAsync`,
`dueResumes`, `clockStep`, `raceSettle`, `exitValue`. Every command arm of claim 1 and every
`iter`/`loop` slot of `popR` installs one of these. The obligation is a structure
`InterpTyped root` with one field per hook ("returns a program typed at the type its consumer
expects, at every world"), proved once for `interpR root`. The body hooks (`suspendBody`,
`iterNext` at `.gen`, `loopEnter`/`loopResume`) reduce to S1 at a point plus one recursion each
over `walkR`/`loopNextRAt`; the rest are closed small programs (`fiberValR`, `pure`, a
`guardR`/`bind`). S2 then never unfolds a hook.

**3.5 The asynchronous completion.** A `perform` on an `.async` row denotes
`.vis (.inr (.async (.registerAwait cell) v)) pure` (`denoteAsync`, `DenoteR.lean:223`); the
answer arrives as code — `denoteStored` of the completion the cell holds (`InterpR.lean:347`,
`:355`; `denoteStored`, `:133`: `.pure (.success v)`, `.pure (.failure c)`, or `storeR (refGet
cell)`). Nothing types that completion: `Stores.WF` excludes it by name
(`STORES-FB-COMPLETION`), and the machine-level `DeferredOk` (`Simulation/Hooks.lean:33`) says
only that it *is* a completion (`CompletionShaped`, `:27`). So today the `async` clause of
`AnswerOk` has no source. The resolution is in §5 and is the deferred analogue of `HeapNat`.

**3.6 Two shape facts the invariant must carry.** A `scopeExit` node arriving as a counted
operation answers `badShapeExit` (`EvaluateR.lean:174-177`); it is meant to be consumed by
`prepareScopedExitR` in the glue pass (`:302`, `:322`). The no-`badShape` corollary therefore
needs "a `scopeExit` head is never counted", i.e. `OpOk` at a counted head is `False` for it
and `TypedFiber` is stated on the configuration *after* `prepareIterR`. And `evaluateRawR`'s
store arm answers `.unit` when `syncOpStep` is `none` (`:293-296`, `evaluateR_store_missing`);
the invariant needs `progress` (`Progress.lean:495`) to show that branch is unreachable for a
typed operation in a well-formed store — the store clause of `OpOk` is exactly `progress`'s
hypotheses.

## 4. The composed graph

```
L0  Typed o Ψ w Q p          generic over Signature; world preorder o; protocol Ψ = (pre, post)
    mono / bind / widen / inl / inr_inv          -- probed, no axioms (appendix)
         │
L1  World := ⟨Γ fibers, Π promises, Ρ cells, s⟩   ordered by table extension + Later s s'
    Ψ_S : the store protocol   pre = progress's hypotheses;  post = answer_typed ∧ valid ∧ WF
    Ψ_F : the fiber protocol   OpOk (40 arms) / AnswerOk (40 arms), tables read in ∀-form
    TypedProg w ty p := Typed o (Ψ_S.sum Ψ_F) w (ExitOk ty) p
    HandlesFit w tys env    (world satisfaction for every handle sort)
         │
L2  SlotOk / StackOk w ty stack;  ParkedOk w f;  TypedFiber w f  (running | parked | exited)
    popR_typed  (one lemma, seven slot cases)  →  deliverR_typed, prepare*_typed
         │
L3  TypedState m := ∃ w, fibers ∧ races' programs ∧ dispatcher tasks ∧ command residue
                     ∧ coverage (every fiber ever forked is in Γ) ∧ stores in the columns
    InterpTyped (interpR root)        fourteen hook fields, proved once
         │
S1  denoteR_typed  weight induction (Intro.lean:27 shape); ~25 Eff arms via combinator lemmas;
    ~25 R-combinator lemmas; walkR / loopNextRAt / layerBuildR / closeSeqStepR
S2  five families:  (a) evaluateFiberR's 40 arms, each = OpOk ⇒ AnswerOk for the answer
                        produced + world extension, closed by L0's vis inversion;
                    (b) popR_typed and the glue;  (c) the nine delivery sites + the sink;
                    (d) the frame lemma and its seven command / two observer instances;
                    (e) Keeps.lean, the unary ladder (scout §A.3 item 1)
S3  transfer through replay_rel / BMeans.exitOf; TypedProgram.run_typed; no badShape; DI-17
```

**Layer 0** is the piece that was missing from both documents and it is the one that makes
"monotone by construction" true instead of a lemma: the continuation clause is
`∀ w', o.le w w' → ∀ ans, Ψ.post w' op ans → Typed o Ψ w' Q (k ans)`. Weakening is a single
`cases` (no induction on the tree); `bind`, `widen` and the coproduct lift `inl` are one
induction each; inversion at a fiber node hands the arm exactly `pre` now and `post` at every
later world. Built against `Effects.Algebra.Sum` as pinned (v0.8.0, `a4ee7a1`), no axioms.
The scout's `monoΓ` (a separate induction, `[propext]`) and the `∀`-form-as-repair story become
unnecessary: table reads are still written in `∀`-form because that is what an `await` means,
not because variance forces it.

**Layer 1** keeps the scout's shape B and adds the `pre` half (§3.1) and the two handle tables
the cut fixes at a constant (§5). The store protocol's `pre` is the hypothesis list of
`progress` (`Progress.lean:495`) and its `post` is that lemma's conclusion; the store clause of
`TypedProg` is therefore *one* application of an existing theorem, which is the honest form of
"the store half carries over".

**Layer 2** is where the proposal's cluster idea lands correctly: not four clusters of
operations but one typed-context judgement that every operation's saved slot satisfies, so
delivery is proved once.

**Layer 3** adds what the scout found (races' `programs`, dispatcher tasks, the command
residue) plus coverage and the hook structure. `TypedState` stays `∃ w`; a fork extends `Γ`,
`refMake` extends `Ρ`, `deferredMake` extends `Π`.

**S2's count.** Family (a) is 40 arms, but under L0's inversion each is "produce the answer,
show `AnswerOk` at the new world, show the world extends": about 25 are five to fifteen lines
(the inline and helper answers, `frontier`, `interruptScoped` on self), about 15 are real
(`fork`×3 through `spawn`/`start`, `await` through `join`, `awaitAll` through `countdownPark`,
`raceAll` through `beginRace`, `async` both branches, `scoped`, `mask`, `guard_`,
`gen`/`loop`/`closeIter` through hooks, `unguard`/`finishFinalizer` through `popR_typed`,
`refuse`). Family (c) is ten. Family (d) is one lemma with nine instances. That is the whole
of the 65 arms, organised so that the hard proofs (`popR_typed`, the fork triple, the
countdown, the race registration) are named and the rest are mechanical.

## 5. Async versus sync, answered for the owner

There is no capability wall. The alphabet the reference runs is the whole `FiberOp` list
(forty operations, `Sched.lean:96-160`) and the whole store list (`SyncOp`, `Stores.lean:568-641`:
refs, deferreds, the clock, scopes, memo maps), and the scheduler is the one shared
`RunMachine`. The typed-state statement covers all of it at the empty external table, as
`run_eq_ref` does. What the milestone must add for the asynchronous rows, and what it inherits:

- **`sleep`** (`Native.lean:234`: `.async`, answer `.unit`): the clock owes `Prim.success
  Val.unit` (`InterpR.lean:357`) — typed at `unit` by inspection. Nothing to decide.
- **`deferredAwait`** (`:225`: `.async`, request `deferredTy`, answer `.nat`, error `.nat`).
  This cut's `Deferred` is `Deferred<number, number>` (`:138-150`), and `deferredSucceed` /
  `deferredFail` / `deferredCompleteWith` take a `nat` request (`:218-`), exactly as refs are
  `Ref<number>` with `HeapNat` (`Progress.lean:71`, the `.nat` column, `E4-PROGRESS-CE-002`). So
  the missing invariant is **`DeferredNat`**: every stored completion is `.success (Val.nat _)`
  or a failure whose cause admits `.nat`, or `ofRefGet cell` (typed by `HeapNat`). It widens
  `CompletionShaped` (`Simulation/Hooks.lean:27`) in the same shape, is preserved by the four
  completing rows via their typed requests (the `answer_typed` pattern), and it is what makes
  `denoteStored` typed at `⟨nat, nat⟩` = the row's answer. **This is a ruling to make**
  (§7); it is the deferred twin of `HeapNat` and no larger.
- **External rows** (`.external`, kind `.async`): on the reference `registerAsync` parks them
  forever (`InterpR.lean:351`, the `_` arm), so the invariant is trivially preserved and the
  statement covers them syntactically. Their delivered answers are the table-aware slice's
  obligation (DI-57, the four gaps of `run_eq_ref`), stated as a typed-tape hypothesis
  ("every `answerAsync` for row `r` carries a value of `r`'s answer type") against the *same*
  `AnswerOk` clause. No redesign later.
- **Polymorphic `Ref<A>` / `Deferred<A, E>`**, which Effect has and this cut spells at
  `number`: the world of §4 carries tables `Ρ : RefKey → Option Ty` and `Π : DeferredKey →
  Option (Ty × Ty)` from the start, with this cut's columns as their constant instances
  (`HeapNat` = `Ρ ≡ nat`, `DeferredNat` = `Π ≡ (nat, nat)`). When the rows become
  type-schematic (the template-table direction of the R4/R5 packet), the checker's rows and
  the tables' extension at `refMake`/`deferredMake` change; the invariant's shape does not.
  That is the "one level higher" rule applied here so the polymorphic extension is a
  refinement, not a rewrite.
- **The rest of the concurrency alphabet** — fork/forkIn/forkScoped/runIn, await/awaitAll/
  failFast/awaitNewChildren, raceAll and its cancel, interrupt/As/Scoped/All, yield, scopes,
  masks, finalizer walks, the dispatcher, the timer — is synchronous from the invariant's
  point of view: every answer is produced by the scheduler from state the world types.
  Their obligations are §3.3's table and family (a) of §4; none needs a new column.

What is *not* in this tree's alphabet at all (Semaphore, Queue, PubSub, STM) is a language
question, not a proof-graph one; the coverage metric (`docs/RUNTIME-COVERAGE.md`) is the
place that tracks it, and adding a primitive later adds rows to `OpOk`/`AnswerOk` and one
family-(a) lemma each. The graph does not close over the alphabet.

**On pulling `Effects` into `Effect4`.** Nothing in S0–S3 needs the `Effects` package to
change: layer 0 imports `Effects.Algebra.Sum` and nothing of `Effect4`, and the frozen
`Effects/Algebra/*` modules stay frozen. It can live at `src/Effect4/Laws/Effects/Protocol.lean`
now and move upstream, or in, later. Vendoring the package under `src/` is mechanical (the
dependency is a pinned git rev; the only casualty is the algebra-parity gate) and is not on the
milestone's path, so I would not spend a moving part on it while S0–S3 are in flight. If the
owner wants the algebra and its laws under one roof for other reasons, it is a separate,
cheap step.

## 6. Sizes, honest

| part | scout | proposal | composed | why |
| --- | --- | --- | --- | --- |
| L0 generic | — | — | ~120 lines, 6 lemmas | probed at 90 lines / 4 lemmas |
| L1 protocol + world + columns | S0 450–600 | 350–450 | ~450 lines | `OpOk`/`AnswerOk` one line per arm; store protocol = `progress`; `HandlesFit`; `DeferredNat` + four preservation lemmas |
| L2 typed stack, `popR_typed`, glue | in S2 | in S2 | 600–800 lines | the one hard delivery lemma, seven cases with masks and deferred interrupts |
| S1 | 1,400–2,200 / 56 | 700–1,000 / 35 | 1,000–1,500 / ~55 | short arms, same count; hook bodies added |
| S2 | 3,000–5,000 / 65 arms | 1,200–1,800 / 25 | 2,000–3,000 / ~70 | families (a)–(e) of §4; `InterpTyped` ~14 fields |
| S3 + battery | 300–550 | 250–400 | ~350 | as the scout |
| **total** | **5,300–8,600 / ~150** | **2,620–3,830 / ~75** | **4,500–6,300 / ~130** | |

The cut against the scout is 20–30 %, not 55 %. The larger gain is structural: every S2 arm is
a small goal against a named lemma, the two hardest pieces (`popR_typed`, the fork/spawn/start
triple) are proved once, and the async route is a column beside `HeapNat` instead of a
discovery in the middle of S2.

## 7. Rulings owed (three, one of them already open)

1. **`HandlesFit`** (open since the scout): add the world-satisfaction field, leave
   `Val.hasTy` coarse. Unchanged recommendation; §2 gives it its principled reading.
2. **`DeferredNat`**: widen the machine-level deferred invariant from "is a completion" to
   "is a completion typed at the cut's `⟨nat, nat⟩`", the twin of `HeapNat`, preserved by the
   completing rows' typed requests. Needed for the `async` clause; recommended.
3. **Layer 0's home**: `src/Effect4/Laws/Effects/Protocol.lean` now (imports the pinned
   `Effects` only); upstream or vendor later. Recommended; the pull-in is not on the path.

## 8. The order, amended

Move 1 (`evaluateR_*` into `EvaluateR.lean`) → `Keeps.lean` → **L0 `Protocol.lean`** (the
probe, generalised to the file) → L1 in `Typed/Residual.lean` with `OpOk`/`AnswerOk`, the
world, `HandlesFit`, and `DeferredNat` beside `HeapNat` once ruled → **L2 `Typed/Stack.lean`
with `popR_typed` first**, because it is the risk → S1 by combinator lemmas, hook bodies last →
`InterpTyped` → S2 families (d), (c), (a) in that order (frame, delivery, operations) → S3.

The aesop set of scout §C stands with three changes: `Typed.vis` is the constructor rule (its
world quantification is what `aesop` needs to instantiate, so `Typed.inr_inv` is `safe
destruct`), `OpOk` joins `AnswerOk` as `norm simp`, and `Later`'s forward rules are joined by
`WorldLe.trans` as `safe forward`.

## Appendix: probe Q1

`scratchpad/probe/Q1_protocol.lean` in this session's scratch directory, copied to
`docs/research/probes/2026-09-18-Q1_protocol.lean` (force-added). Built with `lake env lean`
against the tree at `1246d121`:

```
'Probe.Typed.mono' does not depend on any axioms
'Probe.Typed.bind' does not depend on any axioms
'Probe.Typed.inl' does not depend on any axioms
'Probe.Typed.inr_inv' does not depend on any axioms
```

Two slips on the way, both binder hygiene under `autoImplicit false` (an unbound `w`, and a
`bind`/`widen` continuation hypothesis not passed through the induction); neither touches the
design.
