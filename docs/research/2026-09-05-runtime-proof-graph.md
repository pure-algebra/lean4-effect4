# The runtime's proof graph: admitted Eff programs and Effect v4 behavior

## Current graph and authority, 2026-09-06

The owner's goal is the generic machine running arbitrary admitted programs
through Eff/NativeEff, with the established closure limit. The pinned Effect
v4 TypeScript implementation is the ground truth and guidance for semantics.
The theorem domain is the admitted IR, not a finite test corpus or a request
to implement general JavaScript. The original reader-image wording and
signatures below are historical and do not narrow this goal.

[The revised synthesis](2026-09-06-wave2-synthesis.md) owns the next work order;
[the wave-2 audit](2026-09-06-wave2-audit.md) and
[checkpoint audit](2026-09-06-p0-checkpoint-audit.md) own their findings. Implementation
is paused at a1fb467. These edges supersede the earlier dispatch graph:

| Obligation | Depends on | Current status |
| --- | --- | --- |
| Source-defined behavior | Pinned TypeScript implementation/API, printed constructors and the admitted IR domain | P0 first inventories/checks the source/reference connection. Executed exit/gen/loop discrepancies and yield/resume phases require named corrections before broad simulation. |
| SIM/checkpoints | Corrected source/reference contract; counted entry, uncounted delivery and selected next code | Next prototype. Blanket marker folding/uniform tick are refuted. Distinguish operation-answer slots and source handlers; prove local outcome/nested-command clauses. |
| SIM/address | Point addresses the source being compiled/denoted | Existing resolve_of_at and child laws reused; missing premise exposed by the audit. |
| SIM/unfolding | Runtime loop/generator prototype; actual continuations and residual state | Prefer removing the extra unfolding budget with checked runtime back edges. Otherwise prove adequacy before introduction. Source addresses and compile/scan/choice/unsupported frontiers remain either way. |
| SIM/actions | Existing FiberCore/WithFiberAction and source-grounded adapter laws | Shared extraction follows the corrected reference baseline, serialized with term evaluator work. One generic getId case is checked. Masks and park/cancel inputs retain their own obligations. |
| SIM/invariant and local steps | Checkpoints, address/unfolding obligations and actual interpreter hooks | Reuse delivering-tail closure, cleanup joint state and minimal list relations. Old BookMeans remains a candidate to correct. |
| SIM/commands and decisions | Local steps plus related residual work, core operations and queued/race code | Conditional scouting lemma exists; real hypotheses and stuttering lift remain open. |
| AGR/replay | SIM/decisions and both sufficient receipts at fixed initial code | run_eq_ref remains open, with its exact domain and direction to be frozen. |
| REF/base (R5) | AGR/replay plus existing frame replay_Mexit/run_eq_meaning | Short corollary path checked. Old fixed fuel bound needs a sufficiency bridge. No separate localRunR/OwesR lane. |
| IR/acquisition and PROV/join | Source-defined ambient-scope registration; existing Scope/Layer protocols; captured code/resource/context | Open vertical integration. Do not replace acquisition lifetime with immediate onExit release. |
| IR/operation families and PROV/denote | Existing Eff/row/component owners, plus relevant runtime bridges | Extend admitted families without duplicating stores or canonical syntax. |
| Target conformance | Actual emitted/imported IR programs, pinned host and the named observations | Finite host evidence is separate from Lean-to-Lean proofs; reader round trips and common helpers do not establish it. |

AGR/congruence and optimization remain downstream of scheduling-sensitive
agreement. Dropping trace does not license folding observable yield
checkpoints. Runtime census coverage is not IR execution closure or host
conformance. No new module, calculus or companion record is required solely
to restate an already-owned operation.

## Historical graph and implementation checkpoints

Checkpoint 2026-09-06: R3/REF-state and R4/REF-step are implemented on the
shared loop; current contracts are `Test/contracts/program-runtime-r.contract.md`
and the amended `program-denote-r.contract.md`. Record:
`2026-09-06-r3-r4-implementation.md`. The older signatures below are sketches:
raw terms now retain control markers, straight restriction uses their explicit
erasure, and arbitrary frame/term simulation and R5 remain open.

Implementation checkpoint, 2026-09-06: the first-slice changes and checked
statement corrections are recorded in
[`2026-09-06-first-slice-implementation.md`](2026-09-06-first-slice-implementation.md).
W1, D1, D6, observation fuel independence and conditional finite fairness have
implementations and receipts. W3 has a checked external-answer counterexample
and awaits the input-domain ruling. No term scheduler or simulation has landed.
The plan and owed sketches below are retained as the original dispatch record.

Status: a plan, 2026-09-05 night, one seat. Nothing here is proved; the Lean in the fences
is the *shape* of each node, written so that a lane can start from it, and every fence is
marked owed. Reviewed for reuse against the tree in
`docs/research/2026-09-05-runtime-graph-reuse-review.md`, which also refines D5 to D5'.
Naming: the tree already calls `Fibers.lean` "the reference machine" (the Lean machine as
opposed to rc.112), so the second scheduler of Layer R is the **term scheduler**, `Sched`;
where this note still says "reference" of Layer R, read "term scheduler". The mathematics behind each layer is in
`docs/research/2026-09-05-runtime-semantics-core-math.md` (cited as "core math §n"); the
straight-line base is `docs/research/DENOTE-DAG.md`; the gaps G1–G8 and the abstractions
A1–A7 are `docs/research/2026-09-05-effects-papers-review.md`.

## Revisions from the probes (2026-09-05, late)

The strategy seat's findings (`2026-09-05-tactics-cheatsheet-dag-strategy.md` §0) override
the sketches below where they conflict: **F1** `frameMeaning` is a relation
(`CodeMeans`/`FrameMeans`), not a function, so read §4's `Sim` with "means" in place of
"equals"; **F2** ten machine types carry a `Prim` and the tape is one of them, so R1 holds
for six decisions and `answerAsync` must be re-cut to a first-order answer or translated
(C15 from the other side), and the D1 types need a universe pin; **F3** D5' is cheap;
**F4** bind non-recursed arguments before the colon in any definition with eleven or more
pattern arguments. Entry point for dispatches: `2026-09-05-dispatch-brief.md`.

## 0. The goal, and the two boundaries that do not move

The goal is to play any program the reader produces (`ts/eff`, the A4 reader, the OCaml
host) on the Lean machine, with a proof that what the machine does is the program's
meaning. "Meaning" past the straight line is a function of the host's decision tape
(DB-03): the same program on the same tape has one behaviour, and the theorems are
statements about that function. Closures are out by construction: a program is data, so
the reader is a reader and the run is a machine.

The two boundaries: every theorem is Lean machine against Lean semantics, and rc.112 stays
on the truth-tape and census side (never a bisimulation against it, arbiter ruling); and
the trace is not an observation (`E4-DEN-CE-003`), so the behaviour is exits and stores.

What exists tonight, in the graph's terms:

* `Api.replay e fuel tape` is the operational semantics (`Fibers.lean`): seven decisions
  (`fire`, `flush`, `evaluate`, `yieldVerdict`, `answerAsync`, `interruptFrom`,
  `installMiddleware`), eight commands, six observer kinds, twenty `withFiber` actions, the
  yield and async parks, Deferred with waiters, scopes, races, masks and interrupts.
* `meaning e env s` is the denotation of the straight-line fragment into
  `Effects.Program StoreSig` under the store handler, and `run_eq_meaning` is the agreement
  with no op-budget hypothesis (`Program/Agreement/Machine.lean`).
* G2, in flight: `driveState`, `drive_add`, stability, the trace extends, the observation
  order and the least sufficient fuel (`Machine/Approximation.lean`).
* Not joined: the logical clock (`workshop/Timer`), the WHATWG streams package.

## 1. The layers

```
E   equations on the algebra          Program + iter laws; meaning_* ; rewrite passes
A   agreement + congruence            Beh (load e) tape = BehR (loadR e) tape ; congruence
S   simulation, per feature           Sim m r  →  Sim (stepDecision d m) (stepR d r)
R   the term scheduler           fibers hold algebra terms; the same decisions, store,
                                      ids, tokens, dispatchers, races
B   behaviour over tapes              G2: fuel chain, order, colimit; Obs; Beh
L   liveness rows on Beh              Fair tapes, flush_fair, Deadlocked, Eventually
```

B is the semantics of the *machine* (any machine state, any tape). R is the semantics of
a *program*: the term scheduler over algebra terms, the handler of core math §5 written
as a state machine. S is the proof that the fiber machine simulates R, one decision at a
time, with fuel accounting. A is what S gives at the top, plus the congruence that makes
rewrite passes on `Eff` correct once for the whole runtime. E is the equational layer,
already present for the straight line, extended to iteration later. L states fairness and
deadlock on B and needs neither R nor S.

## 2. Layer B: the behaviour of a machine over tapes

The first three nodes landed with G2 the same night (`Machine/Approximation.lean`, 119
declarations, packet `Test/contracts/machine-approximation.contract.md`, note
`docs/research/2026-09-05-fuel-laws.md`); the names below are the landed ones. The last
two are the next small lane (`Machine/Behaviour.lean`, owed).

```lean
-- BEH/split (landed). Fuel is a chain within one unit of work: the loop with its residual
-- commands, and fuel splits.
def driveState (interp) : Nat → Machine → List Cmd → Machine × List Cmd
theorem drive_eq_driveState : drive interp n m c = (driveState interp n m c).1
theorem driveState_add :
    driveState interp (a + b) m c =
      driveState interp b (driveState interp a m c).1 (driveState interp a m c).2
theorem drive_add : drive interp (a + b) m c = drive interp b (driveState interp a m c).1 (driveState interp a m c).2
theorem drive_stable_of_done :
    (driveState interp n m c).2 = [] → ∀ k, drive interp (n + k) m c = drive interp n m c
theorem flushAll_stable : (flushAllState interp fuel rounds m).2 = true →
    ∀ k j, flushAll interp (fuel + k) (rounds + j) m = flushAll interp fuel rounds m

-- BEH/trace (landed). The trace only grows, through every helper the loop calls.
theorem drive_trace_extends : ∃ ev, (drive interp n m c).trace = m.trace ++ ev
theorem replayEval_trace_extends : …

-- BEH/order (landed). Frontiers are below what extends them; terminal results are maximal.
def ReplayResult.le : ReplayResult → ReplayResult → Prop
theorem replay_obs_mono_of_suffices : Suffices interp n tape m = true → n ≤ n' →
    ReplayResult.le (replayEval interp n tape m) (replayEval interp n' tape m)
-- and for one-decision single-loop tapes without the side condition:
theorem replay_frontier_mono_single, replay_stuck_mono_single

-- BEH/colimit (landed). "Fuel n suffices for tape from m", decidable, and the least such fuel.
def Suffices (interp) (fuel : Nat) (tape : List Decision) (m : Machine) : Bool
theorem replay_stable : Suffices interp n tape m = true → ∀ k,
    replayEval interp (n + k) tape m = replayEval interp n tape m
def leastSufficient (interp) (bound : Nat) (tape) (m) : Option Nat   -- hand-written bounded search
theorem replay_colimit, replay_colimit_eq_of_sufficient : …          -- sound, least, independent of the bound

-- BEH/obs (owed, small). The observation: every fiber's exit, and the stores.
-- Frame events are not observed (E4-DEN-CE-003).
structure Obs where
  exits : List (FiberId × Option ExitV)
  stores : Stores
deriving DecidableEq
def obs : Machine → Obs

-- BEH/tape (owed, small). The behaviour of a machine on a tape it settles, as a total
-- function of the tape (core math §2: the final Moore coalgebra is `List Decision → Obs`).
def Beh (interp) (m : Machine) (tape : List Decision) (fuel : Nat)
    (h : Suffices interp fuel tape m = true) : Obs :=
  obs (replayEval interp fuel tape m).machine
theorem Beh_fuel_irrelevant : Beh interp m tape n h = Beh interp m tape n' h'   -- from replay_stable
theorem obs_mono_of_le : ReplayResult.le r r' → obs r.machine ⊑ obs r'.machine   -- the projection is monotone
```

**The finding G2 made, and what it changes here.** The review's `replay_obs_mono` over an
arbitrary tape is false on this machine (`E4-APPROX-CE-003`, `E4-APPROX-CE-004`,
`APPROX-FB-REFRESH`): fuel is *refreshed* at every task in `fire`, every round in
`flushAll` and every decision in `replayEval`, and exhaustion is silent, so the next unit of
work runs on a half-done machine and the observations at fuel `n` and `n + 1` need not be
comparable. Monotonicity holds within one unit of work, and along a whole tape only under
`Suffices`. Consequences: `Beh` is defined only with the `Suffices` witness (as above,
which is what the plan wanted anyway); the Kleisli chain of core math §2 is a chain *per
unit of work*, not per tape; and there is a design point **D5**, the owner's call: make
the frontier sticky in `drive` (exhaustion recorded and absorbing, so the chain is a chain
along the tape and `replay_obs_mono` becomes true as reviewed), or leave the machine as it
is and keep every behaviour statement under `Suffices`. The plan works either way; D5
decides whether L (§7) can quantify over fuel at all or must quantify over sufficient fuel.

Design point D3: `Obs` is exits and stores only. G2's order is on the machine (trace
prefix), which is finer; `obs_mono_of_le` transports monotonicity along the projection so
nothing in G2 has to be restated.

## 3. Layer R: the term scheduler over algebra terms

The reference is the scheduler handler of core math §5, as a state machine, with three
design decisions that decide whether the simulation of §4 is tractable:

* **R1, the same decisions.** `stepR : Decision → RState → RState` consumes the machine's
  `RunDecision` unchanged. No tape translation, ever.
* **R2, the same bookkeeping.** `RState` reuses the machine's `Dispatcher`, `Task`,
  `Observer`, `Pending`, `Race`, the `armed` FIFO, `nextId`, `nextToken`, `nextRace`, and the
  very same `Stores` with the same `syncOpStep` and `dueResumes` (core math §7: one comodel
  on both sides). Ids and tokens are allocated in the same order by construction, so the
  tape's `answerAsync id token` names the same thing on both sides.
* **R3, fibers hold algebra terms, scoped operations carry addresses.** An R-fiber's code
  is a `Program RSig ExitV` plus a small scope stack. `RSig` extends `StoreSig` with the
  fiber operations, all first-order; the operations that enclose a program (`fork`, `mask`,
  `scoped`, `raceAll`, `finalizer`) carry a `Point` (an address into the root program with
  its environment), not a `Program`, because a program-valued operation parameter is not a
  positive definition (core math §5). The scheduler denotes the child at start.

```lean
-- REF/sig (owed). The fiber signature beside the store signature.
inductive FiberOp
  | fork (child : Point) (options : ForkOptions)            -- answers Val.fiber id
  | forkIn (child : Point) (options) (scope : Nat)
  | forkScoped (child : Point) (options) (key : Nat)
  | await (target : FiberId) (mode : ObserverMode)         -- parks; answers the exit value
  | awaitAll (targets : List FiberId) | awaitAllFailFast (targets : List FiberId)
  | yieldNow (priority : Nat)                              -- parks on the own dispatcher
  | async (register : NativeOp) (request : Val)            -- parks; answered by the tape
  | interrupt (target : FiberId) | interruptAll (targets) (interruptor : Option FiberId)
  | mask (flag : Bool) (body : Point)                      -- scoped: enter, run, restore
  | scoped (body : Point) | acquireRelease (acquire release : Point)
  | raceAll (entrants : List Point)
  | getId | getContext | setContext (ctx : Ctx)
  | snapshotChildren | awaitNewChildren (snapshot : List FiberId) | runIn (target) (scope) (key)
abbrev RSig : Effects.Signature := ⟨SyncOp ⊕ FiberOp, fun | .inl _ => Val | .inr _ => Val⟩

-- REF/denote (owed). The denotation of the whole IR into RSig terms, fuel-unrolled on loops.
-- `denote` (Denote.lean) is the straight-line restriction: denoteR n e env = denote e env
-- when Straight e, for every n.
def denoteR (fuel : Nat) : NativeEff → List Val → Effects.Program RSig ExitV
theorem denoteR_straight : Straight e = true → denoteR n e env = liftStore (denote e env)
theorem denoteR_whileLoop : denoteR (n + 1) (.whileLoop init test step body) env = …  -- one unrolling
theorem denoteR_gen : …                                                              -- one statement

-- REF/state (owed). The reference fiber and machine.
inductive ScopeFrame
  | restoreMask (flag : Bool)                -- the twin of Prim.setInterruptible
  | afterFinalizer (ex : ExitV)              -- the twin of the restore/merge continuations
  | closeScope (scope : Nat) (strategy)      -- the twin of the scope-close frame
structure RFiber where
  id : FiberId
  code : Effects.Program RSig ExitV          -- what is left to run
  scopes : List ScopeFrame
  interruptible : Bool
  interruptedCause : Option CauseV
  deferredInterrupt : Bool
  running : Bool
  parked : Parked
  pending : List Pending
  finalizing : Option ExitV
  exit : Option ExitV
  currentOpCount maxOpsBeforeYield : Nat
  preventYield : Bool
  yieldOverride : Option Bool
  observers : List Observer
  children : List FiberId
  dispatcher : Dispatcher
  context : Ctx
structure RState where
  fibers : List RFiber
  races : List Race
  nextId nextToken nextRace : Nat
  middlewareInstalled : Bool
  armed : List FiberId
  stores : Stores
  stuck : Option Stuck

-- REF/step (owed). One decision; the skeleton is stepDecision's with evaluateR in place
-- of evaluatePrim (see D1). evaluateR on `pure ex` is the exit path; on `perform (inl op) k`
-- it is syncOpStep; on `perform (inr fop) k` it is the fiber-level arm.
def evaluateR : RState → RFiber → Bool → IterR
def driveR : Nat → RState → List Cmd → RState
def stepR (fuel : Nat) : RState → Decision → RState
def replayR (fuel : Nat) : List Decision → RState → ReplayResultR
def loadR (e : NativeEff) (fuel : Nat) (choices : List Bool) : RState
def obsR : RState → Obs
def SufficientR (fuel) (tape) (r : RState) : Bool
def BehR (e : NativeEff) (tape) (fuel) (h : SufficientR fuel tape (loadR e fuel)) : Obs

-- REF/base (owed, first thing to prove about R). One straight-line fiber is the meaning.
theorem replayR_straight (hs : Straight e = true) (hfuel : …) :
    obsR (replayR fuel [Api.evaluate, Api.flush] (loadR e fuel)).state =
      ⟨[(Api.root, some (meaning e [] Stores.empty).1)], (meaning e [] Stores.empty).2⟩
```

Design point D1 (the owner's call, and the biggest lever on cost): should `RunMachine` be
made polymorphic in what a fiber holds, so that `drive`, `stepDecision`, `fire`,
`flushAll`, `replayEval` and every skeleton lemma of `Clauses.lean` (`fire_eq`,
`flushAll_round`, `drive_evaluate_*`, `drive_resume_*`, `drive_finish`, `drive_launch_*`,
`drive_link`, the observer lemmas) are shared by both instances? Today `RunFiber.frame :
FrameFiber` is concrete and `evaluatePrim`, `exitFiber`, `interruptRecord`, `runloopTop`
inspect it. The refactor makes the fiber's code a type parameter with a small
`FiberCore` interface (`evaluate`, `deferredInterrupt`, `setInterruptible`, `exitOf`,
`finalizerOf`) and instantiates it twice. Cost: a mechanical parameter added through
`Fibers.lean` and `Clauses.lean` (the same kind of edit as tonight's resume-token
parameter, on a larger surface), a coordinator seat, one gate. Benefit: R's skeleton is
not a copy but the same code, so R1 and R2 hold by construction and S never has to prove
that two copies of the scheduler agree. Recommendation: do it, before any S lane starts;
without it every skeleton lemma is proved twice and drifts.

Design point D2: loops by fuel-unrolling (`denoteR fuel`), not by an `iter` combinator. The
machine side is fuel-indexed already (`Point.fuel`, `compileEff` at fuel), so the agreement
is stated at every fuel above the sufficient one and the meaning of a loop is the join
(core math §2, §4). The `iter` laws are Layer E's business.

## 4. Layer S: the simulation, one decision at a time

The invariant relates a machine state and a reference state fiber by fiber. The heart of
it is the map from a frame fiber to an algebra term: what tonight's `localRun_compile`
proved along one run, stated as a function of any reachable frame stack.

```lean
-- SIM/inv (owed; the crux). The meaning of a frame stack: the current primitive, then each
-- frame's continuation, each an address resolved through interpOf (contAOf/contEOf).
def codeMeaning (root : NativeEff) (fuel : Nat) : NCode → Effects.Program RSig ExitV
def frameMeaning (root) (fuel) (fr : NFiber) : Effects.Program RSig ExitV
def scopesOf (fr : NFiber) : List ScopeFrame              -- setInterruptible frames, restore/merge names, scope-close frames
def Addressed (root) : NFiber → Prop                       -- every frame is one the compile emits or a hook answers, at an address in root (PlainCode/PlainFrame, generalised)
def fiberOfR (root) (fuel) : RFiber → NRunFiber            -- the machine fiber a reference fiber stands for (up to the frame stack)
def Sim (root) (fuel) (m : Machine) (r : RState) : Prop :=
  m.fibers.length = r.fibers.length ∧
  (∀ i, Addressed root (m.fibers[i]).frame ∧
        frameMeaning root fuel (m.fibers[i]).frame = (r.fibers[i]).code ∧
        scopesOf (m.fibers[i]).frame = (r.fibers[i]).scopes ∧
        eraseCode (m.fibers[i]) = eraseCode (fiberOfR root fuel (r.fibers[i]))) ∧
  m.armed = r.armed ∧ m.nextId = r.nextId ∧ m.nextToken = r.nextToken ∧ m.nextRace = r.nextRace ∧
  m.races = r.races ∧ m.middlewareInstalled = r.middlewareInstalled ∧
  m.state = r.stores ∧ m.stuck = r.stuck ∧
  Minted m                                                 -- G5: every Val.fiber/promise/scope handle names a fiber, a cell, a scope that exists

-- SIM/local (owed; tonight's Layer A re-cut as an invariant step). One local step of a
-- plain frame fiber is zero or one `interpret` step of its meaning.
theorem frameMeaning_step : Addressed root fr → localStep root fr s = .running fr' s' →
    (frameMeaning root fuel fr' = frameMeaning root fuel fr ∧ s' = s) ∨
    (∃ op k, frameMeaning root fuel fr = .perform (.inl op) k ∧ syncOpStep op s = some (s', v) ∧ frameMeaning root fuel fr' = k v)

-- SIM/decision (owed; the theorem of the layer). Every decision preserves Sim, with fuel.
theorem sim_stepDecision (d : Decision) (h : Sim root fuel m r) :
    ∃ c, ∀ F, c ≤ F → Sim root fuel (stepDecision (interpOf root) F m d) (stepR F r d)
```

The per-feature lemmas are the arms of `sim_stepDecision`, one per `evaluatePrim` arm, per
command, and per observer. Each is the shape of tonight's `drive_loop_running`: the machine
does one or two commands, the reference does one `evaluateR`, the bookkeeping matches by
`rfl` on records, the fuel bound is carried as `∃ c`.

| lemma (owed) | machine arm | what the reference does | new ground |
| --- | --- | --- | --- |
| `sim_local` | `stepFrame` on plain code | zero steps (the term is unchanged) | none: `frameMeaning_step` |
| `sim_sync` | `Prim.sync` store thunk, `drainDue` | `perform (inl op)`; the same `syncOpStep`, the same `dueResumes` | drops `Quiet`: due resumes are commands on both sides |
| `sim_yield` | `injectYield`, `Prim.yieldNowWith` | `yieldNow`: park, task, arm | `Myield`, `fire_Myield`, with the priority |
| `sim_fork` | `withFiber (fork/forkIn/forkScoped)` | `fork p`: a fresh id, `Task.start`, `untrackChild` observer, the child's code is `denoteR fuel (at p)` | the child's `Addressed` and `frameMeaning` at start: `compile` at an address vs `denoteR` |
| `sim_await` | `parkOf` join park, `resumeAwait` observer, `exitValue mode` | `await id mode`: park; the target's exit path resumes | `Minted` for the handle |
| `sim_async` | `Prim.async`, `register`, `answerAsync`, cancel names | `async op req`: register on the store, park or answer now | the `AsyncFinalizer` frame on interrupt |
| `sim_mask` | `setInterruptible` frames, `runloopTop_deferred`, `interruptRecord` | `mask flag p`: push `restoreMask`, run the body | interrupts applied when the mask lifts; the cause algebra |
| `sim_interrupt` | `interruptFrom`, `interrupt`, `interruptAll` | the same records on `RFiber` | the deferred interrupt under a mask meets `sim_mask` |
| `sim_scope` | `link`, `dropScopeFinalizer`, scope-close programs | `scoped p`, `acquireRelease`, `closeScope` frame | D4 below: synthesized programs |
| `sim_race` | `launch`, `raceCallback`, `accepted`, `raceResume` | `raceAll ps`: fork the entrants in order, first settle wins, interrupt the rest | after `sim_fork`, `sim_interrupt`, `sim_await` |
| `sim_loop` | the compile's loop and generator code at `Point.fuel` | `denoteR (n+1)` unrolled once | the sufficient fuel is a function of the reference run's length |
| `sim_exit` | `exitFiber`: observers in order, children untracked, middleware | the same, on `RFiber` | `installMiddleware` |
| `sim_context` | `setContext/getContext/getId`, the budget fields | the same fields | none |

Fuel accounting, as tonight: `∃ c` commands per reference step, `c ≤ 2` for local and store
steps, and for a yield round the reference loses at least `defaultBudget - 1` steps. The
induction of `sim_stepDecision` is on the commands, not on a program, because after `fork`
there is no single program to recurse on; the term `code` of each fiber is what shrinks.

## 5. Layer A: agreement and congruence

```lean
-- AGR/behaviour (owed; the top theorem). For every program the reader produces, on every
-- tape the reference settles, the machine settles and observes the same thing.
theorem run_eq_ref (e : NativeEff) (choices) (tape : List Decision) (fuel : Nat)
    (h : SufficientR fuel tape (loadR e fuel choices) = true) :
    ∃ fuel' h', Beh (interpOf e) (Api.load e fuel' choices) tape fuel' h' = BehR e tape fuel h

-- AGR/straight (owed, a corollary): run_eq_meaning recovered through REF/base.
-- AGR/fuelFor (owed, a corollary): the sufficient machine fuel is computed from the
-- reference run's command count — G2's fourth theorem for Eff, for free from the ∃ c.
theorem fuelFor_sufficient : Sufficient (interpOf e) (fuelFor e tape) tape (Api.load e _) = true

-- AGR/congruence (owed). Two programs with the same reference behaviour on every tape are
-- interchangeable under every context of Eff (core math §1, the handler-correctness route
-- of §5: the scheduler is a homomorphism out of the free algebra, so equal terms up to the
-- handler's equations run equally).
def EffCtx : Type                       -- one-hole contexts of Eff
theorem ref_congruence (h : ∀ tape fuel hs, BehR e₁ tape fuel hs = BehR e₂ tape fuel hs') :
    ∀ (C : EffCtx) tape fuel hs, BehR (C.fill e₁) tape fuel hs = BehR (C.fill e₂) tape fuel hs'
theorem run_congruence : … -- through run_eq_ref on both sides
```

What the congruence unlocks in the estate: the printer's inlining of pure statements
(`iteratorFolded`), the A4 reader's round trip, `ts/eff`'s reading, any rewrite pass on
`Eff`, and the host conformance oracle: a host agrees with the machine when it agrees with
`BehR` on the corpus, per tape.

## 6. Layer E: the equational layer (later)

`meaning_*` exists for the straight line. E extends it to the fiber operations as
equations on `RSig` terms under the scheduler (what commutes with what: two pure steps of
different fibers commute, G3 `term_central`; a `fork` followed by `await` on its handle is
the child's meaning, on a tape that fires it), and to iteration through the Elgot laws
(core math §4) once loops have an `iter` reading beside the fuel one. The bind law's side
condition (G8) lives here. Nothing in A depends on E.

## 7. Layer L: liveness rows on B

```lean
-- LIVE/fair (owed, small, independent of R and S).
def FairTape (m : Machine) (tape : List Decision) : Prop      -- every armed owner is eventually fired, every parked async eventually answered
theorem flush_fair : the round-robin of flushAll on the armed FIFO fires every armed owner (R2-15)
-- LIVE/deadlock (owed, G6).
def Deadlocked (m : Machine) : Prop := m.finished = false ∧ ∀ d, d ≠ interrupt → obs (stepDecision _ m d) = obs m
-- LIVE/eventually (owed, G7). Under a fair tape a fiber that is not blocked on an unanswered async exits.
```

## 7a. Layer P: provision, the Effect TS layers

Layers are reified twice already, and both halves are reused as they stand.

* **The Layer machine** (`src/Effect4/Machine/Layer.lean`, 2047 lines, 42 theorems, in the
  default library): rc.112's `Layer.ts` transcribed as *a second instantiation of the same
  fiber machine* over its own alphabets (`interp : LayerTable → RunInterp Name Thunk Val Err
  Defect FiberId Ann Ctx St`, line 1224), with the memo world (`MemoMap`, `MemoEntry`,
  `memoBuild_*`, `memoRelease_*`, `memoGet_hit`, `memoize_hit`), the ambient scope
  (`build_uses_ambient_scope`, `buildWithScope_forks_memo`), parallel merge
  (`mergeAll_scopes`, `mergeExitContexts_*`), and six `SHIM` copies of the Deferred and
  scope stores marked for merging into `Stores.lean`. The sixteen `layer.*` census rows are
  witnessed on it (disposition `separateCalculus`). Identity is `LayerId` into a declared
  `LayerTable`, the model's stand-in for rc.112's memo map keyed on the layer object.
* **The provision algebra** (`src/Effect4/Program/Provision.lean`, 882 lines, 22 theorems):
  requirement rows over `ServiceKey` with `Row.diff`, `LayerTy` and the laws of `provide`,
  `provideMerge`, `merge`, `orDie` on signatures, the first-order `LayerTerm` (one
  constructor per rc.112 export the corpus uses, `Eff` bodies at the `effect` leaves),
  `App` for `Effect.provide(program, layer)`, and `build : LeafSem → LayerTerm → Ctx → Option
  Ctx`, the *specification* of provisioning, with `build_total`; `lower` sends a term into
  the machine and `lower_refines_build` is the owed refinement theorem (the provision note
  §9, row R3). The context laws (`Machine/Context.lean`, about forty-five theorems on
  `lookup`, `setEntries`, `merge`, `satisfies`, `usesOnly`) are the algebra of `Ctx`.
* **What the main compile does today**: the Layer and Context rows of `Eff` are
  `RowKind.program` and compile to the frontier (`Compile.lean` line 16), and `scoped`
  compiles to `scopeProvide` (`getCtx`, then `setCtx` with the ambient scope, lines
  559–565). So `Effect.provide` is modelled and witnessed on the layer instance, but not yet
  played by the one machine that plays the rest of a program.

The nodes:

```lean
-- PROV/join (owed, coordinator: Stores.lean and Compile.lean are shared surfaces). The
-- alphabet merge the S5 spike planned: the layer instance's shims become Stores' own
-- Deferred and scope stores, the memo world becomes a store component with its SyncOp
-- rows, the layer interp's hooks become arms of interpOf, and RowKind.program rows compile
-- into the machine instead of the frontier. After it, one machine plays layers.
-- PROV/denote (owed). A LayerTerm denotes a scoped program producing a context:
def denoteLayer (fuel : Nat) : LayerTerm NativeOp → Point → Effects.Program RSig (Option Ctx)
--   provide: build the layer in the ambient scope, then setContext (previous.add …) around
--   the body, which is what scopeProvide already spells; merge: fork the parts into parallel
--   scopes (sim_fork); memoization is a store effect, not a term.
-- PROV/spec (owed, R3 of the provision note): the context the machine builds is build's.
theorem lower_refines_build : keysRow (decode (machine's built context)) = keysRow (build sem term ctx)
-- PROV/sharing (owed): the memo rows as invariants of Sim — built once per memo map,
-- finalizer at the last observer, fresh drops sharing — consuming memoBuild_*, memoRelease_*.
-- PROV/identity (row): LayerId allocation identity versus rc.112 object identity versus the
-- CAS address of the layer document; two structurally equal layers are one by address and
-- two in rc.112 (E4-PROV-CE-007's sibling; G5 allocKey).
```

Dependencies: PROV/join after `sim_sync` and the clock join (C11) share the `Stores`
change; PROV/denote and PROV/sharing after `sim_scope` and `sim_fork` (a merge is a fork
into parallel scopes). The Layer machine's 42 theorems are the machine-side equations of
`sim_provide`, as `Clauses.lean`'s are for the other features. Layer E gets the row laws
(A1: rows as free-variable sets, `provide` as substitution) from `Provision.lean` as they
are.

C16 (reader). `ts/eff/read.ts` does not read `Layer.*` or `Effect.provide`; the corpus has
layers on the print side (`Codegen/Layer.lean`). "Play any Effect TS program" needs the
reader to produce `LayerTerm` and `App`, a reader lane, not a proof lane.

## 8. Foreseen challenges

C1. **Two schedulers or one.** If D1 is refused, R copies the skeleton and S must prove the
copies agree on every command that touches no fiber code, roughly the clause set of
`Clauses.lean` a second time. Mitigation: D1.

C2. **From runs to an invariant.** Tonight's simulation follows one compiled program; S
needs `frameMeaning` defined on *every reachable* frame stack, including the lazily
resolved continuations (`EffName.cont p` answered by `resolve`), the restoring frames a
mask leaves, and the finalizer program's `restore`/`merge` names. `Addressed` is the
invariant that every such frame is at an address in the root; `plain_at`, `resolve_of_at`,
`suspendBodyAt_*` are its pieces. Risk: `frameMeaning` on `Prim.onExit b fin false` needs
`finalizerProgram fin ex` for an `ex` not yet known; it is a function of the exit, so the
term is `bind (meaning of b) (fun ex => bind (denoteR (fin at ex)) …)`, which is what
`denote (.onExit b f)` already is. The definition is by recursion on the stack with an
accumulator; the lemma `frameMeaning_step` is the whole of tonight's step lemmas restated.

C3. **Loops have no term.** `Program` has no iteration; `denoteR` unrolls by fuel (D2), so
the reference fiber's code depends on the fuel, and `frameMeaning` must agree with the
compile's `Point.fuel` accounting: the compile of a loop at `Point.fuel = n` and
`denoteR n` must unroll in step. Risk: `compileEff` charges fuel per child (`childWith`)
while a denotation charges it per iteration; the two measures differ by a constant factor
per constructor, which the `depth` function already tracks for the straight line. Plan:
define `denoteR` on points, not on terms (`denoteR : Point → Program …`), so both sides use
the same fuel field.

C4. **The observation and G2's order.** G2's order is `ReplayResult.le` on the machine's
trace, so D3's projection lemma `obs_mono_of_le` is the join. And the fuel refresh
(§2, D5): any statement of the form "for all fuel above n" must go through `Suffices`, or
D5 must land first. `sim_stepDecision`'s `∃ c, ∀ F ≥ c` is stated per decision with the
reference's own fuel, so it is unaffected; `run_eq_ref` carries `SufficientR` explicitly.

C5. **Masks and interrupts.** The deferred interrupt is applied at `runloopTop` when the
mask lifts, the cause merges through `Exit.restoreAfterFinalizer`, and an interrupt during
a finalizer must not re-enter it. The frame side is modelled (tonight's `exitFrom`,
`maskStack`, the interruptible flag); the reference side needs `restoreMask` frames and the
same `interruptRecord`. Risk: `interruptFrom` runs `drive [evaluate target]` *inside the
decision* when the interrupt applies now, so `sim_stepDecision` for that decision has a
nested simulation; keep `sim_evaluate` as a lemma callable from a decision.

C6. **Races.** `Cmd.launch` forks entrants one per command (R2-11: once accepted, no more
entrants), `raceCallback` observers settle the race, the host resumes with the interp's
`raceResume` program, and the losers are interrupted through `interruptAll`. The reference
`raceAll ps` must reproduce the launch order and the accepted latch exactly. Dependencies:
`sim_fork`, `sim_await`, `sim_interrupt`. Large.

C7. **Programs the runtime synthesizes.** Scope-close programs (`closeProgram scope
strategy`), the race-resume program, `interruptAll` programs and the `AsyncFinalizer`
cancel programs are `Prim` terms built by `interpOf` at run time, not compiled from an
`Eff` subterm; `frameMeaning` has no address for them. Design point D4: give each a
denotation directly (`closeMeaning strategy finalizers : Program RSig ExitV`) and prove the
interp's `Prim` for it has that meaning, once per synthesized shape. Four shapes, each a
small lemma in the style of `compileEff_*`; but it is a `Compile.lean` reading, a shared
surface, so a coordinator seat.

C8. **Async and cancel names.** `Prim.async register withSignal cancel` registers a waiter
on the store through `interp.register` and may answer immediately; the tape's
`answerAsync id token` resumes it; on interrupt the cancel program runs under a name the
interp attaches to the waiter (`asyncCancelNameOf`). The reference must keep the same
waiter identity in the same store cell, which R2 gives. Medium.

C9. **`choose`.** Decided at compile time by `choices`; `loadR` takes the same list. Easy,
but every theorem carries `choices`.

C10. **Engineering traps, met tonight.** (a) `omega` on a goal that is not arithmetic (an
`∃`) negates it classically and brings `Classical.choice`; close by `absurd`. (b) `decide`
on a measure of a deep program term hits `maxRecDepth`; use the measure's closed form by
induction and `omega`. (c) `rw` needs the literal `n + 1` shape; take fuel apart with
`obtain ⟨f, rfl⟩ : ∃ f, F = f + 1 + 1 + c`. (d) Threading one more bookkeeping field through
the machine abstraction (`nt` tonight) touched twenty-five statements; carry the bookkeeping
as one record parameter from the start. (e) `rcases` on the `Stores` constructor breaks
when `Stores` gains a field (C11); state store facts through projections. (f) Record
equalities by `simp` risk `Classical.choice` through decidable-equality lemmas; keep `rfl`
lemmas like `M_update`. (g) Every new `evaluatePrim` arm wants its clause lemma in
`Clauses.lean`, a shared surface; batch them per wave.

C11. **The clock.** Not in `Stores`; the timer spike's store is a `Stores` field to add, the
tape gains a time decision (`advance steps`), and `dueResumes` gains fired timers. Breaks
constructor patterns (C10e) and every `Quiet`-style lemma. Coordinator seat, one wave of
its own, after `sim_sync` exists so the new due source has a home.

C12. **Streams.** Not the fiber machine's rows; the WHATWG package's own coinduction. The
join is the reader's mapping of stream constructs to generators; state it as a row on the
reader, not on R.

C13. **Handles (G5).** `sim_await` needs the awaited handle to name an existing fiber;
`Minted` is the invariant, and it is also `handles_minted` of the earlier review. Land it
first, on the machine alone, as an agent lane.

C14. **Fairness needs the tape quantified.** L's rows are over sets of tapes; once tapes
are quantified, `choose` and the FIFO become branching, and the choice-tree machinery
(core math §4) is the reference. Not before L.

C15. **The decision alphabet is frame-typed.** Measured on `Fibers.lean`: the answer of
`RunDecision.answerAsync`, of `Task.resume` (the yield's own resume, line 760) and of
`Cmd.resume` (line 1199) is a `Prim`; a join resumes with `interp.exitValue exit mode : Prim`
(line 811), a race with `raceSettle`, an interrupt writes `Prim.failure cause` into the
current (lines 570, 738). So "the same decisions" (R1) cannot mean the same Lean type on
both sides unless the term scheduler can take a `Prim` as an answer. Two readings: (a)
the term scheduler reads tape-provided code through `codeMeaning` (total on `Addressed`
code, a defect otherwise), and every theorem carries `TapeAddressed root tape` (every
answer on the tape is code the compile could have emitted at an address); (b) D1 makes
the answer type part of the fiber-core parameter, `RunDecision`/`Task`/`Cmd` become
polymorphic in it, and `Sim` relates a machine tape to its image under `codeMeaning`, so
R1 weakens to "the same decisions up to the answer map". Reading (a) keeps R1 literal
and is the one the plan takes; reading (b) is what D1 forces if the decision types are
threaded through the parameter. The D1 design must choose: keep `Prim` as the universal
answer currency with an `inject : Prim → κ` field on the core (the frame instance's
identity, the term instance's `codeMeaning`), or thread the answer type. Recommendation:
`inject`, so that tapes, batteries and the witnesses stay as they are. Measured on the
tree: every `answerAsync` on an existing tape (seven, in `Witnesses.lean` and
`CompileContract.lean`) answers with `Prim.success v`, a leaf whose meaning is
`pure (Exit.success v)`, so `TapeAddressed` holds for every battery there is once
`Addressed` admits value leaves, which it must anyway.

## 9. Waves, lanes and the split

Two seats at a time, as tonight; the coordinator takes the crux of each wave.

| wave | lane | seat | depends on | size |
| --- | --- | --- | --- | --- |
| 0 | G2: BEH/split, BEH/order, BEH/colimit | agent (in flight) | — | medium |
| 1 | D1: the fiber core as a parameter of `RunMachine`; `Clauses.lean` re-elaborated | coordinator | — | medium, one gate |
| 1 | C13 `Minted` (`handles_minted`) on the machine | agent | G2 landed (for the lock) | small |
| 1 | BEH/obs, BEH/tape (`Machine/Behaviour.lean`) | agent, after C13 | G2 | small |
| 2 | REF/sig, REF/denote, REF/state, REF/step, REF/base | coordinator | D1 | large |
| 2 | LIVE/fair, `flush_fair` | agent | BEH/tape | small |
| 3 | SIM/inv, SIM/local, `sim_sync`, `sim_yield`, `sim_exit`, `sim_context` (the straight line plus yields as an invariant; AGR/straight recovered) | coordinator | REF | large, the crux |
| 3 | `sim_fork`, `sim_await` | agent, paired with the coordinator's SIM/inv | SIM/inv | medium |
| 4 | `sim_mask`, `sim_interrupt` | coordinator | SIM/local | medium |
| 4 | `sim_async` | agent | `sim_sync`, `sim_interrupt` | medium |
| 5 | D4 synthesized programs; `sim_scope` | coordinator | `sim_mask` | medium |
| 5 | `sim_loop` and AGR/fuelFor | agent | SIM/local, D2 | medium |
| 6 | `sim_race` | coordinator | fork, await, interrupt | large |
| 6 | AGR/behaviour, AGR/congruence | agent | all `sim_*` of the fragment claimed | medium |
| 7 | C11 the clock | coordinator | `sim_sync` | medium |
| 7 | LIVE/deadlock, LIVE/eventually | agent | LIVE/fair | medium |
| 7 | PROV/join (the alphabet merge: shims into `Stores`, memo world as a store, program rows compiled) | coordinator, with C11 | `sim_sync`, `sim_scope` | medium |
| 8 | PROV/denote, PROV/spec (`lower_refines_build`, R3), PROV/sharing, PROV/identity | agent, then coordinator for the `Sim` rows | PROV/join, `sim_fork`, `sim_scope` | large |
| later | Layer E: `iter`, G3, G8 | either | AGR | open |

Every lane lands the same way: module, battery with `#guard` on explicit tapes
(`Api.replay e fuel tape`, the pattern of the `yielded` guard), axiom report, packet
ENSURES, register rows, one narrow build under the lock, the coordinator's gate.

## 10. Rows to file as the graph grows (refusals by name)

* the trace is never observed (`E4-DEN-CE-003` stays);
* nothing about rc.112, never a bisimulation against it;
* `runSyncExit` flushes the root's dispatcher only (R2-14): `Beh` under `runSync` is a
  different entry and gets its own row;
* the bind law only for neutral stacks (G8) until Layer E;
* closures: not representable, by construction, one row on the reader;
* the middleware latch (`installMiddleware`) is a tape decision, not a program's: `Beh`
  is stated per tape, so two tapes differing only there may differ in observation, and
  that is not a defect;
* `choose` is compile-time: the same program with different `choices` is a different
  loaded machine, not a nondeterministic run.

## 11. Decisions asked of the owner

* **D1** share the scheduler skeleton by making the fiber core a parameter (recommended),
  or copy it into the reference and prove the clauses twice;
* **D2** loops by fuel-unrolling in the reference (recommended), `iter` later in Layer E;
* **D3** the observation is exits and stores (recommended), no trace;
* **D4** synthesized runtime programs get direct denotations, proved once per shape;
* **D5** a sticky frontier in `drive` (exhaustion absorbing, fuel monotone along a tape,
  `replay_obs_mono` as reviewed becomes true) versus the machine as it is with every
  behaviour statement under `Suffices` (G2's finding, `APPROX-FB-REFRESH`). A sticky
  frontier changes `Fibers.lean` and every clause that unfolds `drive`; it is the more
  honest machine (rc.112 has no fuel, so exhaustion is the model's artefact and should not
  be silent), and it is a coordinator seat with one gate, best done together with D1.
