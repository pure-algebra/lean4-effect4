# Runs, tapes, hosts, liveness and lowering: what the API needs next (2026-10-03)

Lead note after M6 closed (`053aa3d9`) and M7a–c followed (`4dcb2bfa`). The owner's ask: a grounded
theoretical discussion of liveness, reachability, host answers, tapes, runs, the host session API
and lowering, generalized across the program fragments (straight, looped, scheduled, layers), so
that the next theorems serve robust, expressive APIs for authoring, manipulating and composing
non-trivial first-order program data as monads. Every claim about the tree below names its file;
the two probes are reproducible (§8).

**First.** The typing spine is general and done: every checked program, of every fragment, keeps
the typed state on every answer-free run, and the frame machine's observation is typed. What the
API goal needs next is not more typing. It is three things the tree does not yet have:
1. an **observational preorder with congruence**, which composition laws, optimizations and
   lowering all have to be stated against;
2. **host-checkable admission**, so the public session route carries the typed guarantee;
3. **operational progress**, so a stopped run names what it waits for.

Liveness proper comes after progress.

## 1. The objects, precisely

- **A program is data.** `Eff` is the free object of its signature (AGENTS.md vocabulary; the
  nodes in `Program/Eff.lean`). `bind` is a constructor, not a function. Every traversal is a fold
  (`cata_eff`; the traversal census). Points address nodes by path (`Node.at_`,
  `Program/Refs.lean:44`), and checking is a fold with located refusal (`Checker.check`).
- **A machine** is `RunMachine` (`Machine/Fibers.lean`): fibers, races, stores, counters, a
  `stuck` marker. It has two implementations:
  - the frame machine, running `compileEff`'s first-order code (`Api.replay`);
  - the term reference (`replayR`, `Laws/Program/InterpR.lean`).
- **A decision** is one of eight choices:
  - `evaluate id` (run a fiber);
  - `fire owner` and `flush` (dispatcher work);
  - `advance millis` (the clock);
  - `yieldVerdict id v`;
  - `interruptFrom i anns target`;
  - `installMiddleware`;
  - `answerAsync id token answer` (a host answer).

  (The constructors are read off `Laws/Machine/Approximation.lean:1475-1482`.) Every source of
  nondeterminism is a decision: scheduling, time, external interrupts and the host. Nothing else
  chooses.
- **A run** is the fold of `stepDecisionState` over a tape from the loaded machine, under a
  per-command budget (`replayEval`, `Machine/Lift.lean`). For a fixed tape the run is a function.
  Fuel exhaustion and an unanswered call are frontiers, never errors (AGENTS.md representation
  rules).
- **The observation** is `obs m`: each fiber's id and exit, and the stores
  (`Laws/Program/Typed/Assembly.lean`, `ExitsFit`/`StoresFit`), with the outcome classified
  (`classify`).
- **Reachability** is `RReachable root fuel m := ∃ tape, (∀ d ∈ tape, NoHostAnswer d) ∧
  m = (replayR root.program fuel tape).machine` (Assembly.lean). It is answer-free by design:
  `E4-SCHED-CE-015` (a `sleep` answered with `42`).
- **The host session** (`Api/HostSession.lean`) offers `start`, `bindCall`, `preflight`, `submit`,
  `applyReply`, `applyPending`, `advance`, `retire` and `inspect`. `advance` refuses a plain
  `answerAsync` (`:239-243`), so a reply enters only through `submit` and `applyReply`, which
  admit it (`Program/Admit.lean`).

**The semantic stance this gives, and which the API should keep.** A program's meaning is its
**behaviour**: the map `Beh(e) : Tape → Obs × Outcome`, deterministic per tape, all choice in the
tape. This is the coalgebraic Moore reading the semantics doc already cites for concept 10 (Jacobs,
`semantics.md` §2.10). Equivalence, refinement, laws and lowering are all statements about `Beh`.
A denotation such as `meaning` (`MeaningSound.lean`) is a canonical representative of `Beh` on a
fragment, not a second semantics.

## 2. What is proved, fragment by fragment

| Fragment | Typed state (M5, M6) | Frame = reference | Meaning agreement | Observation typed (M7a–c) | Host answers |
| --- | --- | --- | --- | --- | --- |
| Straight (one fiber, sync rows) | yes | yes (`run_eq_ref`) | `run_eq_meaning`, `meaning_typed` (`Agreement/Machine.lean:1922`, `MeaningSound.lean:742`) | yes | none in the fragment |
| Looped (`iterate`) | yes | yes | `loopAgreement` (`Agreement/Loop.lean:839`) | yes | none |
| Generators (`gen`) | yes (`genProtocol`, `Clauses/Gen.lean`) | yes | no | yes | none |
| Scheduled (fork, await, race, async, interrupt, scopes) | yes (the M6 clauses) | yes | **no** | yes | answer-free tapes only |
| Layers (provide, memo, build, merge) | yes (M5 layer arm, the memo rows) | yes | **no** | yes | answer-free tapes only |
| Host-answered runs | **no** (`RReachable` excludes them) | **no** (`run_eq_ref` holds at the empty table; DI-57) | no | no | the open lane, R6 |

Each "yes" holds under its own conditions:
- **Typing (M5, M6):** lawful, checked, closed requirement row (`rootTy.requires = empty`).
- **M7a–c:** the M7 fragment (`M7Fragment`: also the empty host table and answer-free tapes).
- **`run_eq_ref`:** no fragment restriction at all, but only the empty host table and the empty
  oracle (`RuntimeR.lean:200-215`).

Two readings follow.
1. **Typing is generalized across every fragment.** The owner's "generalized for scheduled,
   straight, layers" holds for typing.
2. **Behavioural meaning is not.** A denotation exists for straight-line code, an agreement for
   loops, and nothing behavioural for scheduled programs or layers beyond the reference machine
   itself. That is exactly where the composition laws an API needs would live.

## 3. Safety, progress and liveness, kept apart

The literature line is the one the semantics doc already draws (§2.4, Lynch–Vaandrager,
Manna–Pnueli): simulation and invariants give safety and trace inclusion, never liveness.

**Safety (what we have).** Properties of every finite run prefix:
- `J` on every reachable machine (`typedState_reachable`);
- M7c, the frame machine never halts on the fragment (`stuck = none`).

`machineTyped_not_halted` is an invariant consequence, not progress (row 139, `semantics.md`
§2.4).

**Operational progress (owed; `scheduler-progress`, row 139, R12).** The shape:

> `MachineTyped w m → Finished m ∨ (∃ d internal, Enabled m d ∧ Progresses m d) ∨ Frontier m r`

Here `r` names what the run awaits:
- a host answer at a key in `outstanding`;
- the clock;
- the budget;
- `Deadlocked`, which by R12 requires nothing armed.

Today armed dispatcher work is invisible to the frontier (`awaitDecision_iff`, system map R12). So
a session cannot tell "the program waits for me" from "the scheduler has work". Progress is what
makes the session API honest to drive: when `outstanding` is empty and no internal decision is
enabled, the run is finished or the program deadlocked itself, and that is not the host's
business.

**Liveness (after progress; `fair-scheduling`, R12).** Liveness talks about infinite behaviour, so
it needs:
- infinite tapes;
- a fairness hypothesis: `FairTape`, weak fairness over internal decisions with row-specific
  enabling;
- the external host-progress assumption (`host-progress`, `semantics.md` §2.9: answers eventually
  arrive; an assumption, not an obligation).

Under those, the honest statement is relative:

> every fair run either finishes, stops at `Deadlocked`, or the program itself diverges, by an
> `iterate` or a generator that does not end.

Liveness never promises termination of a program that does not terminate.

**Three liveness-flavoured results are worth more to an API than termination:**
- **Interrupt responsiveness.** An interrupt delivered to an interruptible fiber takes effect
  within a fair-tape bound. This is what makes cancellation APIs robust.
- **Finalization.** On every run where a scope closes, its finalizers ran, at most once each, in
  close order, before the close is observed (R11). This is a safety property over traces, and
  provable now by the same induction as M6.
- **Bounded dispatcher fairness.** `flush_fair` (`Laws/Machine/Scheduling.lean:413`) already
  exists.

## 4. Host answers and the session API

**What the lift already gives.** `replayEval_lift` (`Machine/Lift.lean:731`) carries `J` through
every tape that is *admitted*: each decision satisfies `∀ w, J w m → AnswerOk w m d` at the
machine it meets (`AdmittedReplay`, `:712`). `decision_preserves` is proved with exactly that
`AnswerOk` premise. So **typing over admitted host answers is already a theorem in substance**:
`reachable_of_ledger` with `admittedReplay_noHostAnswer` swapped for the admitted tape (probe 2,
§8).

**Why that is not yet the public promise.** `AnswerOk` reads the ghost world's token table `Θ`,
which no host can see. The missing link is a soundness theorem for the executable admission the
session runs:

> `admit_sound : MachineTyped w m → admit m d = true → AnswerOk w m d`

It needs two facts.
1. **`RequestFits`** (`host-boundary.md` §4.1): for a fiber parked on an external call, `Θ` at its
   token is the row's answer type at the evaluated request. This is a clause of `J` to add or
   derive.
2. **Admission is at least as strict as `Fits` at that type.** Row 97's hole breaks this today:
   `Val.hasTy` checks a handle by kind only, and a checked `nat` program finishes with a string on
   the certified session (`host-boundary.md` §3).

The end theorem is then:

> `session_typed`: every state reached through `HostSession`'s operations (`start`, `submit`,
> `applyReply`, `advance`) from a checked, closed program satisfies `MachineTyped`.

That is the "typed programs using host services stay typed" claim `host-boundary.md` §1 withholds
until the lane lands (row 99). For the frame machine the same claim also needs the table-aware
agreement (DI-57).

**Session laws that make the API ergonomic.** Each is small and some exist:
- the observation is a projection of the session (`api-surface.md` §3.1);
- independent replies commute (`reply_commute`, `Laws/Api/HostSession.lean:112`);
- application is at most once per key, and a refusal is located and changes nothing;
- `inspect` exposes exactly the outstanding calls progress names (§3).

## 5. Composition and manipulation: "programs as monads"

**What composition needs semantically.**
- **Typing congruence.** The type of `bind a b` comes from the parts. We have this: the checker is
  a fold, and its inversions are proved by aesop in the `Effect4.Checker` bank
  (`Typing/CheckInversion.lean`).
- **Behavioural laws.** The monad laws, `catch` over `bind`, `scoped` over a pure body, and
  `provide` over a body that needs nothing hold **only up to an observational equivalence, never
  as data**. `bind (succeed t) k` and `k t` are different trees.
- **Congruence of that equivalence.** If `e₁ ≈ e₂` then `C[e₁] ≈ C[e₂]` for every constructor
  context `C`: `bind`, `catchCause`, `fork`, `scoped`, `provideLayer`, `gen` and the rest. Without
  it a law proved for a combinator does not transfer into a program that uses the combinator. This
  is R10 ("library code inherits theorems … by a stuttering route", system map) and post-Phase C
  §11.4.

**The equivalence has to be defined with care, and these four choices are the design:**
1. **Per-tape equality is too strong.** Two equivalent programs consume decisions differently:
   administrative steps, fiber ids and tokens shift. The relation compares behaviours up to an
   identity bijection on fibers and tokens (R8 already uses "up to one identity bijection") and a
   tape correspondence.
2. **Stuttering must be bounded.** A step that becomes several needs a bound or a progress
   measure, or infinite stuttering satisfies safety vacuously (`lcnf-route.md` §8, the stage
   rules).
3. **Frontiers must correspond.** Fuel is a frontier, so equivalent programs agree up to
   compatible prefixes (DB-03): one may reach a frontier where the other has more to do under the
   same budget.
4. **Observation and contexts.** Equivalence is relative to `obs` and the outcome. Contextual
   equivalence closes it under contexts; the congruence theorem is what makes the closure free.

**The recommendation:** make `Beh` (equivalently the reference machine) the one semantics, define
the preorder `⊑` (refinement) and `≈` over it, prove congruence once over the generated algebra
(one fold, as the coherence principle asks), and prove a small core of laws at `≈`. The fragment
theorems become corollaries: on `Straight`, `meaning` is the canonical representative
(`run_eq_meaning`). This is the generalization across straight, looped, scheduled and layers that
the owner asked for, at the behavioural level.

## 6. Lowering

There are two compilations, and they must not be confused (`lcnf-route.md` §8):
- **`compileEff`** turns `Eff` at a point into first-order frame code (`Prim`). Its correctness is
  `run_eq_ref`: every program, the same tape driving both machines, equal observation. That is a
  forward simulation with no tape translation, at the empty host table.
- **The LCNF route** translates persisted Lean declarations (the machine, the compiler) through
  mono LCNF into OCaml. It joins no theorem from Lean definitions to execution
  (`lcnf-route.md`, review boundary).

**The criterion for every further stage** is the preorder of §5, read across languages:
- target behaviours refine source behaviours under the named observation, up to the identity
  bijection and the budget correspondence;
- typing is preserved;
- no new stuck state;
- bounded stuttering.

**One preorder serves three consumers**, which is the reason to build it once:
1. composition laws and refactoring in the authoring API;
2. optimizations, which are rewrites `e ↦ e'` with `e' ⊑ e`;
3. faces and lowerings: the TypeScript printer, the OCaml engine, each "inside its profile equal,
   outside it refusing" (R8; numbers per DI-56 and row 108).

A table-aware `run_eq_ref` (DI-57) is the host-answer extension of the first stage.

## 7. Candidate theorems, ranked

Each entry gives the statement, its semantic value (what a consumer may rely on), its placement,
and its feasibility as measured.

**T1. Observed exits have the meaning layer's type, on every fragment.**
- **Statement.** On `M7Fragment root rootTy tape`, every recorded exit `(id, some ex)` of
  `obs (Api.replay root.program fuel tape).machine` satisfies `Denote.ExitHasTy ty.answer
  ty.error stores ex` at `id`'s declared type `ty`, and the root's type is `rootTy`.
- **Value.** The frame machine's results satisfy the same executable judgment that
  `meaning_typed` concludes for straight code (`Val.hasTy` and store validity). So "a checked
  program's result has its checked type" holds in one judgment for scheduled programs and layers
  too, not only straight-line code. It is the headline a codegen target or an agent can quote.
- **Ingredients.** All exist except the last:
  - `m7_proved`;
  - `exitHandles_valid_closed` (probe 1, proved);
  - `exitHasTy_of_fitsExit` (`Typed/ExitConnector.lean`);
  - the native fact that answer-free runs allocate no external handle. Every store row keeps
    `externals` (`restate_world`, `complete_world`, `poke_world` all take `externals = …` by
    `rfl`), so this is an invariant through `replayEval_lift` with `J := externals = []`.
- **Placement.** Concept 10 (`translation-simulation`), registry `m7-capstone-goals` (serves);
  the M7 ledger.
- **Feasibility.** Small.
- **Not established.** Host answers; open requirement rows.

**T2. `M7.exitHandles_valid`.** Its statement lacks the closed requirement row, and `J` exists only
on closed rows, so the typed route (probe 1) proves only the closed-row form. Two ways:
- **(a)** restate the goal with the closed row: a contract change to a ledger statement, owner's
  call;
- **(b)** prove the open-row goal by row 180 (a)'s native invariant: every value frame's handle
  byte is registered, beside `handles_minted`, then `exitHandles_valid_of_registered`
  (`Typed/Edits.lean:528`).

Recommendation: land `exitHandles_valid_closed` now as T1's ingredient, and keep the open goal for
(b).

**T3. Operational progress** (row 139, `scheduler-progress`; R12).
- **Statement.** The classification of §3, with frontier reasons as data, and armed dispatcher
  work made visible to the frontier.
- **Value.** A stopped run names exactly what it awaits. The session can drive to completion
  without guessing. It is the base for any liveness claim.
- **Placement.** Concept 4.
- **Feasibility.** Medium. The halting arms are already classified (row 139's census in each
  command proof); the new part is the enabled-decision side.

**T4. Host admission soundness and the typed session** (rows 97–99, R6).
- **Statement.** `admit_sound` and `session_typed` (§4).
- **Value.** The public promise for programs that call the host: no host that follows the session
  API can break typing.
- **Placement.** Concept 9 (`typed-replay-session`, `host-session-protocol`).
- **Feasibility.** Blocked on row 97 (handle declarations from creation evidence) and a
  `RequestFits` clause. The lane is parked by the owner (2026-09-30). The typing half over ghost
  admission is nearly free (§4).

**T5. The observational preorder, congruence, and a core of laws** (R10, R8).
- **Statement.**
  - `⊑` and `≈` over `Beh`;
  - congruence for every `Eff` constructor;
  - laws: `bind`–`succeed` both sides, associativity, `catchCause`–`bind`, `scoped`–pure,
    `provideLayer`–unused.
- **Value.** Sound refactoring and composition in the authoring API, sound optimization, and the
  criterion for every lowering (§6). This is the foundation for "manipulation and composition of
  program data as monads".
- **Placement.** Concepts 7 and 10.
- **Feasibility.** Large; design first, on the four choices of §5. A first probe should prove
  `bind (succeed t) k ≈ k t` on the reference with an explicit tape correspondence, to fix the
  relation's shape before the congruence proof.

**T6. Resource safety over runs** (R11).
- **Statement.** On every reachable run, each registered finalizer runs at most once, and exactly
  once, in close order, if its scope closes.
- **Value.** `acquireRelease` and scopes are robust under interruption and failure.
- **Feasibility.** Medium. One close is proved (`ScopeMachine.runState_complete`); the run-level
  statement is the M6 induction with a trace invariant.

**T7. Liveness under `FairTape`** (R12). After T3.

**T8. R9 part two** (row 117: no `missingService` on closed rows). Contract work on frames.

**T9. Table-aware `run_eq_ref`** (DI-57). The host extension of the first lowering stage; with T4,
the frame-machine form of the session promise.

**Recommended order:** T1 (with T2's closed form) now; T3 next; a T5 design note and its first-law
probe in parallel; T4 when host services are needed (the owner's parking stands); T6, then T7.

## 8. Probes (reproducible)

**Probe 1.** Scope-handle validity on closed rows, by the typed route, against
`Effect4.Laws.Program.Typed.Commands.Clauses.All` at `4dcb2bfa`. It compiles; axioms
`[propext, Quot.sound]`:

```lean
theorem exitHandles_valid_closed (root : ProgramSource) (rootTy : EffTy) (fuel : Nat) (m : RState)
    (lawful : LawfulSource root) (checked : Program.typeOfProgram root.signature root.program = some rootTy)
    (row : rootTy.requires = Env.Requirement.empty) (reach : RReachable root fuel m) :
    ∀ f ∈ m.fibers, ∀ v, f.exit = some (.success v) → Val.validIn m.state v = true := by
  intro f hf v hx
  obtain ⟨w, typed⟩ := typedState_reachable root rootTy fuel m lawful checked row reach
  have store := storeTyped_of_typedState typed
  obtain ⟨⟨valid, ok, _, _, _, _⟩, _, _⟩ := typed
  obtain ⟨ty, declared⟩ := Option.isSome_iff_exists.mp
    ((valid.fibers f.id).mpr (List.mem_map_of_mem hf))
  have hex := (ok.c0 f hf).c3 _ hx ty declared
  have hfit := (fitsExit_success_iff w ty v).mp hex.1
  rw [← valid.state]
  exact fits_validIn store hfit
```

It rests on the capability-membership repair (F-WF): a member of any type is valid in a typed store
(`fits_validIn`, `Typed/Adequacy.lean:113`). `Typed/ExitConnector.lean`'s docstring ("the typed
state supplies neither premise today") is stale for the validity premise and should be corrected
when T1 lands.

**Probe 2.** Reading the lift (no new code):
- `AdmittedReplay J A` (`Machine/Lift.lean:712`) requires admission at every world that types the
  machine;
- `replayEval_lift` (`:731`) takes any such tape;
- `reachable_of_ledger` (Assembly.lean) instantiates it with `admittedReplay_noHostAnswer`.

So a host-answered reachability theorem over ghost-admitted tapes is the same proof with that one
argument generalized. The work is `admit_sound` (§4), not the lift.

## 9. Placement summary (AGENTS.md)

| Theorem | Concept | Question | Unlocks |
| --- | --- | --- | --- |
| T1 | 10 | the M7 ledger, `m7-capstone-goals` | the end-to-end typed-result claim for every fragment |
| T2 | 10 | `M7.exitHandles_valid` | closes the M7 ledger (with (b)) |
| T3 | 4 | `scheduler-progress` (row 139) | R12; an honest session driver |
| T4 | 9 | `typed-replay-session` (rows 97–99) | R6; the host promise |
| T5 | 7, 10 | R10, R8 (new claims to register) | API laws, optimization, lowering criterion |
| T6 | 3 | R11 | robust resource APIs |
| T7 | 4 | `fair-scheduling` (R12) | liveness |

None of these is started in the tree by this note. It proposes; T1's ingredients are the only code
measured.
