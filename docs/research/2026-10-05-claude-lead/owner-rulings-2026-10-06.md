# 2026-10-06 the open questions: a recommended ruling for each, with its evidence

Status: research note (history, not authority). Base: `4834760e`. The coordinator wrote it on
the owner's request of 2026-10-06. Every ruling here is a recommendation. A ruling is made
when the owner says so and the coordinator writes it into `docs/core/decisions.md`.

Corrected the same day, after Codex's relay: F8 and A5 said that no lane runs the compiler
checkpoint. A job of the CI workflow runs it, and the local sweep does not.

## Question

Which questions are open for the owner on 2026-10-06? What does the coordinator recommend for
each, and what evidence stands behind the recommendation?

## How to read this note

The questions are in three groups.

- **Group A needs the owner's word.** Each changes a meaning, a supported domain, a
  representation, the trust rule or the limit of seats.
- **Group B is decided by the coordinator** inside a policy that the owner has ruled. The owner
  may overrule any of them.
- **Group C needs no decision now.** Each names the event that opens it again.

Each piece of evidence carries its word from `docs/core/controlled-english.md` §3.8. "Proved"
is a theorem that the kernel accepted. "Tested" is a finite run that passed. "Reading" is a
source that was read, with no run.

## The rulings asked for

| # | The question | The recommended ruling | The main evidence |
| --- | --- | --- | --- |
| A1 | Semaphore: how a release wakes the waiters | The live scan: one visit at a time, and a wake reserves nothing | tested on rc.112 and 4.0.1; reading of our machine; rows 219, 221 and 233 |
| A2 | Semaphore: the first operations | As the card lists them; the raw `take` and `release` stay | reading: the pinned `Pool.ts` uses them; tested: `releaseAll` breaks the total |
| A3 | Semaphore: a release of more than is taken | The law takes a premise; the step releases at most what is taken | tested on three builds; reading of the atom `sub` |
| A4 | The OCaml target evaluator and the trust ceiling | Bring it under the ceiling in one slice of its own, later | tested: four pinned axiom lines |
| A5 | The compiler checkpoint in the local sweep | Join the existing check to the local sweep, by one marker rule | reading: a CI job runs it at a push, and no `make` target runs it |
| A6 | The boundary of a compiler client | Accept the three owners; build it inside `tools/target` with its next caller | reading: Codex's review; two callers exist |
| A7 | Semaphore's cell and steps, now, as a third seat | Yes, after A1 to A3 | reading: the Queue's steps needed no mask; the free disk is measured |
| A8 | One changed file of a filed packet | The owner runs one command | tested: `git diff` |

One word answers the table: "yes to all", or the numbers to change.

## What was read or run

| Item | How |
| --- | --- |
| `semaphore-wake.ts` (`docs/research/2026-10-05-claude-lead/module-cards/semaphore-probes/`) on rc.112, 4.0.1 and Effect 3.22.2, with bun 1.4.2; each output sits beside it | tested: nine cases, one schedule each |
| A `Set` that changes under a `for … of` loop, in a scratch file, with bun 1.4.2 | tested: one run |
| `vendor/effect-4.0.0-rc.112/src/Semaphore.ts`, `Scheduler.ts`, `Pool.ts`, `Schedule.ts` and `Array.ts`; `callbackOptions`, `FiberImpl.evaluate`, `FiberImpl.runLoop` and `interruptUnsafe` of `internal/effect.ts` | reading |
| `vendor/effect-4.0.1/src/Semaphore.ts` against the pin's file | tested: `diff` shows documentation only |
| Our machine: `DeferredStore.complete` (`src/Effect4/Machine/Stores.lean`); `WakeMode` (`src/Effect4/Machine/Wake.lean`); `drainOwed`, `driveStep`, `yieldVerdict` and `injectYield` (`src/Effect4/Machine/Fibers.lean`) | reading |
| `NativeAtom.row` at `natSub` (`src/Effect4/Machine/Term.lean`) | reading |
| `applyReply` and `retire` (`src/Effect4/Api/HostSession.lean`); `tapeFrom` (`Test/Dogfood/Scenario.lean`); `retryForm` (`Test/Dogfood/P1HttpCache.lean`) | reading |
| The receipts of seats T3b, M0, LOWER, DOGFOOD, FOLD, T5, QSTEPS and QTYPES, their sections of proposals | reading |
| Decisions rows 219 to 258; `docs/STATE.md`; the waiting design (`docs/research/2026-10-05-claude-lead/waiting-design.md`) | reading |
| Codex's reviews under `docs/research/2026-10-05-codex-foundation-packet/implementation-audit/`: `tsgo-research/`, `module-factory-review/`, `heartbeat-0451-fixtures-semaphore/` and `heartbeat-0553-semaphore-qtypes/` | reading; their probes were not run again |
| `Test/Audit/LetReturn.lean`, whose `#guard_msgs` pins four axiom lines | tested at each default build |
| `.github/workflows/lean_action_ci.yml`, the job `check-ocaml`; the `Makefile`'s rules for `scripts/check-conform.py` | reading: the configuration only, and no remote run |
| The merge of seat QTYPES's last part, `4834760e`: the default build, the gates, `check-semantics`, `check-docs`, `check-conservativity` | tested |

## Findings

### F1. On the pin a resumed waiter takes inside the wake's walk

The pin posts one task for a release. The task walks the waiters in order (reading:
`SemaphoreImpl.releaseUnsafe`). The probe records each read of the free count. So it shows
where the walk reads and where a waiter takes. The builds rc.112 and 4.0.1 answer alike on
every case (tested).

| Case | What the pin answers |
| --- | --- |
| P1. Total 2. B asks for 2, then C for 1. A release of 2 follows. | B takes 2 between two reads of the walk. The walk then reads 0 and stops. C is not visited. |
| P2. Two permits are held. B asks for 2, then C for 1. A release of 1 follows. | The walk passes B and serves C. B keeps its place. |
| P3. B asks for 1 and then for 1 again, with no yield. C asks for 1 after B. A release of 2 follows. | B takes both permits inside the walk. C waits. |
| P4. B and C wait in the protected form. Their bodies do not wait. | B's body and its release run inside the walk, and then C's. |
| P9. P1, with B under a scheduler that tells it to yield at its resume. | The walk goes on. C takes 1. B checks again later and waits again. |

So the walk is live. A waiter's retry runs inside it, and then that waiter's caller runs, until
the fiber yields, parks or ends. Effect 3.22.2 answers P1 in another way: its walk resumes B
and C, and both retry later (tested).

### F2. Our machine resumes a waiter in the same way

A `Deferred` owes each waiter its resume in the mode `WakeMode.now`
(`DeferredStore.complete`). `drainOwed` makes such a resume the next command. The resume
clause of `driveStep` then evaluates the waiter's fiber. So a waiter runs inside the task that
resolves its hint (reading). The machine also has the yield of P9: the tape may answer the
question of `yieldVerdict` at a fiber's resume (reading).

No Semaphore program ran on our machine. This finding is a reading of the declarations named
here.

### F3. Three ruled rows bear on the wake

- Row 221 rules the shared waiting wrapper: a wake invites another attempt and reserves no
  result.
- Row 219 rejects a reservation for the Queue. Its two countermodels are about messages: a
  returned message changes the order, and a reserved one breaks the capacity
  (`docs/research/2026-10-05-claude-lead/queues-review.md`). Permits have no order, so neither
  countermodel refutes a reserved count.
- Row 233 names Semaphore as the wrapper's second consumer.

### F4. The card's first recommendation was wrong, and why

The card of 2026-10-05 recommended a grant at the wake: the posted task commits each fitting
waiter's count in one step. It gave two reasons, and both fail.

- It said that our machine resumes a waiter by scheduling it. F2 shows the contrary.
- It said that the grant is the pin's path with no yield. P3 shows another answer on such a
  path. Codex's review of 2026-10-06 found the same from the retained outputs.

The coordinator wrote both sentences from the pin's source alone, before any run. The card is
corrected (`docs/research/2026-10-05-claude-lead/module-cards/semaphore.md`).

### F5. The pin accepts counts that break its own total

- A release of 1 with nothing taken answers a free count of 3 at a total of 2. Three takers
  then proceed (P5, tested).
- A request for -1 and a request for 0.5 are both accepted (P6, tested).
- `releaseAll` beside a protected holder ends with `taken` at -1 (P8, tested). The release
  4.0.1 documents this as a known trap (reading: the comment on `releaseAll`).

On our two faces the atom `sub` is the truncated subtraction. Lean computes it on natural
numbers, and the TypeScript prelude prints `a <= b ? 0 : a - b` (reading).

### F6. The pinned Pool is built on the raw operations

`Pool.ts` calls `take(1)`, `release(1)`, `take(size)` and `releaseAll` on its semaphore
(reading). So a first profile without the raw `take` and `release` would not serve Pool.

### F7. The target evaluator is outside the trust ceiling by two rules

`Test/Audit/LetReturn.lean` pins the axiom lines of `Conform.Lcnf.Target.evalT` and of
`let_return_outcome` (`tools/Conform/Lcnf/TargetLaws.lean`): both reach `Classical.choice`
(tested). Seat LOWER measured the cause in a scratch probe: `String.length`, and `<` on two
strings. The byte size, the bytes, `==`, `++` and the integer rules do not reach it
(`docs/research/2026-10-05-seat-LOWER-receipt.md`). So the law of `let x = e in x` is
kernel-checked and is not proved in the dictionary's sense.

### F8. The compiler checkpoint runs in CI and in no local sweep

- The CI workflow's job `check-ocaml` runs `python3 scripts/check-conform.py compiler` after
  the build. It runs at a push, at a pull request and at a manual run (reading of
  `.github/workflows/lean_action_ci.yml`). No remote run was checked.
- The `Makefile` has a marker rule for the profile `cases` and one for `native`. It has none
  for `compiler` (reading). So `make check-full` does not run the checkpoint.
- The checkpoint was red on this checkout until `21b7da47` repaired it on 2026-10-05 (reading:
  `docs/STATE.md`). The branch is ahead of its remote (tested: `git status`), so the CI job has
  not run on its latest commits.
- Seat LOWER's receipt says that nothing runs the profile but a person. That is wrong about
  CI. This note's first version repeated it, and Codex's relay of 2026-10-06 corrected it.

### F9. Three small facts of the scenarios' findings

- `applyReply` answers `applied` when the reply's guard is consumed. The command loop may have
  run out of fuel after that. `tapeFrom` checks the fuel itself (reading).
- A call that is cancelled before the host held it leaves no retired record (tested: seat
  DOGFOOD's finding). A reply for a key with no pending slot is refused with `noCall`
  (reading: `submit`, `src/Effect4/Api/HostSession.lean`).
- `retryForm` doubles its delay before its first sleep. Its docstring states the pin's rule,
  which sleeps the base first (reading of both, and of the pinned `exponential`).

### F10. The changed file holds no new result

`git diff` shows one file of the filed decision probes, `emit-comparison.json`. Its recorded
paths changed, and its three hashes did not (tested). A run of the packet's own script in this
checkout wrote it. The repository's guard refuses the coordinator's `git restore`.

## Proposals (not rulings)

### Group A: for the owner's word

#### A1. Semaphore: the live scan

**The question.** When a release wakes the waiters, who commits a waiter's permits, and when?

**The recommendation.** The live scan, which is the pin's own policy.

1. A release posts one helper, by row 238's construct.
2. The helper visits one waiter at a time, in the order of enrolment.
3. At each visit it stops if no permit is free.
4. Otherwise it resolves the hint of the next waiter whose count fits.
5. That waiter resumes inside the helper's task and runs its own take step, which checks the
   count again.
6. The helper then reads the state again for its next visit.

A wake reserves nothing, and the permit commits in the waiter's own step.

**Why.**

- It is the policy that the pin showed on every case of the probe (F1).
- Our machine already resumes a waiter inside the resolving task (F2). The helper needs no
  new construct.
- Rows 219 and 221 stay as they are, and the Queue's wrapper serves Semaphore unchanged (F3).
- The take and the hook's installation stay one masked region of the waiter's own fiber, as
  on the pin. The grant would commit in the waker's step and install the hook later.
- Each take step checks the count in its own atomic step. So the accounting does not depend
  on the walk.

**The other two profiles.**

| Profile | What it is | Why it is not recommended |
| --- | --- | --- |
| Grant at the wake | One atomic step commits a count for every waiter that fits | It differs from the pin on P3 and P9. It needs a rule for a granted request that is interrupted. It needs an amendment of row 221 and a second mode of the wrapper |
| Snapshot | One atomic selection, and each selected waiter retries later | It gives Effect 3's answer on P1: it resumes a waiter that the pin's walk does not visit |

**The cost.** The helper is a loop of visits. The cell gains a counter, and each waiter a
stamp, as the walk's cursor. The law of the expansion is stated for one visit. A visit reaches
the resumed caller's work up to its own cut: a yield, a park or its exit (Codex's review). So
the budget premise of row 226 covers that work, or the first profile restricts the callers.

**What it does not settle.** It promises no order of service and no fairness. It is no claim
that the expansion agrees with the pin: that is the planned `semaphore-expansion-agrees`.

**To undo it.** The profile is a card and no code. A later choice of the grant costs the
card's revision and row 221's amendment.

#### A2. Semaphore: the first operations

**The recommendation.** The first profile has `make`, `take`, `release`, `withPermits`,
`takeIfAvailable` and `withPermitsIfAvailable`, at a fixed total of at least 1. It excludes
`resize`, `releaseAll`, a request above the total, and a count that is no natural number.

**Why.** The raw `take` and `release` are the pinned Pool's operations (F6), and they are the
same two steps as the protected form's. `releaseAll` breaks the total beside a protected
holder (F5). `resize` changes the total under waiters and holders, and no first consumer
needs it (reading).

**What it does not settle.** Pool's shutdown uses `releaseAll` on the pin. Pool's card must
say what replaces it.

#### A3. Semaphore: a release of more than is taken

**The recommendation.** The profile's law takes a premise: a release asks for at most
`taken`. The step itself is total, and it releases at most what is taken. The card states
this as a difference from the pin.

**Why.** The pin lets the free count exceed the total (F5). A natural number cannot hold a
negative `taken`, and the atom `sub` has one meaning on both faces (F5). So the step needs no
new number type, and the printed program computes what Lean computes.

**The alternatives.** A defect at such a release makes the caller's fault visible, and it
needs a named defect. The pin's own rule needs an integer field or a stored free count, and it
gives up the bound.

#### A4. The target evaluator comes under the trust ceiling

**The question.** Seat LOWER's law is kernel-checked in the tool library, outside the ceiling
(F7). Three options stand: keep it there; write the two string rules in their byte forms;
exempt the law by name in the gate.

**The recommendation.** The byte forms, as one slice of its own, when a seat is free. Then the
law moves into a battery with its placement, and the registry claim
`ocaml-let-return-outcome` gets its witness. Until then the semantics registry holds no
witness for it.

**Why.** The byte forms are the target's own meaning: the emitted helper counts bytes, and
OCaml orders strings by bytes (reading: the seat's receipt). An exemption by name is ruled
for a rendering declaration, and the evaluator is none (`AGENTS.md`, "Trust"). The slice
needs one new control, for the order of two strings.

**Why later.** The law serves R8's part on the OCaml route. Row 204 keeps the lowering of that
route parked, and no module slice waits for it.

#### A5. The compiler checkpoint joins the local sweep

**The question.** CI runs the compiler profile, and the local sweep does not (F8). Should the
local sweep run it too?

**The recommendation.** Yes, by one marker rule beside the rules of `cases` and `native`.
`check-full` names it, and `make` skips it while its inputs are unchanged. It is the existing
command. It adds no CI job, no profile and no new check. The same change corrects the label of
the workflow's step: it says one mutation, and the profile runs three (seat LOWER's receipt).

**Why.** Nothing of this stretch is pushed, so the CI job does not run on the work as it
lands. A seat's merge runs the local gates alone. The checkpoint was red on this checkout
until its repair (F8).

**A separate decision.** The runner's own script tests stay run by hand. The owner retired the
lanes that test scripts.

**What it does not settle.** The cost of one run is not measured here.

#### A6. The boundary of a compiler client

**The question.** Codex proposes a shared client for the TypeScript compiler, taken from
`tools/target/oracle.ts` and `tools/target/checker.ts`.

**The recommendation.** Accept the boundary, and build no package.

- The Lean `typescript` package keeps syntax and rendering, with no compiler client.
- The client lives inside `tools/target`, as a session with a versioned request and report.
- This tree keeps program admission and the comparison of answer, error and requirement
  types.
- The first build comes with the client's next caller: the control files generated from Lean
  pins (row 258, point 7).

**Why.** Two callers exist today, so the extraction has consumers. The owner's guidance of
2026-10-05 already names the two files for reuse. Codex's review is source reading, and it
measured no speed.

#### A7. Semaphore's cell and steps start now, as a third seat

**The question.** Row 233 puts Semaphore after the Queue's other parts, and row 237 limits
the seats to two. May the cell, the model and the steps of Semaphore start beside the mask's
seat?

**The recommendation.** Yes, once A1 to A3 are ruled. The seat writes the contract packet, the
model, the cell and the steps, with each step's agreement and typing. The wrapper and the
protected form wait for the mask and for the Queue's public path.

**Why.** The Queue's cell and steps needed neither the faces nor the mask. Seat QSTEPS ran as a
third seat on the owner's word (row 237's amendment). Semaphore's steps reuse the same pieces
(the card, section 7). The files are new folders, so they meet no other seat's files.
The disk has 27 GiB free (tested: `df`).

**What stays as ruled.** Row 233's order holds for every other slice. Seat HOST takes the
slot that seat QTYPES freed, inside row 237.

#### A8. The changed file of the filed packet

Run this command. It puts the file back as Codex filed it (F10).

```bash
git -C /Users/pooks/Dev/lean4-effect4 restore -- docs/research/2026-10-05-codex-foundation-packet/implementation-audit/decision-probes/literals/outputs/emit-comparison.json
```

### Group B: decided by the coordinator, open to the owner's overrule

| # | The decision | Its evidence | Where it is recorded |
| --- | --- | --- | --- |
| B1 | `pair` and `tuple` widen a number or a Boolean type in an immediate slot | tested under tsgo 7.0.0-dev.20260629.1, by seat T5 and by Codex's probe | row 256, landed |
| B2 | The wrapper's law takes a step's typing as a proof parameter | proved since: the five typing goals are theorems at every scope | row 257, landed |
| B3 | What seat T5 leaves open, with each point's next step | reading: the seat's receipt | row 258 |
| B4 | `take` and `drop` take the list first | reading: the pinned `Array.take` takes the collection first, and so does the tree's `get` | seat FOLD's receipt, item 9 |
| B5 | `sameHandle` types by the head of each argument's type, and it refuses a union of handle types | proved: `handle-identity-laws` holds for this typing (`src/Effect4/Laws/Program/Typed/ListFold.lean`) | seat FOLD's receipt, item 9 |
| B6 | The scenarios' planned goals stay in the requirement rows | reading: a requirement with a placed goal is proved only when that goal is | row 254 |
| B7 | The two new typing modules stand under `store-typing` | tested: `check-semantics` passes on `4834760e` | the semantics registry |
| B8 | A scenario's record lists assembled clauses and associated laws | tested: the gate's own fixtures | seat DOGFOOD's receipt, row a |
| B9 | The driver's four general laws move into the law graph, and `meaning_onExit` gets its placement | proved: the four laws; the move is not done | seat DOGFOOD's receipt, item 9.5 |
| B10 | `retryForm` is repaired to sleep its base first, and the timeout scenario's fixtures are written again | reading (F9); the repair is not done | seat DOGFOOD's receipt, row f |
| B11 | The token `under` becomes a keyword in its three commands only | tested on a toy syntax by seat QTYPES; not applied to the tree | seat QTYPES's receipt, item 10 |

B9 to B11 are the coordinator's side work. B11 goes in with the mask's merge, which builds
the same modules again.

### Group C: no decision now

| # | The question | Where it stands | What opens it again |
| --- | --- | --- | --- |
| C1 | `applyReply` at an exhausted budget: `applied`, or a frontier? | It stays `applied`: the word reports the guard, once (F9) | Row 226's driver suspension, which gives the cut its own representation |
| C2 | Does the session record a cancellation of a call that the host never held? | No. A reply for such a key is refused with `noCall` (F9) | A host adapter that must tell a withdrawn call from an unknown one |
| C3 | An identity for one invocation of a finalizer, in a run's observation | Not built | Semaphore's protected-permit law, whose observation needs the same identity |
| C4 | A third evidence kind for a placement: a measured dependency | Not built; B9 tags the one theorem that needed it | A second theorem with the same need |
| C5 | Does opening a database fail with a typed error? | Deferred with its reason (row 253); the row keeps the pin's `never` | The data plane's slice of the migration |
| C6 | Pool's and Cache's first profiles | No card yet; the coordinator writes both next | Each card puts its choices to the owner once |
| C7 | The proof that well-formed layer references expand fully; the journal's cut laws | Candidates with no seat; each brings its registry claim | A free seat, compared with the next module slice |
| C8 | Seat M0's proposals A to F; the release audit's proposals | Inside the migration, which follows the features (row 253) | The first slice that cuts an area over |
| C9 | Three changes of Codex's macro research | No seat and no date | A second consumer of each |
| C10 | The older open rows of the register; the report of `U-01` to Effect | The register and `docs/STATE.md` own them | The owner's own order |

## What this does not establish

- Each probe case is one finite run on one schedule, with bun 1.4.2. None is a proof.
- The probe replaces one getter with the same subtraction and a log. It is no run of an
  unchanged runtime.
- No Lean statement of Semaphore exists, and no Semaphore program ran on our machine or on the
  generated engine.
- F2 is a reading of the machine's declarations. It is no theorem about a wake.
- The recommendation A1 states no fairness, no order of service and no agreement with the pin.
- The byte forms of A4 were not written, and no control reaches the order of two strings.
- The cost of A5's rule and the speed of A6's client were not measured. No remote run of the
  CI job was checked.
- B9, B10 and B11 are not done.
- No recommendation here is a ruling.
