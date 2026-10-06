# Dogfood: the rc.112 programs as acceptance tests

Decisions row 206 (ruled 2026-10-04) makes the five model-probe programs tracked acceptance
tests. This folder holds them. Each program has one plan row below. The row names the stage its
battery measures today, what the program waits on, and the slice expected to move it. Each slice
of row 204 moves at least one program forward.

## The folder

- `rc112/` holds the reference texts: the five rc.112 programs, their run scripts, three
  controls, the recorded runs and the checksums. No gate runs them.
- `Stage.lean` holds the words the five batteries share: `verdict`, `Reach`, `Answer` and
  `formAdmits`.
- `P1HttpCache.lean` to `P5LedgerService.lean` hold one battery per program. `Test/All.lean`
  imports each one, so the module-closure gate and the axiom gate cover them.
- Each battery declares two literals that the semantics report reads (`make gen-semantics`):
  - `stage`, the stage the program reaches;
  - `waitsOn`, the requirements of the system map's §8 that its row below explains.
  `generated/semantics.md` prints them in its section "Acceptance programs", with the programs
  each requirement keeps waiting.
- `Scenario.lean` holds what the scenarios share: the script alphabet, the driver, the readers of a
  run's session part and the driver's laws. It also holds a scenario's record and the gate
  `#scenario_gate`. Its last section holds the one `note` of the scenarios' logs. A note appends
  an entry to a log cell, under a minted name for the cell's value.
- `Scenario/` holds one battery per scenario. `Scenario/Tape.lean` holds the text of their lowered
  runs, and `Scenario/Lowered.lean` binds the engine's fixtures to it. `Scenario/Faces.lean` pins
  that each scenario's program prints and reads back. `Test/All.lean` imports each one.

## The reference texts

The model probe's programs seat wrote the five programs on 2026-09-30, and its verifier reran
them with identical lines (`docs/research/2026-09-30-model-probe/synthesis.md` §2.4). Commit
`ce2ece4f` recorded them
(`git:ce2ece4f:docs/research/2026-09-30-model-probe/programs/ts/hostruns.log`), and `f7ccf52e`
dropped them from the research tree. Every file of `rc112/` is byte-identical to its blob at
`ce2ece4f`.

| Fact | Value | Source |
| --- | --- | --- |
| Effect | 4.0.0-rc.112, the pinned package under `ts/eff/node_modules` | `rc112/hostruns.log`, first line |
| Runtime | bun 1.4.2 | `rc112/hostruns.log`, first line |
| Type check | tsgo 7.0.0-dev.20260629.1: exit 0 on the five programs and two controls; exit 1 on `rc112/red-control.ts` with its three errors | `rc112/typecheck.log` |
| Checksums | SHA-256 of the fourteen TypeScript files | `rc112/sha256.txt` |

The `tsconfig` files resolve `effect` by absolute paths into the main checkout's
`ts/eff/node_modules`. To rerun the recorded checks, follow these steps.

1. Change to `Test/Dogfood/rc112`.
2. Run `shasum -a 256 -c sha256.txt`. Every line reads `OK`.
3. Run tsgo with `tsconfig.json`, then with `tsconfig.red.json`, as `rc112/typecheck.log` records.
4. Run bun on each `run-p*.ts` file with `--tsconfig-override=./tsconfig.bun.json`.
5. Run `run-p2-noenv.ts` without `ADMIN_TOKEN` in the environment.

## The plan rows

Each stage below is the `stage` declaration of the program's battery. A guard in the battery ties
that declaration to the measurement, so the row and the battery cannot disagree while
`Test/All.lean` builds.

| Program | What it does | Stage today | Waits on | Slice of row 204 that moves it |
| --- | --- | --- | --- | --- |
| p1: `rc112/p1-http-cache.ts`, battery `P1HttpCache.lean` | Fetches a quote over HTTP. A 2 s timeout bounds each attempt, failures retry on an exponential schedule, a 404 is a typed `HttpError`, and a `Cache` serves the second lookup. | `Api.Author.build` admits the program, and it runs under a scripted host. It answers the body text where rc.112 answers `42`. It prints as TypeScript and reads back: the retry loop states its cursor's type, and the checked type reader reads it (DI-91; the state plan's T5, part B). Refused: a `Quote` record in the key-value cache (`requestNotSubtype`). The payload part `HttpError{status, url}` builds as a typed failure, runs to `Err.payload` with rc.112's recorded 404 error, prints as a module that declares its `Data.TaggedError` class and fails with `new HttpError({ … })`, and reads back (row 120, part E2). A signed `status` is refused at admission (row 121). | R10: DI-89 (`retry`, `catchTag`), DI-39, post-Phase C's W6 (`timeout`), DI-91. R3: row 121 (`status: number`). R7: row 82 (`Cache` keeps code). R6, parked: the retirement notice. | Error payloads (row 120), with the derived forms beside them |
| p2: `rc112/p2-handler-layers.ts`, battery `P2HandlerLayers.lean` | Handles a request over layered services: `UserRepo` runs SQL through a captured client, `AppConfig` reads `Config`, and a middleware provides `CurrentUser`. | `Api.Author.build` admits the handler program at `Response`, bounded as seat W10's brief bounds it. It runs to rc.112's three answers, prints as TypeScript and reads back. Refused: a string or record service carrier (`serviceCarrier: signature none`); a number in a template string (`typing: term`). The payload parts `NotFound{id}` and `Unauthorized{reason}` build as typed failures and run to `Err.payload`, and `tagIs` catches a payload by its `_tag`; each prints as a module that declares its `Data.TaggedError` class and fails with `new`, and reads back (row 120, part E2). | R3: row 130 (`catchTag`'s residual over records). R5 and R7: rows 21, 82, 118 (code-valued services, structured carriers). R13: rows 51, 83 (`Config` at load). Row 131 (number to text); row 123 (decoding inside a program). R10: DI-39, DI-89, row 130 (`catchTag`). | Error payloads (row 120), with the derived forms beside them |
| p3: `rc112/p3-worker-queue.ts`, battery `P3WorkerQueue.lean` | Drains a bounded queue with three workers. Each worker holds a connection that it releases on any exit. A `Deferred<void>` gate ends the run, and the program interrupts the pool. | `Api.Author.build` admits the program, with the queue as two host rows, and it runs under a scripted host. It answers `[3, 5]` (closes, jobs) where rc.112 answers its log. It prints as TypeScript and reads back. Refused: the log's first append at `Ref<never[]>`, at the term's result (`resultNotSubtype`). The gate as `Deferred<void>` builds and runs since T3a. Since the state plan's T5, part B, it prints as `Deferred.make<void, never>()` and reads back. Since the state plan's T3b the log's append is rc.112's `Ref.update` with a binder term: at a cell ascribed `ReadonlyArray<string>` it builds and runs to its lines. rc.112's `finish`, one `Ref.modify` that counts and decides "last", builds and answers a boolean over a number cell. Since the state plan's T5, part A, both rows print as functions of the current value, and each module reads back. The payload part `JobFailed{id, reason}` builds as a typed failure, runs to `Err.payload`, prints as a module that declares its `Data.TaggedError` class and fails with `new JobFailed({ … })`, and reads back (row 120, part E2). | R4: rows 42–43 step 5, the faces (the log's element type as a type argument, `Ref.make<A>`). R10: DI-11 (the queue composite), DI-89 (`forEach`). R3: row 130 (`catchTag`'s residual over records). Row 131. R11. | State at any type: its step 5, the faces. Then queues |
| p4: `rc112/p4-rate-limiter.ts`, battery `P4RateLimiter.lean` | Dogfood 1's fixed-window rate limiter: three requests per window, a refill daemon, five concurrent requests and a shutdown. | Since the state plan's T3b the measured program is rc.112's: one `Window` cell, and each request one `Ref.modify` whose term decides and rewrites the record in one store step. `Api.Author.build` admits it, and it runs to rc.112's `[3, 2, 3]`, with or without a yield before a request's step. Since the state plan's T5, part A, its terms print as functions of the window, so it is printed and read back. The printed request type-checks under tsgo 7 since the literal rule (decisions row 256), and the truth program `pRateRequest` agrees with rc.112 on `[true, false, 3, 1, 3]`. The race control is the earlier three-cell program, which prints and reads back: with a yield between its read and its write it answers `[5, 0, 5]`. | R10: DI-89 (`all`). | The derived forms |
| p5: `rc112/p5-ledger-service.ts`, battery `P5LedgerService.lean` | A `Ledger` service over an `Account` record with a list of variants. It fails with `InsufficientFunds`, keeps listeners and removes them by identity, and wraps a host timer with `Effect.callback`. | `Api.Author.build` admits no program for it. The `Account` record in one `Ref` builds, written and read, since the state plan's T3a. Since T3b the pure part of a deposit is one atomic `Ref.modify` over the record, whose term captures the amount: it builds and runs, and since the state plan's T5, part A, it prints as a function of the account and reads back. Refused: a signed number (table admission refuses an `int` column as uninhabited). The payload part `InsufficientFunds{needed, available}` with natural fields builds as a typed failure, runs to `Err.payload`, prints as a module that declares its `Data.TaggedError` class and fails with `new InsufficientFunds({ … })`, and reads back (row 120, part E2); signed fields are refused at admission. `settle` alone runs on the logical clock to `"settled"`. | R4: rows 42–43 step 5, the faces (the state plan's T5). R3: row 121 (`int`). R7: row 82 (listeners, effect-valued answers, the cancel effect). R10: DI-89, DI-39. R6, parked, or the logical clock. | State at any type, and error payloads |

The diagram below shows which slice of row 204 each program waits on. It claims no order among
the programs.

```mermaid
flowchart LR
  S1["state at any type<br/>rows 42–43, the faces left"] -->|moves| P3["p3 worker queue"]
  S1 -->|moves| P4["p4 rate limiter"]
  S1 -->|moves| P5["p5 ledger service"]
  S2["queues<br/>DI-11 composites"] -->|moves| P3
  E["error payloads<br/>row 120"] -->|moves| P1["p1 HTTP cache"]
  E -->|moves| P2["p2 handler"]
  E -->|moves| P3
  E -->|moves| P5
  F["derived forms<br/>DI-89, DI-39"] -->|moves| P1
  F -->|moves| P2
  F -->|moves| P3
  F -->|moves| P4
  S1 -->|comes before| S2
```

## How to read a stage

A battery measures one `Reach` value (`Stage.lean`) and pins it to its `stage` declaration. The
fields have these meanings:

| Field | Meaning |
| --- | --- |
| `refused` | Each part of the rc.112 program that the language refuses today, with the build's `verdict` |
| `admitted` | `Api.Author.build` elaborates the battery's program from its authoring source, types it and admits it with its row table |
| `answer` | The run's root exit against rc.112's recorded answer: `rc112`, `differs`, `unfinished` or `notRun` |
| `printed` | `Api.print` answers TypeScript syntax for the program. A read-modify-write row prints its binder term as a function of the current value (the state plan's T5, part A) |
| `readBack` | `Api.readable` holds: reading the program's printing gives the program back |

A battery also pins each error payload part apart from the program's stage (`PartReach`,
`Stage.lean`; decisions row 120). The fields are the build's verdict, whether the part's run
fails with its record as the first typed failure, the module printer's answer (`Api.emitModule`:
`printed`, or a payload class refused by name with its tag) and whether the printed module reads
back (`Api.readModule`). Since part E2 the module declares one `Data.TaggedError` class per tagged
payload type and constructs the payload with `new`.

Each run is a finite probe: one scripted host and one decision tape per run. A stage is not a
theorem. An equal answer is a test on one recorded run, and the battery claims no simulation.

## How a slice moves a program

1. Build the program's battery after the slice lands.
2. If a pin turns red, read what moved: a refused part builds, or a run reaches rc.112's answer.
3. Rewrite the battery's program with the spelling the slice lands.
4. Update the battery's `stage`, then the program's row in this file.
5. Name the moved program in the slice's receipt.

## The scenarios

Decisions row 254 (owner, 2026-10-05) adds scenarios to the acceptance programs. A scenario tests
the semantics where features compose. It is one unit with six parts.

| Part | Content |
| --- | --- |
| Program | One program through `Api.Author.build`, built on the consumer of a battery above |
| Script | A `List Move` (`Scenario.lean`): control decisions, held calls, reply receipts and reply applications. The record lists each script once, as a named run |
| Observation | One named structure read from the run. Every control compares it |
| Claim | One theorem whose proof assembles the clauses. Each clause is a theorem or a planned goal with its placement |
| Controls | For each clause, and for each associated law, a green control and at least one red control. A control names the runs that its comparison reads |
| Lowered runs | The same observation on the generated OCaml engine and on the printed TypeScript module, or the stage that run waits on |

The driver plays a script into the run's own journal. It keeps the reply receipt and the reply
application apart, and it selects a live call by its key. The run a script reaches is the run its
journal reaches (`replays`, `Scenario.lean`), so a replay calls no fixture.

A scenario's record names its program, its observation and its claims as declarations
(`Scenario`, `Scenario.lean`). It lists two kinds of entry.

- An **assembled clause** is a claim that the scenario's claim uses in its proof.
- An **associated law** has controls only. The record claims no dependency of the claim on it.

`#scenario_gate` stands at the foot of each scenario's battery. It checks the record against the
environment and runs the controls once. It refuses:

- a program or an observation that does not resolve to a declaration;
- a claim that is no theorem and no planned goal;
- a claim with no placement (decisions row 207);
- a claim whose proof does not reach one of its assembled clauses;
- a claim that rests on a planned goal which no clause names;
- a clause or a law with no green control, or with no red control;
- a record that lists one run's name twice;
- a named run that no control reads;
- a control that names no clause and no law;
- a control that reads a run which the record does not list;
- a control that fails.

A battery's declaration carries its own placement at a requirement. Any other declaration carries
`@[semantics]`, or the semantics registry places it: as a requirement's top node, as a claim's
pointer, or by its module.

The gate measures the two dependency findings on the planning graph (`ProofGraph.buildPlan`,
`tools/ProofGraph/Plan.lean`). A planned goal is reached when the claim rests on it. A theorem is
reached when the walk from the claim's proof reaches it through the batteries' declarations.

So no control stands outside a scenario, and no scenario stands without a placed claim. Each
control is a finite probe: one script on the Lean machine. A claim's standing is derived from its
proof: `#plan_status` prints it, with the planned goals the claim rests on.

The gate has controls of its own: `Scenario/Gate.lean` runs it over fixture records of that
battery. The gate accepts some, and it refuses the others by name. Most stand on a planned goal
of that battery, which states nothing of a program. Some hold named runs on a small program of
that battery, so that the gate's playing of a run has its controls.

### Where a script lives, and who reads it

A scenario's record lists each of its scripts once, as a **named run** (`NamedRun`,
`Scenario.lean`). A named run holds a name, the built program opened for a run, and the script.
A control holds no script. It names the runs that its comparison reads, and the comparison is a
function of those runs as played.

The diagram shows the three readers of a record's named runs. It claims no order among them.

```mermaid
flowchart LR
  R["a scenario's record<br/>runs: each named run, once"]
  C["a control<br/>reads: the names of its runs"]
  G["the gate<br/>#scenario_gate"]
  H["the host lane<br/>harness/truth/session/Keyed.lean"]
  E["the engine's lane<br/>Scenario/Tape.lean"]
  C -->|names runs of| R
  G -->|plays each run of| R
  G -->|hands the played runs to| C
  H -->|performs each run of| R
  E -->|takes the runs that it names from| R
```

| Reader | What it takes | Where |
| --- | --- | --- |
| The gate | It plays each named run once. It hands each control the runs that the control names, as played. | `Scenario.problems`, `Scenario.lean` |
| The host lane | It performs each named run of the five records, in the record's order. It holds no script. | `Wire.runs`, `harness/truth/session/Keyed.lean` |
| The engine's lane | It takes the runs that `taken` names. It holds two scripts of its own, which no record lists. | `taken` and `own`, `Scenario/Tape.lean` |

A lane quotes a run as the scenario's name, a slash and the run's name. One name has one script
on every lane. The engine's lane refuses an own run that carries the name of a record's run
(`findings`, `Scenario/Tape.lean`), and its writer then writes nothing.

So a changed script of a battery reaches each reader with no second edit:

- the gate, at the battery's next build;
- the host lane, at the next `make check-host-protocol`;
- the engine's fixture, at the next `make gen-fixtures`. The lowered battery is red until then.

Some comparisons do more than read a played run.

- The timeout battery's frontier control sets the fuel of a played run to zero. Then it plays
  one reply application. A script holds no budget, so that one move stands in the comparison.
- The two journal controls play a run's own journal again from the opened program.
- One workers control makes the run that `P3WorkerQueue.drive` drives.
- A control that reads no run compares a program, a typing answer or a run of `Api.run`.

The gate refuses a named run that no control reads. So each run that a lane performs has a
control on the Lean machine.

| Scenario | Program | Observation | Claim, assembled clauses and associated laws | Lowered runs |
| --- | --- | --- | --- | --- |
| workers: `Scenario/Workers.lean`, on p3's consumer | `crew`: two workers with identities. Each holds a connection that its scope releases, takes jobs from the host and notes each assignment in a shared cell. | `Observation`, seven fields: the assignment of jobs to workers, the accepted reply receipts, the reply applications, the retired calls, the cleanup identities, the root's exit and the work left. | `workers` assembles four clauses: `receipt_inert`, `applied_selects` and `control_retires` (theorems of `Scenario.lean`), and the planned goal `releases_once`. That goal says: under every script the crew releases no connection twice. Associated law: `replays`. | Engine: `workers.txt`, five runs of the machine clause. Host: the keyed lane performs each named run that a host can perform. The host measures six entries by itself: the reply receipts, the reply applications, the retired calls, the root's exit, the live calls and the stored replies. It measures five entries through a reader, at the script's end: the assignment and the cleanups through the cells reader, the timers through the sleeps reader, and the runnable fibers and the armed owners through the dispatchers reader, as a count of zero. Where the run's own wait follows the last act, that wait gives the zero. Those two entries then show only that the host came to rest, and the check's table names the scripts. No entry waits. One script has no host run: a forged reply is no act of a host. The program prints and reads back since the state plan's T5, part A (`Scenario/Faces.lean`). |
| queue-workers: `Scenario/QueueWorkers.lean`, on p3's consumer and the public Queue | `crew`: a feeder takes each job from the host row `Jobs.take` and offers it to a queue of capacity 1. Two workers take from the queue, note each assignment and run each job on the host row `Jobs.run`. The root reads the queue's size and polls once at its exit. So the program holds the five public operations of `src/Effect4/Modules/Queue/Ops.lean`. Each of the three crew members holds a connection that its scope releases. | `Observation`, eleven fields: the assignment, the queue's cell up to its handles, the fed jobs, the accepted reply receipts, the reply applications, the retired calls, the opened and the released connections, the count of finished jobs, the root's exit and the work left. | `queueWorkers` assembles seven clauses. Three are theorems of `Scenario.lean`: `receipt_inert`, `applied_selects` and `control_retires`. Four are planned goals over scripts. `held_within_fed`: no job is held more often than the host fed it. `fed_accounted`: each fed job is held, but for one job of a feeder that is gone. `queue_settled`: at rest the queue's registrations are the crew's waits, and no job is stranded. `releases_once`: no connection is released twice. Each goal takes the budget premise `funded`, and the two middle ones hold at rest, on scripts of host acts. Associated laws: `replays` and `funded_replays`. | Engine: `queue-workers.txt`, three runs of the machine clause: the whole run to the root's exit, and the two cancellations between a reply application and its flush. Host: the keyed lane performs each named run that a host can perform. The host measures seven entries by itself: the fed jobs, the reply receipts, the reply applications, the retired calls, the root's exit, the live calls and the stored replies. It measures eight entries through a reader, at the script's end. Five come through the cells reader: the assignment, the queue's cell, the opened connections, the released connections and the count of finished jobs. The timers come through the sleeps reader. The runnable fibers and the armed owners come through the dispatchers reader, as a count of zero, under the limit of the workers scenario's row. No entry waits. The lane compares the queue's cell up to its handles ("The host runs", below). Six scripts have no host run. A forged reply is no act of a host. Three scripts give another row where the machine has work for a flush. Two cancel a fiber between a reply application and its flush, and the third plays the second one's moves on a faulty crew. A host lets every dispatcher run after each act, so it reaches no such state. The engine's fixture holds the two on the crew. Two scripts run at a command budget that cuts a step, and a host has no budget. The program prints and reads back (`Scenario/Faces.lean`). |
| routing: `Scenario/Routing.lean`, on p2's consumer | `request`: p2's handler on its two host rows. `handleOn` writes it over any repository row and any two handler tests. | `Observation`, three fields: the exact response or the failure that escapes, the repository's calls, and the refused rows with the session's reason. | `routing` assembles three clauses: `tagIs_pair` (a theorem: the handler's test is exact on the pair spelling), and the planned goals `infrastructure_escapes` and `unauthorized_calls_nothing`. Associated law: `submit_success_prepared_fits`, a theorem of the law graph. | Engine: `routing.txt`, four runs of the machine clause. Host: the keyed lane performs each named run that a host can perform. The host measures the outcome and the repository's calls. The recorder's ledger predicts the refused rows, and Lean's replay gives the session's verdict of each. No field waits. Two scripts have no host run: the session refuses a reply as `envelope`, and a host has no reply admission. A third stays out: tsgo 7 refuses the printed module of the exact error column. The program prints and reads back (`Scenario/Faces.lean`). |
| atomic: `Scenario/Atomic.lean`, on p4's and p5's consumers | `shop`: a rate-limited ledger. Each request decides over the window in one store step, and an admitted request deposits its number in one store step. Request 2 fails behind both commits. Each request's finalizer notes what it sees. | `Observation`, five fields: each request's outcome, the whole window, the whole account, the count of completed requests and the cleanup log. | `atomic` assembles five clauses. Four are planned goals over every script: `bounded`, `counted`, `committed` and `cleans_once`. One is a theorem on the straight fragment: `unsuspended_runs`. Associated law: `syncRow_typed`, a theorem of the law graph. | Engine: `atomic.txt`, three runs of the machine clause. Host: the keyed lane performs each named run that a host can perform. The shop has no host row, so the host measures no field by itself. It measures all five fields through a reader, at the script's end: the window, the account and the cleanup log through the cells reader, and each request's outcome and the completed count through the fibers reader. No field waits. One script has no host run: it interrupts request 2, whose fiber made no call, so a host with no reader has no name for it. The program prints and reads back since the state plan's T5, part A (`Scenario/Faces.lean`). |
| timeout: `Scenario/Timeout.lean`, on p1's consumer | `fetch`: p1's quote fetch, with a 2000 ms timeout around each attempt and three retries. Each attempt counts itself before its host call, and its finalizer notes how it ended. | `Observation`, nine fields: what became of each held call, the accepted reply receipts, the reply applications, the retired calls and the stored replies. Then the attempts started, the cleanup log, the root's ending and the timer work. | `timeout` assembles three clauses, each a planned goal: `retries_declared`, `stale_never_applies` and `cleanup_keeps`. Associated laws: `applyReply_zero` and `advance_answer_refuses`, theorems of the law graph, and `replays`. | Engine: `timeout.txt`, six runs of the machine clause, and p1's own program as the handle case. Host: the keyed lane performs each named run that a host can perform. The host measures six fields by itself: each held call's fate, the reply receipts, the reply applications, the retired calls, the stored replies and the root's ending. It measures the attempt count and the cleanup log through the cells reader, at the script's end. It measures the timers through the sleeps reader in each script where every sleeping fiber is the root or made a call. In the other scripts the timers wait: a timer's fiber makes no call, so it has no number on the host, and Lean's replay is the timers' only evidence there. So the scenario's whole-observation comparison waits on the timers in those scripts, and the check's table names them. Two scripts have no host run: a forged reply and a direct answer decision are no acts of a host. The program prints since the state plan's T5, part A, and reads back since part B's second step: the checked type reader reads the retry loop's stated cursor type (`Scenario/Faces.lean`). |

A statement over a scenario's runs takes its budget as a premise, under one name: `funded`
(`Scenario.lean`). A funded run is a run that no budget cut: the tape of its own journal, read
from its fresh open, leaves no row unread. The journal's verdicts alone do not decide it. A
reply application has the verdict `applied` as soon as its call's guard is gone, whatever fuel
its step had left. `funded_replays` says what the premise gives: the machine of a funded run is
the raw replay of its tape's decisions. The queue-workers record holds the controls, on one
journal at three command budgets. At the battery's budget the run is funded. At a smaller
budget the journal has a stopped row and the funded run's verdicts, and the queue is not
settled. At a third budget the cut leaves the machine at rest: no work is left, and the root
has no exit. So a machine at rest does not show that its run is funded.

Two cases have no control, and each battery's header states its case.

- A cleanup replayed under one registration (atomic). The cleanup log counts writes by identity,
  and it does not count a finalizer's invocations.
- A timer that fires inside a masked region (timeout). That cut waits for the mask's contract
  (decisions rows 244 to 246).

### The lowered runs

The generated OCaml engine holds no session: no stored reply, no retired call, no consumed call.
So a scenario's observation lands as two clauses.

- **The session clause** is the whole observation. Each scenario's battery checks it on the Lean
  machine. The host run checks it on the printed TypeScript module, on the keyed lane ("The
  host runs", below).
- **The machine clause** is `machineView` (`Scenario.lean`). It holds six readings: the root's
  exit, the cells, the calls the machine waits on, the armed owners, the runnable fibers and the
  timers.

`Scenario/Tape.lean` holds what Lean writes for the machine clause: each scenario's lowered runs,
their machine tapes and the fixture text. Its one gate, of the record `cuts`, reads no committed
file, so it builds whatever the committed files hold. A lowered run with the name of a record's
run is that named run. `taken` lists those names, and the lane writes no script of them. The
lane's own runs are the two of `own`.

The record `cuts` is the journal's cut as a scenario. The driver's reading of a journal stops at
its first stopped row. That row ends at a frontier, or the raw replay does not read past its
decision. The rows before it are the completed prefix.

- **Program and runs.** The crew of the workers scenario, on two of its scripts. The budget
  `cutBudget` makes each journal stop.
- **Claim.** `shown_views_opened`: at a fresh open, a lowered run's views are those of its
  positions, even when later rows stay unread. Its proof uses the clause `position`
  (`tapeFrom_position_replays`): the machine after a position is the raw replay of the decisions
  up to it.
- **Associated laws.** `cut` (`tapeFrom_cut_replays`) and `append` (`tapeFrom_append`). The
  record claims no dependency of the claim on them.
- **Controls.** The second record, `unstopped`, plays the same scripts at the workers' own
  budgets, where no journal stops. The gate must refuse each control that reads a journal for its
  stop.
- **Limit.** No law states the machine after a stopped row. Two red controls show that it is not
  the raw replay of the completed prefix's tape.

A fixture holds the canonical bytes of the admitted program and of each row, and the budgets. It
also holds the machine tape: each decision that moved the session machine, with the view after
it. A decision of the tape may leave the view as it was, as a second interruption of an exited
fiber does. The lane's red control cuts a tape before its last decision that moves the view. That
shorter tape must end at another view than the whole tape's.

`Scenario/Lowered.lean` binds each committed fixture under `ocaml/engine/test/scenarios/` to that
text. `ocaml/engine/test/scenarios/test_scenarios.ml` replays each prefix of each tape through the
generated `api_replay`, with the row table read from its wire bytes, on both instances. It compares
the engine's view with Lean's at every position.

A fixture's line `table differs` or `table same` records one comparison, in one projection. It
says whether the raw replay with the empty table shows another machine view at some position.
`table same` does not say that the replay reads no row of the table. The run `handle/cache` of
`timeout.txt` is p1's own program, whose first host row answers a handle. It is the one run that
says `table differs`.

The theorem `tape_replays` (`Scenario.lean`) is the Lean half. A journal's machine is the raw
replay of its tape, for every run and every journal whose tape reads to its end. The tape holds
the decision that the session hands the machine: for a reply application, the reply's own answer
decision. The battery also checks it at every position of every fixture, as finite runs.
The engine's session clause waits: the engine has no session to compare.

To write the fixtures again, follow these steps from the repository's root.

1. Run `make gen-fixtures`. It builds `Test.Dogfood.Scenario.Tape` and runs the writer,
   `ocaml/engine/test/scenarios/write.lean`. It writes a file only where its bytes differ.
2. Build `Test.Dogfood.Scenario.Lowered`, which binds the files.
3. Run `dune test --force engine/test/scenarios` in `ocaml/`, through `opam exec --switch=effect4`.

Lake does not see a fixture as an input of the battery. So after a change of a fixture alone,
`lake build` takes the battery from its cache and binds nothing. The group `fixtures` closes
that gap (`docs/GENERATED.md`). Its marker depends on the fixtures themselves, so
`make gen-fixtures` writes a changed fixture again from Lean. `make check-gen` refuses a
committed fixture that Lean does not write, and `make check-ocaml` runs after the group.

### The host runs

The keyed lane (`harness/truth/session/`) performs a scenario's scripts on its printed
TypeScript module, on effect 4.0.0-rc.112 under bun. `make check-host-protocol` runs it, and its
last lines give each scenario's counts.

- **A host run** is one named run of a scenario's record: a script, on the program that the
  record opens for it. The lane takes each run from the record (`Wire.runs`, `Keyed.lean`), and
  it holds no script. Lean writes the run's fixture: the printed module, the row table, the
  journal rows that the script leaves and the battery's observation (the mode `scenarios`).
- **The host** acts out each row through the lane's recorder, and it writes a recording.
- **Lean's replay** plays the recording's rows with `Run.play`, and it reads the battery's
  observation. That observation must be the script's.

Each field of an observation has one source of evidence on the host
(`harness/truth/session/keyed-observation.ts`). The check writes each entry's source as one table,
`scenario-evidence.md`, among the results in its work folder. The table's last column gives a
reader's limit on an entry, with the scripts where the limit holds.

| Source | Meaning |
| --- | --- |
| Measured by the host | The host reads the field by itself, from the root's exit and the recorder's ledger. |
| Predicted by the ledger | The field holds the session's refusals. The recorder predicts each one, and the check compares it with the verdict of Lean's replay. |
| Measured through a reader | The host reads the field through a note inside the program's state, at the script's end. |
| Replay only | The host has no reader. Lean's replay is the only evidence, and the scenario's whole-observation comparison waits. |

There are four readers: the cells that the module makes, the fibers that it forks, the pending
sleeps and the count of armed dispatchers. A reader is on only where Lean grants it for a run.
The lane performs each script with no reader, with its readers, and with each reader alone.
Each recording must be the bytes of the run with no reader.

A script has no host run where a host has no act for one of its rows. The driver gives the
reason (`performable`, `harness/truth/session/Keyed.lean`). A run that is not funded has no
host run either: a host has no budget (`emitRun`, in the same file).

The lane compares a module's private cell up to its handles. The queue-workers scenario reads
the Queue's cell, whose waiting requests hold `Deferred` handles. A host has no number for a
`Deferred`. So both faces write one image for it, `{"handle": "deferred"}`, each in a writer
named `cellJson`.

- On the host only the cells reader calls it (`keyed-recorder.ts`). A `Deferred` in a call's
  request or in an exit stays outside the transport profile.
- On the Lean face a scenario's wire chooses it for an entry (`Keyed.lean`). The queue-workers
  wire chooses it for the entry `queue` alone, and every other entry keeps `valJson`.

So a `Deferred` in any other compared value is red.

- The lane compares how many requests stand in the cell, and each request's other fields.
- The lane does not compare which handle stands where.

Two runs of the scenario differ only there. After `parked` the earliest waiting taker is
worker 1's request, and after `rewaiting` it is worker 2's. The two cells differ on the Lean
machine, and their images are equal. The runs `fed` and `rewaiting-fed` show the difference
in an entry that the lane does compare: the next fed job goes to the earliest taker.

Each host run is a finite host run of one script. It establishes no agreement for another
script, no host adequacy and no liveness.

## The earlier dogfood programs

The dogfood notes of 2026-09-15 and 2026-09-16 record findings F1 to F30 over four applications.
Their source files were never committed, so this folder tracks none of them. Program p4 is
dogfood 1's rate limiter, written as an rc.112 user writes it.
