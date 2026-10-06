# 2026-10-05 seat HOST receipt: the four scenarios on their printed TypeScript modules

Status: receipt (history, not authority). Written on 2026-10-06. Brief:
`docs/research/2026-10-05-claude-lead/briefs/seat-host-brief.md`, with the dispatch message and
the coordinator's seven messages of 2026-10-06. Design note:
`docs/research/2026-10-05-seat-HOST-design.md`.

**The one thing to know before merging:** the host driver restates each control's script. So a
changed script of a battery's control does not reach the host runs, and the check stays green
on the old script.

A battery holds a control's script inside a Boolean expression (`controlsOf`,
`Test/Dogfood/Scenario/Workers.lean`). The driver cannot take that script as data. It builds
each script again from the battery's named parts and its literal moves (`routingRuns`,
`workersRuns`, `timeoutRuns` and `atomicRuns`, `harness/truth/session/Keyed.lean`). Two events
of 2026-10-06 show the cost.

- The retry repair (`0f76dd2a`) changed the delays in five scripts of the timeout battery. One
  is a named part, and it reached the driver's draft by its name. Four are inline, and I moved
  each one in the draft by hand.
- My audit of the four batteries found one script that the driver did not list. It was the
  reference run of the workers control of a stale reply. Step 10 adds it.

After a change of a control's script, compare the driver's list with the battery by hand.
Proposal (a) of the last section removes the cause.

Eleven more facts stand beside it.

- **What the merge brings.** Steps 1 and 2 are on main since `11616581`. The next merge brings
  the timeout scenario, the atomic scenario and six later steps. The branch holds main at
  `4990177f`.
- **The head is green.** At `cd0c7172` the default build has 978 jobs and no error, and
  `make check-host-protocol` passes.
- **No theorem lands, and no status moves.** Each host run is a finite host run of one script.
  Its evidence word is tested. It proves nothing.
- **The lane's check is wider.** It builds the four batteries and performs 48 scripts in 171
  runs, so a red battery makes it red. It pins the digest of the four older fixture families'
  recordings (`CASES_SHA256`, `scripts/check-host-protocol.py`). A change of such a family that
  is meant needs a new pin by hand.
- **Routing.** The host measures two entries. The refused rows are the session's: the
  recorder's ledger predicts them, and the verdict is Lean's.
- **Workers.** The host measures six entries by itself and five through a reader. Two of the
  five are zero by the run's own wait in 12 of 17 scripts. Three entries hold one value in
  every script.
- **Timeout.** The whole-observation comparison waits on `timers` in 5 of 15 scripts.
- **Atomic.** The host measures no entry by itself. All five entries come through a reader.
- **Seven scripts have no host run,** and four kinds of control have no script.
- **A reader's effect on its own entries has no control.** No run without the reader reads
  those entries.
- **One printed module does not type-check.** tsgo 7.0.0-dev.20260629.1 gives two diagnostics
  `TS2375` for the routing twin with the exact error column. The lane does not run it.

## Base and head

| Item | Value |
| --- | --- |
| Branch | `seat/host`, in the worktree `/Users/pooks/Dev/lean4-effect4-qtypes` |
| Base at dispatch | `310c8314` |
| Fast-forwards before the first commit | `0f76dd2a`, the retry repair; then `1d292a3d`, seat MASK's first step |
| Step 1 | `2f315cde`: the lane's extension, the design note and the routing scenario |
| Step 2 | `9df7410c`: the workers scenario |
| Step 3 | `16153949`: the timeout scenario |
| Merge of main | `63c68021`, of `c1e22c0a` |
| Step 4 | `13506219`: the atomic scenario |
| Step 5 | `d81e68fd`: the runner refuses another `effect` than the pinned one |
| Step 6 | `c4c37194`: the readers' premises have their controls |
| Step 7 | `e568e3ff`: the readers' control in three parts |
| Step 8 | `5a692205`: the documents |
| Merge of main | `b30d1a03`, of `f569d4af` |
| Step 9 | `e9bdfaf2`: the acceptance line names the scripts that wait |
| Step 10 | `d3494e18`: the audit of the scripts, and the dispatchers reader's limit |
| Head of the work | `d3494e18` |
| Receipt | `0322ad76`: this file, on top of `d3494e18` |
| Merge of main | `69fd8f5a`, of `8528496f` |
| The receipt's first revision | `16a3460c` |
| Merge of main | `796fe8e6`, of `25a90200` |
| Merge of main | `cd0c7172`, of `4990177f`: the head that the coordinator named in the seventh message |
| The receipt's last revision | the commit that revises this file, on top of `cd0c7172` |

Nothing is pushed. On 2026-10-06 the coordinator merged steps 1 and 2 as `11616581`. Three
merges of main follow the head of the work. They bring no file that a step of mine changes
after `f569d4af`. On 2026-10-06 I ran the default build and the lane's check again at each of
the three merged heads. The check gives the same digests and the same table each time.

## Changed files

`git diff --stat 1d292a3d d3494e18`, over the paths below, counts 14 files, 2266 added lines and
55 removed lines. `git diff --stat f569d4af d3494e18` counts the steps that main does not hold
yet: 9 files, 454 added lines and 90 removed lines. The receipt's two commits add this file and
one sentence of the design note's header.

| File | What changed |
| --- | --- |
| `harness/truth/session/Keyed.lean` | The modes `scenarios` and `scenario-batch`: the runs, the rule `performable`, the readers' premises, the fixture and the replay. `consume` reads a record through `command`. |
| `harness/truth/session/keyed-recorder.ts` | A fixture may be `scripted`: the ledger of held calls, `hold`, `cancel`, `flush`, `snapshot` and the ledger's predictions. Records enter the value wire. |
| `harness/truth/session/keyed-bindings.ts` | The scripted host, the rows of a scenario's table, the cells reader's `Ref`, the fibers reader's `Effect` and the count of armed dispatchers. |
| `harness/truth/session/clock.ts` | The sleeps reader, off by default. |
| `harness/truth/session/keyed-observation.ts`, new | Each entry's source on the host, for each scenario. |
| `harness/truth/session/run-keyed.ts` | The scenarios' half: it performs each script with no reader, with its readers and with each reader alone. It refuses another `effect` than the pinned one. |
| `harness/truth/session/prepare-keyed-controls.ts` | The moved recordings of Lean's replay control. |
| `harness/truth/session/check-keyed.ts` | The four comparisons, the red controls, the table `scenario-evidence.md` and the acceptance line. |
| `harness/truth/session/keyed-protocol.test.ts` | Twelve unit tests of the scripted recorder and of the readers. |
| `scripts/check-host-protocol.py` | The scenarios' steps, the pin `CASES_SHA256`, and the builds of the four batteries. |
| `Makefile` | The batteries and the prelude are inputs of the check's marker. |
| `Test/Dogfood/README.md` | Each scenario's host result, and the section "The host runs". |
| `docs/GENERATED.md` | One paragraph under "Host protocol projections". |
| `docs/research/2026-10-05-seat-HOST-design.md` | The design note, with the coordinator's ruling in its section 8. |

No file under `src/`, `ts/` or `generated/` changes. No battery changes. The printer and the
prelude are as main has them. No fixture of a scenario is committed: the check writes each one
afresh. I did not edit `docs/core/decisions.md`, `lakefile.toml`, `docs/STATE.md` or
`generated/semantics.md`.

## Commands and results

`SLOT` is `LEAN_NUM_THREADS=3 /Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`. Each Lean
command and each Lake command below runs through it. One version query is the exception, and
the table of the other commands names it. `FLAGS` is
`-o build -o ts/eff/node_modules -o harness/truth/node_modules`. `WORK` is
`harness/truth/session/.work/latest`, which the check writes and git ignores.

| Tool | Version | Command |
| --- | --- | --- |
| The host | bun 1.4.2 | `bun --version` |
| The pinned library | effect 4.0.0-rc.112, loaded from the directory `ts/eff/node_modules/effect` | the runner's first line, and `WORK/host/versions.json` |
| The TypeScript compiler | tsgo 7.0.0-dev.20260629.1, the pinned `@typescript/native-preview` | `node ts/eff/node_modules/@typescript/native-preview/bin/tsgo --version` |
| node, which starts tsgo | v22.23.2 | `node --version` |
| Lean | 4.33.1 | `lean-toolchain` |

The seat runs no `tsc` and no `typescript` below 7. It installs nothing and downloads nothing.
The two `node_modules` folders are links to the coordinator's folders.

### The default build

```text
SLOT lake build
```

| Tree | Result |
| --- | --- |
| `310c8314`, the base | `Build completed successfully (956 jobs).` |
| `13506219`, step 4 | `Build completed successfully (963 jobs).` |
| `b30d1a03`, main merged at `f569d4af` | `Build completed successfully (972 jobs).` |
| `d3494e18`, the head of the work | `Build completed successfully (972 jobs).` |
| `69fd8f5a`, main merged at `8528496f` | `Build completed successfully (977 jobs).` |
| `796fe8e6`, main merged at `25a90200` | `Build completed successfully (978 jobs).` |
| `cd0c7172`, main merged at `4990177f` | `Build completed successfully (978 jobs).` |

### The lane's check

```text
SLOT make FLAGS check-host-protocol
```

Its result at `cd0c7172`, exit status 0. At `d3494e18`, `69fd8f5a` and `796fe8e6` it gives the
same lines, but for the time of the unit tests.

```text
python3 scripts/check-host-protocol.py
Build completed successfully (421 jobs).
Build completed successfully (422 jobs).
Build completed successfully (439 jobs).
Build completed successfully (438 jobs).
Build completed successfully (449 jobs).
Build completed successfully (450 jobs).
Build completed successfully (28 jobs).
keyed host: effect 4.0.0-rc.112 under bun 1.4.2, loaded from /Users/pooks/Dev/lean4-effect4/ts/eff/node_modules/effect
PASS keyed host: 57 actual rc.112 runs; 52 admitted printed programs
PASS keyed scenarios: 48 scripts performed on actual rc.112 in 171 runs: each with no reader, with its readers, and with each reader alone; 7 scripts with no host run
bun test v1.4.2 (744846f84)

 54 pass
 0 fail
 468 expect() calls
Ran 54 tests across 4 files. [62.00ms]
PASS keyed differential: 57 runs, 52 programs, 30 controls; exact exits and keyed applications
PASS keyed scenarios on effect 4.0.0-rc.112 under bun 1.4.2: routing 8 scripts (2 entries measured by the host, 1 predicted by the ledger; no entry waits); workers 17 scripts (6 entries measured by the host, 5 through a reader, 2 of them zero by the run's own wait in 12 scripts; no entry waits); timeout 15 scripts (6 entries measured by the host, 2 through a reader, timers through a reader in 10 scripts; the whole-observation comparison waits on timers in 5 scripts (parked, timed-out, late, received, eager)); atomic 8 scripts (0 entries measured by the host, 5 through a reader; no entry waits); 7 scripts with no host run; 40 red controls
PASS host-protocol: fresh projections, typed host programs, keyed replay and negative controls; the scenarios' scripts on their printed modules
```

The seven build lines are the narrow builds. In order they are
`Test.Api.HostSessionContract`, `Test.Api.KeyedHostContract`, the batteries
`Test.Dogfood.Scenario.Workers`, `Routing`, `Atomic` and `Timeout`, and `Tools.ProfileJson`.
`harness/truth/session/Keyed.lean` is the one Lean file that I changed. It is a driver, and no
Lake library holds it. The check elaborates it with `-DwarningAsError=true`, once for each of
its six calls.

The check has these steps for the scenarios.

1. Lean writes the fixtures: `Keyed.lean scenarios`.
2. The runner performs the scripts: `run-keyed.ts`.
3. The script compares the digest of `cases.json` with its pin.
4. tsgo 7 checks 157 written modules and the lane's sources. Of them 48 are a scenario's module
   under the plain header, and 57 are one under another header.
5. Lean replays the recordings and the moved recordings: `Keyed.lean scenario-batch`, twice.
6. `check-keyed.ts` compares, and it writes the table.

### The documents

```text
python3 scripts/check-docs.py
PASS check-docs: every path, link, citation and make target in 75 documents resolves
```

`make FLAGS check-docs` exits with status 0 on the same tree. `python3 scripts/check-language.py
--show FILE` gives no finding for the design note and for this receipt. It gives 2 findings for
`Test/Dogfood/README.md`, at two sentences that the base holds. It gives 20 findings for
`docs/GENERATED.md` before my paragraph and 20 after it.

### The other commands

| Command | Result |
| --- | --- |
| The check's script with one digit of the pin changed, in a copy | `FAIL host-protocol: the recordings of the four fixture families moved`, exit status 1 |
| `bun harness/truth/session/run-keyed.ts WORK/fixtures.json OUT WORK/scenarios.json`, five times | Six output files, each with one digest over the five runs and the check's run |
| `SLOT lake env lean PlanStatus.lean`, with one `#plan_status` line a node | The statuses of the section "Open obligations" |
| The loop over the written modules, below | 57 modules, each with 0 differing lines under its header |
| The count of fork heads, below | 78 `forkChild`, 8 `forkDetach` and 34 `forkScoped`, each with an effect first; 15 `raceAll` |
| `lean --version`, once, outside `SLOT` | A version query: it elaborates nothing |

```text
cd harness/truth/session/.work/latest/host
for f in *.readers.ts *.only-*.ts *.drops-assignment.ts; do
  diff "${f%%.*}.ts" "$f" | grep '^[<>]' |
    grep -v -c '^[<>] \(import \|const Ref = \|const Effect = \|namespace \)'
done | sort | uniq -c
cat $(ls | grep -E '^(routing|workers|timeout|atomic)-[^.]*\.ts$') |
  grep -o 'Effect\.\(fork[A-Za-z]*\|race[A-Za-z]*\)(.' | sort | uniq -c
```

### Not run

The brief excludes each command below. Each is **not run**.

- `make check-gen`
- `make check-slow`
- `make check-corpus`
- `make check-target`
- `make check-truth`
- the conservativity script
- the ledger promotion

These are not run either.

- `make check` and `make check-full`, as wholes, and `lake build Test`.
- `make check-tsdiag` and `make check-schema-ts`: the brief names them as red before this work.
- Any command of the OCaml estate.

At the end of the work, on 2026-10-06, the disk had 24 GiB free.

## Axiom output

No declaration of an `Effect4.*` module or of a `Test.*` module changes. The axiom gate audits
those modules, so its result is the one of main. `Keyed.lean` states no theorem. It holds five
`#guard` lines of the readers' premises and no `sorry`.

## Evidence

Each host run is a finite host run of one script: tested. Each comparison with the base's bytes
is reproduced. A fact that I take from a source is marked reading. Nothing here is proved.

All of it is bounded, and all of it is host-only. A host run holds for one script, one schedule
and one program, on effect 4.0.0-rc.112 under bun 1.4.2. It establishes no agreement for another
script or another entry, no host adequacy and no liveness.

### The brief's acceptance

| Item of the brief | Result at `cd0c7172` |
| --- | --- |
| 1. Routing and workers run, for each script that a host can perform. | 8 and 17 scripts. Each entry with a source on the host agrees, and Lean's replay gives each observation. |
| 2. Each printed module type-checks under tsgo 7, or its diagnostics are here. | 16 modules type-check. One twin's module has two diagnostics, quoted below. |
| 3. The three red controls are red, each at its connector. | 1, 4 and 8 of the 40 red controls. |
| 4. `make check-host-protocol` passes, and the lane's own runs are unchanged. | It passes. Five files are the base's bytes. |
| 5. Timeout and atomic: landed, or waiting. | Landed: 15 and 8 scripts. Timeout waits on `timers` in 5 of them. |
| 6. The builds, the lane's check and `make check-docs`. | Under "Commands and results". |
| 7. The commands that the seat does not run. | Under "Not run". |

### Each entry's source of evidence

A source is not an evidence word. An entry of an observation has one of four sources.

| Source | Meaning |
| --- | --- |
| host | The host measures the entry by itself, in the run with no reader. |
| ledger | The entry holds the session's refusals. The recorder's ledger predicts each one, and the check compares it with the verdict of Lean's replay. The verdict is replay evidence. |
| reader: N | The host measures the entry through the reader N, at the script's end. It is no unassisted host measurement. |
| replay only | The host has no reader. Lean's replay is the only evidence, and the scenario's whole-observation comparison waits. |

The check writes the table below at each run, as `WORK/host/scenario-evidence.md`. Its command
is `SLOT make FLAGS check-host-protocol`. This copy is the file's bytes at `d3494e18` and at
each of the three merged heads after it.

| Scenario | Entry | Evidence | Scripts | Limit |
| --- | --- | --- | --- | --- |
| routing | `outcome` | host | all 8 |  |
| routing | `repositoryCalls` | host | all 8 |  |
| routing | `refusals` | ledger | all 8 |  |
| workers | `assignment` | reader: cells | all 17 |  |
| workers | `receipts` | host | all 17 |  |
| workers | `applications` | host | all 17 |  |
| workers | `retired` | host | all 17 |  |
| workers | `cleanups` | reader: cells | all 17 |  |
| workers | `rootExit` | host | all 17 |  |
| workers | `workLeft.runnable` | reader: dispatchers | all 17 | zero by the run's own wait, in 12 of 17: applied-2, applied-1-2, applied-2-1, unreceived, applied-1, stale, cancelled-running, cancelled-between, cancelled-root, lowest, cancelled, twice |
| workers | `workLeft.queued` | reader: dispatchers | all 17 | zero by the run's own wait, in 12 of 17: applied-2, applied-1-2, applied-2-1, unreceived, applied-1, stale, cancelled-running, cancelled-between, cancelled-root, lowest, cancelled, twice |
| workers | `workLeft.awaiting` | host | all 17 |  |
| workers | `workLeft.pending` | host | all 17 |  |
| workers | `workLeft.timers` | reader: sleeps | all 17 |  |
| timeout | `calls` | host | all 15 |  |
| timeout | `receipts` | host | all 15 |  |
| timeout | `applications` | host | all 15 |  |
| timeout | `retired` | host | all 15 |  |
| timeout | `stored` | host | all 15 |  |
| timeout | `attempts` | reader: cells | all 15 |  |
| timeout | `cleanups` | reader: cells | all 15 |  |
| timeout | `root` | host | all 15 |  |
| timeout | `timers` | replay only | 5 of 15: parked, timed-out, late, received, eager |  |
| timeout | `timers` | reader: sleeps | 10 of 15: 503, four, 404, before, second, kept, timer-interrupt, host-interrupt, applied, resetting |  |
| atomic | `decisions` | reader: fibers | all 8 |  |
| atomic | `window` | reader: cells | all 8 |  |
| atomic | `account` | reader: cells | all 8 |  |
| atomic | `completed` | reader: fibers | all 8 |  |
| atomic | `cleanups` | reader: cells | all 8 |  |

In each of the 48 scripts every entry with a source on the host is the entry of the Lean
machine. Lean's replay of each recording gives the script's observation, field for field. Each
of the ledger's 11 predictions is the session's verdict of the same record, and the session
refuses no other record.

Five statements keep the table from showing more than it holds.

- **Routing's refused rows.** The host has no session, so it refuses nothing. The ledger
  predicts a refusal, and Lean's replay gives it. One script of the eight has refused rows:
  `eager`.
- **The dispatchers reader.** The run with its readers waits until no dispatcher is armed. The
  reader reads its count after that wait in 12 scripts, so its zero shows only that the host
  came to rest. In the 5 other scripts a held call or a reply receipt ends the script. No wait
  follows it, and the zero shows that the act armed no dispatcher.
- **Three constant entries.** `workLeft.runnable`, `workLeft.queued` and `workLeft.timers` are
  the empty list in each of the 17 scripts, on both sides. The count comes from the fixtures:
  each other entry of the four scenarios has from 2 to 10 values over its scripts.
- **Timeout's timers.** In 5 scripts the timer's fiber sleeps at the end. It made no call, so
  the host has no number for it, and Lean refuses the sleeps reader there.
- **Atomic.** The shop has no host row. The recorder sees no call and names no fiber but the
  root. So the cells reader and the fibers reader give all five entries.

### The scripts

The driver lists 55 scripts. A host performs 48 of them. The names are the driver's.

| Scenario | Performed | No host run |
| --- | --- | --- |
| routing | 8: `200`, `404`, `401`, `escape`, `business-tag`, `misnamed`, `catch-all`, `eager` | 3: `wide`, `exact-business-tag`, `exact-escape` |
| workers | 17: `parked`, `received`, `received-reversed`, `duplicate`, `applied-2`, `applied-1-2`, `applied-2-1`, `unreceived`, `applied-1`, `stale`, `cancelled-running`, `cancelled-early`, `cancelled-between`, `cancelled-root`, `lowest`, `cancelled`, `twice` | 1: `crossed` |
| timeout | 15: `parked`, `503`, `timed-out`, `four`, `404`, `before`, `second`, `late`, `kept`, `timer-interrupt`, `host-interrupt`, `received`, `applied`, `eager`, `resetting` | 2: `crossed`, `direct` |
| atomic | 8: `started`, `refilled`, `finished`, `stopped`, `racy`, `erased`, `undone`, `twice` | 1: `interrupted` |

The 48 scripts run on 16 printed modules: 6 of routing, 2 of workers, 3 of timeout and 5 of
atomic. They hold 317 acts. The 171 runs are 48 with no reader, 48 with the readers and 75 with
one reader alone.

Lean gives the reason of each script with no host run (`performable`, `Keyed.lean`).

| Script | Reason |
| --- | --- |
| `routing/wide` | The session refuses the reply as `envelope`, and a host has no reply admission of its own. |
| `routing/exact-business-tag` | The same refusal. |
| `routing/exact-escape` | tsgo 7 refuses the printed module of the exact error column. |
| `workers/crossed` | A forged reply: a host's reply carries the call id of the call that it holds at the key. |
| `timeout/crossed` | A forged reply. |
| `timeout/direct` | A direct answer decision is no act of a host. |
| `atomic/interrupted` | The host has no name for fiber 3: it made no call before its cancellation. |

Four kinds of control have no script, so they have no host run either.

- The timeout battery's frontier control edits the budget of a run.
- The journal controls of the workers battery and of the timeout battery play a journal.
- One workers control compares the run that `P3WorkerQueue.drive` makes.
- The atomic battery's straight clause runs the request alone with `Api.run`, at a bound. It
  compares no `Observation`.

The driver lists one script that no control plays alone: the timeout battery's part `parked`.

### The red controls

The check counts 40 red controls of the scenarios. Each one must fail, and the check fails
where one passes.

| Connector | Count | Fault | Where it must fail |
| --- | --- | --- | --- |
| The host's measurement | 1 | A faulty `Ref` of the host drops one update of the cell `assigned`, in `workers/lowest`. The root's exit does not read that cell. | At `assignment`, and at no other entry. |
| The comparator | 4 | One changed expectation of a fixture, in one script of each scenario. | By the run's name, at the changed entry. |
| Lean's replay | 8 | One recording with a moved record. Four move a reply application before its receipt, or the second record before the first. Four move a late reply to stand after its call. | Lean shows another observation, or a verdict that the ledger did not predict. |
| The readers' control | 4 | One dropped record of a recording, in one script of each scenario. | At the comparison of the two recordings. |
| The ledger's predictions | 8 | One prediction taken away, in each script that has one. | At a verdict that no prediction covers. |
| A reader's premise | 15 | The timeout program holds a race. | Lean refuses the fibers reader in each of the 15 scripts, with the race as its reason. |

Three more controls stand outside that count.

- **The pin.** With one digit of `CASES_SHA256` changed, the check's script exits with status
  1, and its message gives both digests. Tested on 2026-10-06, in a copy that I removed. No
  fixture keeps this control.
- **The driver's guards.** `Keyed.lean` holds five `#guard` lines of the readers' premises on
  small programs. With one guard negated in a copy, the driver stops at that guard. Tested on
  2026-10-06.
- **The unit tests.** Twelve tests of `keyed-protocol.test.ts` cover the scripted recorder and
  the readers. One shows that a fixture with no mark takes no scripted branch.

### The four older fixture families

The lane's own runs are as they were. Five files of the check's work folder are the bytes of
the same files at the base `310c8314`: reproduced.

| File | What it holds |
| --- | --- |
| `fixtures.json` | Lean's fixtures of the four families |
| `host/cases.json` | The recordings of the 57 runs |
| `host/controls.json` | The 30 control recordings |
| `lean.json` | Lean's replay of the recordings |
| `controls-lean.json` | Lean's replay of the controls |

The digest of `host/cases.json` is the pin. So `consume`, which now reads a record through
`command`, gives the verdicts of the base.

### The readers and the six conditions

The coordinator settled four readers on 2026-10-06, under six conditions. The design note's
section 8 holds the ruling.

| Condition | How the lane meets it | Evidence |
| --- | --- | --- |
| A transparency control | The runner performs each script with no reader, with its readers, and with each reader alone. The check compares each recording with the plain run's, byte for byte. It compares the root's exit and each entry of the plain run too. | Tested: no difference in 48 scripts, so the control refuses no reader. |
| Off by default | A reader is on only where Lean grants it in the fixture (`readersOf`, `Keyed.lean`). | Reproduced: the digest pin. Tested: two unit tests. |
| Harness only | Each reader lives under `harness/truth/session/`. The module's text under the header is the same bytes. | Tested: the loop above, 57 modules. tsgo 7 checks each module under each header. |
| A spy gives the pinned object | The reader's `Ref` and `Effect` inherit from the pinned ones (`withSpies`, `keyed-bindings.ts`). A spy calls the pinned head and hands on the cell or the fiber that it made. | Tested: two unit tests compare each other member by identity, the cell by identity and a fiber by its id. |
| An evidence word a field | The table above. | The check writes it. |
| A reader refuses, and does not guess | Lean checks each premise on the program and the run. The runner compares each count with Lean's, and it refuses a reader on a difference. | Tested: the premise's 15 red controls, and Lean's 5 refusals of the sleeps reader. |

One thing of the fourth row is exact only in part. The cell and the fiber are the pinned
objects. The effect that makes one is the pinned effect under one `Effect.map`, which holds the
note. So a run with a reader has one more step at each cell and at each fork. The transparency
control is what checks that this step changes nothing that the plain run shows.

**The header's difference.** `diff` of the plain module and the module with readers gives these
changed lines for an atomic script, and no other one.

```text
< import { Cause, Context, Data, Deferred, Effect, Exit, Fiber, Layer, Option, Ref, Scope, pipe } from "effect"
> import { Cause, Context, Data, Deferred, Effect as PinnedEffect, Exit, Fiber, Layer, Option, Ref as PinnedRef, Scope, pipe } from "effect"
< import { scenarioRows } from "./../../../keyed-bindings.ts"
> import { scenarioEffect, scenarioRef, scenarioRows } from "./../../../keyed-bindings.ts"
> const Effect = scenarioEffect("atomic/started")
> namespace Effect { export type Effect<A, E = never, R = never> = PinnedEffect.Effect<A, E, R> }
> const Ref = scenarioRef("atomic/started")
> namespace Ref { export type Ref<A> = PinnedRef.Ref<A> }
```

A workers module and a timeout module take the four `Ref` lines only. A routing module has no
second header. The module of the host's fault differs from the workers module in one word:
`scenarioRef("workers/lowest", "drops-assignment")`. The sleeps reader and the dispatchers reader
change no header.

**The fork heads.** The fibers reader's `Effect` owns `forkChild`, `forkScoped` and `forkDetach`,
each in both call forms. The 48 modules print 120 fork heads, each with the effect first and an
options object after it. No module prints a head with the options alone. A unit test covers that
second form. `raceAll` is no fork head, and the fibers reader has no premise for a program that
holds one.

**The scheduler.** The dispatchers reader makes `new Scheduler.MixedScheduler("async", f)`. The
second argument is the real `setImmediate` behind a counter. The default of rc.112 is the same
class in the same mode, over its own wrapper of `setImmediate`. Its source is `MixedScheduler`
(`vendor/effect-4.0.0-rc.112/src/Scheduler.ts`): reading. The run with no reader passes no
scheduler.

**The fixed wait.** The run with no reader cannot see whether a dispatcher is armed, so it
waits 64 turns after an act. So does a run with one reader alone. Both are references of the
readers' control. No value measured through a reader uses the fixed wait: each one comes from
the run with the exact wait. The entries with the source host come from the run with no reader,
so they stand on the fixed wait. The control requires that the run with the exact wait gives
the same entries, and it does in 48 scripts.

**What each reader has alone.** The cells reader, the fibers reader and the sleeps reader each
have a run alone: 75 runs. The dispatchers reader is the scheduler itself, so it has no run
alone under the plain scheduler. A routing script's run with readers has the counting scheduler
and no reader beside it.

### The recorder's extension

The coordinator had no objection to the design on 2026-10-06, and added one rule. A note of the
recorder is a prediction, and the recorder is no second session.

- **Only a marked fixture.** A fixture with `scripted: true` takes the new branches. A fixture
  of the four older families has no mark, and a unit test holds that it refuses as before.
- **A late reply.** A cancellation retires the held calls whose callback it interrupts. A reply
  for a retired call is written as a `reply` record, stored nowhere and predicted as `noCall`.
- **Two rules, both the session's.** The ledger predicts `noCall` for a reply or an application
  with no live call, and `pendingReply` for a second reply at a key. They are `submit`'s and
  `applyReply`'s (`src/Effect4/Api/HostSession.lean`).
- **Each prediction is checked.** The check compares the 11 predictions with Lean's verdicts,
  record for record. Eight scripts have one.
- **A script that ends with live work.** `finish` refuses a live call. A scripted run ends with
  `snapshot`, which writes the records so far and appends no flush.

### Two finite host probes outside the lane

Neither probe is in the check. Each ran on 2026-10-06, on effect 4.0.0-rc.112 under bun 1.4.2.
Their files are in my scratch folder and in the ignored work folder.

**The reply admission.** The probe has three steps.

1. Take the fixture of `routing/200` from `WORK/scenarios.json`, and name it `routing/wide`.
2. Widen the second reply's host answer: the caller's record gets the field `createdAt`.
3. Run the runner on that one fixture, then `Keyed.lean scenario-batch` on its recording.

The host performs the ten acts.

| Side | `outcome` | `repositoryCalls` | Refused rows |
| --- | --- | --- | --- |
| The host | the response 200 with `bob` | `[1, 2]` | none predicted |
| Lean's replay of the host's recording, as `routing/wide` | none | `[1]` | five |

Lean's verdicts are, in order: `progressed`, `bound`, `preflight`, `applied`, `bound`, then the
refusals `envelope`, `noCall`, `staleCall`, `noCall` and `noCall`. So a host with no reply
admission goes on where the session stops. The lane has no act for that refusal.

**The exact error column.** The module of the battery's twin `exact` gets two diagnostics.

```text
harness/truth/session/.work/dev/exact/host/routing-exact-escape.ts(6,407): error TS2375: Type 'Effect<never, readonly ["Unauthorized", "bad token"], never> | Effect<{ readonly id: number; readonly name: string; readonly role: "admin" | "member"; }, readonly ["NotFound", "1"] | readonly [...] | readonly [...] | readonly [...], never>' is not assignable to type 'Effect<{ readonly id: number; readonly name: string; readonly role: "admin" | "member"; }, readonly ["Unauthorized", "bad token"], never>' with 'exactOptionalPropertyTypes: true'. Consider adding 'undefined' to the types of the target's properties.
harness/truth/session/.work/dev/exact/host/routing-exact-escape.ts(6,700): error TS2375: Type 'Effect<never, readonly ["Unauthorized", "not yours"], never> | Effect<{ readonly id: number; readonly name: string; readonly role: "admin" | "member"; }, readonly ["NotFound", "2"] | readonly [...] | readonly [...], never>' is not assignable to type 'Effect<{ readonly id: number; readonly name: string; readonly role: "admin" | "member"; }, readonly ["Unauthorized", "not yours"], never>' with 'exactOptionalPropertyTypes: true'. Consider adding 'undefined' to the types of the target's properties.
```

The compiler is tsgo 7.0.0-dev.20260629.1, and it exits with status 1. Both places are a
printed `ifElse`: `Effect.suspend(() => test ? Effect.fail(…) : Effect.flatMap(…))`. Under the
exact column the two arms' error types have no common supertype among them. That sentence is
my reading of the two diagnostics. With the reason taken out in a copy of the driver, the host
performs `exact-escape`. Its three entries are the Lean machine's, and Lean's replay gives the
script's observation. The other 16 modules type-check, the shop's and the fetch's among them.

## Landed theorems and their placement

None. The slice states no theorem, so it has no placement block. Its evidence is a control of
claims that the tree places already.

| Evidence | Claim that it is a control of | Reach | It does not establish |
| --- | --- | --- | --- |
| An entry with the source host, or with a reader | The scenario's claim: `routing`, `workers`, `timeout` or `atomic`. Then `host-session-protocol`, R6, and `translation-simulation`, R8. | One script, one schedule, on rc.112 under bun, the entries with that source | No agreement for another script or another entry, no host adequacy, no liveness |
| Lean's replay of the host's recording | The same claim, and `run-tape-replay` for the machine | The recording that the host wrote | Nothing of the host beyond the recording |
| A prediction of the ledger | `host-session-protocol`, R6 | The two refusals `noCall` and `pendingReply`, in eight scripts | No other refusal of the session |

## Open obligations

### The requirements R1 to R13

The statuses below come from two tools at the head: the plan of `generated/semantics.md`, and
`#plan_status` over the batteries. This receipt keeps no status of its own.

**The claims and the requirement rows that the slice adds a control to.** No status moves.

| Requirement | Node | Status | What the slice adds |
| --- | --- | --- | --- |
| R4 | `atomic` (`Test/Dogfood/Scenario/Atomic.lean`) | modulo | 8 scripts, each entry through a reader |
| R6 | `workers` (`Test/Dogfood/Scenario/Workers.lean`) | modulo | 17 scripts |
| R6 | `timeout` (`Test/Dogfood/Scenario/Timeout.lean`) | modulo | 15 scripts |
| R6 | `receipt_inert`, `applied_selects`, `control_retires` (`Test/Dogfood/Scenario.lean`) | proved | The host keeps a receipt and an application apart in each script |
| R8 | `tape_replays`, the claim `run-tape-replay` | proved | Lean replays 48 recordings that a host wrote |
| R8 | The open part on the TypeScript face against rc.112 | open | 48 finite host runs beside the truth harness. The part stays open. |
| R10 | `routing` (`Test/Dogfood/Scenario/Routing.lean`) | modulo | 8 scripts |
| R13 | `replays` (`Test/Dogfood/Scenario.lean`) | proved | Each replay plays a recorded input |

The semantics registry's claims of `host-session-protocol` keep their statuses. `host-progress`
stays assumed: a host run is one external driver at work, and it shows no progress law.

**The goals and the premises that the claims still rest on.** `#plan_status` gives the goals.
Its first line for each claim, at the head:

```text
Test.Dogfood.Scenario.Routing.routing: modulo [Test.Dogfood.Scenario.Routing.infrastructure_escapes, Test.Dogfood.Scenario.Routing.unauthorized_calls_nothing]; nearest []; 0 lemmas, 0 definitions
Test.Dogfood.Scenario.Workers.workers: modulo [Test.Dogfood.Scenario.Workers.releases_once]; nearest []; 0 lemmas, 0 definitions
Test.Dogfood.Scenario.Timeout.timeout: modulo [Test.Dogfood.Scenario.Timeout.cleanup_keeps, Test.Dogfood.Scenario.Timeout.retries_declared, Test.Dogfood.Scenario.Timeout.stale_never_applies]; nearest []; 0 lemmas, 0 definitions
Test.Dogfood.Scenario.Atomic.atomic: modulo [Test.Dogfood.Scenario.Atomic.bounded, Test.Dogfood.Scenario.Atomic.cleans_once, Test.Dogfood.Scenario.Atomic.committed, Test.Dogfood.Scenario.Atomic.counted]; nearest []; 0 lemmas, 0 definitions
Test.Dogfood.Scenario.tape_replays: proved; nearest []; 0 lemmas, 0 definitions
Test.Dogfood.Scenario.replays: proved; nearest []; 0 lemmas, 0 definitions
Test.Dogfood.Scenario.receipt_inert: proved; nearest []; 0 lemmas, 0 definitions
Test.Dogfood.Scenario.applied_selects: proved; nearest []; 0 lemmas, 0 definitions
Test.Dogfood.Scenario.control_retires: proved; nearest []; 0 lemmas, 0 definitions
```

| Claim | Planned goals that it rests on |
| --- | --- |
| `routing` | `infrastructure_escapes` (R10), `unauthorized_calls_nothing` (R5) |
| `workers` | `releases_once` (R11) |
| `timeout` | `retries_declared` (R10), `stale_never_applies` (R6), `cleanup_keeps` (R11) |
| `atomic` | `bounded`, `counted`, `committed` (R4), `cleans_once` (R11) |

The slice's own evidence rests on four premises.

- **The readers' premises.** The root makes every cell before it makes a fiber. A program with
  the fibers reader holds no race and no fork inside a forked program. Lean checks each one on
  the program and the run.
- **The order of a fork.** rc.112 starts forked fibers in fork order. It is observed in each
  run, and no theorem states it.
- **The host's rest.** A run with readers waits until no dispatcher is armed. That the wait
  ends is observed, and it is no liveness law.
- **The driver's scripts.** Each script of the driver is the control's script. I compared them
  by hand on 2026-10-06, and no check holds it.

**The older open parts of the same requirements, which the slice leaves untouched.** Each is an
open part of `generated/semantics.md`, under its requirement. The slice closes none of them.

| Requirement | Open parts | The nearest to this slice |
| --- | --- | --- |
| R4 | 5 | The target half of `handle-identity-laws`; `atomic-attempt-isolation` |
| R5 | 2 | `lower_refines_build` |
| R6 | 7 | Receipt and application on the keyed lifecycle, and their converse; DI-57's table-aware reference; DI-69; the public typed guarantee |
| R8 | 6 | One identity bijection across faces (DI-81); the TypeScript face against rc.112 (DI-49) |
| R10 | 12 | A composed module's law; no form has a behaviour law (DI-89) |
| R11 | 6 | Release at most once for each registration, counted by identity (DB-07) |
| R13 | 4 | Load inputs, the environment snapshot and the seed |

The counts come from one command at `cd0c7172`. They move with main: the merges of 2026-10-06
changed the counts of R4, R8 and R10 while this receipt was written. Take a count from the
tool at the head that you cite.

```text
awk '/^### R[0-9]+:/ {r=$2} /^- Open:/ {c[r]++} END {for (k in c) print k, c[k]}' generated/semantics.md
```

The ten planned goals above stay goals. No open planned goal would not mean that the semantics
is finished.

### The choices

Each choice is mine unless the row names the coordinator.

| Choice | Reason |
| --- | --- |
| The fixture's script is the journal that the battery's driver leaves (`Scenario.play`). | The host acts out a row, so TypeScript resolves no selector a second time. A move with no row has no act. |
| The driver restates each control's script. | A battery holds a script inside a Boolean expression. See the first item. |
| Lean decides by rule which script a host can perform (`performable`). | A script outside the lane gets a reason, and no program is rewritten. |
| The host's readings restate the battery's `observe` in TypeScript (`keyed-observation.ts`). | The cell's index, the exit's ending and a request's outcome are small projections. A difference shows as an entry's disagreement. |
| The recorder writes a record value as its frame. | A scenario's request and its answers are records. The four older families hold none, and the pin shows it. |
| `consume` reads a record through `command`, the one mapping of a record to a row (`Keyed.lean`). | The replay of a scenario's recording uses the same mapping. The older families' verdicts are the base's bytes. |
| A scripted run ends with `snapshot`, and not with `finish`. | A script may end before the root does, with a live call or a stored reply. |
| One module a header text. | Two runs with one header share a module, and its text under the header is verbatim. |
| The fault of the host's measurement lives in one header. | Only the red control's module binds a faulty `Ref`. No other run can take it. |
| The runner refuses another `effect` than the pinned one. | bun loads a newer `effect` from its cache for a module with no `node_modules` above it. |
| The check writes the evidence table, and the documents hold no count. | A count that a person types goes stale. |
| The coordinator: four readers under six conditions, and the ledger as a prediction. | The design note's section 8. |
| The coordinator: the sleeps reader for timeout, granted by script. | Ten scripts measured and five that wait show more than fifteen that wait. |

### The gaps, each with its smallest extension

| Gap | Smallest extension |
| --- | --- |
| A host has no reply admission. Two routing scripts have no act, and the probe shows the host going on. | Route A's row adapter at the binding: the row decodes its answer at its answer type, and a refused answer is an act. |
| A forged reply and a direct answer decision are no acts of a host. Three scripts. | None on the host. A control of Lean's replay can edit a host's recording: one reply under another key. |
| The host has no name for a fiber with no call. One atomic script. | A ruling that a script may need a reader to run. It then has no run with no reader, so the transparency control has no reference for it. |
| A race's fibers have no number on the host. Timeout's `timers` wait in 5 scripts. | The fiber identity carrier of DI-81, or a reader of `raceAll` with a premise of its own. |
| The dispatchers reader gives a count, and its zero is the wait's in 12 scripts. | A reader that names the runnable fibers. It needs the same fiber identity. |
| A reader's effect on its own entries has no control. | A second, independent reader of one entry. I propose none. |
| Both workers call `Jobs.take` with one request. A swap of the two fibers shows only in `assignment` and in the released order. | Distinct requests in the battery, which is the battery's to change. |
| The printed module of the exact error column does not type-check. | A decision on the printed `ifElse` under a union error column. Proposal (c). |
| The pin needs a new digest by hand after a change that is meant. | None: the failure message gives the digest. |
| The driver restates each control's script. | Proposal (a). |
| Four kinds of control have no script. | None in this lane: each compares something that is no `Observation` of a script. |
| The engine has no session clause. | Outside this slice. |

### Outside the slice

- **Red, and not mine.** `Test/Dogfood/README.md` has two sentences above the limit of the
  language checker. The base holds both. I did not run `make check-tsdiag` and
  `make check-schema-ts`, which the brief names as red.
- **A fresh worktree needs one build more.** The default build does not build the library
  `Tools`. On 2026-10-06 the base's check stopped in my fresh worktree at a missing object file
  of that library. I built `Tools.ProfileJson`, `Tools.HostProtocol` and `Tools.GeneratedStamp`
  once, in 144 jobs. The check's script builds `Tools.ProfileJson` since step 1.
  `tools/Tools/HostProtocol.lean` still imports `Tools.GeneratedStamp`, which no step builds:
  reading.
- **The truth lane reads the lane's sources.** `scripts/check-truth.py` gives tsgo each
  TypeScript file of `harness/truth/session/`, in the tree: reading. The marker of
  `make check-truth` holds those files as inputs, so that check runs again at the merge. I did
  not run it. My lane's check gives tsgo the same files under the same base configuration, and
  it passes. The coordinator's seventh message names main's changes of the truth harness. None
  is a file of the keyed lane, and the lane's check passes on the tree that holds them.
- **A refused command.** On 2026-10-06 the permission classifier refused one of my commands.
  The command read the head of the slot script and listed my own logs. I did not route around
  the refusal, and I did not read the slot script again.
- **The seat's scratch files** are in the session's scratch folder, under `host/`. They hold
  each log of this receipt. Nothing there is committed.

## Proposed decisions rows (proposals only)

I do not edit the register. Each row is a proposal for the coordinator.

| Row | Proposal | Why |
| --- | --- | --- |
| (a) | A control carries its script as data: the battery names each control's program and its `List Move`, and the host driver takes that list. | The driver then restates nothing. The first item of this receipt is its cost today. |
| (b) | A host's reply admission is route A's row adapter, and a script with an `envelope` refusal waits for it. Until then such a script is replay evidence only. | Two routing scripts, and the probe of the wider record. |
| (c) | Decide the printed form of `ifElse` under a union error column: the printer states the type arguments of `Effect.suspend`, or the reader's domain refuses the column. | Two diagnostics `TS2375` of tsgo 7.0.0-dev.20260629.1. The twin's host run agrees with the Lean machine all the same. |
| (d) | The fiber identity carrier of DI-81 names a race's fibers on the host. | Timeout's `timers` wait in 5 scripts, and the dispatchers reader's count names no fiber. |
| (e) | Rule whether a script may run with a reader only. | `atomic/interrupted` needs the fibers reader to name fiber 3, and then it has no reference run. |
| (f) | The open part of R8 on the TypeScript face names the keyed lane's scenario runs beside the truth harness. Its status stays open. | The semantics registry is the coordinator's. The slice adds finite checks to that part and closes nothing. |
| (g) | Keep the four source words of an entry as the lane's words: host, ledger, reader and replay only. | `Test/Dogfood/README.md` defines them today. The dictionary has no entry for them. |
