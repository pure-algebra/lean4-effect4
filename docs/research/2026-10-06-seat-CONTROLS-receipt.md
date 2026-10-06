# 2026-10-06 seat CONTROLS receipt: a scenario lists its runs, and three readers take the one list

Status: receipt (history, not authority). Written on 2026-10-06. Brief:
`docs/research/2026-10-05-claude-lead/briefs/seat-controls-brief.md`, with the dispatch message
and the coordinator's messages of 2026-10-06. Design note:
`docs/research/2026-10-06-seat-CONTROLS-design.md`. Its section 8 holds the coordinator's rulings.

The coordinator merged the slice as `4ffdf83f` the same day, and ruled on its two questions. The
last section, "Addendum", holds what followed. The sections before it give the slice as it was
merged, at `d7892c9d`.

**The one thing to know before merging:** the host lane did not move, and the engine's lane
did. The host lane's work folder is the base's bytes in 285 of 286 files. By the coordinator's
rulings of 2026-10-06, five runs of the engine's fixtures took the batteries' scripts. The lane's
red control has a new reading, in `Test/Dogfood/Scenario/Tape.lean` and in
`ocaml/engine/test/scenarios/test_scenarios.ml`.

**The incident: one `make` run of mine installed packages in the worktree.** It broke the rule
of no install. The coordinator's checkout did not change, and the worktree is as the dispatch
states it again.

- **When.** 2026-10-06, 04:43. The run's log opens with `Tue Oct  6 04:43:58 CDT 2026`.
- **The cause.** I held make's three `-o` flags in one shell variable. zsh does not split a
  variable into words, so make got no `-o` flag.
- **The three commands that make ran.** They stand in that log, in this order:
  `set -o pipefail; lake build 2>&1 | tee .lake/gen/build.log`, then
  `rm -rf ts/eff/node_modules`, then `cd ts/eff && bun install --frozen-lockfile`. The first ran
  inside my slot and built nothing. The second removed the worktree's link, and no file of the
  coordinator's folder. The third printed `18 packages installed [766.00ms]`.
- **What I cannot show.** bun took the packages in under a second. I cannot show that it made
  no network request.
- **What I did.** I moved the installed folder, 95 MB, into the scratch folder, as
  `controls/installed-by-mistake/node_modules`. I did not delete it, and no run uses it. I made
  the link again. The coordinator reports the folder to the owner.
- **The evidence.** That one run counts for nothing. Its host line reads
  `loaded from /Users/pooks/Dev/lean4-effect4-qtypes/ts/eff/node_modules/effect`. Every run that
  this receipt cites has the line
  `keyed host: effect 4.0.0-rc.112 under bun 1.4.2, loaded from /Users/pooks/Dev/lean4-effect4/ts/eff/node_modules/effect`.
  The table of the lane's check gives each such run. The final runs keep the flags in a bash
  array (`accept-all.sh`, in the scratch folder).
- **The cause on main.** The coordinator changed the install rule on main (`6e629bb4`). This
  branch has the old rule until the merge.

Nine more facts stand beside these.

- **No script is written twice.** A scenario's record lists each script once, as a named run.
  The gate, the host driver and the engine's lane take it from that list.
- **The same runs.** The driver's fixtures for the 55 runs are the base's bytes. The evidence
  table is the base's, line for line.
- **No script, no observation and no claim changes.** Each control of the four batteries keeps
  its kind, its clause and its name. The ten planned goals keep their statements.
- **The goal gate's count does not move.** It gives 24 planned goals and 11 declarations that
  rest on goals, on the base and at the head.
- **One named run has no control.** It is the timeout scenario's `parked`. The gate reports it,
  and the battery pins the report. The coordinator rules at the merge: see the addendum.
- **Two names hold one script.** They are `timeout/before` and `timeout/applied`. Both stay, so
  that the lane's table stays equal. The coordinator rules at the merge: see the addendum.
- **The engine's test has the same count of checks.** The scenarios' test has 183 checks on the
  base and at the head. It compares 101 positions on the base and 102 at the head.
- **One command is red for a reason outside the slice.** `dune test --force engine` exits with
  status 1 in this worktree, on the base too. The worktree holds no printed corpus.
- **No theorem lands, and no status moves.** The slice advances no requirement.

## Base and head

| Item | Value |
| --- | --- |
| Branch | `seat/controls`, in the worktree `/Users/pooks/Dev/lean4-effect4-qtypes` |
| Base | `1e280f24`, the head of `refactor/phase1-phase3` at the dispatch |
| The design note | `b8f17066` |
| Step 1 | `bd52e477`: the records, the gate, the four batteries, the gate's own battery |
| Step 2 | `51d32688`: the host driver takes its runs from the records |
| Step 3 | `15112c61`: the engine's lane takes its runs from the records; the red control's new reading; five runs of the fixtures |
| Step 4 | `2417fc97`: the README |
| Step 5 | `ba65ffd4`: the batteries' headers, and one control's name |
| Step 6 | `d7892c9d`: one function quotes a run on both lanes; the frontier control's move stands once |
| Head of the work | `d7892c9d`: every result of this receipt is measured there, but where a row names another tree |
| Receipt | the commit that adds this file and section 8 of the design note, on top of `d7892c9d` |

Nothing is pushed. The branch holds no merge of main: the coordinator sent no merged head.

## Changed files

`git diff --numstat 1e280f24 d7892c9d` counts 15 files, 1177 added lines and 590 removed lines.

| File | What changed |
| --- | --- |
| `Test/Dogfood/Scenario.lean` | `NamedRun` and `NamedRun.played`. `Control` gets `reads` and a comparison over the played runs. `Scenario` gets `runs`. `Scenario.run?`, `Scenario.quote`, `Scenario.repeated` and `Scenario.unread` are new. `Scenario.problems` plays each named run once. The gate's command logs each unread run. |
| `Test/Dogfood/Scenario/Workers.lean`, `Routing.lean`, `Timeout.lean`, `Atomic.lean` | `runsOf` lists the named runs. Each control names the runs that it reads. `runsAndControls` builds each program once. The timeout battery pins the gate's one report. |
| `Test/Dogfood/Scenario/Gate.lean` | The nine fixture records in the new form, and five more on a small program of the battery. |
| `Test/Dogfood/Scenario/Tape.lean` | `taken`, `own`, `clashesOf`, `findingsOf`, `findings`, `fixturesOf`. `Shown.lines`, and the new reading of `Shown.lastCounts`. The lane writes no script that a record lists. |
| `Test/Dogfood/Scenario/Lowered.lean` | The controls in the new form. The red control's new name. Three new controls: a tape that never moves, and the two controls of the lane's names. |
| `ocaml/engine/test/scenarios/write.lean` | The writer prints each finding of the lane's names and writes nothing then. |
| `ocaml/engine/test/scenarios/atomic.txt`, `timeout.txt` | Five runs moved. `make gen-fixtures` wrote both files. |
| `ocaml/engine/test/scenarios/test_scenarios.ml` | S4's red control, its label and the property list's sentences. No other line. |
| `harness/truth/session/Keyed.lean` | `Wire`, `Wire.runs`, `keptOut`, `stale` with its guard, and `runs` with its two refusals. The four lists of runs and the helper `build` are gone. |
| `Test/Dogfood/README.md` | The section "Where a script lives, and who reads it". The gate's refusals. The host runs and the lowered runs as named runs. |
| `docs/research/2026-10-06-seat-CONTROLS-design.md` | The design note, with the coordinator's rulings in its section 8. |

No file under `src/`, `tools/`, `generated/` or `ts/` changes. I did not edit
`docs/core/decisions.md`, `lakefile.toml`, `docs/STATE.md`, `generated/semantics.md` or
`tools/Tools/SemanticsRegistry.lean`. No program of `Test/Dogfood/P*.lean` changes.

## Commands and results

`SLOT` is `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`. Each Lean, Lake and make
command below runs through it. `FLAGS` is
`-o build -o ts/eff/node_modules -o harness/truth/node_modules`. `WORK` is
`harness/truth/session/.work/latest`, which the lane's check writes and git ignores. `SCRATCH`
is the seat's scratch folder, `controls/` under the session's scratchpad. It holds each log.

| Tool | Version | Command |
| --- | --- | --- |
| The host | bun 1.4.2 | `bun --version` |
| The pinned library | effect 4.0.0-rc.112, loaded from `/Users/pooks/Dev/lean4-effect4/ts/eff/node_modules/effect` | the runner's first line, and `WORK/host/versions.json` |
| The TypeScript compiler | tsgo 7.0.0-dev.20260629.1, the pinned `@typescript/native-preview` | `node ts/eff/node_modules/@typescript/native-preview/bin/tsgo --version` |
| node, which starts tsgo | v22.23.2 | `node --version` |
| Lean | 4.33.1 | `lean-toolchain` |
| OCaml and dune | 5.1.1 and 3.24.2 | `opam exec --switch=effect4 -- ocaml -version`, `opam exec --switch=effect4 -- dune --version` |

The seat runs no `tsc` and no `typescript` below 7. But for the incident above, it installs
nothing and downloads nothing.

### The default build and the gates

```text
SLOT lake build
SLOT lake env lean -M6144 -DwarningAsError=true Test/All.lean
```

The second command elaborates `Test/All.lean` afresh, as `make check-roots` does. It prints the
gates' lines where Lake takes a built module from its cache.

| Tree | Build | Modules and declarations at `[propext, Quot.sound]` | Planned goals | Declarations that rest on goals |
| --- | --- | --- | --- | --- |
| `1e280f24`, the base | `Build completed successfully (978 jobs).` | 728 and 87145 | 24 | 11 |
| `bd52e477`, step 1 | `Build completed successfully (978 jobs).` | 728 and 87200 | 24 | 11 |
| `ba65ffd4`, step 5 | `Build completed successfully (978 jobs).` | 728 and 87207 | 24 | 11 |
| `d7892c9d`, the head | `Build completed successfully (978 jobs).` | 728 and 87208 | 24 | 11 |

The gate lines at the head:

```text
Effect4 library-root gate: 170 API/utility modules, 296 Laws-only modules; every library source is reachable; Effect4 never reaches Laws
Effect4 module and axiom gate: checked 728 modules and 87208 declarations; [...] semantic/test axioms are [propext, Quot.sound]; exact implementation boundary (17 module(s), 23 declaration(s)) additionally allows Classical.choice
Effect4 goal gate: 24 planned goal(s), each a theorem whose body is `sorry` outside the Effect4 root; 11 declaration(s) rest on goals; no other declaration reaches sorryAx
```

Step 2 has the Lean sources of step 1. Steps 3 and 4 have the Lean sources of step 5, but for
one control's name and four docstrings. A build of those sources at 04:25, before I cut the
commits, gave 87207 declarations, 24 planned goals and 11 declarations that rest on goals. Each
of the three trees built with 978 jobs.

### The lane's check

```text
SLOT make FLAGS -W scripts/check-host-protocol.py check-host-protocol
```

`-W` makes the marker's rule run where its inputs did not change. The result at the head, exit
status 0:

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
Ran 54 tests across 4 files. [61.00ms]
PASS keyed differential: 57 runs, 52 programs, 30 controls; exact exits and keyed applications
PASS keyed scenarios on effect 4.0.0-rc.112 under bun 1.4.2: routing 8 scripts (2 entries measured by the host, 1 predicted by the ledger; no entry waits); workers 17 scripts (6 entries measured by the host, 5 through a reader, 2 of them zero by the run's own wait in 12 scripts; no entry waits); timeout 15 scripts (6 entries measured by the host, 2 through a reader, timers through a reader in 10 scripts; the whole-observation comparison waits on timers in 5 scripts (parked, timed-out, late, received, eager)); atomic 8 scripts (0 entries measured by the host, 5 through a reader; no entry waits); 7 scripts with no host run; 40 red controls
PASS host-protocol: fresh projections, typed host programs, keyed replay and negative controls; the scenarios' scripts on their printed modules
```

Each run of the check, with the folder that its host line names and its result:

| Tree | Time on 2026-10-06 | `effect` loaded from | Result | `WORK` against the base's |
| --- | --- | --- | --- | --- |
| `1e280f24`, the base | 03:40 | the coordinator's folder | passes | the reference |
| `bd52e477`, step 1 | 04:30 | the coordinator's folder | passes | the fixtures and the table are the base's bytes |
| `51d32688`, step 2 | 04:32 | the coordinator's folder | passes | 285 of 286 files |
| `ba65ffd4`, step 5 | 04:43 | the mistaken install | not used | not used |
| `ba65ffd4`, step 5 | 04:45 | the coordinator's folder | passes | 285 of 286 files |
| `d7892c9d`, the head | 04:51 | the coordinator's folder | passes | 285 of 286 files |

```text
diff -rq SCRATCH/base/latest WORK
Files SCRATCH/base/latest/tsconfig.json and WORK/tsconfig.json differ
```

That one file holds the path of the check's temporary folder. The other 285 files are the
fixtures, the written modules, the recordings, each result file and the evidence table.

### The fixtures group

```text
SLOT make FLAGS -W ocaml/engine/test/scenarios/write.lean gen-fixtures
git status --short
```

At the head the group writes seven files, and it prints
`PASS generate: requested producers ran in dependency order`. `git status --short` then lists
one line: the design note, whose section 8 was not committed yet. No fixture moves.

### The OCaml estate

```text
cd ocaml
opam exec --switch=effect4 -- dune build -j 2
opam exec --switch=effect4 -- dune test -j 2 --force engine
E4_LEAN_CORPUS=/Users/pooks/Dev/lean4-effect4/.lake/corpus opam exec --switch=effect4 -- dune test -j 2 --force engine
```

`dune build` exits with status 0 on the base and at the head.

| Tree | The corpus folder | Exit status | Lines `PASS` and `FAIL` | The scenarios' test |
| --- | --- | --- | --- | --- |
| the base | none in this worktree | 1 | 1725 and 1 | 183 checks, 0 failures, 101 positions |
| the base | the coordinator's, by `E4_LEAN_CORPUS` | 0 | 1726 and 0 | 183 checks, 0 failures, 101 positions |
| the head | none in this worktree | 1 | 1725 and 1 | 183 checks, 0 failures, 102 positions |
| the head | the coordinator's, by `E4_LEAN_CORPUS` | 0 | 1726 and 0 | 183 checks, 0 failures, 102 positions |

The one failing line is `FAIL the Lean corpus is present` of `test_diff.ml`. That test reads the
programs that `make corpus` prints under `.lake/corpus`, and this reused worktree has none. I
read the coordinator's folder, and I wrote nothing there.

### The documents

```text
SLOT make FLAGS -W scripts/check-docs.py check-docs
PASS check-docs: every path, link, citation and make target in 75 documents resolves
```

`python3 scripts/check-language.py --show FILE` gives no finding for this receipt and for the
design note. It gives one finding for `Test/Dogfood/README.md`: a long sentence of the base. It
stands in the section "How to read a stage", which this slice does not edit. The base has two
findings in that file. I repaired the other, in the section on the lowered runs.

### The searches of acceptance 1

```text
grep -cE '\.(start|tick|cancel|hold|receive)\b|Scenario\.(script|answer|ok|failed)\b' harness/truth/session/Keyed.lean
grep -n 'Move\|moves' harness/truth/session/Keyed.lean
```

| Search | The base | The head |
| --- | --- | --- |
| A constructor of `Move` that no journal row shares, or a script helper | 31 lines | 0 lines |
| The word `Move` or `moves` | 14 lines | 5 lines |

The five lines at the head are these: one docstring, the field `HostRun.moves`, and the two
places that play a run's script. The fifth is the line `moves := run.moves` of `Wire.runs`.

### The scratch runs

Each command below stands in a script of the scratch folder. No copy enters the tree.

| Script | What it does |
| --- | --- |
| `drive.sh` | It compiles a scratch copy of one battery with `lean -o`. Then it runs `Keyed.lean scenarios` with that copy in front of the tree's compiled battery. |
| `lane.sh` | It performs the lane's scenario steps on those fixtures: the runner, Lean's replay, the moved recordings and `check-keyed.ts`. It runs no build and no tsgo. |
| `engine.sh` | It runs the tree's writer with the scratch battery in front, into a scratch folder. Then it runs the engine's scenario test there. |
| `accept3.sh` | Acceptance 3 and the scratch red controls, from fresh copies of the head's files. |
| `accept-all.sh` | Every command of this section at the head, with the flags in an array. |
| `probe/AuditBase.lean`, `probe/AuditHead.lean` | The driver's 55 runs of the base against the engine's lane, and against the records. |
| `probe/AuditEngine.lean`, `probe/Still.lean`, `probe/Parked.lean`, `probe/PlanStatus.lean` | The five colliding runs under each script; a fixture that never moves; the unread run; `#plan_status`. |

A scratch battery stands in front by an overlay folder on Lean's search path. Lean takes every
module `Test.*` from the first folder that holds `Test`. So the overlay links each compiled
module of the tree and holds the one compiled copy.

### Not run

The brief excludes each command below. Each is **not run**.

- `make check-gen`
- `make check-slow`
- `make check-corpus`
- `make check-target`
- `make check-truth`
- the conservativity script
- `make gen-semantics`

These are not run either: `make check` and `make check-full` as wholes, `make check-tsdiag` and
`make check-schema-ts`, and `make corpus`.

On 2026-10-06, at the end of the work, the disk had 22 GiB free.

## Axiom output

The axiom gate audits every declaration of the changed `Test.*` modules. Its line at the head
gives 728 modules and 87208 declarations at `[propext, Quot.sound]`. The base has 87145. The
count grows by 63 with this slice's definitions and with what Lean generates for them. I did
not list the 63 one by one. No exemption changes: 17 modules and 23 declarations, as on the base. `Keyed.lean` is a driver
outside the audited libraries. It holds six `#guard` lines now, and no `sorry`.

## Evidence

Each host run and each scratch run is a finite run: tested. Each comparison of bytes with a
fresh producer run is reproduced. A fact from a source text is marked reading. Nothing here is
proved. The host evidence is bounded and host-only: one script, one schedule, on effect
4.0.0-rc.112 under bun 1.4.2.

### Each consumer of a script, before and after

| Consumer | On the base | At the head |
| --- | --- | --- |
| The gate | It judged one Boolean a control. The Boolean's expression held the script and played it (`controlsOf`). A script that two controls shared was written twice, or bound to a local name. | `Scenario.problems` plays each named run of the record once. It hands each control the runs that the control names. |
| The host driver | `Keyed.lean` held four lists with 55 runs. Each restated a script from the battery's named parts and literal moves. | `Wire.runs` maps the 55 named runs of the four records. The file holds no list of moves. |
| The engine's lane | `Tape.lean` wrote 19 runs. Twelve were a control's script. Five carried the name of a control's run and another script. Two were its own. | `taken` names 17 runs of the records. `own` holds the two scripts that no record lists. |
| The lowered battery's run at a small budget | It took the named part `Workers.lowest` and built the crew again. | It takes the program and the script of the workers record's run `lowest`. |

The mechanical audit at the head is `probe/AuditHead.lean`: tested.

- The base's 55 runs of the driver and the records' 55 named runs agree position by position.
  Each pair has one name and one list of moves. Each pair opens one program, with one table,
  one session name and the same budgets.
- Of the engine's 19 runs, 17 are a record's run with the same script and opening. Two names no
  record lists: `workers/refused` and `handle/cache`.

### The brief's acceptance

| Item | Result at `d7892c9d` | Evidence word |
| --- | --- | --- |
| 1. No script is written twice. | The searches above: no move stands in `Keyed.lean`. | tested |
| 2. The same runs. | `WORK/scenarios.json` and `WORK/host/scenario-evidence.md` are the base's bytes. So are 283 more files. | reproduced |
| 3. A changed script reaches the host. | One control of each scenario, below. The engine's lane, for two runs. | tested |
| 4. The engine's fixtures, as amended. | Five runs move, and no other. `make gen-fixtures` leaves `git status` as it is. | reproduced |
| 5. The four commands. | Under "Commands and results". | tested |
| 6. The commands that the seat does not run. | Under "Not run". | — |

### Acceptance 3: the fault on the base, and its repair

**The fault, on the base.** Two scratch copies of the workers battery, each with its gate green.

| Change in the copy | The driver's fixtures against the base's |
| --- | --- |
| One inline script of one control: `between` plays `.apply w1, .apply w2` and no longer `.apply w2, .apply w1` | The same bytes. The host would perform the old script. |
| One named part: a flush after `lowest` | Two runs differ, `workers/lowest` and `workers/twice`: 15 acts become 16. So the copy is the module that the driver loads. |

**The repair, at the head.** One script changes in a scratch copy of each battery. No other
line of the copy changes, and the driver is the tree's.

| Scenario | The changed script | The driver's fixtures | The host's recordings | The lane's comparison |
| --- | --- | --- | --- | --- |
| workers | `cancelled-between`: the two reply applications swapped | 1 of 48 differs: acts 7 and 8 of `workers/cancelled-between` | 1 of 48 differs: records 7 and 8. The ledger's prediction moves with the refused record. | passes |
| routing | `200`: the configuration's `pageSize` is 21 and no longer 20 | 1 of 48 differs: act 2 of `routing/200` | 1 of 48 differs: record 2 | passes |
| timeout | `host-interrupt`: the last clock step is 150 and no longer 100 | 1 of 48 differs: act 6 of `timeout/host-interrupt` | 1 of 48 differs: record 6 | passes |
| atomic | `finished`: the last clock step is 600 and no longer 500 | 1 of 48 differs: act 3 of `atomic/finished` | 1 of 48 differs: record 3 | passes |

Each of the four changes keeps the scenario's observation, so the copy's gate stays green. The
lane's comparison then holds for the new script. Each entry with a source on the host is the
Lean machine's. Lean's replay of the host's recording gives the script's observation. The 57
recordings of the four older families do not move in any of the four runs.

**The engine's lane.** The tree's writer and the tree's compiled `Tape.lean` run with the
scratch battery in front. No edit and no second compilation of `Tape.lean` is needed.

| Scratch battery | The fixtures against the tree's | The engine's test on the scratch fixtures |
| --- | --- | --- |
| routing, as above | 1 run moves, `routing/200`: the first answer decision's bytes end in `15` and no longer in `14` | 183 checks, 0 failures |
| atomic, as above | 1 run moves, `atomic/finished`: `advance 600` and no longer `advance 500` | 183 checks, 0 failures |

**The gate is the first reader.** In a fifth copy the workers run `applied-2` applies worker
1's reply. Its observation changes, and the copy does not compile. The gate's finding is
`workers: the control "the reply application at worker 2's key advances worker 2 alone" fails`.

### The five runs of the engine's fixtures that moved

`SCRATCH/fixture-diff.py` compares the fixtures of `1e280f24` with the tree's, run by run. Five
runs move, each in its tape only. The program, the rows, the budgets and the table line of each
are the same. The other 14 runs are the same bytes.

| Run | The script on the base (`Tape.lean`) | The script now (the battery's named run) | The tape on the base | The tape now |
| --- | --- | --- | --- | --- |
| `atomic/interrupted` | `[.start, .cancel ⟨3⟩, .flush]` | `interrupted`: `[.start, .cancel ⟨3⟩, .flush, .cancel ⟨3⟩]` | 3 decisions | 4 decisions: one more `interrupt - 3`, which moves no view |
| `timeout/late` | `timedOut`, the first attempt's answer, then the second attempt's answer | `timedOut`, then the first attempt's answer | 5 decisions | 4 decisions: no answer decision. The session refuses both rows of the late reply. |
| `timeout/kept` | `parked`, a reply receipt, `.tick 2000`, `.apply first`, `.tick 200` | the same without `.tick 200` | 4 decisions | 3 decisions |
| `timeout/404` | `parked`, then the answer that fails with the 404 | the same, then `.tick 100, .flush, .hold http` | 3 decisions | 5 decisions: `advance 100` and `flush` more, which move no view |
| `timeout/four` | `.start`, then ticks of 2000, 200, 2000, 400, 2000, 800 and 2000 | `.start`, then ticks of 2000, 100, 2000, 200, 2000, 400 and 2000 | 8 decisions | 8 decisions, with the delays of the repaired retry form |

The engine's `timeout/four` was the battery's script until the retry repair (`0f76dd2a`). That
commit changed the battery's delays and left the copy in `Tape.lean`: reading, from the commit's
diff. So the fault of this slice had one more event, on the engine's lane.

### The engine's test: the count of its checks, and two scratch fixtures

The scenarios' test prints 183 checks on the base and 183 at the head. Its output has 189 lines
in both. Beside the red control's new label, 11 lines differ, and each has its reason.

| Run | The base | The head | Reason |
| --- | --- | --- | --- |
| `atomic/interrupted` | 4 positions | 5 positions | one decision more |
| `timeout/late` | 6 positions, 1 answer value | 5 positions, 0 answer values | the second attempt's answer is no part of the battery's script |
| `timeout/kept` | 5 positions | 4 positions | one decision fewer |
| `timeout/404` | 4 positions | 6 positions | two decisions more |
| `timeout/four` | 9 positions | 9 positions | the same count, other clock readings |
| the total | 101 positions | 102 positions | the sum of the four differences |

Each line of a run stands once for each of the two instances, and the total stands once. The
count of checks does not move: each run keeps its checks, and the test has no check by position.

The red control's new reading meets the coordinator's six conditions.

| Condition | How it is met | Evidence |
| --- | --- | --- |
| 1. The cut tape ends at another view than the whole tape's. | `Shown.lastCounts` (`Tape.lean`), and S4 of the test. | tested: 19 runs in Lean, 38 checks on the engine |
| 2. The cut is Lean's data. | The test takes the last position at which two neighbouring view lines of the fixture differ. `Shown.lastCounts` reads the same lines, `Shown.lines`: the outcome word and the view. | reading. One more fact is tested, by a script over the fixtures: in each of the 19 runs the outcome word never moves alone. |
| 3. A run that never moves fails. | `Still.lean` writes a fixture of two flushes on the opened shop. Lean gives `lastCounts` false. The test fails S4 on both instances and exits with status 1. The lowered battery holds a red control of it. | tested |
| 4. No second comparison of the trailing decisions. | S2 compares each position. The property list says so. | reading |
| 5. The label and the sentence. | The label reads "the tape cut before its last decision that moves the view ends at another view (red control)". | reading |
| 6. A fixture with a moving decision removed. | Below. | tested |

**The removed decision.** A scratch copy of `atomic.txt` keeps the run `atomic/interrupted`
alone. I removed the line `step flush`, and one of the two equal view lines after it. So the
flush's view stays, as the last view. The test exits with status 1: `8 checks, 2 failures`. Both
failures are S2's, `the engine's view is Lean's at each of 4 positions`, at position 3, one for
each instance.

### The other scratch red controls

| Fault, in a scratch copy | Result |
| --- | --- |
| An own run of `Tape.lean` gets the name `workers/lowest`. | The writer prints `write.lean: the name workers/lowest carries two scripts: an own run of the lane and a run of a record`. It exits with status 1 and writes no file. The lowered battery fails two controls against that module: the lane has its fixtures, and the lane's names are in order. |
| `keptOut` of the driver names `routing/gone`. | The driver exits with status 2: `the lane keeps out the run routing/gone, and no scenario lists it`. |
| A record of the driver lists no run. | The driver exits with status 2: `the scenario atomic lists no run: a program of its battery does not build`. |

`Gate.lean` holds the gate's own red controls as fixtures. There are three: a comparison on the
run that its control did not name, an unlisted run, and a name listed twice.

## Landed theorems and their placement

None. The slice states no theorem, so it has no placement block. Each control stays a finite
control of the clause or the law that its record names.

## Open obligations

### The requirements R1 to R13

The slice advances no requirement. The statuses below come from two tools at the head:
`#plan_status` over the batteries, and the plan of `generated/semantics.md`. This receipt keeps
no status of its own.

**The claims whose controls the slice touches.** Each control keeps its comparison, so no status
moves.

| Requirement | Node | Status |
| --- | --- | --- |
| R4 | `atomic` (`Test/Dogfood/Scenario/Atomic.lean`) | modulo |
| R6 | `workers` (`Test/Dogfood/Scenario/Workers.lean`), `timeout` (`Test/Dogfood/Scenario/Timeout.lean`) | modulo |
| R6 | `receipt_inert`, `applied_selects`, `control_retires` (`Test/Dogfood/Scenario.lean`) | proved |
| R8 | `tape_replays` (`Test/Dogfood/Scenario.lean`), `unsuspended_runs` (`Atomic.lean`) | proved |
| R10 | `routing` (`Test/Dogfood/Scenario/Routing.lean`) | modulo |
| R10 | `tagIs_pair` (`Routing.lean`) | proved |
| R13 | `replays` (`Test/Dogfood/Scenario.lean`) | proved |

**The goals that the claims rest on.** `#plan_status` gives them, at the head:

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
Test.Dogfood.Scenario.Atomic.unsuspended_runs: proved; nearest []; 0 lemmas, 0 definitions
Test.Dogfood.Scenario.Routing.tagIs_pair: proved; nearest []; 0 lemmas, 0 definitions
```

| Claim | Planned goals that it rests on |
| --- | --- |
| `routing` | `infrastructure_escapes` (R10), `unauthorized_calls_nothing` (R5) |
| `workers` | `releases_once` (R11) |
| `timeout` | `retries_declared` (R10), `stale_never_applies` (R6), `cleanup_keeps` (R11) |
| `atomic` | `bounded`, `counted`, `committed` (R4), `cleans_once` (R11) |

The ten goals keep their statements. No open planned goal would not mean that the semantics is
finished.

**The open parts that the slice leaves untouched.** Each is an open part of
`generated/semantics.md`, under its requirement. The slice closes none.

| Requirement | Open parts | The nearest to the scenarios |
| --- | --- | --- |
| R1 | 4 | none |
| R2 | 5 | none |
| R3 | 6 | none |
| R4 | 5 | the target half of `handle-identity-laws`; `atomic-attempt-isolation` |
| R5 | 2 | `lower_refines_build` |
| R6 | 7 | reply receipt and reply application on the keyed lifecycle, and their converse; DI-57's table-aware reference; the public typed guarantee |
| R7 | 4 | none |
| R8 | 6 | the TypeScript face against rc.112 (DI-49); one identity bijection across faces (DI-81) |
| R9 | 1 | none |
| R10 | 12 | a composed module's law; no form has a behaviour law (DI-89) |
| R11 | 6 | release at most once for each registration, counted by identity (DB-07) |
| R12 | 7 | none |
| R13 | 4 | load inputs, the environment snapshot and the seed |

The counts come from one command at the head. Take a count from the tool at the head that you
cite.

```text
awk '/^### R[0-9]+:/ {r=$2} /^- Open:/ {c[r]++} END {for (k in c) print k, c[k]}' generated/semantics.md
```

### The findings of the audit

| Finding | Evidence | What the slice does |
| --- | --- | --- |
| The driver's 55 runs were the batteries' scripts. No script of a control was missing, and none was misread. | reading: each control's script on the base against its named run, one by one. Tested: `probe/AuditHead.lean`, and each control's comparison holds on its named run. | The records hold the same 55, in the same order. |
| The driver listed `timeout/parked`, and no control plays that script alone. | tested: `Scenario.unread` gives `["parked"]` for timeout, and the empty list for each other record | It stays a named run. The gate reports it, and the battery pins the line. |
| `timeout/before` and `timeout/applied` are one script on one program. `answer` is a reply receipt and a reply application. | tested: `probe/AuditHead.lean` finds this pair, and no other | Both stay. |
| Five names carried one script on the host lane and another on the engine's lane. | tested: `probe/AuditBase.lean` | Each takes the battery's script. |
| None of the engine's seven other scripts was a battery's script under another name. | tested: `probe/AuditBase.lean` compares moves and openings | `workers/refused` and `handle/cache` stay the lane's own. |
| The engine's `timeout/four` and the last tick of its `timeout/kept` were copies that the retry repair left behind. | reading: `git show 0f76dd2a` | Both runs take the battery's script. |
| Two battery scripts end with decisions that move no machine view: `atomic`'s `interrupted` and timeout's `404`. | tested: `probe/AuditEngine.lean` gives `lastCounts` false for both under the old reading | The red control's new reading, by the coordinator's ruling. |
| `Test/Codegen/TermRows.lean` imports the timeout battery. | reading | It builds with no change. |
| `Test/Dogfood/Scenario/Faces.lean` still says that the host clause waits. | reading | Not repaired: the file holds no script. |

### The choices

Each choice is mine unless the row names the coordinator.

| Choice | Reason |
| --- | --- |
| The coordinator accepted it: the list of runs stands at the scenario, and a control names its runs. | A name has one script by construction. The gate plays each run once. |
| The list keeps the driver's order of the base. | The lane's fixtures and its table then stay the base's bytes. The order is the first reading by a control in workers, and the driver's own in the three others. |
| A control's comparison takes a list of runs, in the order of `reads`. | A comparison that gets another count of runs fails, and the gate names the control. |
| The gate plays every listed run, read or not. | A script that does not play is then found at the battery. |
| The coordinator ruled it: the gate allows an unread run and reports it. The battery pins the line with `#guard_msgs (info)`. | A new unread run fails the build until its line is written. |
| One `runsAndControls` a battery. | One match over the builds gives both lists, so a program that does not build leaves no run and one failing control. |
| A comparison keeps a battery's build only where it needs a program. | Five kinds: a journal played again, the run of `P3WorkerQueue.drive`, the typed row, the straight clause, and routing's program pin. |
| The frontier control's one move stays in its comparison. | A script holds no budget, and no lane has an act for one. |
| The lowered record lists no named run. | Its runs are `Tape.lean`'s table, which was data before the slice. |
| `Gate.lean` builds a small program of its own. | The gate's playing of a run then has controls that need no battery. |
| The driver keeps a stated reason by the run's name, and it refuses a name that no record lists. | A reason cannot outlive its run. |
| `Tape.lean` holds one table of taken names, and `findingsOf` takes the own runs as an argument. | The red control of the names then runs the refusal itself, on a clashing run. |
| `Shown.lastCounts` reads the fixture's view lines, with the outcome word. | Lean and the engine's test then take one cut by construction. |
| `Scenario.quote` is the one function for a run's name on a lane. | Two lanes cannot spell one run in two ways. |
| The four batteries' headers no longer say that the host run waits. | The lanes take their scripts from `runsOf`, and the old sentence was stale since seat HOST. |
| Step 1 holds an intermediate `Lowered.lean`. | Each commit is green, and the engine's lane moves in one commit of its own. |

### Questions for the merge

- **The unread run.** `timeout/parked` would fit the clause "cleanup", as a green control: the
  first attempt counts itself before its call, and no finalizer ran. A scratch probe gives
  `shows parked atParked` true, and `cleanupKeeps` true for its observation: tested. I added no
  control. If the run goes instead, the host lane performs 14 timeout scripts, and the pinned
  line goes with it.
- **The pair.** If `timeout/applied` goes, the red frontier control reads `before`. The host
  lane then performs 14 timeout scripts.

### Outside the slice

- **The corpus folder.** `dune test --force engine` needs `.lake/corpus`, and a reused worktree
  has none. `E4_LEAN_CORPUS` names another folder for one command.
- **The mistaken install** stands in the scratch folder, 95 MB. The owner decides.
- **The gate cannot see a move that a comparison plays by itself.** The frontier control's is
  the one today, and the README names it.
- **The batteries' time.** Each battery elaborates in 2 to 3 seconds at the head. That is
  within 0.3 seconds of its time on the base: one run each, on a shared machine.
- **A refused command.** None.

## Proposed decisions rows (proposals only)

I do not edit the register. Each row is a proposal for the coordinator.

| Row | Proposal | Why |
| --- | --- | --- |
| (a) | Record row 266's point 1 as landed: a scenario's record lists each script once as a named run, and the gate, the host driver and the engine's lane take it from there. One name has one script on every lane. | This slice. |
| (b) | Rule on `timeout/parked`: a green control of the clause "cleanup", or its removal. Then let the gate refuse a named run that no control reads. | The gate can only report it today. |
| (c) | Rule on the pair `timeout/before` and `timeout/applied`. | One script is performed twice on the host. |
| (d) | Give the dictionary of `docs/core/controlled-english.md` two entries: "script" and "named run", with `Move` and `NamedRun` as anchors. | The README defines both, and this receipt and the design note use them. |
| (e) | A seat's brief names the corpus folder for `dune test --force engine`, or the dispatch links `.lake/corpus`. | The command is red in a reused worktree, for no fault of the tree. |
| (f) | Repair the sentence of `Test/Dogfood/Scenario/Faces.lean` that says the host clause waits. | It is stale since seat HOST's merge. |

## Addendum

**The addendum's first line:** after the merge, one script has one name, and each named run has
a control. The gate refuses a named run that no control reads. The host lane performs 14 timeout
scripts and no longer 15, and nothing else of the lane moves.

The coordinator merged the slice as `4ffdf83f` on 2026-10-06. It ruled on the two questions of
this receipt and took its proposal (f). This section holds what followed, on the same branch.

### Base and head

| Item | Value |
| --- | --- |
| Base | `4ffdf83f`, the merged head of main, taken by `git merge --ff-only 4ffdf83f` |
| Addendum 1 | `2cadd3ec`: the gate refuses an unread run, and `parked` gets its control |
| Addendum 2 | `d53ab29d`: the timeout run `applied` goes |
| Addendum 3 | `62d6f646`: the sentence of the faces battery |
| Head of the work | `62d6f646`: each result of this section is measured there |
| Receipt | the commit that adds this section, on top of `62d6f646` |

Nothing is pushed. `git diff --numstat 4ffdf83f 62d6f646` counts 5 files, 42 added lines and 45
removed lines.

### The three rulings, and what each changed

| Ruling of 2026-10-06 | What changed | Files |
| --- | --- | --- |
| 1. `timeout/parked` gets a green control at the clause "cleanup". The gate refuses a named run that no control reads: an error, and no information line. | The control "the first attempt counts itself before its call, and no finalizer ran" reads `parked`. It compares the run's observation with `atParked`, and it checks `cleanupKeeps`. `Scenario.problems` gives the finding `no control reads the run`. The gate's command logs nothing more. The pinned `#guard_msgs (info)` is gone. The fixture `unread` is a red control. | `Test/Dogfood/Scenario.lean`, `Test/Dogfood/Scenario/Timeout.lean`, `Test/Dogfood/Scenario/Gate.lean`, `Test/Dogfood/README.md` |
| 2. `timeout/applied` goes, and the red frontier control reads `before`. | `runsOf` of the timeout battery lists 16 named runs and no longer 17. The red control of the law "frontier" names `before`. Its comparison is the same text. | `Test/Dogfood/Scenario/Timeout.lean` |
| 3. Proposal (f). | The header of the faces battery says that the keyed lane performs the scenarios' named runs. A docstring only. | `Test/Dogfood/Scenario/Faces.lean` |

The four records now list 54 named runs. The timeout record has 16 runs and 20 controls. No
record has an unread run, and no two names hold one script on one program. A scratch probe gives
all four facts at the head (`probe/AuditAddendum.lean`): tested. The same probe compares the
base's 55 runs of the driver, without `timeout/applied`, with the records' 54. Each pair has one
name, one list of moves and one opening.

The engine's lane does not list the name `applied`. Its table `taken` names six timeout runs:
`before`, `second`, `late`, `kept`, `404` and `four`. So no fixture of the engine moves.

### Commands and results

`SLOT`, `FLAGS`, `WORK` and `SCRATCH` are as above. Each make command has its three `-o` flags
written out: typed in the command, or in a bash array (`addendum-run.sh`, in the scratch
folder). Each of the three runs of the lane's check has the host line
`keyed host: effect 4.0.0-rc.112 under bun 1.4.2, loaded from /Users/pooks/Dev/lean4-effect4/ts/eff/node_modules/effect`.
The worktree's two links stand at the end as at the start.

**The default build and the gates.**

```text
SLOT lake build
SLOT lake env lean -M6144 -DwarningAsError=true Test/All.lean
```

| Tree | Build | Modules and declarations at `[propext, Quot.sound]` | Planned goals | Declarations that rest on goals |
| --- | --- | --- | --- | --- |
| `4ffdf83f`, the merged head | `Build completed successfully (978 jobs).` | 728 and 87230 | 24 | 11 |
| `2cadd3ec`, addendum 1 | `Build completed successfully (978 jobs).` | 728 and 87230 | 24 | 11 |
| `d53ab29d`, addendum 2 | `Build completed successfully (978 jobs).` | 728 and 87230 | 24 | 11 |
| `62d6f646`, the head | `Build completed successfully (978 jobs).` | 728 and 87230 | 24 | 11 |

The gate lines at the head:

```text
Effect4 library-root gate: 170 API/utility modules, 296 Laws-only modules; every library source is reachable; Effect4 never reaches Laws
Effect4 module and axiom gate: checked 728 modules and 87230 declarations; [...] semantic/test axioms are [propext, Quot.sound]; exact implementation boundary (17 module(s), 23 declaration(s)) additionally allows Classical.choice
Effect4 goal gate: 24 planned goal(s), each a theorem whose body is `sorry` outside the Effect4 root; 11 declaration(s) rest on goals; no other declaration reaches sorryAx
```

**The lane's check.**

```text
SLOT make FLAGS -W scripts/check-host-protocol.py check-host-protocol
```

It passes at the head, with exit status 0. Two of its lines differ from the merged head's:

```text
PASS keyed scenarios: 47 scripts performed on actual rc.112 in 167 runs: each with no reader, with its readers, and with each reader alone; 7 scripts with no host run
PASS keyed scenarios on effect 4.0.0-rc.112 under bun 1.4.2: routing 8 scripts (2 entries measured by the host, 1 predicted by the ledger; no entry waits); workers 17 scripts (6 entries measured by the host, 5 through a reader, 2 of them zero by the run's own wait in 12 scripts; no entry waits); timeout 14 scripts (6 entries measured by the host, 2 through a reader, timers through a reader in 9 scripts; the whole-observation comparison waits on timers in 5 scripts (parked, timed-out, late, received, eager)); atomic 8 scripts (0 entries measured by the host, 5 through a reader; no entry waits); 7 scripts with no host run; 39 red controls
```

| Count | The merged head | The head | Reason |
| --- | --- | --- | --- |
| Scripts performed | 48 | 47 | the one run |
| Runs | 171 | 167 | the run had four: with no reader, with its readers, with the cells reader alone, with the sleeps reader alone |
| Timeout scripts | 15 | 14 | the one run |
| Timeout scripts with `timers` through a reader | 10 | 9 | the run was one of them |
| Red controls | 40 | 39 | the run's control of the fibers reader's premise. The five other kinds keep their lists. |
| Scripts with no host run | 7 | 7 | the same seven |

**The lane's table.** `WORK/host/scenario-evidence.md` has 31 lines on both trees. Ten differ,
each a line of timeout. The other 21 are the same.

```text
17,26c17,26
< | timeout | `calls` | host | all 15 |  |
< | timeout | `receipts` | host | all 15 |  |
< | timeout | `applications` | host | all 15 |  |
< | timeout | `retired` | host | all 15 |  |
< | timeout | `stored` | host | all 15 |  |
< | timeout | `attempts` | reader: cells | all 15 |  |
< | timeout | `cleanups` | reader: cells | all 15 |  |
< | timeout | `root` | host | all 15 |  |
< | timeout | `timers` | replay only | 5 of 15: parked, timed-out, late, received, eager |  |
< | timeout | `timers` | reader: sleeps | 10 of 15: 503, four, 404, before, second, kept, timer-interrupt, host-interrupt, applied, resetting |  |
---
> | timeout | `calls` | host | all 14 |  |
> | timeout | `receipts` | host | all 14 |  |
> | timeout | `applications` | host | all 14 |  |
> | timeout | `retired` | host | all 14 |  |
> | timeout | `stored` | host | all 14 |  |
> | timeout | `attempts` | reader: cells | all 14 |  |
> | timeout | `cleanups` | reader: cells | all 14 |  |
> | timeout | `root` | host | all 14 |  |
> | timeout | `timers` | replay only | 5 of 14: parked, timed-out, late, received, eager |  |
> | timeout | `timers` | reader: sleeps | 9 of 14: 503, four, 404, before, second, kept, timer-interrupt, host-interrupt, resetting |  |
```

**The files that leave, and what does not move.** `SCRATCH/addendum-compare.py` compares the two
work folders. It takes the run out of each value of the merged head, and it compares the rest.

```text
python3 SCRATCH/addendum-compare.py SCRATCH/addendum/merged/latest SCRATCH/addendum/final/latest timeout/applied
files: 286 before, 283 after
3 files leave:
  host/timeout-applied.json
  host/timeout-applied.readers.ts
  host/timeout-applied.ts
0 files appear:
9 files of both folders differ; 274 are the same bytes
  host/scenario-alone-cases.json: the run stands 2 times before and 0 after; with the run taken out, the rest is the same value
  host/scenario-cases.json: the run stands 1 times before and 0 after; with the run taken out, the rest is the same value
  host/scenario-checked.json: the run stands 10 times before and 0 after; with the run taken out, the rest is the same value; the count of timeout scripts: 15 -> 14
  host/scenario-evidence.md: 31 lines before, 31 after
    10 lines differ, each a line of timeout; 21 lines are the same
  host/scenario-host.json: the run stands 1 times before and 0 after; with the run taken out, the rest is the same value
  host/scenario-reader-cases.json: the run stands 1 times before and 0 after; with the run taken out, the rest is the same value
  scenario-lean.json: the run stands 1 times before and 0 after; with the run taken out, the rest is the same value
  scenarios.json: the run stands 1 times before and 0 after; with the run taken out, the rest is the same value
  tsconfig.json: the path of the check's temporary folder, as in every run
RESULT: nothing moves but the run
```

| What leaves | Where it stood |
| --- | --- |
| The run's fixture | One entry of `WORK/scenarios.json`: the printed module, five acts, one call and the observation |
| The run's recordings | `WORK/host/timeout-applied.json`, and four entries of three files: one with no reader, one with its readers, and two with one reader alone |
| The run's two written modules | `WORK/host/timeout-applied.ts` under the plain header, and `WORK/host/timeout-applied.readers.ts` under the cells reader's header |
| The host's result for the run | One entry of `WORK/host/scenario-host.json` |
| Lean's replay of the run's recording | One entry of `WORK/scenario-lean.json` |

The script checks each of the ten lines of the table too. Each differs from its old line by the
count of scripts alone, and the last one by the name `applied` as well. The fixture that leaves
had the acts, the call, the observation and the module of `timeout/before`: tested, on the merged
head's fixtures. So the host still performs that script, under its one name.

**The fixtures group, the OCaml estate and the documents.**

```text
SLOT make FLAGS -W ocaml/engine/test/scenarios/write.lean gen-fixtures
cd ocaml && opam exec --switch=effect4 -- dune build -j 2
cd ocaml && E4_LEAN_CORPUS=/Users/pooks/Dev/lean4-effect4/.lake/corpus opam exec --switch=effect4 -- dune test -j 2 --force engine
SLOT make FLAGS -W scripts/check-docs.py check-docs
```

| Command | Result at the head |
| --- | --- |
| `make gen-fixtures` | `PASS generate: requested producers ran in dependency order`. `git status --short` is empty after it. The four scenario fixtures are the merged head's. |
| `dune build` | exit status 0 |
| `dune test --force engine`, with the corpus folder | exit status 0, with 1726 lines `PASS` and no line `FAIL`. The scenarios' test prints 183 checks, 0 failures and 102 positions. Its output is the merged head's bytes. |
| `make check-docs` | `PASS check-docs: every path, link, citation and make target in 75 documents resolves` |

`python3 scripts/check-language.py --show` gives no finding for this receipt and for the design
note. It gives the one finding of the base for `Test/Dogfood/README.md`.

### The red controls

| Control | Where it stands | Result |
| --- | --- | --- |
| A record with a named run that no control reads | The fixture `unread` of `Test/Dogfood/Scenario/Gate.lean` | The gate refuses it: `unread: no control reads the run "opened"`. A guard pins that the record has this one finding. |
| The timeout record itself, before `parked` had its control | A run between the two edits of addendum 1 | The battery failed with `timeout: no control reads the run "parked"`: tested. |
| An unread run added again | A scratch copy of the timeout battery that lists `applied` once more | The copy does not compile: `timeout: no control reads the run "applied"`: tested. |
| The new control on another script | A scratch copy whose run `parked` is `[.start, .flush]`, so the host holds no call | The copy does not compile: the control "the first attempt counts itself before its call, and no finalizer ran" fails: tested. |
| The comparison of the two work folders | The same script with the name `timeout/before` | It exits with status 1 and reports 8 differences that it does not expect: tested. |

### What the addendum does not change

- **No theorem, no status.** `#plan_status` gives the same line for each of the eleven nodes as
  at `d7892c9d`. The ten planned goals keep their statements. The slice advances no requirement.
- **The open parts.** The counts of `generated/semantics.md` are the ones of the table above,
  for each of R1 to R13. The merge did not change that file.
- **The other controls.** Every other control keeps its kind, its clause, its name and its
  comparison. The timeout battery has one control more, and no control fewer. A script compares
  the three words of each control at the merged head and at the head: tested.
- **The engine's lane.** Its fixtures, its test and its red control are as at the merged head.

### Not run

The same commands as above are **not run**: `make check-gen`, `make check-slow`,
`make check-corpus`, `make check-target`, `make check-truth`, the conservativity script and
`make gen-semantics`. The coordinator ran its gates at the merge. On 2026-10-06, at the end of
the addendum, the disk had 22 GiB free.

### Still open, and not mine

- The dictionary's entries for "script" and "named run": the coordinator adds them.
- Row 266's record: the coordinator's.
- The mistaken install stays in the scratch folder, for the owner.
- Proposal (e), the corpus folder of `dune test --force engine`, stands as proposed.
