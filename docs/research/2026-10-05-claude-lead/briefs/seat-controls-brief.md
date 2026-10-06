# 2026-10-06 brief for seat CONTROLS: a scenario's control carries its script as data

Status: a brief (history, not authority). Base: the head of `refactor/phase1-phase3` that the
dispatch message names. The coordinator dispatches it under decisions rows 237 and 266. Row
266's first point is this slice.

## Why this slice exists

A scenario's battery holds each control's script inside a Boolean expression (`controlsOf`,
`Test/Dogfood/Scenario/Workers.lean`). So no other tool can take the script. The host driver
writes each script again, from the battery's named parts and literal moves (`routingRuns`,
`workersRuns`, `timeoutRuns` and `atomicRuns`, `harness/truth/session/Keyed.lean`). A changed
script of a battery then does not reach the host runs, and the lane stays green on the old
script. Seat HOST's receipt records two events of 2026-10-06 that show the cost
(`docs/research/2026-10-05-seat-HOST-receipt.md`, its first item).

The owner's rule (2026-10-05): remove the cause. A table is data, and its consumers are
derived from it.

**The goal.** Each control names its scripts as data. The battery's gate plays them, and the
host driver takes them from the battery. No script is written twice.

## Who and where

You are one seat of the Effect4 estate. The coordinator wrote this brief and merges your
branch. You work alone and hand back a receipt.

- **Worktree, branch and scratch folder:** the dispatch message names them.
- **The coordinator's checkout** is `/Users/pooks/Dev/lean4-effect4`. Read it freely. Write
  nothing there.
- **Lean:** run every Lean and Lake command through
  `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`. Never run a bare `lake build`. Never
  send a Lean command's standard error to `/dev/null`. Run one `lake` at a time.
- **Make:** give `make` the flags `-o build -o ts/eff/node_modules -o harness/truth/node_modules`,
  and run it through the slot script too.
- **TypeScript:** only tsgo 7, the pinned `@typescript/native-preview`. Never `tsc`.
- **The host:** bun, with the pinned `effect` 4.0.0-rc.112, loaded by its directory.
- **OCaml:** only through `opam exec --switch=effect4 -- dune …`.
- **No install and no download.**
- **Git:** never push. Commit on your branch, by explicit paths. Use `git add -f` for a file
  under `docs/research`. Read `git status` before each commit.
- **Disk:** stop and report below 4 GiB free.

## Read first, in this order

1. `AGENTS.md`, in full.
2. Seat HOST's receipt and its design note: `docs/research/2026-10-05-seat-HOST-receipt.md`
   and `docs/research/2026-10-05-seat-HOST-design.md`.
3. `Test/Dogfood/Scenario.lean`: `Move`, `script`, `play`, `Control`, `Scenario` and
   `#scenario_gate`. Then the four batteries under `Test/Dogfood/Scenario/`, and `Gate.lean`.
4. `harness/truth/session/Keyed.lean`: the four lists of runs, `emit` and the replay.
5. The engine's lane of the scenarios: `Test/Dogfood/Scenario/Tape.lean`, `Lowered.lean` and
   `ocaml/engine/test/scenarios/write.lean`.
6. `Test/Dogfood/README.md`, the sections on the scenarios.

## The assignment

### 0. The design note, first

Write `docs/research/2026-10-06-seat-CONTROLS-design.md`, one page, before the first Lean
commit.

- The record of a control: its named runs, each with its program and its list of moves, and
  its comparison over the played runs.
- How the gate plays a control, and how it still refuses what it refuses today.
- How the host driver finds its runs. A run keeps the name that the lane's fixtures and its
  evidence table use today.
- The four kinds of control that have no script, as seat HOST's receipt lists them, and how
  each is written.
- Whether the engine's lane restates a script too. If it does, it takes its scripts from the
  same records.

Send the note's path to the coordinator in one message, and go on without waiting.

### 1. The records

Each control of the four batteries names its runs as data. A control's comparison reads the
played runs. Keep each control's name, its clause, and whether it is red.

### 2. The gate

`#scenario_gate` plays each control's runs and judges the comparison. It refuses what it
refuses today. Its own red controls in `Test/Dogfood/Scenario/Gate.lean` stay, in the new
form.

### 3. The host driver

`harness/truth/session/Keyed.lean` takes each scenario's runs from the battery's records. It
holds no list of moves of its own for a scenario. A run that a host cannot perform keeps its
stated reason.

### 4. The documents

`Test/Dogfood/README.md` says where a script lives and who reads it.

Where the design leaves a choice open, make it and state it in the receipt. Do not change a
script, an observation or a claim. If the audit finds a script that a consumer missed or
misread, report it, and add it as the battery has it.

**Reuse first.** Use the driver, the gate and the lane as they are. Before you add a helper,
name its consumer in this slice.

## The files

You may edit `Test/Dogfood/Scenario.lean`, the files of `Test/Dogfood/Scenario/`,
`harness/truth/session/Keyed.lean`, `Test/Dogfood/README.md`, and
`ocaml/engine/test/scenarios/write.lean` if the design needs it.

Do not edit `docs/core/decisions.md`, `lakefile.toml`, `docs/STATE.md`,
`generated/semantics.md` or `tools/Tools/SemanticsRegistry.lean`. Do not edit a program of
`Test/Dogfood/P*.lean`.

## The obligations and their placement

No theorem is asked for.

- Each scenario's claim, its clauses and its planned goals keep their statements. The goal
  gate's count does not move.
- A theorem that is proved today stays proved: `tape_replays`, `replays`, `receipt_inert`,
  `applied_selects` and `control_retires`.
- No `partial`, `unsafe`, `native_decide`, `axiom`, `extern` or `implemented_by`. Every
  warning is an error.
- A battery `def` over rendered text reaches `Classical.choice`: keep rendered bytes inside
  `#guard`s.

## Acceptance

1. **No script is written twice.** The four lists of `Keyed.lean` are derived from the
   batteries' records. Show it by a search: no list of moves for a scenario stands in that
   file.
2. **The same runs.** The lane's evidence table equals the base's, line for line. Its command
   is in seat HOST's receipt. A difference is a finding: report each one.
3. **A changed script reaches the host.** In a scratch copy, change one script of one control
   in a battery. The host run of that control then changes, with no edit of the driver. Do
   this for one control of each scenario. Keep the scratch copy out of the tree.
4. **The engine's fixtures do not move.** `make gen-fixtures` leaves `git status` empty.
5. **Run these, and give each result in the receipt:**
   - the default `lake build`, with the gate lines of `Test/All.lean`;
   - `make check-host-protocol`;
   - `dune build` and `dune test --force engine`;
   - `make check-docs`.
6. **Do not run:** `make check-gen`, `make check-slow`, `make check-corpus`,
   `make check-target`, `make check-truth`, the conservativity script, `make gen-semantics`.
   The coordinator runs them at the merge. List each as "not run".

Commit each finished step, so that the branch's head is always green.

## What is not in this slice

- A new script, a new control or a new scenario.
- A change of an observation or of a program.
- A proof of one of the ten open scenario goals.
- A reader, the recorder or the lane's check, but for what the driver's new source needs.

## Known, and not yours to repair

- `Test/Dogfood/README.md` has two sentences above the language checker's limit. Repair them
  if you edit their paragraph, and leave them otherwise.
- `make check-tsdiag` and `make check-schema-ts` are red for reasons outside this work.
- One printed module of the routing scenario does not type-check on the target (row 266,
  point 3). The lane keeps it out. Leave it out.
- A fresh worktree needs `Tools.GeneratedStamp` built once for the lane's check.

Report anything else that is red for a reason outside your slice. Do not repair it.

## The receipt

Write `docs/research/2026-10-06-seat-CONTROLS-receipt.md`, in the handoff form of `AGENTS.md`:

1. first, the one thing the coordinator must know before merging;
2. the base and head commits, and each step's commit;
3. the changed files;
4. each command with its result, the host's versions, and the evidence word for each claim;
5. each consumer of a script, before and after: the gate, the host driver and the engine's
   lane;
6. the result of acceptance 3, for each scenario;
7. each choice you made, and each finding of the audit.

The receipt also accounts for the requirements R1 to R13, in three lists taken from
`generated/semantics.md` and from `#plan_status`. This slice advances no requirement: say so,
and name the open parts that it leaves untouched.

Your last message gives the head commit, the receipt's path and the first item of the receipt.
