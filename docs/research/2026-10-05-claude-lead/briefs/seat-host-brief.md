# 2026-10-05 brief for seat HOST: the scenarios on the printed module, on the keyed lane

Status: a brief (history, not authority), written ahead of its dispatch. Base: the head of
`refactor/phase1-phase3` that the dispatch message names. It is the host half of the scenarios'
lowered link (decisions row 254). Seat DOGFOOD handed that half back
(`docs/research/2026-10-05-seat-DOGFOOD-receipt.md`, items 8 and 9.4). Revised the same day,
before any dispatch, after Codex's review. A field's evidence is a host measurement or Lean's
replay, and the two are never mixed.

## Why this slice exists

The owner's words, 2026-10-05: dogfooding joins a proof in Lean to the code that the tree
lowers. A scenario has one named observation, and the machine, the generated OCaml engine and
the printed TypeScript module are compared on it.

Two of the three are done. Each scenario runs on the Lean machine, and its machine clause
replays on the generated engine. No scenario runs as a printed module on rc.112 yet. This slice
adds that run, on the lane that keeps a reply's receipt and its application apart.

Three rules bind every line you write.

1. **One observation, and one source of evidence a field.** The host run is compared on the
   battery's own `Observation`, the session clause. Add no second, looser comparison. Each
   field is either measured on the host or read from Lean's replay of the host's recording. A
   field that only the replay gives is replay evidence. Never call it a host measurement.
2. **One lane.** Extend the keyed lane. Write no second runner and no second recorder.
3. **A check has a claim.** Each host run is a control of its scenario's placed claim. Its
   evidence word is "finite host run". It proves nothing.

## Who and where

You are one seat of the Effect4 estate. The coordinator wrote this brief and merges your
branch. You work alone and hand back a receipt.

- **Worktree, branch and scratch folder:** the dispatch message names them.
- **The coordinator's checkout** is `/Users/pooks/Dev/lean4-effect4`. Read it freely. Write
  nothing there.
- **Lean:** run every Lean and Lake command through
  `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`. Never run a bare `lake build`. Never
  send a Lean command's standard error to `/dev/null`. Run one `lake` at a time.
- **Make:** give `make` the flags `-o build -o ts/eff/node_modules -o harness/truth/node_modules`.
- **The host packages:** a worktree has no `node_modules`. Link `ts/eff/node_modules` to the
  coordinator's folder, and `harness/truth/node_modules` to that link, as seat DOGFOOD did (its
  receipt, item 5.1). Git ignores both links.
- **TypeScript:** only tsgo 7, the pinned `@typescript/native-preview`. Never `tsc`. A result
  names its compiler and version.
- **The host:** bun, with the pinned `effect` 4.0.0-rc.112 of `ts/eff/node_modules`. Load the
  package by its directory, and print its version in each host result.
- **No install and no download.**
- **Git:** never push. Commit on your branch, by explicit paths. Use `git add -f` for a file
  under `docs/research`. Read `git status` before each commit.
- **Disk:** stop and report below 4 GiB free.

## Read first, in this order

1. `AGENTS.md`, in full.
2. `Test/Dogfood/README.md`, the sections "The scenarios" and "The lowered runs".
3. `Test/Dogfood/Scenario.lean`: the script alphabet `Move`, the driver `play`, the readers,
   and the theorem `tape_replays`. Then the four batteries under `Test/Dogfood/Scenario/`:
   each one's program, scripts, `Observation` and controls.
4. Seat DOGFOOD's receipt, `docs/research/2026-10-05-seat-DOGFOOD-receipt.md`: items 3, 7.2, 8
   and 9.4.
5. The keyed lane: `harness/truth/session/Keyed.lean`, `run-keyed.ts`, `keyed-recorder.ts`,
   `keyed-bindings.ts`, `clock.ts`, `prepare-keyed-controls.ts` and `check-keyed.ts`. Then its
   check, `scripts/check-host-protocol.py`, and its battery `Test/Api/KeyedHostContract.lean`.
6. `docs/core/host-boundary.md`, and `src/Effect4/Api/HostSession.lean`.
7. Codex's reviews under
   `docs/research/2026-10-05-codex-foundation-packet/implementation-audit/`:
   `open-questions-review/dogfood/review.md`, `heartbeat-dogfood-2207/review.md`, and
   `heartbeat-host-brief-0236/review.md`: the review that this brief's item 3 follows.

## What the lane does today

- Lean writes one fixture a program (`Keyed.lean`, `emit`). A fixture holds the printed
  expression, the row table, a plan of the calls and their answers, and the expected exit.
- `run-keyed.ts` runs the printed expression on rc.112 under `KeyedRecorder`. A host row parks
  until the recorder applies its reply. The recorder writes a recording: the calls, the reply
  receipts, the reply applications and the controls, in the order they happened.
- Lean replays each recording through the session (`Keyed.lean`, `batch`).
- `check-keyed.ts` compares the exit, the consumed calls and what is pending.

Its programs are four fixtures of the lane's own. No program of `Test/Dogfood` runs there.

## The assignment

1. **A scenario's fixture.** Lean writes one fixture for each script that a host can perform.
   It holds the scenario's printed module and its row table. It holds the script as an ordered
   list of host actions, and the expected `Observation` with the root's exit. The script is the
   battery's own `List Move`. Write no second script by hand. A driver in Lean may import the
   batteries.
2. **The host's run.** The runner performs the script's actions in order on the printed module,
   through `KeyedRecorder`. An action holds a call, receives a reply, applies a reply, cancels a
   fiber or advances the clock. A scenario's host answers are scripted completions. The
   recorder writes the recording as it does today.
3. **The comparison,** in two parts that the receipt keeps apart.
   - **The host's measurements.** For each field of the battery's `Observation` that the host
     can read, the host measures it by itself and writes it beside the recording. The check
     compares it with the same field of the script's observation on the Lean machine. The
     root's exit, the calls, the reply receipts and the reply applications are such fields
     today.
   - **Lean's replay.** Lean replays the host's recording with `Run.play` and reads the
     battery's `Observation`. It must be the observation of the same script on the Lean
     machine, field for field. This shows that the session accepts what the host did. It
     measures nothing more of the host.
   - **A scenario is accepted on its whole observation** only when every field has a host
     measurement that agrees. Where a field has no permitted reader on the host, the
     scenario's whole-observation comparison is waiting, and the receipt lists the field. Do
     not put the exit's equality or a projection in its place.
4. **The order of the scenarios.**
   - **routing** first. Its program prints and reads back, and its calls come in sequence. Its
     observation holds the root's exit, the repository's calls and the refused rows. State for
     the refused rows whether the host or the replay gives them.
   - **workers** second: two pending replies, both application orders, a cancellation. Its
     observation also reads two cells of the program and the work left
     (`Workers.observe`). The recorder shows neither today.
   - **timeout** third: the clock, a retry, a late reply. Its observation reads the attempt
     count, the cleanup log and the timers.
   - **atomic** last. Its observation reads the window, the account and each request's exit.
     Its printed module may not type-check: see "Known".
5. **The one extension that is planned.** The recorder refuses an operation that completes
   after its cancellation. Two controls of workers and two of timeout need that case. Record
   such a completion as a late reply that the session refuses. Design it before you build it:
   send the coordinator the design in one message, and go on with the scripts that do not need
   it.
6. **Three red controls, one for each connector.** Name the connector that each one tests.
   - **The host's measurement:** a fault on the host only. It drops one assignment or one
     cleanup update and keeps the root's exit. The comparison of the host's fields must fail
     at that field. Without this control a comparison of exits would pass for the whole.
   - **The comparator:** one changed expectation fails the check by the scenario's name.
   - **Lean's replay:** one recording with a moved record is refused.
7. **A script that ends with live work.** `KeyedRecorder.finish` refuses a live call and a
   stored reply, and it appends a terminating flush. A script may end before the root does.
   It then needs a named snapshot of the recorder, or an entry "not performable" in the design
   note with this reason. Do not run a script to its end only to obtain a recording.
8. **The documents.** Each scenario's row of `Test/Dogfood/README.md` gets its host result,
   with the fields that the host measures and the fields that only the replay gives.

Where the lane cannot carry a script, state the gap and the smallest extension that would
close it. Do not rewrite a program to make it run. Do not change a production API.

**Reuse first** (the owner, 2026-10-05). Use the recorder, the bindings, the clock boundary and
the lane's check. Before you add a helper, name its consumer in this slice.

## Design first, in one short note

Before the first commit, write `docs/research/2026-10-05-seat-HOST-design.md`, one page:

- **one table a scenario, with a row for each field of its `Observation`.** A row gives the
  host's own measurement of the field and its serialization. It gives the identity mapping
  that the field needs: a runtime fiber to a fiber of the machine, a call to its key. It gives
  the checkpoint where the field is read. A field with no reader on the host says "replay
  evidence only". Write this table before you choose the first script;
- how a `Move` becomes a host action, for each constructor;
- which scripts of each battery a host can perform, and which it cannot, with the reason;
- how the host knows a scripted completion for a call;
- how a script's schedule is fixed on rc.112, where the scenario forks. If rc.112 chooses an
  order that the script does not state, say how the recording carries that order to Lean;
- where the new files live, and what `scripts/check-host-protocol.py` runs.

Extend the recorder's observer or the bindings only where that shows a field of a scenario.
If a field needs a reader inside the program's own state (a cell, the runnable fibers, a
timer), do not build it. Send the coordinator the narrow reader you propose, in one message:
what it reads, where, and what it cannot change. The coordinator settles it first.

Send the note's path to the coordinator in one message, and start routing without waiting.

## The obligations and their placement

No theorem is asked for. If you state one, place it first, as `AGENTS.md` requires.

| Evidence | Claim it is a control of | Reach | It does not establish |
| --- | --- | --- | --- |
| A field measured on the host | The scenario's claim (`workers`, `routing`, `atomic`, `timeout`), `host-session-protocol` R6 and `translation-simulation` R8 | One script, one schedule, on rc.112 under bun, the fields with a host reader | No agreement for another script or another field, no host adequacy, no liveness |
| Lean's replay of the host's recording (replay evidence) | The same claim, and `run-tape-replay` for the machine | The recording that the host wrote | Nothing of the host beyond the recording: no cell, no fiber and no timer that the recorder does not see |

- A theorem that is proved today stays proved.
- Do not edit `docs/core/decisions.md`, `lakefile.toml` or `docs/STATE.md`.
- No `partial`, `unsafe`, `native_decide`, `axiom`, `extern` or `implemented_by`. No `sorry`
  outside a `proof_goal`. Every warning is an error.

## Acceptance

1. **routing and workers** run on rc.112, for each script that the design note lists as
   performable. Every field with a host measurement agrees with Lean's. Lean's replay of each
   recording gives the script's observation. The receipt says for each scenario whether its
   whole observation is measured on the host, or which fields wait.
2. **Each printed module** type-checks under tsgo 7 against the prelude, or its diagnostics
   are in the receipt with the compiler's version.
3. **The three red controls** of the assignment's item 6 are red, each at its connector.
4. **`make check-host-protocol`**, with the three flags above, passes. The lane's existing
   runs are unchanged.
5. **timeout and atomic:** landed, or stated as waiting with the first refusal and its cause.
6. **Run these, and give each result in the receipt:**
   - the narrow `lake build` of each Lean module you changed, and the default `lake build`
     once at the end;
   - the lane's check above;
   - `make check-docs`.
7. **Do not run:** `make check-gen`, `make check-slow`, `make check-corpus`,
   `make check-target`, `make check-truth`, the conservativity script, the ledger promotion.
   The coordinator runs them at the merge. List each as "not run".

Commit each finished scenario, so that the branch's head is always green.

## What is not in this slice

- A session on the engine's side. The engine's session clause stays waiting.
- A proof of any of the ten open scenario goals.
- A change of a scenario's program, script or observation.
- The truth lane: it does not keep a receipt and an application apart.
- The move of the driver's laws into the law graph.

## Known, and not yours to repair

- **Literal types on the target.** `pair` and `tuple` keep the literal type of a number and of
  a boolean. The rate limiter's request does not type-check for that reason
  (`Test/Codegen/TermRows.lean`, `fourRequests`). `Atomic.shop` uses that request. The repair is
  the owner's to rule. If a module fails only there, report it and let the scenario wait.
- **`Timeout.fetch` prints and does not read back:** its retry loop states its cursor's type,
  which seat T5's part B reads. A host run needs the printed module only.
- `make check-tsdiag` and `make check-schema-ts` are red for reasons outside this work.

Report anything else that is red for a reason outside your slice. Do not repair it.

## The receipt

Write `docs/research/2026-10-05-seat-HOST-receipt.md`, in the handoff form of `AGENTS.md`:

1. first, the one thing the coordinator must know before merging;
2. the base and head commits, and each step's commit;
3. the changed files, by group;
4. each command with its result, the host's versions, and the evidence word for each claim;
5. each scenario's scripts: performed, or not, with the reason; and each field of each
   observation with its source of evidence;
6. each choice you made, and each gap of the lane with its smallest extension;
7. what is bounded and what is host-only;
8. proposed decisions rows. Do not edit the register.

Your last message gives the head commit, the receipt's path and the first item of the receipt.

The receipt also accounts for the requirements R1 to R13, in three lists taken from
`generated/semantics.md` and from `#plan_status` (the owner's direction of 2026-10-05;
`docs/research/2026-10-05-claude-lead/module-factory-plan.md`):

- the existing claims and requirement rows that the slice advances, with each node's status;
- the goals and the premises that its theorems still rest on;
- the older open parts of the same requirements that it leaves untouched.

Keep no second list of statuses. A conditional theorem keeps each premise that it does not meet.
