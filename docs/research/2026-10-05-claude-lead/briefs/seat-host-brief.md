# 2026-10-05 brief for seat HOST: the scenarios on the printed module, on the keyed lane

Status: a brief (history, not authority), written ahead of its dispatch. Base: the head of
`refactor/phase1-phase3` that the dispatch message names. It is the host half of the scenarios'
lowered link (decisions row 254). Seat DOGFOOD handed that half back
(`docs/research/2026-10-05-seat-DOGFOOD-receipt.md`, items 8 and 9.4).

## Why this slice exists

The owner's words, 2026-10-05: dogfooding joins a proof in Lean to the code that the tree
lowers. A scenario has one named observation, and the machine, the generated OCaml engine and
the printed TypeScript module are compared on it.

Two of the three are done. Each scenario runs on the Lean machine, and its machine clause
replays on the generated engine. No scenario runs as a printed module on rc.112 yet. This slice
adds that run, on the lane that keeps a reply's receipt and its application apart.

Three rules bind every line you write.

1. **One observation.** The host run is compared on the battery's own `Observation`, the
   session clause. Add no second, looser comparison.
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
   `open-questions-review/dogfood/review.md` and `heartbeat-dogfood-2207/review.md`.

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
3. **The comparison.** Lean replays the host's recording with `Run.play` and reads the
   battery's `Observation`. It must be the observation of the same script on the Lean machine,
   field for field. The host's exit must be Lean's exit.
4. **The order of the scenarios.**
   - **routing** first. Its program prints and reads back, and its calls come in sequence.
   - **workers** second: two pending replies, both application orders, a cancellation.
   - **timeout** third: the clock, a retry, a late reply.
   - **atomic** last. Its printed module may not type-check: see "Known".
5. **The one extension that is planned.** The recorder refuses an operation that completes
   after its cancellation. Two controls of workers and two of timeout need that case. Record
   such a completion as a late reply that the session refuses. Design it before you build it:
   send the coordinator the design in one message, and go on with the scripts that do not need
   it.
6. **A red control for each scenario on the host.** One changed expectation fails the check by
   the scenario's name. One recording with a moved record is refused by Lean's replay.
7. **The documents.** Each scenario's row of `Test/Dogfood/README.md` gets its host result.

Where the lane cannot carry a script, state the gap and the smallest extension that would
close it. Do not rewrite a program to make it run. Do not change a production API.

**Reuse first** (the owner, 2026-10-05). Use the recorder, the bindings, the clock boundary and
the lane's check. Before you add a helper, name its consumer in this slice.

## Design first, in one short note

Before the first commit, write `docs/research/2026-10-05-seat-HOST-design.md`, one page:

- how a `Move` becomes a host action, for each constructor;
- which scripts of each battery a host can perform, and which it cannot, with the reason;
- how the host knows a scripted completion for a call;
- how a script's schedule is fixed on rc.112, where the scenario forks. If rc.112 chooses an
  order that the script does not state, say how the recording carries that order to Lean;
- where the new files live, and what `scripts/check-host-protocol.py` runs.

Send its path to the coordinator in one message, and start routing without waiting.

## The obligations and their placement

No theorem is asked for. If you state one, place it first, as `AGENTS.md` requires.

| Evidence | Claim it is a control of | Reach | It does not establish |
| --- | --- | --- | --- |
| A scenario's host run | The scenario's claim (`workers`, `routing`, `atomic`, `timeout`), `host-session-protocol` R6 and `translation-simulation` R8 | One script, one schedule, on rc.112 under bun | No agreement for another script, no host adequacy, no liveness |
| Lean's replay of the host's recording | The same claim, and `run-tape-replay` for the machine | The recording that the host wrote | Nothing of a host that the recorder does not see |

- A theorem that is proved today stays proved.
- Do not edit `docs/core/decisions.md`, `lakefile.toml` or `docs/STATE.md`.
- No `partial`, `unsafe`, `native_decide`, `axiom`, `extern` or `implemented_by`. No `sorry`
  outside a `proof_goal`. Every warning is an error.

## Acceptance

1. **routing and workers** run on rc.112 and agree with Lean on the whole observation, for
   each script that the design note lists as performable.
2. **Each printed module** type-checks under tsgo 7 against the prelude, or its diagnostics
   are in the receipt with the compiler's version.
3. **The red controls** of the assignment's item 6 are red.
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
5. each scenario's scripts: performed, or not, with the reason;
6. each choice you made, and each gap of the lane with its smallest extension;
7. what is bounded and what is host-only;
8. proposed decisions rows. Do not edit the register.

Your last message gives the head commit, the receipt's path and the first item of the receipt.
