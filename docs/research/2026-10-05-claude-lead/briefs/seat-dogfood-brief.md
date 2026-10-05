# 2026-10-05 brief for seat DOGFOOD: four scenarios on the acceptance programs

Status: a brief (history, not authority). Base: the head of `refactor/phase1-phase3` that the
dispatch message names. The owner asked for this work on 2026-10-05 (decisions row 254). The
scenarios come from Codex's review of the acceptance programs.

## Why this slice exists

The owner's words, 2026-10-05: dogfooding must be rigorous. It tests the core semantics, the
coherence of the APIs and their ergonomics, above all where features compose. It joins a proof
in Lean to the code that the tree lowers to OCaml and prints as TypeScript. It is not a pile of
checks that slow the build and connect to nothing. Its purpose is sanity: using the language shows what proof work alone hides.

Four rules follow, and they bind every line you write.

1. **A check has a claim.** Every check is a control of one placed claim or planned goal. A
   check with no claim is not written.
2. **A scenario has one named observation.** The machine, the generated OCaml engine and the
   printed TypeScript module are compared on that observation, and on nothing looser.
3. **A scenario composes.** It joins at least two features of the language. A test of one
   spelling is not a scenario.
4. **The default build stays fast.** A scenario is a few small runs. Report each module's
   build time before and after.

## Who and where

You are one seat of the Effect4 estate. The coordinator wrote this brief and merges your
branch. You work alone and hand back a receipt. Another seat may run beside you on the term
language and its faces. Your files and its files do not meet in slices 1 to 3.

- **Worktree and branch:** the dispatch message names both. The dependency packages are cloned
  there already.
- **The coordinator's checkout** is `/Users/pooks/Dev/lean4-effect4`. Read it freely. Write
  nothing there.
- **Lean:** run every Lean and Lake command through
  `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`. Never run a bare `lake build`. Never
  send a Lean command's standard error to `/dev/null`. Run one `lake` at a time.
- **OCaml:** only through `opam exec --switch=effect4 -- dune …`.
- **TypeScript:** only tsgo 7, the pinned `@typescript/native-preview`. Never `tsc`.
- **No install and no download.**
- **Git:** never push. Commit on your branch, by explicit paths. Use `git add -f` for a file
  under `docs/research`. Read `git status` before each commit.
- **Scratch files:** under the scratch folder that the dispatch message names.
- **Disk:** stop and report below 4 GiB free.

## Read first, in this order

1. `AGENTS.md`, in full. Its trust rules, its placement rule for every obligation and its
   writing rules bind you.
2. `Test/Dogfood/README.md` and `Test/Dogfood/Stage.lean`: the instrument that exists. A
   battery pins one `Reach` value to its `stage` declaration.
3. Codex's review, your specification:
   `docs/research/2026-10-05-codex-foundation-packet/implementation-audit/open-questions-review/dogfood/review.md`.
   It gives each scenario its concept, observation, hypotheses, reuse, controls and exclusions.
   Then its follow-up on the two lowered routes:
   `docs/research/2026-10-05-codex-foundation-packet/implementation-audit/heartbeat-dogfood-2207/review.md`.
4. The five batteries, `Test/Dogfood/P1HttpCache.lean` to `P5LedgerService.lean`.
5. The run API and its laws: `src/Effect4/Run.lean`, `src/Effect4/Laws/Run.lean` and
   `src/Effect4/Laws/Api/HostSession.lean`. Then their batteries: `Test/Run/RunContract.lean`
   and `Test/Api/KeyedHostContract.lean`.
6. `Test/Program/MeaningEqContract.lean`, with `StraightEq.run_agrees` in
   `src/Effect4/Laws/Program/MeaningEq.lean`.
7. `docs/core/semantics.md` §2.3, §2.4, §2.8, §2.9 and §2.10, and
   `docs/core/host-boundary.md`.

## What a scenario is

A scenario is one unit with six parts.

| Part | Content |
| --- | --- |
| Program | One program through `Api.Author.build`, from an existing battery where one fits |
| Script | The run's commands: controls, receipts, applications and clock steps, as `Run` commands |
| Observation | One named value read from the run: exits, calls, the whole record, cleanup identities |
| Claim | One theorem or planned goal that states the property, with its placement |
| Controls | The positive run, and one deliberate defect for each clause of the property |
| Lowered runs | The same observation on the generated OCaml engine and on the printed TypeScript module |

A scenario's record names its claim as a declaration. A scenario whose claim does not resolve
must fail the build.

## The slices

Land each as its own green commit, in this order.

### 1. The shared scenario driver

A new module, `Test/Dogfood/Scenario.lean`.

- It selects a live call by its key, through `Api.HostSession.Call.at`
  (`src/Effect4/Run.lean`).
- It keeps receipt and application apart. `Rows.receive` is the receipt. The application is the
  command `.apply key`, through `Run.step` or `Run.play`, as the driver of
  `Test/Dogfood/P3WorkerQueue.lean` does.
- Do not use `Rows.answer` after a receipt. It binds, submits and applies in one, so the journal
  would hold a second receipt that the session refuses.
- Every decision goes into the existing journal. Replaying the journal must not run the host
  fixture again (`journal_replays`, `play_controls_eq_replay`, `src/Effect4/Laws/Run.lean`).
- It holds the scenario's record: its name, its observation's name and its claim.
- One command at the foot of each battery fails when a scenario's claim does not resolve.
- It is a test utility over `Run`. It adds no scheduler and no program representation.
  `Run.Reactor` is synchronous and gets no key, so it cannot express these scripts alone.

### 2. Workers: two pending replies

Extend the consumer of `Test/Dogfood/P3WorkerQueue.lean`.

- Two workers hold one pending host call each.
- Receive both replies. Apply them in both orders. Then cancel one worker.
- **The property:** a receipt does not advance the machine. Only the selected live key
  applies. Cancelling one worker retires only its call. Each registration cleans up at most
  once.
- **The observation** has seven fields: the assignment of jobs to workers, the accepted
  receipts and the selected applications. Then the retired calls, the cleanup identities, the
  root exit and the work left.
- **Controls:** a duplicate answer, a stale answer and a wrong-key answer are refused. A
  cancellation before the receipt, and one between receipt and application. Both application
  orders around one shared cell: they may differ, and `reply_commute` is a law of receipts only.
- Keep the lowest-fiber schedule of today as the positive control.

### 3. Routing: exact handlers, and the call that must not happen

Extend the consumer of `Test/Dogfood/P2HandlerLayers.lean`, on its admitted `handle` program.

- **The property:** each handler catches only its named failure. An infrastructure failure
  escapes the business handler. An unauthorized request makes no call of the repository.
- **The observation:** the exact response or the failure that escapes, the repository's calls,
  and the refusal's phase.
- **Controls:** an infrastructure error that no handler names, a wrong failure tag, a wider
  record, and a handler that catches every failure.
- Do not start the refused service fragments. The structured service carrier waits for its
  own slice.

### 4. The lowered link

Begin this slice only after the coordinator's message that the term seat is merged. Merge
`refactor/phase1-phase3` into your branch first.

**The host.** Two routes exist, and you add none.

- **A script that keeps receipt and application apart** runs on the keyed lane:
  `harness/truth/session/Keyed.lean`, `run-keyed.ts`, `keyed-recorder.ts` and `check-keyed.ts`.
  Its controls `KeyedTool.two` and `KeyedTool.shared` already run two parked calls in both
  arrival orders and both application orders, on a printed program.
- **A script with no separate order** may enter the truth lane: `corpus` in
  `harness/truth/Truth.lean`. Its `fixtureRun` calls `Api.run` with a list of completions, so
  it does not keep the two commands apart.
- The keyed recorder refuses an operation that completes after its cancellation. A scenario
  that needs that case states it as waiting, and you propose the bounded extension.
- A program that does not print stays out. The printer refuses a binder term by name until
  the faces of a binder term land. Record that stage as waiting. Do not rewrite a program to
  avoid the refusal.

**The engine.** The production interface `E4_engine.INSTANCE` takes no row table.
`ocaml/engine/api_engine_inst.ml` and `api_engine_ref.ml` fix the table to the empty list.

- Call the generated `api_replay` (`ocaml/engine/api_engine.ml`) through an adapter that lives
  in the test. It takes the program, the command fuel, the decision tape, the answers, the row
  table and the compile fuel. Do not change the production interface.
- Read the row table from its wire bytes, with `decode_row` and its helpers in
  `ocaml/eff/eff_wire.ml`. Convert it into the instance's row type by a checked conversion.
  Bind those bytes to the Lean fixture that `Api.Author.build` admits. Never write a table by
  hand.
- Compare after each control that made progress and after each applied answer. A refused
  receipt leaves the machine unchanged. An application at budget zero leaves its reply pending.
- Do not turn a frontier into a successful application, and keep its remainder.

**The observation's boundary.** The generated engine holds no session state: no pending reply,
no retired call, no consumed call. So a scenario's observation lands as two placed clauses.

1. The session clause: the whole observation, checked in Lean and on the keyed host lane.
2. The machine clause: a named projection of the machine, checked by the table-aware replay on
   the engine.

The engine's session clause stays waiting, and you say so. Do not copy Lean's session record
into the OCaml result: that would test nothing of OCaml.

**A lane that cannot carry a script is a finding.** State the gap and the smallest extension
that would close it. Do not write a second runner, and change no production API.

Do not run `make gen-truth-ledger` or `make check-truth-release`. The coordinator promotes the
build ledger at your merge.

### 5. Atomic state with failure and cleanup

On the consumers of `P4RateLimiter.lean`, `P5LedgerService.lean` and
`Test/Program/MeaningEqContract.lean`.

- **The property:** between refills the used capacity stays bounded. Each completed request
  adds one to exactly one outcome count. A continuation that fails leaves the committed state
  for finalization.
- **The observation:** the decision, the whole record, the count of completed requests and the
  cleanup identities. The returned answer alone is not the observation.
- **Controls:** the separate read and write of today, and the answer and state types swapped.
  Then the store update erased while the answer stays, and a cleanup replayed under one
  registration.

### 6. Replies at a timeout's boundary

On the consumer of `P1HttpCache.lean`.

- **The property:** only the declared failures retry. A reply of a timed-out attempt never
  applies to a later attempt. Cleanup keeps the committed state.
- **Controls:** one reply before the timeout, after it, and received before it but applied
  after it. A failure that must not retry. The new attempt's key in an old reply.
- A case whose cut depends on the mask waits for the mask's slice. State it as waiting, and
  write no guess.

Then give the lowered runs of slices 5 and 6, as slice 4 does.

## The obligations and their placement

State each property as a planned goal first, in its battery, with its placement. Prove it in
place when an existing law gives it in a few lines. A finite run is a control of the goal, and
it is reported as a finite probe.

| Scenario | Concept; requirement | Reach | It does not establish | Reuse |
| --- | --- | --- | --- | --- |
| Workers | `host-session-protocol`, R6; `scope-lifetime-finalization`, R11; live frontiers, R12 | Exact live keys, compatible reply envelopes, named interruption state, explicit decisions and budgets | No Queue backpressure and no fairness. Host application typing and the retirement edge stay open R6 work | `submit_machine`, `reply_commute`, `submit_duplicate`, `applyReply_zero`, `applied_reply_refused` (`src/Effect4/Laws/Api/HostSession.lean`) |
| Routing | `context-requirements`, R5 and R10; reply admission, R6 | The exact record rows and the admitted carrier types of today | No code-valued service and no layer lowering. `build_total` assumes typed leaf semantics | `preflight_success_prepared_fits`; `provide_discharges` and `provide_closed` (`src/Effect4/Program/Provision.lean`) under their premises |
| Atomic | `store-typing`, R4; `translation-simulation`, R8, for the rewrite | Natural-valued fields, a fitting initial world and store, one atomic update for each request, an explicit refill boundary | No scheduler guarantee without a bound, no host transaction, no whole-run resource theorem | `StraightEq.run_agrees`; the generic store preservation; the binder-term typing of the read-modify-write rows |
| Timeout | `host-session-protocol`, R6; `translation-simulation`, R10; frontiers, R12 | Explicit time steps, the reply key's identity, the saved interruption state, finite budgets | No Cache contract, no deadline fairness, no physical clock | The stale and duplicate refusals of the host session; the run's replay connection |

- Give each goal `@[semantics "<concept>" (requirement := Rn)]`, and name its consumer in its
  docstring: the scenario.
- The session clauses reuse the registry's `reply-commute` and its admission claims, under R6.
  The machine clause of slice 4 belongs to `translation-simulation`, serving R8 and R13.
  Cleanup by identity is a clause of `scope-lifetime-finalization`, under R11.
- State the projection, the real table, the budgets, the value profile and the accepted-phase
  premises before you state a goal. Keep receipt and application apart, safety and progress
  apart, and a finite run and a proof apart.
- Do not edit `tools/Tools/SemanticsRegistry.lean`. Propose each registry claim in the receipt.
- Before a proved top node of a requirement would rest on a new goal, stop and report.
- Keep the seven judgments apart. An accepted receipt does not establish the executable
  connector of reply admission. One finite application that succeeds does not either.
- Do not state the associativity of a raw bind as a law. The system map leaves it open.

## What keeps this slice from being loose checks

- No `#guard` without the scenario it controls, and no scenario without its claim.
- No exploration over schedules in a default import. A wide run goes to the slow lane, listed
  in `slowLane` of `Test/Audit/AxiomGate.lean`, and you propose it first.
- No new module may take longer to build than the slowest battery of today. No battery's build
  time may double. Measure both and report them.
- Keep rendered bytes inside `#guard`s. A battery `def` over rendered text reaches
  `Classical.choice`.
- No `partial`, `unsafe`, `native_decide`, `axiom`, `extern` or `implemented_by`. A `sorry`
  exists only as the body of a `proof_goal`.

## Ergonomics is a result

Write each scenario through the public authoring API, as a user would. Each time the API
resists, record a finding. Do not hide it with a helper.

A finding has four parts:

1. what you tried to write;
2. what the API asked for in its place;
3. the refusal's verdict, or the count of lines that the detour cost;
4. a proposal.

The findings go in the receipt, numbered. They are proposals for the owner, and you change no
API.

## What is not in this slice

- The Queue, the mask, the Semaphore, the fold and the faces of a binder term.
- A change under `src/`. If a scenario needs one, stop that scenario and report.
- `docs/core/decisions.md`, `lakefile.toml`, `docs/STATE.md` and the semantics registry:
  propose in the receipt.
- The retained baselines under `Test/fixtures/baseline/<commit>/`.
- The release's build ledger.

## Acceptance

Give each result in the receipt.

- `lake build` of each touched module, through the slot, with its time before and after.
- For each claim: its exact proposition, its `#plan_status` line and its `#print axioms`
  output.
- `make gen-semantics`, then `make check-semantics`: the batteries' `stage` and `waitsOn`
  literals still read.
- `make check-docs` and `make check-language`, after `Test/Dogfood/README.md` gains the
  scenarios' rows.
- For slice 4: `make corpus`, then `dune build`, `dune test --force eff gen clock` and
  `dune test --force engine`; `make check-truth`.
- The default `lake build` once at the end, with the gate lines of `Test/All.lean`.

Import a new module in `Test/All.lean` on the line after `import Test.Dogfood.P5LedgerService`.

## Known, and not yours to repair

- `make check-tsdiag` and `make check-schema-ts` are red for reasons outside this work.
- `lake build Effect4Gen`, the library target, fails. It is not a gate.
- A stale `.lake/corpus` makes one engine check fail after a wire change. `make corpus` prints
  the corpus again.

Report anything else that is red for a reason outside your slices. Do not repair it.

## The receipt

Write `docs/research/2026-10-05-seat-DOGFOOD-receipt.md`, in the handoff form of `AGENTS.md`:

1. first, the one thing the coordinator must know before merging;
2. the base and head commits, and each slice's commit;
3. the changed files;
4. a table with one row for each scenario. Its columns are the program, the observation, the
   claim with its status, and the controls. Three more columns give the runs on the machine,
   the engine and the host, each with its evidence word;
5. each command with its result, and the build times;
6. the axiom output of each proved theorem;
7. the ergonomics findings, numbered;
8. each lane that could not carry a scenario, with the smallest extension that would close it;
9. the open obligations, and the proposed registry claims and decisions rows.

Your last message gives the head commit, the receipt's path and the first item of the receipt.
