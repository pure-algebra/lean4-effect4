# 2026-10-05 seat DOGFOOD receipt: four scenarios on the acceptance programs

Status: receipt (history, not authority). Brief:
`docs/research/2026-10-05-claude-lead/briefs/seat-dogfood-brief.md`, with the dispatch message,
the coordinator's message on seat FOLD's merge, and addenda 2, 3 and 4.

**The one thing to know before merging:** the four fixtures under
`ocaml/engine/test/scenarios/` hold exact bytes. They hold the canonical bytes of each admitted
program, of each row and of each value, and each machine view. A merge that moves one of those
bytes turns `Test.Dogfood.Scenario.Lowered` red by name, and `lake build Test.All` with it.
That is the binding at work. The repair is the four steps of `Test/Dogfood/README.md`, section
"The lowered runs", then `dune test --force engine/test/scenarios`. Seat T5 changes how the
printer turns a binder term into TypeScript. I did not measure its branch, so I do not know
whether it moves a byte here.

Six more facts stand beside it.

- **Lake does not see a fixture as an input.** `include_str` is no dependency of the build. With
  one byte of a fixture changed, a fresh elaboration of the battery fails by name, and
  `lake build` succeeds from its cache (tested, item 5.4). So a fixture edited alone is not
  bound until the battery is elaborated afresh. Item 9.6, row b, proposes the repair.
- **Eleven planned goals are new, and none is under `src/`.** The goal gate of `Test/All.lean`
  counts 25 planned goals and 11 declarations that rest on goals. After slice 1, which adds
  no goal, it counted 14 and 7. Item 9.1 names the eleven. No proved top node of a requirement
  rests on a new goal.
- **The semantics report does not load the scenario modules.** So `generated/semantics.md` shows
  none of the eleven goals and none of the placed theorems. Item 9.5 proposes the roots, and
  says what they change.
- **No host run exists.** Every scenario's host run is waiting on T5. Addendum 4 takes the
  host half of slice 4 back, and item 9.4 lists what it needs. The engine compares the machine
  clause only (item 8).
- **Two controls of the brief are not delivered.** They are a cleanup replayed under one
  registration (atomic) and a timer that fires inside a masked region (timeout). Item 8 gives
  each reason.
- **Every run is bounded.** Each control is one finite run. Each search is a finite probe over
  short scripts. Six placed theorems are proved, and the four scenario claims are proved
  modulo their planned goals (item 4).

No file under `src/` changed. No existing battery changed: `Stage.lean` and the five program
batteries are as at the base, with the pin lines that seat T5 edits.

## 1. Base and head

| Item | Value |
| --- | --- |
| Branch | `seat/scenarios`, in the worktree `/Users/pooks/Dev/lean4-effect4-lower` |
| Base at dispatch | `c09826c0` |
| Base after the coordinator's message | `87c9b562`, by a fast-forward before the first commit |
| Slice 1 | `5d6d44b9`: the shared driver, its laws and its gate |
| Slice 2 | `c27d5745`: the workers scenario |
| Slice 3 | `6bfc1649`: the routing scenario |
| Slice 4, engine half | `6c0b4778`: the machine clause on the generated engine |
| Addendum 2 | `01bc224b`: the gate measures what a claim assembles; the table flag names its observation |
| Slice 5, with addendum 3 | `fbecf14b`: the atomic scenario |
| Slice 6 | `1d06f97d`: the timeout scenario |
| Lowered runs of slices 5 and 6 | `df60c819`: two more fixtures, on the generated engine |
| Head of the work | `df60c819` |
| Receipt | the commit that adds this file, on top of `df60c819` |

Nothing is pushed. Slice 4's host half has no commit: addendum 4 takes it back (item 9.4).

## 2. Changed files

`git diff --stat 87c9b562..df60c819` counts 16 files and 4094 added lines. No line is removed.

| Group | Files | What they hold |
| --- | --- | --- |
| Driver | `Test/Dogfood/Scenario.lean` | The script alphabet `Move`, the driver `play`, the readers, the driver's four laws, `tape_replays`, the record `Scenario` and the gate `#scenario_gate` |
| Scenarios | `Test/Dogfood/Scenario/Workers.lean`, `Routing.lean`, `Atomic.lean`, `Timeout.lean` | One battery a scenario: program, scripts, observation, claims, controls, record |
| Lowered runs, Lean | `Test/Dogfood/Scenario/Tape.lean`, `Lowered.lean` | The lowered runs and the fixture text; the binding of the committed fixtures, with its controls |
| Lowered runs, OCaml | `ocaml/engine/test/scenarios/dune`, `test_scenarios.ml`, `write.lean` | The test adapter over the generated `api_replay` with the real row table; the writer |
| Fixtures, generated | `ocaml/engine/test/scenarios/workers.txt`, `routing.txt`, `atomic.txt`, `timeout.txt` | Written by `write.lean` from `Tape.lean`; marked `GENERATED` in their first line |
| Root | `Test/All.lean` | Seven import lines after `import Test.Dogfood.P5LedgerService` |
| Documents | `Test/Dogfood/README.md`, this receipt | The section "The scenarios", with one row a scenario |

`ocaml/engine/test/test_engine.ml` and `ocaml/engine/test/dune` are not touched. The new test
has its own folder and its own dune file.

## 3. The scenarios

Each scenario's evidence word is tested: finite runs on named inputs. A claim's status is in
item 4. A record has two kinds of entry (addendum 2). The claim's proof uses an assembled
clause. An associated law has controls only.

| Scenario | Program | Observation | Claim, with its status | Controls | Machine | Engine | Host |
| --- | --- | --- | --- | --- | --- | --- | --- |
| workers | `crew`, `Scenario/Workers.lean`, on p3's consumer | `Observation`, seven fields: the assignment, the reply receipts, the reply applications, the retired calls, the cleanup identities, the root's exit, the work left | `workers`: proved modulo `releases_once`. Assembled: `receipt_inert`, `applied_selects`, `control_retires` (proved) and `releases_once` (planned goal). Associated: `replays` (proved) | 17: 9 green, 8 red | tested: 17 finite runs | tested: `workers.txt`, 5 runs, the machine clause only | waiting on T5: the printer refuses the program (`binderTerm Ref.update`) |
| routing | `request`, `Scenario/Routing.lean`, on p2's consumer | `Observation`, three fields: the response or the failure that escapes, the repository's calls, the refused rows | `routing`: proved modulo `infrastructure_escapes` and `unauthorized_calls_nothing`. Assembled: `tagIs_pair` (proved) and the two planned goals. Associated: `submit_success_prepared_fits` (proved, law graph) | 11: 5 green, 6 red | tested: 11 finite runs | tested: `routing.txt`, 4 runs, the machine clause only | waiting on T5: the program prints and reads back, and the keyed lane's files are barred |
| atomic | `shop`, `Scenario/Atomic.lean`, on p4's and p5's consumers | `Observation`, five fields: each request's outcome, the window, the account, the completed requests, the cleanup log | `atomic`: proved modulo `bounded`, `counted`, `committed` and `cleans_once`. Assembled: those four planned goals and `unsuspended_runs` (proved). Associated: `syncRow_typed` (proved, law graph) | 17: 10 green, 7 red | tested: 17 finite runs | tested: `atomic.txt`, 3 runs, the machine clause only | waiting on T5: the printer refuses the program (`binderTerm Ref.update`) |
| timeout | `fetch`, `Scenario/Timeout.lean`, on p1's consumer | `Observation`, nine fields: each held call's fate, the receipts, the applications, the retired calls, the stored replies, the attempts, the cleanup log, the root's ending, the timer work | `timeout`: proved modulo `retries_declared`, `stale_never_applies` and `cleanup_keeps`. Assembled: those three planned goals. Associated: `applyReply_zero`, `advance_answer_refuses` (proved, law graph) and `replays` (proved) | 19: 10 green, 9 red | tested: 19 finite runs | tested: `timeout.txt`, 6 runs and the handle case, the machine clause only | waiting on T5: the printer refuses the program (`binderTerm Ref.update`) |
| lowered | the 19 lowered runs of `Scenario/Tape.lean` | `machineView`, six readings: the root's exit, the cells, the calls waited on, the armed owners, the runnable fibers, the timers | `tape_replays`: a planned goal, and its own one clause | 4 in Lean: 2 green, 2 red. In OCaml: properties S1 to S5 of `test_scenarios.ml` | tested: the raw replay shows the session machine at 101 positions | tested: 183 checks, 0 failures, on both instances | none: the machine clause has no host half |

The controls count 68 in Lean: 36 green and 32 red. The gate runs them once a build, and a
failing control fails its battery by name. One changed expectation fails the gate by name
(tested on the timeout battery, with two changed lines and two named findings).

**What a scenario composes.** Each joins features where they meet.

- workers: a scope with a release, a fork into a scope, a loop, a handled failure, and calls
  that the host answers by key.
- routing: two nested handlers by tag, a branch on a host answer, host calls in sequence, and a
  typed failure that a host answer carries.
- atomic: two record cells with one atomic row each, and forked requests. Then a typed failure
  behind two commits, a finalizer, and a refill on the logical clock.
- timeout: a race with a timer, a retry loop with a typed test, and a call answered by key.
  Then an interruption that retires a held call, and a finalizer.

## 4. The claims

Each claim below is a declaration with its placement (`@[semantics "concept" (requirement :=
Rn)]`, decisions row 207). A standing is read from the claim's proof with goals as leaves
(`ProofGraph.standing`, `tools/ProofGraph/Goal.lean`). "Proved" is said only of a theorem that
rests on no goal. The standings and the `nearest` lists come from `ProofGraph.buildPlan` with
the scope `Test`, as the gate builds it. `#plan_status` gives the same standings.

### 4.1 The driver's laws, `Test/Dogfood/Scenario.lean`

| Claim | Placement | Standing | Axioms |
| --- | --- | --- | --- |
| `replays` | `host-session-protocol`, R13 | proved | `[propext, Quot.sound]` |
| `receipt_inert` | `host-session-protocol`, R6 | proved | `[propext, Quot.sound]` |
| `applied_selects` | `host-session-protocol`, R6 | proved | `[propext, Quot.sound]` |
| `control_retires` | `host-session-protocol`, R6 | proved | `[propext, Quot.sound]` |
| `tape_replays` | `translation-simulation`, R8 | planned goal | `[propext, sorryAx, Quot.sound]`, its own body |

```lean
theorem replays (b : Api.Built) (id : String) (budget : Api.Budget) (profile : String)
    (moves : List Move) :
    (Run.open b id budget profile).play (play (Run.open b id budget profile) moves).journal =
      play (Run.open b id budget profile) moves

def Inert (before after : Run) : Prop :=
  after.machine = before.machine ∧ after.session.applied = before.session.applied ∧
    after.session.consumed = before.session.consumed ∧
    after.session.retired = before.session.retired

def ReceiptInert : Prop :=
  ∀ (s : Run) (call : Sel) (completion : Api.HostSession.Answer),
    Inert s (step s (.hold call)) ∧ Inert s (step s (.receive call completion))

def AppliedSelects : Prop :=
  ∀ {program : Api.Program} {table : RowTable} (s : Session program table) (key : Key) (fuel : Nat),
    (Api.HostSession.applyReply s key fuel).phase = .applied →
    ∃ selected, s.active.find? (fun b => b.key == key) = some selected ∧
      (Api.HostSession.applyReply s key fuel).session.consumed =
        s.consumed ++ [selected.call.callId] ∧
      (Api.HostSession.applyReply s key fuel).session.applied = s.applied + 1

def ControlRetires : Prop :=
  ∀ {program : Api.Program} {table : RowTable} (s : Session program table) (fuel : Nat)
    (decision : NativeDecision) (selected : BoundCall),
    selected ∈ s.active →
    (∀ why, (Api.HostSession.advance s fuel decision).phase ≠ .refused why) →
    ((Api.requestOf (Api.HostSession.advance s fuel decision).session.machine
          selected.call.fiber selected.token).isSome = true →
        selected ∈ (Api.HostSession.advance s fuel decision).session.active) ∧
      ((Api.requestOf (Api.HostSession.advance s fuel decision).session.machine
          selected.call.fiber selected.token).isNone = true →
        (⟨selected, Api.HostSession.readReply s.pending selected.key⟩ :
            Api.HostSession.RetiredCall) ∈
          (Api.HostSession.advance s fuel decision).session.retired)

def TapeReplays : Prop :=
  ∀ (s : Run) (rows : List Command), (tapeFrom s rows).2 = [] →
    (s.play rows).machine =
      Run.machineOf (Run.replayFrom s.built.program s.built.table s.budget.fuel
        ((tapeFrom s rows).1.map (·.decision)) s.machine)
```

`receipt_inert : ReceiptInert`, `applied_selects : AppliedSelects`, `control_retires :
ControlRetires` and `tape_replays : TapeReplays`.

### 4.2 Workers, `Test/Dogfood/Scenario/Workers.lean`

| Claim | Placement | Standing | Axioms |
| --- | --- | --- | --- |
| `releases_once` | `scope-lifetime-finalization`, R11 | planned goal | `[propext, sorryAx, Quot.sound]`, its own body |
| `workers` | `host-session-protocol`, R6 | modulo `[releases_once]`; nearest `releases_once`, `control_retires`, `applied_selects`, `receipt_inert` | `[propext, Quot.sound]` beside the goal |

```lean
def ReleasesOnce : Prop :=
  ∀ (total : Nat) (budget : Api.Budget) (b : Api.Built) (moves : List Move),
    Effect4.Api.Author.build (crew total) = .ok b →
    (observe (Scenario.play (Run.open b "workers" budget) moves)).cleanups.Nodup

theorem workers : ReceiptInert ∧ AppliedSelects ∧ ControlRetires ∧ ReleasesOnce
```

### 4.3 Routing, `Test/Dogfood/Scenario/Routing.lean`

| Claim | Placement | Standing | Axioms |
| --- | --- | --- | --- |
| `tagIs_pair` | `residual-program-typing`, R10 | proved | `[propext]` |
| `infrastructure_escapes` | `translation-simulation`, R10 | planned goal | `[propext, sorryAx, Quot.sound]`, its own body |
| `unauthorized_calls_nothing` | `context-requirements`, R5 | planned goal | `[propext, sorryAx, Quot.sound]`, its own body |
| `routing` | `translation-simulation`, R10 | modulo `[infrastructure_escapes, unauthorized_calls_nothing]`; nearest those two and `tagIs_pair` | `[propext, Quot.sound]` beside the goals |

```lean
theorem tagIs_pair (tag other : String) (message : Val) :
    NativeAtom.eval .tagIs [.str tag, .list [.str other, message]] =
      some (.bool (other == tag))

def InfrastructureEscapes : Prop :=
  ∀ (id : Nat) (idText tag message : String) (b : Api.Built),
    Effect4.Api.Author.build (request "secret" id idText) = .ok b →
    tag ≠ "NotFound" → tag ≠ "Unauthorized" →
    (observe (Scenario.play (opened b) (failing tag message))).outcome =
      some (.failure (Cause.fail (.tagged tag message)))

def UnauthorizedCallsNothing : Prop :=
  ∀ (token : String) (id : Nat) (idText : String) (b : Api.Built) (moves : List Move),
    Effect4.Api.Author.build (request token id idText) = .ok b →
    (∀ reply pageSize, Effect4.Api.Runner.Command.submit reply ∈
        (Scenario.play (opened b) moves).journal →
      reply.completion ≠ ok (configOf token pageSize)) →
    (observe (Scenario.play (opened b) moves)).repositoryCalls = []

theorem routing :
    (∀ (tag other : String) (message : Val),
      NativeAtom.eval .tagIs [.str tag, .list [.str other, message]] =
        some (.bool (other == tag))) ∧
    InfrastructureEscapes ∧ UnauthorizedCallsNothing
```

### 4.4 Atomic, `Test/Dogfood/Scenario/Atomic.lean`

| Claim | Placement | Standing | Axioms |
| --- | --- | --- | --- |
| `bounded` | `store-typing`, R4 | planned goal | `[propext, sorryAx, Quot.sound]`, its own body |
| `counted` | `store-typing`, R4 | planned goal | `[propext, sorryAx, Quot.sound]`, its own body |
| `committed` | `store-typing`, R4 | planned goal | `[propext, sorryAx, Quot.sound]`, its own body |
| `cleans_once` | `scope-lifetime-finalization`, R11 | planned goal | `[propext, sorryAx, Quot.sound]`, its own body |
| `unsuspended_runs` | `translation-simulation`, R8 | proved | `[propext, Quot.sound]` |
| `atomic` | `store-typing`, R4 | modulo `[bounded, cleans_once, committed, counted]`; nearest those four and `unsuspended_runs` | `[propext, Quot.sound]` beside the goals |

```lean
def Bounded : Prop :=
  ∀ (b : Api.Built) (moves : List Move), Effect4.Api.Author.build (shop .none) = .ok b →
    (observe (Scenario.play (opened b) moves)).used ≤ 3

def Counted : Prop :=
  ∀ (b : Api.Built) (moves : List Move), Effect4.Api.Author.build (shop .none) = .ok b →
    (observe (Scenario.play (opened b) moves)).counted = true

def Committed : Prop :=
  ∀ (b : Api.Built) (moves : List Move), Effect4.Api.Author.build (shop .none) = .ok b →
    let o := observe (Scenario.play (opened b) moves)
    o.decisions[1]? = some .failedBehind → o.committed = true

def CleansOnce : Prop :=
  ∀ (b : Api.Built) (moves : List Move), Effect4.Api.Author.build (shop .none) = .ok b →
    (observe (Scenario.play (opened b) moves)).cleaned.Nodup

def Unsuspended : Prop :=
  ∀ (e : NativeEff), Straight e = true →
    (Api.run e (StraightEq.fuelFor e)).outcome = .finished ∧
      (Api.run (unsuspend e) (StraightEq.fuelFor (unsuspend e))).outcome = .finished ∧
      (Api.run e (StraightEq.fuelFor e)).exit =
        (Api.run (unsuspend e) (StraightEq.fuelFor (unsuspend e))).exit ∧
      (Api.run e (StraightEq.fuelFor e)).stores =
        (Api.run (unsuspend e) (StraightEq.fuelFor (unsuspend e))).stores

theorem atomic : Bounded ∧ Counted ∧ Committed ∧ CleansOnce ∧ Unsuspended
```

`Observation.counted` and `Observation.committed` are decidable readings of the observation,
defined in the battery beside `observe`. A control evaluates the same reading that its goal
states. The helper `unsuspend_eq` is proved at `[propext, Quot.sound]`: a straight program and
the program without its suspensions are `StraightEq`.

### 4.5 Timeout, `Test/Dogfood/Scenario/Timeout.lean`

| Claim | Placement | Standing | Axioms |
| --- | --- | --- | --- |
| `retries_declared` | `translation-simulation`, R10 | planned goal | `[propext, sorryAx, Quot.sound]`, its own body |
| `stale_never_applies` | `host-session-protocol`, R6 | planned goal | `[propext, sorryAx, Quot.sound]`, its own body |
| `cleanup_keeps` | `scope-lifetime-finalization`, R11 | planned goal | `[propext, sorryAx, Quot.sound]`, its own body |
| `timeout` | `host-session-protocol`, R6 | modulo `[cleanup_keeps, retries_declared, stale_never_applies]`; nearest those three | `[propext, Quot.sound]` beside the goals |

```lean
def RetriesDeclared : Prop :=
  ∀ (b : Api.Built) (moves : List Move), Effect4.Api.Author.build fetch = .ok b →
    moves.all Move.plain = true →
    (observe (Scenario.play (opened b) moves)).retriesDeclared = true

def StaleNeverApplies : Prop :=
  ∀ (b : Api.Built) (moves : List Move), Effect4.Api.Author.build fetch = .ok b →
    (observe (Scenario.play (opened b) moves)).staleNeverApplies = true

def CleanupKeeps : Prop :=
  ∀ (b : Api.Built) (moves : List Move), Effect4.Api.Author.build fetch = .ok b →
    (observe (Scenario.play (opened b) moves)).cleanupKeeps = true

theorem timeout : RetriesDeclared ∧ StaleNeverApplies ∧ CleanupKeeps
```

### 4.6 What each claim does not establish

Each docstring states its reach and its limits. The common ones follow.

- A planned goal is not proved. Its finite runs and its bounded search are finite probes.
- Each scenario goal is a statement about one program and one observation.
- `receipt_inert`, `applied_selects` and `control_retires` are safety laws of the session. They
  establish no progress, no reply admission at the application and no order of applications.
- `tape_replays` states machine equality under a whole tape. It states no equal session ledger,
  and nothing of a lowered engine: that link is the finite comparison of item 5.3.
- `unsuspended_runs` holds on the straight fragment only. The shop forks and yields, and a
  control shows that it is outside the fragment.
- The log-based goals (`releases_once`, `cleans_once`, `cleanup_keeps`) count writes by
  identity. They count no finalizer invocation, and they show no registration that ran twice.
- The host boundary stays where `docs/core/host-boundary.md` puts it. No claim here speaks of a
  host run.

## 5. Commands and results

Each Lean or Lake command ran through `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`,
named `SLOT` below. Each `make` call carried `-o build`. Each OCaml command ran through
`opam exec --switch=effect4 --`, named `OPAM` below, in `ocaml/`.

### 5.1 The builds

`SLOT lake build Test.All` ran green on each slice's tree before its commit. The table gives the
gate lines of `Test/All.lean` each time.

| Tree | Modules | Declarations | Planned goals | Declarations that rest on goals |
| --- | --- | --- | --- | --- |
| slice 1, `5d6d44b9` | 676 | 83636 | 14 | 7 |
| slice 2, `c27d5745` | 677 | 83739 | 15 | 8 |
| slice 3, `6bfc1649` | 678 | 83797 | 17 | 9 |
| slice 4, `6c0b4778` | 679 | 83937 | 18 | 9 |
| addendum 2, `01bc224b` | 680 | 83948 | 18 | 9 |
| slice 5, `fbecf14b` | 681 | 84174 | 22 | 10 |
| slice 6, `1d06f97d` | 682 | 84404 | 25 | 11 |
| lowered runs, `df60c819` | 682 | 84407 | 25 | 11 |

| Command | Result | Evidence |
| --- | --- | --- |
| `SLOT lake build`, the default build, on `df60c819` | `Build completed successfully (932 jobs)` | proved, tested |
| `Test/All.lean`, library-root gate | 165 API and utility modules, 278 Laws-only modules; every source reachable; `Effect4` never reaches Laws | tested |
| `Test/All.lean`, module and axiom gate | 682 modules, 84407 declarations; allowed axioms `[propext, Quot.sound]` | proved |
| `Test/All.lean`, goal gate | 25 planned goals; 11 declarations rest on goals; no other declaration reaches `sorryAx` | tested |
| `SLOT make -o build gen-semantics` | exit 0; `generated/semantics.md` has no diff | reproduced |
| `SLOT make -o build check-semantics` | `PASS semantics controls: imported tags and all statuses; 34 report refusals; 18 register controls; 4 traversal controls` | tested |
| `generated/semantics.md`, section "Acceptance programs" | the five batteries' `stage` and `waitsOn` literals read, as at the base | tested |
| `make check-docs` | `PASS check-docs: every path, link, citation and make target in 74 documents resolves` | tested |
| `make check-language` | `PASS check-language self-test: 48 of 48 controls`; no finding in the two checked documents | tested |
| `python3 scripts/check-language.py --show Test/Dogfood/README.md` | one finding, in a sentence of the base (the payload part's fields); no finding in the scenarios' sections | tested |
| `python3 scripts/check-language.py --show` on this receipt | no finding | tested |
| `SLOT make -o build corpus` | `kept 408 (readable 385) refused 0`; no tracked file changes | tested |
| `OPAM dune build` | exit 0; one warning 8 in `gen/api_check.ml`, a file of the base (item 9.7) | tested |
| `OPAM dune test --force engine/test/scenarios` | `101 positions compared on each of the two instances`; `183 checks, 0 failures` | tested |
| `OPAM dune test --force eff gen clock` | exit 0; `test_eff: 619 checks, 0 failures`; `prop_wire: 6345 checks, 0 failures (seed 42)`; `test_val_frames: 26 checks, 0 failures`; `test_lean_wire: 117 checks, 0 failures`; `metadata: 207 checks passed` | tested |
| `OPAM dune test --force engine` | exit 0; every lane ends `ALL PASS: 0 failure(s)`; the scenarios' lane ends `183 checks, 0 failures` | tested |
| `SLOT make -o build -o ts/eff/node_modules -o harness/truth/node_modules check-truth` | `23 pass, 0 fail` in four test files; `PASS: 39 programs agree on exits, schedules and sync exits; 1 signed divergence(s)`; `PASS truth: …; the regenerated modules type-check` | tested, host-only |

The truth check ran with two links and no install: `ts/eff/node_modules` to the coordinator's
folder, and `harness/truth/node_modules` to that link. Both are ignored by git. The check reads
the truth lane's files and writes none of them. It tests the base's truth lane on this branch:
no scenario is in that lane (item 8).

### 5.2 Build times

Fresh elaboration of one file, with the two precompiled libraries that Lake loads for a `Test`
module. Five runs each, on 2026-10-05 at 20:30, at a load average near 3. The column "before"
is the same measure at `87c9b562` at 18:05, without the two libraries.

| Module | Before, min / median (s) | After, min / median (s) |
| --- | --- | --- |
| `Test/Dogfood/Stage.lean` | 0.87 / 0.88 | 0.78 / 0.87 |
| `Test/Dogfood/P1HttpCache.lean` | 1.95 / 2.04 | 1.74 / 1.79 |
| `Test/Dogfood/P2HandlerLayers.lean` | 0.89 / 1.05 | 0.90 / 0.90 |
| `Test/Dogfood/P3WorkerQueue.lean` | 1.08 / 1.14 | 0.95 / 0.96 |
| `Test/Dogfood/P4RateLimiter.lean` | 0.94 / 1.00 | 0.85 / 1.00 |
| `Test/Dogfood/P5LedgerService.lean` | 0.85 / 0.88 | 0.88 / 0.90 |
| `Test/Run/RunContract.lean` | 2.51 / 2.68 | 2.27 / 2.41 |
| `Test/Api/KeyedHostContract.lean` | 2.60 / 2.83 | 2.34 / 2.42 |
| `Test/Program/MeaningEqContract.lean` | 1.48 / 1.50 | 1.35 / 1.48 |
| `Test/Dogfood/Scenario.lean` | new | 2.34 / 2.38 |
| `Test/Dogfood/Scenario/Workers.lean` | new | 1.88 / 1.93 |
| `Test/Dogfood/Scenario/Routing.lean` | new | 1.80 / 1.81 |
| `Test/Dogfood/Scenario/Atomic.lean` | new | 2.41 / 2.49 |
| `Test/Dogfood/Scenario/Timeout.lean` | new | 1.96 / 2.04 |
| `Test/Dogfood/Scenario/Tape.lean` | new | 1.44 / 1.46 |
| `Test/Dogfood/Scenario/Lowered.lean` | new | 2.31 / 2.33 |

- No existing battery's file changed, so no battery's build time changed by this work.
- The seven new modules add 14.4 s of elaboration, by their medians. They build in parallel.
- A scenario module's import floor is 1.43 s. The floor is the cost of its imports alone.
- The slowest new module is `Atomic.lean`, at 2.49 s. The slowest battery of the Run, Api and
  Dogfood folders is `KeyedHostContract.lean`, at 2.42 s.
- The slowest `Test` module of a whole build is `Test.Audit.ProofStyle`, at 51 seconds. Seat
  LOWER's build log of the same day gives that number, and I did not measure it again.
- The gate's dependency check costs about 0.3 s a command (item 7.1, finding 14).

### 5.3 The engine's comparison

`test_scenarios.ml` calls the generated `api_replay` on a prefix of the tape, with the real row
table and the fixture's budgets. It passes no preloaded answers. It reads the table from its
wire bytes with `Eff_wire.decode_row_exact`. It runs on both instances, Fast
(`Api_engine_inst`) and Ref (`Api_engine_ref`).

| Fixture | Runs | What the runs are |
| --- | --- | --- |
| `workers.txt` | 5 | the lowest-fiber schedule, both orders of the reply applications, a cancellation, a refused row |
| `routing.txt` | 4 | the three requests, and an infrastructure failure |
| `atomic.txt` | 3 | the scripted run to the root's exit, an interrupted request, an interrupted root |
| `timeout.txt` | 7 | a reply before the timeout, the second attempt's reply, a late reply, a reply kept and never applied, a 404, four timeouts, and the handle case |

- Nineteen runs, 101 positions on each instance: the engine's view is Lean's at each position.
- The engine reifies an interrupted exit, with its annotations, to the bytes Lean writes.
- Every run with two decisions or more has its red control: the tape without its last decision
  ends at another view.
- `handle/cache` is p1's own program, whose first host row answers a handle. It is the one run
  with `table differs`. The engine shows the same difference on both instances.
- The other 15 runs with a host row say `table same`. That line records equal machine views
  under the empty table. It does not say that the replay reads no row (addendum 2).

### 5.4 The instruments' own red controls

Each line is tested: I ran the fault and read the refusal.

| Instrument | Fault | Refusal |
| --- | --- | --- |
| The binding battery | the fixtures of before a change of the text | `lowered: the control "each committed fixture is the text Lean writes for the admitted programs" fails` |
| The binding battery, fresh elaboration | one byte of `timeout.txt` | the same finding |
| The binding battery, `lake build` | the same byte | none: `Build completed successfully`, from the cache. This is the limit of the first list |
| The engine test | one digit of one expected view in `atomic.txt` | two `FAIL` lines, one for each instance; exit 1 |
| The gate, dependency check | the workers record under the claim `receipt_inert` | three findings, each naming a clause that the proof does not reach |
| The gate, placement | `Effect4.Run.step_id` as an associated law | `has no placement: no semantics attribute and no row of the semantics registry` |
| The gate, controls | two changed expectations of the timeout battery | two findings, each naming its control |
| The searches | a faulty program for each clause | see item 5.5 |

After each fault I put the file back, and compared it byte for byte with the saved copy.

### 5.5 The finite probes

Each search is a finite probe, outside the build. It plays every script of an alphabet up to a
length, from named start states, and checks a goal's statement on every run. The probes are in
the scratch folder of the session, and they are not committed.

| Goal | Alphabet and length | Scripts | Runs against the statement |
| --- | --- | --- | --- |
| `releases_once` | 23 moves, length 4 at most, three start states | 877680 | 0 |
| `unauthorized_calls_nothing` | 14 moves, length 5 at most | 579194, of which 541984 meet the hypothesis | 0 |
| `infrastructure_escapes` | 96 instances of tag, message and user | 96 | 0 |
| `tape_replays` | 19 moves, length 4 at most from the opened crew, length 3 from a later state | 144799 whole tapes | 0 |
| `bounded`, `counted`, `committed`, `cleans_once` | 17 moves and 15 moves, length 4 at most, eight start states | 606420 | 0 for each |
| `retries_declared` | 16 plain moves, length 4 at most, four start states | 279616 | 0 |
| `stale_never_applies`, `cleanup_keeps` | the same scripts, and 24 moves with raw rows, length 3 at most, two start states | 308464 | 0 for each |

The searches find planted faults, so their silence carries weight.

| Faulty program | Clause | Runs against the statement |
| --- | --- | --- |
| the shop that reads and writes in two steps | `bounded` | 18931 of 54240 |
| the shop whose term leaves the window | `counted` | 2768 of 3615 |
| the shop whose finalizer takes the deposit back | `committed` | 1421 of 3615, every run that meets the premise |
| the shop whose finalizer notes twice | `cleans_once` | 3542 of 3615 |
| the client that retries every failure | `retries_declared` | 30 of 69904 |
| the client whose finalizer resets the count | `cleanup_keeps` | 2594 of 4368 |
| two business tags in `infrastructure_escapes` | the conclusion | 2 of 2 |
| scripts outside the hypothesis of `unauthorized_calls_nothing` | the conclusion | 440 reach the repository |

`stale_never_applies` has no faulty twin: a program cannot make the session apply a stale
reply. Its red controls are the session's refusals, in the battery.

### 5.6 Not run

The dispatch message and the brief exclude each command below. Each is **not run**.

- `make check-gen`
- `make check-slow`
- `make check-corpus`
- `make check-target`
- `bash scripts/check-conservativity.sh`
- `make gen-truth-ledger`
- `make check-truth-release`

These are not run either. Addendum 4 stops every further gate, so the coordinator runs them at
the merge.

- `make check` and `make check-full`, as wholes, with `make check-roots` and
  `make check-proof-style`. The default build runs `Test/Audit/ProofStyle.lean`, which passes.
- `make check-cases`: no match on a policy family is new under `src/`.
- `make check-tsdiag`, `make check-schema-ts` and `lake build Effect4Gen`: the brief names
  them as red before this work.
- Any host run of a scenario: the keyed lane waits on seat T5 (item 9.4).
- `make check-docs` after this receipt's commit. It passed on `df60c819`.

The disk had 30 GiB free at the end.

## 6. The axiom output of each proved theorem

```text
'Test.Dogfood.Scenario.replays' depends on axioms: [propext, Quot.sound]
'Test.Dogfood.Scenario.receipt_inert' depends on axioms: [propext, Quot.sound]
'Test.Dogfood.Scenario.applied_selects' depends on axioms: [propext, Quot.sound]
'Test.Dogfood.Scenario.control_retires' depends on axioms: [propext, Quot.sound]
'Test.Dogfood.Scenario.Routing.tagIs_pair' depends on axioms: [propext]
'Test.Dogfood.Scenario.Atomic.unsuspend_eq' depends on axioms: [propext, Quot.sound]
'Test.Dogfood.Scenario.Atomic.unsuspended_runs' depends on axioms: [propext, Quot.sound]
```

The four scenario claims and the eleven planned goals print `[propext, sorryAx, Quot.sound]`.
The gate of `Test/All.lean` admits `sorryAx` only as a goal's own body, and it counts what rests
on goals. The law-graph theorems that the records cite print as follows.

```text
'Effect4.Api.HostSession.submit_success_prepared_fits' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Typed.syncRow_typed' depends on axioms: [propext, Quot.sound]
'Effect4.Api.HostSession.applyReply_zero' depends on axioms: [propext, Quot.sound]
'Effect4.Api.HostSession.advance_answer_refuses' depends on axioms: [propext, Quot.sound]
```

The gate's two declarations stay under the ceiling: `expandScenarioGate` and `registered` each
print `[propext]`.

## 7. Findings

### 7.1 Friction with the API

Each row is one case, in the brief's four parts. No scenario hides a case behind a helper of
the API: each detour is in the battery that needed it.

| # | What I tried to write | What the API asked for | Verdict, or the cost | Proposal |
| --- | --- | --- | --- | --- |
| 1 | `Rows.receive` for a call that the host already holds | the recorded claim and one `submit` row by `Rows.reply` | `Call.at` gives the next call id: the bind is refused `duplicateCall`, the submit `callOrder`. Cost: 10 lines of `Move.rows` and `bound` | `Rows.deliver`, for a held call |
| 2 | which keys were received, applied and refused, from `Run.observe` | the journal with its phases: `Run.Observation` holds a count | nine readers, about 45 lines of `Scenario.lean` | `Run.ledger`: receipts, applications and refusals by key |
| 3 | `#eval` of a run's exit | a hand printer: `ExitV` and `FiberStatus` have no `Repr` | 10 lines in each probe | a `Repr` instance, or one printer in `Test` support |
| 4 | a short name after `open`: `Answer`, `Refusal`, `start`, `Outcome`, `Cause.interrupt`, `.finished` | the full name | an ambiguity error each time; `Move.start` and `RequestOutcome` are renames | `Authoring` exports no `Cause`; rename `Test.Dogfood.Answer` |
| 5 | `let x ← if c then a else b` in `eff do`, and an `if` as its last statement | parentheses around the `if` | `unsupported statement in eff block` | accept `if` as a statement of `eff do` |
| 6 | a script as `a ++ b ++ [.apply w]` | a typed helper, `script [a, b, …]` | each chain cost 0.1 to 0.25 s of elaboration, and 14 chains cost 3.1 s | a note beside `Move`; the cause is the binary operator's elaborator |
| 7 | `Ref.make` of an empty list | an ascription through a one-field record (p3's `ascribe`) | one helper, and one call a cell | `Ref.makeAt`, with a stated type |
| 8 | equality of two exits | a normal form: an interruption's exit carries one annotation from the host, two from a fiber | `RequestOutcome` and `Ending`, about 25 lines a scenario | a reader of an exit's shape without its annotations |
| 9 | "did this decision move the machine?" from its verdict | a comparison of machines: a decision with no effect is `progressed` | found by a probe: `fire` steps a queued fiber, `evaluate` does not | a phase for a decision with no effect, or one line a decision in its docstring |
| 10 | a reply application at budget zero on a live run | a record update of the run's budget: `Run.open` fixes it | one line, outside the API's shape | `Run.withBudget`, or a budget argument of `Run.step` |
| 11 | a gate as a function over the environment | a macro that expands to `run_cmd`: a command elaborator in a `Test` module reaches `Classical.choice` | each battery elaborates the body again, 0.13 s | an elaborator under `tools/ProofGraph`, outside the audited modules |
| 12 | a placed claim in a battery | `import Effect4.Laws.Auto.Semantics`, which imports `Lean` | 0.55 s a module | none: it is the price of a placement |
| 13 | `(Api.run e fuel).outcome == .finished` | `Api.Outcome.finished`, and the result type `Api.Inspection` | two errors | none |
| 14 | the gate's dependency check by `ProofGraph.buildPlan` | nothing more | 0.3 s a command: `goalsIn` scans every constant in interpreted code (0.16 s), the axiom closure costs 0.10 s | precompile `ProofGraph.Plan` (item 9.6, row d) |
| 15 | a fixture bound by `include_str` | nothing: Lake takes the file as part of the source | a fixture edited alone is not bound by `lake build` (item 5.4) | item 9.6, row b |
| 16 | a writer that imports the binding battery | a module with no control: a stale fixture fails the battery that the writer needs | one more module, `Tape.lean`, 1.46 s | none: the split is the repair |

### 7.2 What the runs showed of the semantics

Each line is measured on a finite run, and each is in a control or a probe.

1. A cancellation of a call that the host never held leaves no retired record. The session's
   ledger retires held calls only.
2. `applyReply` reports `applied` once the guard is consumed, even when the command loop ran
   out of fuel. So `tapeFrom` checks the fuel itself before it reads a reply application.
3. The repository row's error column is a pair of strings. So a host failure that wears a
   business tag is routed as that business failure. With the exact union column, the session
   refuses that reply at the reply receipt.
4. The handler's type over the exact row keeps the caught tags in its error column (decisions
   row 130).
5. p1's `retryForm` sleeps 200 ms before the first retry, with a base of 100. Its cursor
   doubles before the first sleep. Its docstring says `base · 2^k` before retry `k + 1`.
6. A later attempt parks under another fiber and another guard token: `1.0`, then `5.7`. The
   session refuses a late receipt and a late application with `noCall`. It refuses a forged
   reply with `callOrder`, and a direct answer decision with `directAnswer`.
7. A reply received before the timeout stays with the retired call, and is never applied.
8. A straight program's bounds move under the rewrite: depth 9, 31 steps and fuel 68 with the
   suspensions, and 8, 29 and 64 without them.
9. Fifteen of the sixteen lowered runs with a host row show equal machine views under the
   empty table. The handle case shows another view.

## 8. The lanes that could not carry a scenario

| Lane | What it could not carry | The smallest extension |
| --- | --- | --- |
| Engine, the session clause | every scenario's receipts, applications, retired calls, stored replies and refusals: the generated engine holds no session | none in the test: a copy of Lean's record would test nothing of OCaml. It needs a session on the engine's side |
| Engine, the machine view | a fiber's exit, but the root's: the engine compares the atomic cells, and not each request's outcome | one more reading of `MachineView`: the fibers' exits, with its field in the fixture and in the adapter |
| The fixture's format | a host answer that is not a success or one tagged failure; an interruption with annotations | one more decision line; `write.lean` exits 1 on such a tape today |
| Host, the keyed lane | every scenario: the lane's files are barred until T5 is merged, and three programs do not print | item 9.4 |
| Host, the keyed recorder | an operation that completes after its cancellation: the workers' cancellation between receipt and application, and the timeout's late replies | the recorder records such a completion as a refused late reply; one case, to design with T5's part |
| Host, the truth lane | every scenario: `fixtureRun` calls `Api.run` with a list of completions, so it does not keep receipt and application apart | none: the keyed lane is the route |
| The semantics report | the eleven goals and the six placed theorems: the registry's roots do not load the scenario modules | item 9.5 |
| Atomic, one control | a cleanup replayed under one registration: the log counts writes by identity | an identity of a finalizer's invocation in the observation. None exists today |
| Timeout, one control | a timer that fires inside a masked region | the mask's contract (decisions rows 244 to 246) |

## 9. Open obligations and proposals

### 9.1 The eleven planned goals

Each is `proof_goal` in a battery, with its placement and its docstring. Each consumer is its
scenario. `tape_replays` has one more: the lowered runs.

| Planned goal | Battery | Placement | Consumer |
| --- | --- | --- | --- |
| `tape_replays` | `Test/Dogfood/Scenario.lean` | `translation-simulation`, R8 | the lowered runs of every scenario |
| `releases_once` | `Scenario/Workers.lean` | `scope-lifetime-finalization`, R11 | workers |
| `infrastructure_escapes` | `Scenario/Routing.lean` | `translation-simulation`, R10 | routing |
| `unauthorized_calls_nothing` | `Scenario/Routing.lean` | `context-requirements`, R5 | routing |
| `bounded` | `Scenario/Atomic.lean` | `store-typing`, R4 | atomic |
| `counted` | `Scenario/Atomic.lean` | `store-typing`, R4 | atomic |
| `committed` | `Scenario/Atomic.lean` | `store-typing`, R4 | atomic |
| `cleans_once` | `Scenario/Atomic.lean` | `scope-lifetime-finalization`, R11 | atomic |
| `retries_declared` | `Scenario/Timeout.lean` | `translation-simulation`, R10 | timeout |
| `stale_never_applies` | `Scenario/Timeout.lean` | `host-session-protocol`, R6 | timeout |
| `cleanup_keeps` | `Scenario/Timeout.lean` | `scope-lifetime-finalization`, R11 | timeout |

No goal is proved. `tape_replays` is the nearest to a proof: it extends
`play_controls_eq_replay` (`src/Effect4/Laws/Run.lean`) from control rows to reply
applications. I did not start it.

### 9.2 The split of each record

| Scenario | Claim | Assembled clauses | Associated laws |
| --- | --- | --- | --- |
| workers | `workers` | `receipt_inert`, `applied_selects`, `control_retires`, `releases_once` | `replays` |
| routing | `routing` | `tagIs_pair`, `infrastructure_escapes`, `unauthorized_calls_nothing` | `submit_success_prepared_fits` |
| atomic | `atomic` | `bounded`, `counted`, `committed`, `cleans_once`, `unsuspended_runs` | `syncRow_typed` |
| timeout | `timeout` | `retries_declared`, `stale_never_applies`, `cleanup_keeps` | `applyReply_zero`, `advance_answer_refuses`, `replays` |
| lowered | `tape_replays` | `tape_replays` | none |

The gate measures each assembled clause by the planning graph. It measures a placement by the
declaration's own attribute or by a row of the semantics registry. `submit_success_prepared_fits`,
`applyReply_zero` and `advance_answer_refuses` pass by their module, a default module of
`host-session-protocol`. `syncRow_typed` carries its own attribute.

### 9.3 The three corrections

| Correction | Commit | What changed |
| --- | --- | --- |
| Addendum 2, point 1: the gate did not check that a claim assembles its clauses | `01bc224b` | The record's two kinds of entry. One plan a command, with a memo of its own. A refusal by name of a clause the proof does not reach, and of a goal that no clause names. Placement by evidence, and no module prefix. Ten fixtures, and the workers record under `receipt_inert` |
| Addendum 2, point 2: the table flag said more than it observes | `01bc224b` | `observedTableDifference`, the fixture line `table differs` or `table same`, the engine test's field. The sentence "is not read" is removed. The handle case came with `df60c819` |
| Addendum 3: the atomic draft's "committed" control, and the prose of `counted` | `fbecf14b` | `committed` is a statement of the scenario's stores, with a finalizer that takes the deposit back as its red control. `cleans_once` states the log's multiplicity alone. `counted` is per request for the deposit, and by outcome for the window |

One evidence kind of addendum 2 is not built: a measured dependency connection to a placed
claim. So `Effect4.Program.Denote.meaning_onExit` cannot stand in a record: it has no attribute
and no row of the registry. The docstring of `committed` names it as the supporting law.

### 9.4 The host half of slice 4

It is not mine any more (addendum 4). It waits for seat T5's faces. What it needs:

- **The lane.** The keyed lane's four files: `harness/truth/session/Keyed.lean`,
  `run-keyed.ts`, `keyed-recorder.ts` and `check-keyed.ts`. Its controls `KeyedTool.two` and
  `KeyedTool.shared` already run two parked calls in both orders on a printed program.
- **The programs that must print.** `Workers.crew`, `Atomic.shop` and `Timeout.fetch` are
  refused today by name: `binderTerm Ref.update`. `Routing.request` prints and reads back today.
- **The observation to compare.** Each battery's `Observation`, the session clause: seven
  fields for workers, three for routing, five for atomic, nine for timeout. The interruption's
  annotations are outside each of them.
- **The scripts.** Each battery's scripts are `List Move` values. A journal replays them with
  no fixture (`replays`), so the host lane can take the journal's rows.
- **One extension.** The keyed recorder refuses an operation that completes after its
  cancellation. Two controls of workers and two of timeout need that case (item 8).

### 9.5 Proposed changes of the semantics registry and the law graph

I edited neither. Each line is a proposal.

1. Add the seven scenario modules to `registry.roots`, and to `SEMANTICS_DOGFOOD` and
   `SEMANTICS_ROOTS` of the `Makefile`. Then the eleven goals become nodes of R4, R5, R6, R8,
   R10 and R11, and the report shows them as open.
2. Move the driver's four general laws into the law graph: `receipt_inert`, `applied_selects`
   and `control_retires` beside `src/Effect4/Laws/Api/HostSession.lean`, and `tape_replays`
   beside `play_controls_eq_replay`. They speak of every run, and of no scenario.
3. Move `unsuspend`, `unsuspend_eq` and `unsuspended_runs` beside `StraightEq.suspend_remove`
   (`src/Effect4/Laws/Program/MeaningEq.lean`). They serve `straight-composition-agreement`.
4. Register one claim a scenario goal, under the concept and the requirement of item 9.1.
5. Place `Effect4.Program.Denote.meaning_onExit`: tag it, or make `Effect4.Laws.Program.Denote`
   a default module of a concept.

### 9.6 Proposed decisions rows

| Row | Proposal |
| --- | --- |
| a | A scenario's record lists assembled clauses and associated laws, and `#scenario_gate` measures the first by the planning graph (rows 203 and 254, addendum 2) |
| b | The scenario fixtures become a generated group: a producer for steps 1 and 2 of the README, and `check-gen`'s drift refusal. Or Lake takes each fixture as an input of `Lowered.lean` |
| c | `applyReply` at an exhausted budget: decide whether the phase is `applied` or a frontier (item 7.2, line 2) |
| d | `ProofGraph.Plan` joins the precompiled libraries, or `buildPlan` takes its goals as an argument (item 7.1, finding 14) |
| e | A cancellation of a call that the host never held: decide whether the session records it (item 7.2, line 1) |
| f | p1's `retryForm`: the first delay and its docstring disagree (item 7.2, line 5) |
| g | An identity of a finalizer's invocation in a run's observation, so that a replayed registration has a control (item 8) |
| h | The third evidence kind of a placement: a measured dependency connection to a placed claim (item 9.3) |

### 9.7 Outside these slices, reported and not repaired

- `OPAM dune build` prints one warning 8 in `gen/api_check.ml`: the match of `show_val` names
  no case for `Val_negInt` and `Val_float`. The build exits 0.
- Item 7.2, line 5, is a property of p1's battery, which I did not change.

