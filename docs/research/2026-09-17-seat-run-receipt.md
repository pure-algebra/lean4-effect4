# Seat Run — receipt

Worktree `/Users/pooks/Dev/lean4-effect4-run`, branch `seat/run`, cut from
`refactor/phase1-phase3` at `1a8587f2`. Seven commits, nothing pushed.

**Evidence words, used exactly.**

- **proved** — a theorem with a proof term at the cited line, elaborated by the build named in
  §7 and stamped at `[propext, Quot.sound]` or below.
- **tested** — a `#guard` or `#guard_msgs` that ran green in that build.
- **stamped** — an axiom print I ran and read (§7).
- **assumed** — my own reasoning about code I read, with no theorem behind it. Marked where it
  appears.
- **reproduced** — nothing here is reproduced from another machine.

---

## 1. Commits

| hash | what |
| --- | --- |
| `7b04ff7a` | `Run`, the rows, the claim, the observation, the reactor, the drive, the three named runs; the battery's two examples; the `Api/Built.lean` repair |
| `9b261b29` | `journal_replays` (O-9), `drive_eq_play` (O-6), `open_total` (O-1) and the small facts |
| `21b52f47` | `Call.claim`; `at_eq`, `bindCall_at` (O-5), `receive_rows`/`answer_rows` (O-2, O-3); `preflight_ok`, `submit_accepted`, `applyReply_accepted` |
| `93c56fdb` | `answer_accepted` and `drive_envelope` (O-7) |
| `532bc964` | `answer_once` (O-4) and `runPure_eq_run` (O-10) |
| `851e0abb` | the aesop pass over the law module |
| `605a8ba8` | the battery's clock rows, the second-answer pins and the ceiling stamps |

Files: `src/Effect4/Run.lean` (new, 341 lines), `src/Effect4/Laws/Run.lean` (new, 820 lines),
`Test/Run/RunContract.lean` (new, 177 lines), one import line in `Test/All.lean:83`, one in
`src/Effect4/Laws.lean:41`, and the repair in `src/Effect4/Api/Built.lean` (§2).

---

## 2. The repair outside my files, flagged first

`src/Effect4/Api/Built.lean` (the coordinator's `1a8587f2`, shared with the Author seat) could
not be used as it stood. The file had no `set_option autoImplicit false` and no `open`, so
`RowTable` in its first field did not resolve and auto-bound implicits turned the field into
`table : {RowTable : Type} → RowTable`. That type has no values at all — the structure was
uninhabited and `Api.Built` could not be constructed. The whole brief depends on it, so I made
the smallest repair: `set_option autoImplicit false` and
`open Effect4.Program (RowTable AdmittedProgram)`, nothing else
(`src/Effect4/Api/Built.lean:13-17`). **The coordinator has since landed the same repair on
main as `3cf0d1e8`** and reports the merge will be clean.

Nothing else outside my files was touched.

---

## 3. What landed

### 3.1 The type and the rows (`src/Effect4/Run.lean`)

| line | declaration | note |
| --- | --- | --- |
| `:48` | `structure Run` | `built : Api.Built`, `budget : Api.Budget := {}`, `session : HostSession.Session built.program built.table`, `journal : List Command := []`, `phases : List Phase := []` |
| `:66`, `:69`, `:78` | `Run.id`, `Run.profile`, `Run.machine` | **decision D-1**: the name, the profile and the machine are *projections of the session*, not fields. See §5. |
| `:99` | `Run.open b id budget profile` | total, no refusal; builds the header from the `Built` and loads the machine at `budget.compileFuel` |
| `:110` | `Run.runner` | the `Api.Runner.Runner` the rows are played through |
| `:115`, `:123` | `Run.step`, `Run.play` | one row recorded with its verdict; rows folded |
| `:141` | `Call.claim s key op request` | the claim a row carries; everything but the row and the request is the run's own |
| `:152` | `Call.at s key` | the claim for the call the machine is holding, `none` when it holds none |
| `:167`–`:179` | `Rows.tape`, `Rows.control`, `Rows.start`, `Rows.flush`, `Rows.clock` | `Rows.clock` is `Api.TestClock.adjust` |
| `:182`–`:196` | `Rows.reply`, `Rows.receive`, `Rows.answer` | `Rows.answer = [bind, submit, apply]`; empty when the machine holds no call (§5, D-3) |
| `:206`–`:212` | `Run.answer`, `Run.receive`, `Run.control` | play what the rows say |
| `:221` | `structure Observation` | state, outcome, exit, awaiting, pending, retired, applied, reasons; `deriving DecidableEq` only (§5, D-4) |
| `:241` | `Run.observe` | |
| `:259` | `abbrev Reactor σ := Program.Row → Val → σ → Option (Answer × σ)` | `Answer` is `HostSession.Answer`, the `Completion` of `Machine/Completion.lean` |
| `:264` | `Run.freshCall` | the first call the session has no record of — neither a binding nor a slot |
| `:276` | `Run.driveFrom` | one recursion: the run, the rows it chose, the host's state |
| `:301`, `:311` | `Run.drive`, `Rows.answerAll` | both read off `driveFrom`, so they cannot drift |
| `:324`–`:335` | `Run.runPure`, `Run.runClock`, `Run.runWith` | |

### 3.2 The laws (`src/Effect4/Laws/Run.lean`) — the obligation table of scout A §4.5

| obligation | theorem | line | status |
| --- | --- | --- | --- |
| O-1 `open_total` | `open_total` | `:210` | **proved.** `start` returns exactly the session `Run.open` builds, for any non-empty name. Needed two facts the tree did not have: `admitProgram_certificate` (`:198`) — admission answers with the certificate it is given — and `admitted_unique` (`:187`) — a program has at most one certificate against one table. |
| O-2 `receive_rows` | `receive_rows` | `:346` | **proved**, with `receive_none` (`:352`) for the case the scout did not name. |
| O-3 `answer_rows` | `answer_rows` | `:357` | **proved**, with `answer_none` (`:363`) and `answer_rows_three` (`:368`). |
| O-4 `answer_once` | `answer_once` | `:689` | **proved**, in a different form than the scout expected — see §4. `acceptReply_after_applied` (`:703`) is the refusal form. |
| O-5 `bindCall_at` | `bindCall_at` | `:318` | **proved**, and the stronger `bindCall_at_bound` (`:328`) that the answer law needs. |
| O-6 `drive_eq_play` | `drive_eq_play` | `:177` | **proved.** |
| O-7 `drive_envelope` | `drive_envelope` | `:615` | **proved**, over `Reactor.Envelops` (`:604`). The theorem under it is `answer_accepted` (`:452`), which says much more — see §4. |
| O-9 `journal_replays` | `journal_replays` | `:164` | **proved**, over the invariant `Reached` (`:148`). |
| O-10 `runPure_eq_run` | `runPure_eq_run` | `:798` | **proved**, with the hypothesis that both control rows progressed — see §4. |
| O-8 (the codec) | — | — | **not mine**: the brief says the Face seat's. §6 says what a generated instance would need. |

Twenty-eight more theorems carry those ten. The ones another seat may want by name:

- `play_append` (`:96`) — rows act on runs, so a journal splits anywhere.
- `result_header` (`:101`) — no transition writes the header, which is why `Run.id` cannot drift.
- `preflight_ok` (`:383`), `submit_accepted` (`:400`), `applyReply_accepted` (`:421`) — the
  three session facts `HostSession` does not state: a preflight succeeds on a reply that names
  a binding the machine still holds and carries a completion the machine admits; such a
  receipt stores it and changes nothing else; applying it is applied, or a fuel frontier —
  never refused. **Written in my law module, not in `HostSession`'s**, as the brief asks.
- `observe_awaitingAsync` (`:255`) — a machine holding a call is in the state every receipt and
  every answer is an edge from. Under it `awaits_ne_nil` (`:239`), which uses
  `Program.requestOf_current` (`src/Effect4/Laws/Program/Admit.lean:415`).
- `allows_submit` (`:262`), `allows_answer` (`:268`) — the two protocol edges, by `decide`.
- `advance_step` (`:769`), `advance_progressed` (`:781`) — what a control row can do.
- `replay_eq` (`:740`), `replay_machine` (`:746`), `machineOf_nil` (`:754`),
  `replayFrom_cons` (`:759`) — the raw replay in pieces. `replayFrom` (`:722`) and `enoughFor`
  (`:728`) exist because `stepDecisionState` needs the program's own evaluator instance in
  scope, so a statement about it cannot be written bare; `steppedBy`
  (`src/Effect4/Program/Admit.lean:248`) already did this for the machine half.
- `api_requestOf` (`:289`) — `Api.requestOf` and `Program.requestOf` are two names for one
  definition; the session module reads the first where `Envelope` reads the second.

### 3.3 The battery (`Test/Run/RunContract.lean`)

Scout A §5's two examples, both **tested**:

- **A service call** (`:39`–`:83`). The load-bearing pin is `:50`:
  `driven.journal = Test.Api.RunnerContract.journal ++ Rows.flush` — the rows the host drove
  are *exactly* the journal `Test/Api/RunnerContract.lean:30-33` writes by hand, plus the flush
  that ends the drive. Nothing in the file names a call id, a guard token or a reply. Also
  pinned: the eight phases, the exit, the whole `Observation`, that replaying the journal from
  a fresh `open` reaches the same observation, and that `Call.at` on the started run is the
  hand-written `call0`.
- **A fork and an await** (`:87`–`:134`). The exit `KeyedHostContract` pins, reached with no
  fiber number and no token in the file; and the same run answered by key in the other order,
  which is `reply_commute`'s case.
- The clock rows are the test clock's own tape (`:139`), a second answer for an answered call
  has no rows (`:149`–`:151`), and nine law ceilings are **stamped** in the file
  (`:155`–`:172`) the way `Test/Api/RunnerContract.lean:121-134` stamps its own.

---

## 4. Where the statement I proved differs from the one the brief named

Each of these is a case where the brief's statement is false or weaker than the truth. None is
a weakening.

**D-A. O-4 is not a refusal.** The brief asks for "playing the same `answer` twice refuses the
second". It does not refuse: `Rows.answer` is built from the machine, and after an applied
answer the machine holds no call at that key, so there are **no rows** and playing them changes
nothing (`answer_once`, `:689`; **tested** at `Test/Run/RunContract.lean:149-151`). The refusal
the scout has in mind belongs to a row recorded *earlier* and played again, and that is
`acceptReply_after_applied` (`:703`), which is `applied_reply_refused` lifted to the run. I did
**not** state "the recorded rows refuse with `.staleCall`": by then the session's next call id
has advanced, so the recorded `bind` row is refused `.callOrder` first, not `.staleCall`. That
is **assumed** — I read the order of `bindCall`'s checks (`Api/HostSession.lean:148-154`) and
did not prove it.

**D-B. O-7's hypothesis is about the completion only.** `Reactor.Envelops` (`:604`) asks of the
host exactly the third part of `Envelope` (`Program/Admit.lean:183-185`): every completion it
gives for a call a machine is holding, on the row that call was made on, is one `admit`
accepts. The other two parts — the table and the parked request — are the ones the *run* builds
rather than the host, so asking them of the host would be asking it to restate what `Call.at`
already restates. The quantifier runs over every machine, which is what makes the hypothesis
usable at every round of a drive without an invariant.

**D-C. O-7's conclusion is weaker than what is proved under it.** `drive_envelope` says the
phases a drive adds contain no `.refused .envelope`. `answer_accepted` (`:452`) says the three
rows of an answer are `.bound`, `.preflight`, and then `.applied` or `.frontier` — no row of it
is refused at all, for any reason. The flush rows are the reason the drive's own statement is
only about envelopes: `advance` can refuse `.stuck` or `.protocol`, and neither is about a
completion (`advance_not_envelope`, `:279`).

**D-D. O-10 needs a hypothesis.** `runPure_eq_run` (`:798`) holds when both control rows
progressed. Without that the two routes stop in different places: the session keeps the machine
it stepped to and stops, `Api.replay` keeps walking the rest of its tape. The hypothesis is
stated as a fact about the run's own `phases`, so a caller checks it by evaluation.

**D-E. O-9 needs an invariant, and it is an inductive predicate.** `Reached` (`:148`): a run is
opened, or it is a run with one more row played. I chose this over making `Run` constructible
only through `open`/`play` (which Lean cannot enforce for a structure) and over a
`WellFormed` predicate on the fields (which would restate the journal's meaning). `Reached.play`
(`:153`) closes it under `play`.

---

## 5. Decisions I took, for the owner to overturn if they disagree

**D-1. `Run.id`, `Run.profile` and `Run.machine` are projections, not fields.** The brief lists
`id` and `machine` as fields. A second copy of the name is exactly friction F3 of the scout
note ("the header repeats what the session already has") and it can drift from the name
`bindCall` checks a call against (`Api/HostSession.lean:149`). As projections of the session's
header they cannot. `Run.open` still takes the name as an argument. Cost: a `Run` is not a flat
record for a codec; the Face seat would project it.

**D-2. `runPure`, `runClock` and `runWith` return the `Run`, not the `Observation`.** The scout
returns `Observation`, which throws away the journal — and the journal is the point (O-9).
`(Run.runPure b).observe` is the scout's value, one call away, and the battery pins both.

**D-3. `Rows.receive` and `Rows.answer` are empty when the machine holds no call at the key.**
The alternative is to fabricate a claim and let the session refuse it, which would put invented
data on the wire. Empty rows are the honest reading, `play []` is the identity, and
`receive_none`/`answer_none` say so.

**D-4. `Observation` derives `DecidableEq` only, not `Repr`.** The brief asks for both. `Repr`
is not available: `awaiting : List Await` carries `NativeOp`, which derives `DecidableEq` alone
(`src/Effect4/Program/Native.lean:131`), and `exit : Option ExitV` carries `Exit`, likewise
(`src/Effect4/Machine/Exit.lean:30`). Adding `Repr` to either is an edit to a file that is not
mine; a hand-written `Repr` would traverse a `String` and need a name in `AxiomGate.lean`,
which is also not mine. **Owner call**: either derive `Repr` on `NativeOp` and `Exit`, or leave
`Observation` without it.

**D-5. `Run.drive` has a round budget, default 64.** `planRun` takes fuel and fails when it runs
out (`harness/truth/session/Keyed.lean:296`); a library function must be total, so the drive
stops. It stops on four conditions, all in the docstring (`src/Effect4/Run.lean:269-275`): a
flush that reveals no call, a host that declines, only calls the session already recorded, or
the rounds running out. The last three are all "nothing more this host can do".

**D-6. `driveFrom` is one recursion returning the rows.** `drive` and `Rows.answerAll` are both
projections of it, so O-6 is a real induction rather than a `rfl` between two recursions that
could drift.

**D-7. The `Run` structure is `Type 1`-free but `Effect4.Run` is not in the `Effect4` root.**
`src/Effect4.lean` is not one of my files, so `Effect4.Run` is reachable only through
`Effect4.Laws` (via `src/Effect4/Laws.lean:41`). `Effect4.Api.Built` has the same status and
already did before my branch. **One line for the coordinator**: `import Effect4.Run` in
`src/Effect4.lean`, or the application face still cannot see the run API (friction F10).

---

## 6. What the Face seat needs for a generated `Canonical Observation`

Every field's codec already exists; only the structure's own instance is missing.

| field | instance |
| --- | --- |
| `state : HostProtocol.State` | `src/Effect4/Api/RunnerDerived.lean:1462` |
| `outcome : Api.Outcome` | `src/Effect4/Api/RunnerDerived.lean:1589` |
| `exit : Option ExitV` | `Exit` at `src/Effect4/Api/RunnerDerived.lean:473` |
| `awaiting : List Await` | the shape is already published as `"Outstanding"` (`src/Effect4/Api/RunnerBytes.lean:83`) |
| `pending`, `retired : List Key` | `src/Effect4/Api/Derived.lean:133` |
| `applied : Nat` | generic |
| `reasons : List FrontierReason` | `src/Effect4/Api/Derived.lean:278` |

So the generator's work is one group over `Observation` itself, and `schemas`
(`src/Effect4/Api/RunnerBytes.lean:78`) gains an `"Observation"` entry. That closes the runner
plan's missing `inspectBytes` without a machine codec, which is what scout A's D6 recommends.

---

## 7. Verification

Every command run in `/Users/pooks/Dev/lean4-effect4-run`.

| command | result |
| --- | --- |
| `lake build Effect4.Run` | `Build completed successfully (117 jobs)` |
| `lake build Effect4.Laws.Run` | `Build completed successfully (298 jobs)` |
| `lake build Test.Run.RunContract` | `Build completed successfully (307 jobs)`, every `#guard` and `#guard_msgs` green |
| `lake env lean src/Effect4/Laws/Run.lean` | no error, no warning |
| `lake env lean Test/Run/RunContract.lean` | no error; three `#check` infos |

**Stamped.** A scratch file printing the axioms of all 73 declarations of
`src/Effect4/Laws/Run.lean` (every `theorem`, `def` and `inductive` it declares), and of all 31
declarations of `src/Effect4/Run.lean`: **every one is at `[propext, Quot.sound]` or below**.
Four are below it — `allows_submit` and `allows_answer` reach no axiom at all, `api_requestOf`
and `any_append_key` reach `[propext]`. No `sorry`, no `native_decide`, no new axiom, no
`partial`, no `unsafe`.

`make check` and `make check-host` were **not** run: the brief scopes me to the modules I
write, and those are wave commands for the coordinator.

### The aesop census

`#auto_census Effect4.Laws.Run using aesop` (`src/Effect4/Laws/Auto/Census.lean`), run before
and after the pass:

- before: `23 of 67 theorems closed from their statements; 61 source lines they now take`
- after: `23 of 67 theorems closed from their statements; 58 source lines they now take`

What the pass did. Twenty-three proofs are now one `aesop` call: `admitProgram_certificate`
(eight nested splits before), `open_total`, `journal_replays`, `drive_eq_play`,
`readReply_append_fresh`, `find_append_fresh`, `awaits_ne_nil`, `allows_submit`,
`advance_not_envelope`, `at_none`, `receive_rows`, `receive_none`, `answer_rows`,
`answer_none`, `answer_rows_three`, `any_append_key`, `preflight_ok`, `play_built`,
`requestOf_of_mem_awaits`, `rowOf_external`, `freshCall_facts`, `answer_once`,
`replay_machine`, `machineOf_nil`, `replayFrom_cons`, `advance_step`, `advance_progressed`,
`bindCall_at`, `bindCall_at_bound`, `at_eq`. Each follows the brief's pattern: `unfold` the one
definition the hypothesis is about, bind the conditional facts with `have`, then
`aesop (add norm simp […])`. Two residual goals told me the missing fact rather than the
missing tactic, exactly as the brief says: `admitProgram_certificate` stopped at a structure
equality between two certificates (the fact was `admitted_unique`, registered
`safe apply`), and `advance_progressed` needed the case analysis stated as a lemma
(`advance_step`, handed over as a `have`).

**Three proofs keep hand steps, and why.**

1. `result_header` (`:101`) — `aesop (add norm unfold [Api.Runner.result, …])` closes it, and
   its proof reaches `Classical.choice`. The axiom gate refuses that, so the four arms stay as
   one `rfl` each. Stamped: the hand proof is `[propext, Quot.sound]`.
2. `submit_accepted` (`:400`) — the same, for the same reason.
3. `applyReply_accepted` (`:421`) — aesop reaches the last `if` and stops. Which side it takes
   *is* the difference between the two disjuncts of the statement, so the `split` is the
   statement and not a missing fact; the comment in the file says so.

**What I did not replace, and why.** The 23 theorems the census still reports are the `rfl`
one-liners — the row unfoldings (`step_session_bind`, `step_phases_apply`, …), `play_nil`,
`play_cons`, `open_phases`, `replay_eq`, `api_requestOf`. The census's own measure is where
aesop "does the work of a long proof"; for these, `aesop` is *longer* (one line either way,
but a search per build) and *worse* on the ceiling: a `rfl` reaches no axiom, and the census
reports aesop's proof for each of them at `[propext, Quot.sound]`. `rfl` is also the statement
of what those theorems mean. Three more keep one `simp only` or a short structural proof where
aesop closes nothing: `play_append` (one `simp only`), `admitted_unique` (obtain, subst, `rfl`)
and `at_of_requestOf` (two lines).

---

## 8. What is owed

Nothing I was asked to prove is owed. What is out of scope and named for someone:

1. **O-8, the `Observation` codec** — the Face seat's. §6 is the packet.
2. **A concrete reactor that is provably inside the envelope.** `Reactor.Envelops` is a
   hypothesis; no host in the tree discharges it, and the battery's `echo` cannot, because
   `admit` also checks the machine's `allocated` list and handle liveness
   (`Program/Admit.lean:59-75`), which a reactor does not see. The row-level half of the same
   check already exists as `externalAdmits` (`src/Effect4/Program/Compile.lean:1388`); joining
   it to a reactor needs the typed-park invariant (a parked external request has its row's
   request type), which is the open `TypedState` row of the proof chain. The battery pins the
   *conclusion* by evaluation instead (no `.refused` phase anywhere in `driven.phases` or
   `forked.phases`). This is **assumed**, not proved: I did not prove that no host can
   discharge `Envelops` today, only that I found none.
3. **`Run.openBytes` (O-14, F20)** — not in my brief. It needs a `Canonical RowTable`, which
   does not exist; `Api.ofBytes` covers the program half only (`src/Effect4/Api.lean:180`).
4. **`.frontier` from `applyReply` still has no law** — the gap scout A §2.7 names. My
   `applyReply_accepted` admits that branch as a disjunct rather than closing it; what is
   missing is a statement about the session in it (the reply stays received, the binding stays
   active, the machine has moved).
5. **`Refusal.pendingControl`, `applyPending`, `Refusal.selectionRequired`** — scout A §4.6
   wants them deleted; D9 is the owner's, and the codec regeneration is not mine.
6. **`src/Effect4.lean` does not import `Effect4.Run`** — §5, D-7. One line, the coordinator's.

---

## 9. What I did not check

- I did not run `make check`, `make check-host` or `make check-full`, and I did not touch the
  truth harness. The claim that `Run.drive` replaces `planRun`
  (`harness/truth/session/Keyed.lean:296-325`) is **assumed** from reading both; the drive's
  rule for picking a call is `planRun`'s (`unless current.active.any …`) plus the pending
  slots, and no lane was cut over.
- I did not read `src/Effect4/Api/RunnerDerived.lean` in full; §6's table is from its instance
  headers and `src/Effect4/Api/Derived.lean`.
- I did not check the OCaml or TypeScript sides.
- `Run.runClock`'s agreement with `Api.TestClock.run` is **tested** on the rows
  (`Test/Run/RunContract.lean:139`), not proved as a theorem about the machines; the shape of
  the proof is `runPure_eq_run`'s with the tape generalised, and I did not write it.
