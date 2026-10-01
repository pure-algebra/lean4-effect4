# Brief for Codex: slice 6 and the three bounded fixes

**Amended by [addendum 1](2026-09-30-codex-brief-slice6-addendum-1.md)** (items A–C, after the design pass) **and extended by [addendum 2](2026-09-30-codex-brief-slice6-addendum-2.md)** (items D–H, the owner's rulings). Read all three; the later document wins where they differ.

Repo `lean4-effect4`, Lean `v4.33.1`. **Worktree `/Users/pooks/Dev/lean4-effect4-slice6`, branch
`codex/slice6-fixes`**, made by the coordinator from `refactor/phase1-phase3` at the commit that
adds this brief. Nothing is pushed.

**The one thing first.** A five-seat design pass is running in the main checkout
(`/Users/pooks/Dev/lean4-effect4`). Do not build, write or run anything there. Work only in your
worktree. The pass may change items D and E below; it does not change items A–C.

**Goal.** Close the live host-handle hole, repair M6's finish line, and move each fiber's fork
record onto the machine. Each lands as its own commits with a receipt. The lift proofs and the
membership judgment follow as addenda once the pass is checked.

Plan of record:
- the [fork-ledger plan](2026-09-30-origin-ledger-and-step-invariants-plan.md) (third revision),
  §3 and §7;
- `docs/core/host-boundary.md` §§2, 3 and 5;
- the [host-answers note](2026-09-30-host-answers-and-typed-guarantee.md) §4;
- `docs/core/decisions.md` rows 91–97. The owner gave the go-ahead on 2026-09-30: "finish up slice
  six with the fixes".

## 0. Setup (done by the coordinator)

```bash
git -C /Users/pooks/Dev/lean4-effect4 worktree add /Users/pooks/Dev/lean4-effect4-slice6 -b codex/slice6-fixes refactor/phase1-phase3
cp -Rc /Users/pooks/Dev/lean4-effect4/.lake /Users/pooks/Dev/lean4-effect4-slice6/.lake
```

The second line clones the build cache (a copy-on-write copy on APFS), so the first `lake build`
rebuilds only what you change. If Lake rebuilds everything anyway, let it finish once and say so in
the receipt. The OCaml build directory is not copied; dune rebuilds it.

## 1. Rules this brief leans on

AGENTS.md applies in full. These rules matter most here:
- **Commits.** Commit by explicit paths, never `git add -A`. Never touch `README.md`. Receipts and
  evidence under `docs/research/` are force-added (`git add -f`), since the directory is
  gitignored.
- **Files that are not yours.** `docs/core/decisions.md`, `docs/STATE.md`, everything else under
  `docs/core/` and `docs/core/architecture-map.html` belong to the coordinator, who updates them at
  merge. Propose decision rows in your receipt. You may add lines to
  `Test/Counterexamples/REGISTER.md`.
- **Root imports** (`Test/All.lean`) are edited only at the anchors named below.
- **One Lake at a time** in your worktree. `-DwarningAsError=true` is on.
- **Proofs.** No `sorry`, `native_decide`, `partial`, `unsafe`, `axiom`, `extern` or
  `implemented_by`. The trust ceiling is `[propext, Quot.sound]`. A hand `simp` is `simp only
  [...]`. No `simp_all`, `first` or `try` written by hand under `src/`. Proof search in
  `Laws/**` is `aesop`, with the named banks.
- **OCaml only from LCNF.** After a change inside the engine's closure (check
  `ocaml/gen/closure-api_engine.tsv` for the name), regenerate in the fixed order:
  `LEAN_NUM_THREADS=1 make gen-derived gen-lcnf gen-eff gen-wire gen-cas`. The engine cut takes
  about 15 minutes. Then run `opam exec --switch=effect4 -- dune build` inside `ocaml/`, then
  `make check-ocaml`. Commit the regenerated files with the change that caused them.
- **Builds.** Build narrowly before each commit: `lake build <Module>` and its direct
  dependents, and `lake env lean <file>` for a test. `make check` runs once, at item C step 5.

## 2. Item A: host rows may not answer with internal handles (row 97 interim; `E4-HOST-CE-007`)

**The hole.** On the certified live session (start, bind, submit, apply), a host can answer a
row typed `fiberOf nat` with a live fiber that returns a string, and a program checked at `nat`
finishes with `"wrong"`. `Val.hasTy` checks a handle's kind only, and `mintedIn` checks only that
it exists. The witness is `docs/research/2026-09-30-host-answers-evidence/Probe.lean` §2
(`livePath`).

**Read.**
- `Program/Admission.lean:44-56` (`findIntInTable`, the existing located scan of row types) and
  `:85-130` (`AdmittedProgram`, `admitProgram`).
- `Program/Compile.lean:1350-1392` (`externalValue`, `prepareExternalAnswer`, `externalAdmits`).
- `Program/Typed.lean:12-18` (`internalHandleTargets`); `Api/HostSession.lean:129-136` (`start`
  calls `admitProgram`).
- `Laws/Program/Admit.lean:83-140, 404-470` and `Laws/Program/Handles/Hooks.lean:527-580` (the
  proofs that unfold `externalValue`).
- `docs/research/2026-09-30-host-answers-evidence/PathProbes.lean` path A (`mentionsInternal`,
  `hostRowOk`, the 15 in-tree rows).

**Change.**
1. **Table admission, the rule's letter.** Add `findInternalHandleInTable : RowTable → Option
   Path`. It scans each row's answer and error types, recursing through the constructors that
   contain types, as the probe's `mentionsInternal` does. It flags `fiberOf`, `refOf`,
   `deferredOf`, and `handle t` for `t ∈ internalHandleTargets` (scope and context are reserved
   spellings there). Add a located refusal to `AdmitRefusal`, and a certificate field on
   `AdmittedProgram` in the shape of `intFreeTable`. Check it in `admitProgram` right after the
   table's int scan. It is the same kind of profile rule as `int`.
2. **Reply values, closing every route.** A host reply carries no handle except a fresh external
   allocation.
   - **Success values.** `externalValue`'s non-allocation arm refuses any handle in the value
     (`(Store.Val.handles value).isEmpty`), not only external ones. `externalAdmits` already
     applies this condition to success values at registration.
   - **Typed failures.** The failure arms of `admitAnswer` (`Program/Admit.lean`) and
     `externalAdmits` require every `fail` payload to be handle-free. Today they check only
     `errAdmits`, with no liveness and no handle check.
   - **Why both.** Today a live internal handle passes wherever `Val.hasTy` accepts its kind,
     which includes a row that answers or fails at `unknown`. No honest row can answer with an
     internal handle once step 1 lands, so nothing legitimate is lost.
   - **Prove the guarantee.** An accepted reply carries no internal handle, and the allocation arm
     carries exactly the new external handle. Name the theorems to fit, e.g.
     `externalValue_internalFree`.
   - Repair `externalValue_typed`, `externalValue_minted` and their users.
3. **Counterexample and controls:** `Test/Counterexamples/Machine/Runtime/HostHandleForgery.lean`,
   imported in `Test/All.lean` after `import Test.Counterexamples.Machine.Runtime.LiveStack`.
   - The probe's program and table: `admitProgram` refuses the table at the located path, so
     `start` cannot open the session.
   - A row answering `unknown`, given a live fiber handle on the session: the reply is refused at
     `submit`/`preflight`, with the store unchanged. The same for a row whose error type is
     `unknown`, failing with a fiber handle in its payload.
   - Positive: all 15 in-tree host rows pass the table rule, and an honest allocation reply still
     allocates.
   - Add the register line `E4-HOST-CE-007`, REPAIRED, citing the original witness at the base
     commit.
4. **Regenerate** and run `make check-ocaml`. `externalValue` and `externalAdmits` are in the
   engine's closure; `admitProgram` and `admitAnswer` are not.

**Builds:**
- `lake build Effect4.Program.Admission Effect4.Program.Compile Effect4.Laws.Program.Admit
  Effect4.Laws.Program.Handles.Hooks`, then what breaks downstream;
- `lake env lean` on the new file and on `Test/Api/{HostSessionContract,KeyedHostContract,
  ExternalContract,AcquireHandleContract,PackagesContract,RunnerContract}.lean` and
  `Test/Program/{InvocationContract,HostSpecContract,LinkedRowsContract}.lean`.

**One commit:** "Refuse internal handles in host rows and host replies (E4-HOST-CE-007)".

## 3. Item B: M6 counts only runs with no host answer (row 95; `E4-SCHED-CE-015`)

**The defect.** `RReachable` (`Laws/Program/Typed/Assembly.lean:74-76`) takes every decision tape.
A `sleep` answered with `42` finishes with `42` at type `unit`, so the capstone
`typedState_reachable` is false (`docs/research/2026-09-30-origin-plan-review/Probe.lean`:
`sleeper`, `badTape`, `current_m6_capstone_false`). The reference machine has no
host table. At the empty table the runtime's check refuses every answer
(`emptyTable_refuses_every_answer`, `host-answers-evidence/Probe.lean` §1). So M6 covers exactly
the runs whose tape applies no host answer. Timers resume through `.advance`, not answers
(`Machine/Fibers.lean:452-480`), so the restricted scope still covers sleeps, forks, races and
interrupts.

**Change.**
1. **The predicate.** In `Assembly.lean`, define a predicate on `Api.Decision` that holds for
   every constructor except `answerAsync` (proof side only; no runtime file changes). Restate:
   `RReachable root fuel m := ∃ tape, (∀ d ∈ tape, <no host answer> d) ∧ m = (replayR
   root.program fuel tape).machine`.
2. **The rest of the statement.** `decision_preserves` keeps its `AnswerOk` premise; it is the
   typed layer the table-aware extension will use. The capstone's docstring says "every state a
   tape with no host answer reaches". The `#proof_wanted` list and the ceiling (20) do not change.
3. **The empty-table law.** Land `emptyTable_refuses_every_answer` as a law beside `admit`'s laws
   in `Laws/Program/Admit.lean`, from the probe's proof. It is the stated reason the scope is
   exact.
4. **Counterexample and controls:** `Test/Counterexamples/Machine/Semantics/M6Capstone.lean`,
   imported after `import Test.Counterexamples.Machine.Semantics.TrivialPosts`.
   - Keep the old definition locally as `ReviewedRReachable`, and prove
     `current_m6_capstone_false` against it.
   - The bad tape fails the new premise.
   - **Not vacuous:** a clock tape such as `Test/Program/ExitTypeLane.lean`'s `timers` tape
     finishes the `sleeper` with `.success .unit`. It satisfies the new `RReachable`: a theorem,
     plus a `#guard` on the exit.
   - Add the register line `E4-SCHED-CE-015`, REPAIRED.

**Builds:** `lake build Effect4.Laws.Program.Typed.Assembly Effect4.Laws.Program.Admit`, then what
breaks downstream; `lake env lean` the new file. No regeneration.

**One commit:** "Count M6 over tapes with no host answer (E4-SCHED-CE-015)".

## 4. Item C: the fork ledger, plan steps 3–5 (rows 91–92)

Read the plan's §2, §3 and §7 in full; this section only fixes the choices. `Origin` is
`Machine/Fibers.lean:228-231`, the field `:258`, `RunFiber.make`'s argument `:272`, and `spawn`
`:924-939`.

**Step 3, beside.**
- **The ledger.** `RunMachine` gains `forks : List ForkRecord` (child, parent, daemon, site),
  appended by `spawn` in the same place it emits `forked`. Roots get no record. Forks the runtime
  makes without a source point (finalizer forks `:969`, sourceless races `:1864`) record the empty
  site. Do not add the creating construct's kind; that waits on the registry (row 97's parked
  route).
- **The lookup.** `originOf : FiberId → Option Origin` answers `none` for no such fiber,
  `some .root` for a fiber with no record, and `some (.forked parent daemon site)` for one with a
  record.
- **Statements.** Prove the append statements (what `spawn` does to the list, for any machine).
  Prove the local lookup facts: after `spawn`, the new id finds the new record and every other id
  finds what it found before, given freshness.
- **The comparison runner,** `Test/Api/ForkLedgerRunner.lean`, imported after
  `import Test.Api.SupervisionContract`, modeled on `Test/Program/ExitTypeLane.lean`.
  - It replays each tape one decision at a time (`executePrefix` over `steppedBy`). At every
    decision boundary it compares, for every member fiber, the old field with the new lookup:
    child, parent, daemon flag and site.
  - Inputs: the typed corpus and the lane's tapes, plus fixtures for roots, ordinary forks,
    scoped forks with and without an ambient scope, `forkIn`, race entrants, finalizer forks, and
    several forks in one run.
  - **Control:** a wrong ledger (site dropped, daemon flipped, parent swapped) must fail it.
  - Its result is finite evidence at decision boundaries; report it that way.
- **No regeneration yet.** The engine catches up at step 5, and the branch is not merged before
  then.

**Step 4, readers move,** by the plan's §3 checklist:
- `statusOf` and `Inspection.forked`;
- in `Laws/Api/Supervision.lean`, the ten origin facts and three source connectors;
- `FMeans` and the `M1OriginFibers` obligations in `Simulation/Fibers.lean`;
- `Laws/Machine/{Book,Clauses}.lean`;
- `Laws/Program/Typed/ForkSource.lean`;
- the three `#guard`s in `Test/Api/SupervisionContract.lean:95-106`.

Every restated law is about member fibers of well-formed machines. `statusOf` reads any fiber
value it is handed, so a lookup by id agrees with it only there. If a reader outside the
checklist appears, stop (§6).

**Step 5, delete.**
- Delete `RunFiber.origin` and `RunFiber.make`'s `origin` argument.
- Retire the comparison runner in the same commit (it compares against the deleted field). Keep
  its last result, and the commit it ran at, in the receipt.
- Regenerate, then run `make check-ocaml` and `make check`.

**Commits:** one per step.

## 5. Items D and E: after the design pass (addenda)

- **D, the lifts and users 1–3 (rows 93–94).** The plan's step 6: the trace agreement
  (`M1Trace` 2 → 0), ledger well-formedness on reachable machines, and memo ids. The pass's lift
  seat reports a lift family that also covers M6. That report is not yet checked, so the
  addendum will say which statements to use.
- **E, the membership judgment (row 96).** One constructor-complete judgment over the actual value
  encoding. It comes from the pass's membership seat once that is checked.

The coordinator commits each addendum to `refactor/phase1-phase3` as
`docs/research/2026-09-30-codex-brief-slice6-addendum-<n>.md`. Read it at the main checkout's path
(read only), or merge that branch in when told; it touches documents only. Do not act on anything
under `docs/research/2026-09-30-pass/` before then.

## 6. Stop rules

Stop the item, record the smallest amendment in the receipt, and go on with the next item when:
- a checked counterexample refutes a statement this brief asks for;
- a test or in-tree row legitimately needs an internal handle in a host reply (item A step 2 then
  needs a decision);
- the ledger needs a reader outside the checklist, or a site other than `spawn` creates a fork;
- regeneration changes files outside the four LCNF outputs and the eff, wire and cas groups;
- a proof needs a runtime tag the machine does not carry (rows 44–45 refuse that).

## 7. Receipt

`docs/research/2026-09-30-seat-codex-slice6-receipt.md`, force-added. It opens with the one thing
the coordinator must know before merging. Then:
- base and head commits, and per commit the changed files;
- exact commands and results, and the axiom output of each new theorem;
- the runner's counts and its failing control;
- what is finite evidence and what is proved;
- open obligations;
- proposed decision rows and register lines;
- anything the stop rules triggered.
