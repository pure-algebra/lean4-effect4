# Plan: fork records on the machine, and the lifts for facts every step keeps

Status: **proposed; third revision, 2026-09-30. The ledger part is written to be ratified as it
stands.** Amended the same day after the design pass: three internal fork kinds (§3); the
lifts are proved generically, but the §10 withdrawal of the M6 claim stands (synthesis K1). The
runtime steps are in Codex's hands (brief and addendum 1). Base `be15b062` on `refactor/phase1-phase3`. Nothing is implemented.

This revision folds in two reviews of the second draft, as the owner asked: the
[plan review](2026-09-30-origin-plan-review.md) and its
[ratification conditions](2026-09-30-origin-plan-review/RemediationReview.md). Those reviews
also found that M6's finish line is stated wrong and that the typed API and the runtime's reply
check have gaps. That is a separate track, in
[host answers and the typed guarantee](2026-09-30-host-answers-and-typed-guarantee.md). This
plan no longer claims anything about M6. §10 records what each round changed and what was
withdrawn.

## 1. What this is for

The last slice 6 item is the trace agreement (`step_agrees`, `reachable_agrees`,
`Laws/Api/TraceOrigin.lean`, gate `TraceFacts.M1Trace` ceiling 2): the event log's `forked`
entries and the fibers' origins say the same thing on every reachable machine. Slice 6's other
three items are landed (`40e3bfa3`, `be15b062`). The synthesis places this among the residue
proofs that go beside the foundations slices, not on the path to M6
(`docs/core/post-phase-c-synthesis.md` §F6, §7).

The owner chose on 2026-09-30 to make the agreement hold by construction (route B) and to build
a reusable proof tool. In this plan the reusable part is the three general theorems that carry a
fact through the command loop, one decision and a whole run, and the shared lemma bank; three
proofs use them by hand. A command that writes the per-function statements is built only if
those three show it pays, which is the owner's rule that an instrument is built the second time.

## 2. What we measured (base `be15b062`)

- The `forked` event is built in one function, `spawn` (`Machine/Fibers.lean:924-939`)
  (`#write_census Effect4.Program.steppedBy closure over Effect4.Program.NativeMachine`).
- The census lists 25 functions that rebuild fiber records. A `{ f with … }` copy keeps
  `origin` unchanged; the census reports every field of a rebuilt record because it is called
  without a source record (`Laws/Auto/Positions.lean:253-260`). The real cost of proving
  agreement as the code stands is the read, change, write-back cycle: each handler reads a
  fiber, changes it and writes it back with `update`, so every write needs "what was written
  back is what was read" (the premise pair on `guardState_update`,
  `Laws/Program/Guard/Core.lean:1479-1485`), carried through the guard's 13,851 lines.
- The census omits the machine record itself. Owners come from positions (`Positions.lean:355`),
  and `RunMachine` has no field of a carrier type. Taking owners also from the types the walk
  entered fixes the omission; it does not fix the over-reporting above.
- Readers of `RunFiber.origin`. In the runtime: `statusOf`'s last arm
  (`Api/Supervision.lean:215-227`) and `Inspection.forked` (`:268-273`). In the laws: the origin
  facts of `Laws/Api/Supervision.lean` (`originEntries_emit`, `originEntries_updateRace`,
  `spawn_origins`, `start_origins`, `launchEntrant_origins`, `fork_origins`, `forkIn_origins`,
  `forkScoped_origins`, `forkScoped_none_origins`, `supervision_static_origins`, the three
  `source_*_holds`), `FMeans` and the fiber relation in `Laws/Program/Simulation/Fibers.lean`,
  `Laws/Machine/{Book,Clauses}.lean`, `Laws/Program/Typed/ForkSource.lean`, and three `#guard`s
  in `Test/Api/SupervisionContract.lean` (`:95-106`). The generated OCaml carries the field
  (`ocaml/gen/{fibers,machine,api}_gen.ml`, `ocaml/engine/api_engine.ml`). No frozen contract
  packet mentions it. (`Codegen/Bindings.lean`'s `Origin` is a different type.)
- `emit` is the only trace writer (`Fibers.lean:630`). Of its 34 call sites outside the laws,
  31 pass a literal list and 3 map frame events (`Fibers.lean:1180`, `:1193`,
  `Program/Compile.lean:1623`). Roots are made by `Api.load`, `runFork` and `runCallback`, with
  no event. Nothing removes a fiber.
- The decision runner edits the machine outside the command loop: dispatcher draining and
  disarming (`Fibers.lean:2015-2016`), `clockStep` (`:2045-2048`), `prepareAnswer`
  (`:2096-2097`), `installMiddleware` (`:2108`). The plan review's probe shows
  `installMiddleware` changes the loaded machine with zero command fuel.
- Counts: `driveStep` has 18 command arms and `evaluatePrim.withFiber` 24 action arms. The
  dynamic lane (`Test/Program/ExitTypeLane.lean`, 34,336 runs) checks each run's final root exit
  (`:49-52`); it does not look at intermediate machines.

## 3. The fork ledger (runtime)

**What changes.** `RunMachine` gains one append-only list, `forks`: one record per forked fiber,
with child id, parent id, daemon flag and site. Roots get no record. `RunFiber.origin` and
`RunFiber.make`'s `origin` argument go.

**The site is kept exactly: the ledger has a second user.** The external lane needs a
trustworthy declared type for every fiber handle a host might return
([external runtime contract](2026-09-30-external-runtime-contract.md) §3). For a source fork
that type can be derived from this ledger's site and the checker, with no type stored in any
value. A probe types the fork's body at its recorded site: `string` for a forged fiber, `nat`
for an honest one ([path probes](2026-09-30-host-answers-evidence/PathProbes.lean), path B).

Forks the runtime makes without a source point record the empty site: finalizer forks
(`Machine/Fibers.lean:969`) and races without a source site (`:1864`). The design pass found a third internal
kind: a `merge`/`mergeAll` layer build forks through the `fork` arm with the layer's own path
(`Program/Compile.lean:1453-1455`), so its site names a layer node, not a fork action
([synthesis](2026-09-30-pass/synthesis.md) K4). If the registry is
ratified, the record also carries the creating construct's kind, so those fibers have a
declaration too. This is a proposed refinement of decision 1, not part of the slice as written.

**Forks only.** All three reviews agree. A ledger of every fiber's birth would add three root
writers and a second list of which fibers exist, with its own agreement to prove, for no
benefit to the users here.

**The paired write.** `spawn` is already the one place that creates a forked fiber and emits the
`forked` event; it appends the record in the same place. A small helper that does both
(`RunMachine.fork`) is optional, a convenience for reusing its proof; extracting it is not a new
guarantee. The list law it needs is already checked: appending the same record to two lists
keeps them equal, and keeps them unequal if they were (`pairedAppend_keeps_agreement` in the
review's probe, a `Keeps` of a proposition, with no Boolean wrapper).

**The requirement, stated narrowly.** Ordinary updates to a fiber must not be able to change the
record of where it came from. Keeping that record off the fiber meets it here. This is not a rule
for every future data layout.

**Why not a write-once `update`.** Making `update` keep the stored origin would change what
`m.update f` holds at `f.id`: every lemma that reads a fiber back after an update
(`fiber?_update_self`, `fiber_lookup_update`, the book's `book_update`, the guard's
`guardState_update`) would gain a side condition. A separate list is touched only by `spawn`;
`update`, `modify` and every fiber copy cannot reach it.

**The lookup contract, written before any reader moves.**

`m.originOf id : Option Origin` answers `none` when no fiber has that id, `some .root` for a fiber
with no fork record, and `some (.forked parent daemon site)` for a fiber with one. "No such
fiber" and "a root" are different answers.

Four facts make the lookup mean what the fiber field meant:

1. **Unique:** no two records name the same child.
2. **Bounded:** every record's child and every fiber's id is below the allocation counter `nextId`.
3. **Corresponding:** every record names a fiber of the machine, and fiber ids are distinct.
4. **Fresh at creation:** the id `spawn` allocates is not yet a fiber and has no record.

"The counter only goes up" is why these hold, not a proof of them. The proof has to show that
every site that allocates an id (`spawn`, `runFork`, `runCallback`, `Api.load`) takes the
counter and bumps it, and that nothing else creates a fiber or a record.

Two kinds of statement are kept apart. **Append statements** say what `spawn` does to the list;
they hold for any machine, as today's `spawn_origins` does
(`Laws/Api/Supervision.lean:760-807`). **Lookup statements** say what `originOf` answers; they
take the four facts as premises. The local lookup facts (after `spawn`, the new id finds the new
record and every other id finds what it found before, given freshness) are proved before any
reader moves. The whole-run proof of the four facts is user 2 in §5 and can land after the
migration.

**Compared only where it can agree.** `statusOf` takes any fiber value it is handed and reads that
value's own origin (`Api/Supervision.lean:215`). A lookup by id can agree with it only for fibers
that belong to a well-formed machine. So every before/after comparison and every restated law is
about member fibers of well-formed machines, and of reachable ones for the proofs.

**The comparison runner (new code).** The lane does not do this, so it is written. A Lean runner
replays each tape one decision at a time (`executePrefix` over `steppedBy`) and, at every
decision boundary, compares for every member fiber the old field with the new lookup: child,
parent, daemon flag and site.
- **The site matters.** The trace agreement compares only parent, child and flag, because the
  event carries no site, so a passing trace check cannot stand in for the site check.
- **Inputs:** the corpus and the lane's programs, plus fixtures that cover roots, ordinary
  forks, scoped forks with and without an ambient scope, `forkIn`, race entrants, finalizer
  forks, and several forks in one run.
- **A control:** a deliberately wrong ledger (site dropped, daemon flag flipped, parent swapped)
  must make the runner fail.
- **Scope of the evidence:** the runner observes decision boundaries, not every command, and
  says so with its result. It is finite evidence and is reported as such.

**Slices (build beside, move, delete).**

1. Write the ledger, lookup and append statements down (no implementation).
2. **Beside.** Add `forks`, written by `spawn`, next to the fiber field; the comparison runner;
   the local lookup facts.
3. **Readers move**, by this checklist: `statusOf` and `Inspection.forked`; in
   `Laws/Api/Supervision.lean` the ten origin facts and three source connectors; `FMeans` and the
   `M1OriginFibers` obligations in `Simulation/Fibers.lean`; `BookMeans`/`FiberMeans` in
   `Book.lean` and `Clauses.lean`; the source-path connectors in `Typed/ForkSource.lean`; the
   three `#guard`s in `Test/Api/SupervisionContract.lean`.
4. **Delete** `RunFiber.origin`. Regenerate in order (derived → lcnf → eff → wire → cas,
   `LEAN_NUM_THREADS=1`); OCaml build; the differential (`make check-ocaml`); `make check`. All
   of this before integration: runtime commits before this one stay on the branch until the
   regenerated engine catches up, because `make check` does not regenerate the LCNF output
   (`docs/GENERATED.md:76`).

**What the switch rests on:** the census (`spawn` writes both records and nothing else writes
either), the local lookup facts, and the runner. That is bounded evidence, not a theorem that the
old field and the new lookup agree on every reachable machine, and the final write-up says so.

## 4. The lifts: what is reusable now

**Scope.** Facts about the machine alone, on the native machine's `steppedBy`. M6 is not in
scope:
- its per-command statement also keeps the pending commands typed (`QueueOk`,
  `Typed/Assembly.lean:86-97`);
- its decision statement needs an answer condition (`AnswerOk`, `:218-222`);
- it runs on the reference machine;
- its capstone is being repaired (host-answers note §4).

M6's own lift is designed after that repair and may reuse leaf facts from here; nothing here
claims the procedure carries over.

**Three steps, kept distinct.**

1. **The command loop:** from "every command keeps the fact" to `driveState`, by induction on
   fuel.
2. **One decision:** from step 1 plus one fact for each edit the decision makes outside the loop
   (dispatcher draining and disarming, `clockStep`, `prepareAnswer`, `installMiddleware`; §2).
3. **A whole run:** from step 2, by induction over the history in `Guard.Reachable`.

**Statement shapes.** The step functions return different things: `driveStep` a machine and
commands, `evaluatePrim.withFiber` a five-field `Iter`, `spawn` a machine, a fiber and an id; the
decision steps take fuel twice. The per-function statement for each shape is written by hand
first and checked on a fixture. A function whose result holds no machine is left out on purpose,
a shape that is not supported is refused by name, and the fixture tells the two apart.

**The bank** `Effect4.StepInv` holds the base facts: `update`, `modify`, `emit`, `updateRace`,
`halt`, the paired append, "a frame map carries no fork", and the writes that touch only the
store. Rules that create metavariables stay out of it.

**Hooks.** For the ledger and the trace every writer is machine code. The store is written
through interpreter hooks (`syncState`, `dueResumes`, `wakeList`, `clockStep`, `prepareAnswer`
and the scope operations; 14 `state :=` sites in `Fibers.lean`, 15 in `Scope.lean`). So a store
fact is stated at the native interpreter (`interpOf program table`), with one fact per hook.
`syncOpStep_memoIdsOk` covers the store operations only; the other hooks need their own.

**The census** gets the owner fix of §2 and stays a guide to where the work is, not evidence that
a fact holds.

## 5. Three users, by hand first

1. **Trace agreement.** Every step keeps the proposition `forkedOf m.trace = forkLedger m`, where
   `forkLedger` lists the ledger's records in the shape `forkedOf` returns:
   - `spawn` appends the same entry to both sides (the paired-append law);
   - an `emit` with no fork event keeps the trace side (31 literal sites directly, the three frame
     maps by one lemma);
   - every other write keeps both sides unchanged.

   With `load` this gives `step_agrees` and `reachable_agrees`, and `M1Trace` goes from 2 to 0.
   The agreement stays a proof obligation; it is not retired.
2. **Ledger well-formedness.** The four lookup facts on every reachable machine. This one needs
   its premise (a counter bump can make a bound true that was false), so it is a kept-true fact,
   not an unchanged value.
3. **Memo ids.** `Stores.MemoIdsOk m.state` on every reachable machine (`reachable_memoIdsOk`).
   This closes a gap `be15b062` left: the synthesis (§7) asked the memo cleanup to carry its
   invariant through the machine paths or say which it covers, and that commit did neither. This
   proof covers the native path; the reference path is named as not covered unless the same lift
   is instantiated there.

**The trial** (step 2 in §7). The per-function fact is written by hand, with the bank, for:
- `spawn`, `settle`, `evaluatePrim.withFiber` and three `driveStep` arms;
- for the store user, one store-writing command (the `sync` arm, `Fibers.lean:1140`);
- one outer decision hook (`clockStep` or `prepareAnswer`).

For each user, record what search closed.

**Automation.** Decided after users 1–3 are written. Build the command only if the hand lists
are long (user 1's arm counts put it near sixty statements) and search closed most of them;
otherwise the hand lists land against the same lifts and bank. If it is built, adding checked
theorems to the environment is acceptable: `ProofGraph.addTheorem` checks the declaration in
Lean's kernel (`tools/ProofGraph/Search.lean:128-141`) and the axiom gate walks the environment.
Printing statements to paste is a review preference, not a trust repair.

## 6. `forkedOf` moves to `Test/` (R79.2)

After user 1, `forkedOf` and `Agrees` leave the library for `Test/`, as the control that the
diagnostic log tells the truth about forks. That touches more than `TraceOrigin.lean`:
- the trace laws and obligation declarations in `Laws/Api/Supervision.lean:255-544`;
- their proof references at `:1281-1284`;
- the gate at `:1297`.

Step 8 lists each declaration as moved or restated against the ledger. `Test/` depends on the
library, never the reverse.

## 7. Order and commits

| Step | What | Gate |
| --- | --- | --- |
| 1 | the ledger, lookup and append statements, written down | none (this note) |
| 2 | the trial: seven functions and one outer hook by hand; findings recorded here | none |
| 3 | the ledger beside the fiber field; the comparison runner; the local lookup facts | narrow build; the runner and its failing control |
| 4 | readers move (§3 checklist) | narrow build of the touched laws |
| 5 | `RunFiber.origin` deleted; regenerated; OCaml differential | `make check`, `make check-ocaml`, before integration |
| 6 | lifts and bank; users 1–3 by hand | ledger gates (`M1Trace` 2 → 0) |
| 7 | the automation decision (§5) | none |
| 8 | `forkedOf` to `Test/` (§6); landing note; decisions rows 20 and 79 and R3; STATE; `make gen-architecture` | `make check` |

Each step is its own commit by explicit paths. Nothing is pushed.

## 8. Where this sits

- **Slice 6, last item.** The codex packet lists slice 6 as the five source-site connectors,
  `step_agrees`/`reachable_agrees`, `observe_replace_trace` and the memo cleanup
  (`docs/research/2026-09-21-codex-packet-divergence-and-slice-5.md` §4). The other three are
  landed; this plan is the fourth.
- **Residue, not the critical path.** The synthesis says not to block the protocol design on a
  diagnostic proof (§7).
- **What it feeds.** H (M6) gets leaf facts and what the trial teaches about search; H's own lift
  waits on the M6 statement repair.
- **What it does not touch.** No protocol, no run premise, no machine change beyond the ledger.
  `docs/core/decisions.md` is edited only at step 8, by the coordinator.

## 9. Decisions for the owner

1. **Forks only** (all three reviews; recommended).
2. **The reader switch rests on bounded evidence**: the census, the local lookup facts and the
   runner, stated as such. The whole-run proof of the lookup facts follows as user 2.
   Recommended.
3. **The trace agreement stays a proof obligation**; `forkedOf` moves to `Test/` as its control
   after it is proved. Recommended.
4. **Automation is decided after users 1–3**, by the rule in §5; if built, it may add checked
   theorems. Recommended.
5. **At step 8 the coordinator rewrites decisions rows 20 and 79 and R3** (the 2026-09-20
   packet's one-field origin ruling). The record moves from the fiber to the machine. R3's
   principle, that it is not a second representation of a fact the machine holds, still holds.

## 10. Review record

- **First draft** (coordinator, 2026-09-30).
- **Second draft**, revised the same day against the tree:
  - corrected the reason route A is expensive and the arm counts;
  - added the census owner fix, the paired-write helper, the reader checklist, the signature
    convention, the hook treatment and the stop rule.
- **Coordinator review of the second draft:** M6's per-command statement also keeps pending
  commands typed, and M6 runs on the reference machine.
- **[Plan review](2026-09-30-origin-plan-review.md):**
  - the M6 capstone is false as written (checked counterexample);
  - the helper does not cover M6 (queue, answer admission, reference machine);
  - the decision's edits outside the loop;
  - the lookup contract;
  - the migration test must be built;
  - the signature convention and census precision;
  - the full extent of the `forkedOf` move.
- **[Ratification conditions](2026-09-30-origin-plan-review/RemediationReview.md):**
  - the four lookup facts and the missing-id answer;
  - comparisons restricted to member fibers of well-formed machines;
  - local lookup facts before readers move;
  - append statements kept apart;
  - three M6/API amendments, now in the host-answers note.

**Withdrawn in this revision:**
- the world-indexed helper shape and every claim that the tool covers M6;
- the claim that writing the indexed lift now "costs nothing", which was never measured;
- the blanket design rule;
- the Boolean wrapper around the agreement;
- the hook name `stepTimer` (the runner calls `clockStep` and `prepareAnswer`);
- the reading that the 34,336-run lane already checks intermediate machines;
- the second draft's decision 6 (retire the agreement) and decision 7 (build the command now).
