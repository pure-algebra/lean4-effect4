# Plan: fork records on the machine, and one tool for facts every step keeps

Status: **proposed, for owner review.** Nothing below is implemented. Base `be15b062` on
`refactor/phase1-phase3`. Revised 2026-09-30 after the coordinator's review of the first draft
against the tree; §9 places the plan in the development plan and §10 records what the review
verified and changed.

## 1. What this is for

The last slice 6 item is the trace agreement (`step_agrees`, `reachable_agrees`,
`Laws/Api/TraceOrigin.lean`, gate `TraceFacts.M1Trace` ceiling 2): the event log's `forked`
entries and the fibers' origin labels say the same thing on every reachable machine. Slice 6's
other three items are landed: the five source-site connectors and the observation erasure
(`40e3bfa3`), the memo write-back deletion (`be15b062`). The owner chose route B on 2026-09-30:
make the agreement hold by construction instead of chasing fiber copies through the whole
machine, and build the proof tool so the next invariant (M6) can reuse it.

The synthesis lists this item as F6's second claim and as residue that proceeds beside the
foundations slices, with the touched laws and direct controls as its required builds
(`docs/core/post-phase-c-synthesis.md` §F6, §7). It is not on the path to M6.

## 2. What we measured (2026-09-30, base `be15b062`)

- `#write_census Effect4.Program.steppedBy closure over Effect4.Program.NativeMachine`:
  the `forked` event is built in **one** function, `spawn` (`Machine/Fibers.lean:924-939`).
  **25** functions build fiber copies (`settle`, `driveStep`, `evaluatePrim`, `fireObserver`,
  `linkScope`, `start`, `countOp`, …).
- **What the 25 mean, corrected.** A `{ f with … }` copy keeps `origin` by `rfl`. The census
  lists every field of every copy as a potential write because `#write_census` calls
  `writeSites` without a source record (`Laws/Auto/Positions.lean:233-257,378`; synthesis §F7
  says the same). The cost of proving agreement as the code stands is not 25 hard lemmas; it is
  the read, transform, write-back cycle: every handler reads a fiber at an id, changes it, and
  writes it back with `update`, so the invariant needs "what was written is what was read" at
  every site. That is the hypothesis pair on `guardState_update`
  (`Laws/Program/Guard/Core.lean:1479-1485`, `hf : m.fiber? f.id = some f`, `hid : g.id = f.id`),
  threaded through the guard's 13,851 lines.
- The census lists **no** writes to the `RunMachine` record itself (0 rows; 63 for `RunFiber`,
  33 for `RunEvent`). The reason is precise: `ownersOf` (`Positions.lean:355`) takes the owners
  from the positions, and a position's owner is a type with a carrier-typed field of its own.
  `RunMachine` has none, so it is never an owner. The walk already records every type it
  entered as an edge (`walkOf`); the fix is to take owners from the edges' children as well.
- Readers of `RunFiber.origin`, verified: in the runtime, `statusOf`'s last arm
  (`Api/Supervision.lean:215-227`), which only asks whether the fiber was forked at all, and
  `Inspection.forked` (`:268-273`), which reads parent and daemon flag but not the site.
  In the laws, the origin facts of `Laws/Api/Supervision.lean` (`originEntries_emit`,
  `originEntries_updateRace`, `spawn_origins`, `start_origins`, `launchEntrant_origins`,
  `fork_origins`, `forkIn_origins`, `forkScoped_origins`, `forkScoped_none_origins`,
  `supervision_static_origins`, the three `source_*_holds`), `FMeans.origin` and the fiber
  relation in `Laws/Program/Simulation/Fibers.lean` (30 mentions), `Laws/Machine/{Book,Clauses}`,
  `Laws/Program/Typed/ForkSource.lean`, and three `#guard`s in `Test/Api/SupervisionContract.lean`
  (`:95-106`). The generated OCaml carries the field (`ocaml/gen/{fibers,machine,api}_gen.ml`,
  `ocaml/engine/api_engine.ml`). No frozen contract packet mentions it.
  (`Codegen/Bindings.lean`'s `Origin` is a different type.)
- Other facts the plan rests on, verified: `emit` is the only trace writer (`Fibers.lean:630`);
  of its 34 call sites outside the laws, 31 pass a literal list and 3 pass `events.map
  (RunEvent.frame …)` (`Fibers.lean:1180`, `:1193`, `Program/Compile.lean:1623`). Roots are made
  by `Api.load`, `runFork` and `runCallback` with no event. Nothing removes a fiber
  (`fiberStatuses`' docstring, `Api/Supervision.lean:229`; no `fibers :=` write filters).
  The gate's scope holds three obligations (`load_agrees` in `Supervision.lean:1005` plus the
  two above); ceiling 2 is the two `#proof_wanted`.

| Count the first draft quoted | Draft | Tree |
| --- | --- | --- |
| `driveStep` command arms | 20 | 18 |
| `evaluatePrim.withFiber` action arms | ~40 | 24 |
| Guard proof lines | 13,851 | 13,851 |
| Dynamic lane runs (`Test/Program/ExitTypeLane.lean`) | 34,336 | 34,336 |

## 3. Part 1: the fork records move from the fiber to the machine (runtime)

**The rule this applies.** A fact fixed at creation must not live on a record that handlers
read, transform and write back. It lives in an append-only ledger on the machine, keyed by id,
that only creation writes. Today `origin` is the only such fiber field besides `id`; the rule
decides where every later creation-time fact goes.

**The change.** `RunMachine` gains one append-only list: one record per fiber the ledger
covers (child id, parent id, daemon flag, site). `RunFiber.origin` and `RunFiber.make`'s
`origin` argument go. `m.originOf id` answers the old `f.origin`, with `Origin` kept as the
answer type.

**One primitive for the double write.** `RunMachine.fork m rec` appends the ledger record and
emits `RunEvent.forked rec.parent rec.child rec.daemon` in one definition; `spawn` calls it and
nothing else constructs the `forked` event (the census over `RunEvent` checks that: one site).
The event keeps its shape. Then the bank for part 3 is six facts, and "an emit carries no fork"
is a literal check at 31 sites and one lemma about `map frame` at the other three.

**Forks or births (decision 1).** Two shapes:

- *Forks only.* One record per forked fiber; a fiber with no record is a root. Matches what
  the log carries; `load`, `runFork` and `runCallback` write nothing.
- *Births.* One record per fiber, roots included, with its origin. Root is then a positive
  record rather than a failed lookup, which proofs handle better; any later creation-time fact
  lands in the same ledger; and "every fiber has a birth" (`m.fibers.map (·.id) =
  m.births.map (·.id)`) is a plain `Keeps` fact. Cost: one append in `Api.load`
  (`Api.lean:255-260`), `runFork` and `runCallback` (`Fibers.lean:2180-2199`), and the
  agreement filters the ledger down to forks.

The first draft recommended forks only; the review leans to births, mildly, for the reasons
above. The owner decides.

**Why the machine and not a write-once `update`.** Making `update` keep the stored origin would
change what `m.update f` holds at `f.id`: every lemma that reads a fiber back after an update
(`fiber?_update_self`, `fiber_lookup_update`, the book's `book_update`, the guard's
`guardState_update`) would gain a side condition. A separate list is touched only by `fork`;
`update`, `modify` and every fiber copy cannot reach it, and none of those lemmas change.

**The simulation gets simpler, not bigger.** Today the book and the simulation relate origins
fiber by fiber (`FMeans` carries `f₁.origin = f₂.origin`). After the move they relate one
machine field: `BookMeans` gains a ledger conjunct and `FMeans` loses the origin one.

**Slices (build in parallel, slot in, delete):**

1. **Beside.** Add the ledger, written by `fork`; nothing reads it yet. Finite check, on the
   Lean side (the OCaml engine is not regenerated until slice 3): over the dynamic lane's runs
   (`Test/Program/ExitTypeLane.lean`, 34,336) and the corpus, the ledger equals the list the
   fibers' labels give, at every step. This is a finite probe and is reported as one.
2. **Readers move.** `statusOf`, `Inspection.forked` and the laws read `m.originOf`. The
   checklist is the reader list in §2: the ten origin facts and three source connectors in
   `Laws/Api/Supervision.lean`, the `FMeans` field and `M1OriginFibers` obligations in
   `Simulation/Fibers.lean`, `BookMeans`/`FiberMeans` in `Book.lean` and `Clauses.lean`,
   `Typed/ForkSource.lean`, the three `#guard`s in `Test/Api/SupervisionContract.lean`.
3. **Delete** `RunFiber.origin`. Regenerate in the fixed order (derived → lcnf → eff → wire → cas,
   `LEAN_NUM_THREADS=1`); OCaml build, the differential (`make check-ocaml`), `make check`.

What justifies the reader switch is the census (`fork` is the only writer of either record) and
the finite check in slice 1, **not a theorem**. After slice 3 there is no second copy to
disagree, and part 3 proves the remaining agreement (event log vs ledger).

## 4. Part 2: the tool — facts every step keeps

**One shape, in the form M6 needs.** M6's frozen schematic statement is world-indexed with a
transport between worlds (`docs/core/post-phase-c-synthesis.md` §H):
`TypedState root w m → LegalDecision … d → ∃ w', Transport w w' ∧ TypedState root w' (step …)`.
So the shape the lift is written for is the indexed one:

```
Carries R I F := ∀ w m, I w m → ∃ w', R w w' ∧ I w' (F m)
```

with `Preserves I F := ∀ m, I m → I (F m)` the case `w := Unit`, and `Keeps proj F`
(`Laws/Machine/Keeps.lean`, slice 5) giving `Preserves (fun m => proj m = c) F` in one line.
The lifts need `R` reflexive and transitive, which the world-weakening laws declare (`M3bWorld`).
Chaining forward through a composite is what automated search does well; there is no
before/after relation on the machine, only on the world index. Writing the lift in the indexed
form now costs nothing; retrofitting it for H would cost the lift again.

**What the shape covers, and what it does not.** State-only invariants whose writers are
machine code (the fork ledger) or interp hooks with a bank fact each (the store). It does not
cover the guard's shape: `DriverContract` (`Laws/Program/Guard/Contract.lean:9`) carries
`GuardState m` jointly with two predicates on the pending command list. H's statement is
state-only with a decision premise, so H is in scope; a future invariant over pending
commands is not, and the plan does not claim it.

**The signature convention.** The step functions are not `RunMachine → RunMachine`.
`driveStep` returns a machine and commands; `evaluatePrim.withFiber` returns a five-field
`Iter`; `spawn` returns a machine, a fiber and an id; the decision steps take fuel twice.
For each function the command derives the proposition "for every argument of the machine type
and every machine-typed component of the result, the invariant carries", quantifying the other
arguments. The positions walk finds the machine type in an argument or result type; a function
with no machine in its result is skipped, one with two machine arguments is refused by name.
This convention is written down and checked on a fixture before the command exists.

**Hooks.** For the fork ledger every writer is machine code, so its obligations are generic in
the interp. The store is written through `interp.syncState`, `dueResumes`, `wakeList`,
`stepTimer` and the scope module (14 `state :=` sites in `Fibers.lean`, 15 in `Scope.lean`).
Those hooks are parameters of the generic machine, so a store invariant is stated at the native
instantiation (`interpOf program table`), and the census treats a hook call as a write to
`state` attributed to the hook, whose fact comes from the bank (`syncOpStep_memoIdsOk` is one;
`dueResumes`, `wakeList`, `stepTimer` and the scope operations need theirs).

**Four pieces, in `src/Effect4/Laws/Machine/StepInvariant.lean` (Laws graph only):**

1. **The census, extended.** Owners are the root plus every type the walk entered, so
   `#write_census` reports writes to the root record and `#read_census I` lists which step
   functions write the fields an invariant reads. A function that writes none of them keeps
   it by the `Keeps` ladder; only the writers are real obligations.
2. **The lift, written once.** Three hand-written theorems, generic in `R` and `I`: through the
   command loop (`driveState`, fuel induction), through one decision (`steppedBy`, per decision
   kind, as `Guard/Decision.lean:11` does for `GuardState`), and over a history from `load`
   (`Guard.Reachable`, `executePrefix` induction as `guardState_executePrefix` does). Their only
   premise is the invariant at load and `Carries` for the per-command step and for each decision
   step's direct edits.
3. **The command, if the stop rule says so.** `#step_invariant I from Effect4.Program.steppedBy
   using aesop (rule_sets := [X])` walks the step functions callee-first. For each one it states
   the obligation by the convention above, tries it by the function's own case list
   (`fun_cases`/`fun_induction`) and aesop with the bank plus every lemma already closed, and
   lists what is left by name. Its first version **prints** the statements and proof calls as
   text to paste: a printed theorem that fails is a visible error in a file, and printed text is
   what a reviewer reads. Adding theorems to the environment, kernel-checked as `#frame_rules`
   and the obligation gate do through `ProofGraph.addTheorem`
   (`tools/ProofGraph/Search.lean:128`, audited by the axiom gate, which walks the environment),
   is the upgrade when reruns become routine.
4. **The banks.** `Effect4.StepInv`: the base facts (`fork`, `update`, `modify`, `emit`,
   `updateRace`, `halt`, state-only writes, `map frame` carries no fork). The fold-and-guard
   rules stay in their own banks; no rule that creates metavariables goes in a bank.

**The risk, measured first (step 0).** Before writing anything but the lifts, prove the
per-function fact by hand, with the bank, for seven functions: `spawn`, `settle`,
`evaluatePrim.withFiber`, three `driveStep` arms, and one hook-writing function for the store
user (the `sync` arm, `Fibers.lean:1140`, or `drainDue`). Record how much search closed for
each user. The stop rule for the command: build it only if the hand-written list for the fork
ledger is long (the arm counts in §2 bound it near sixty statements) and search closed most of
it; otherwise land the hand list against the same lift and bank, report that, and revisit at H.
This is the owner's rule that the instrument is built the second time.

## 5. Part 3: the trace agreement is the first user

The agreement is a `Keeps`, not a `Preserves`. Take the Boolean projection
`gap m := (forkedOf m.trace == forkLedger m)`, where `forkLedger` lists the ledger's forks in
the shape `forkedOf` returns. Every primitive keeps `gap` unconditionally:

- `fork` appends the same record to both sides, and `a ++ [x] == b ++ [x]` is `a == b`;
- `emit es` with `forkedOf es = []` keeps the trace side (31 literal sites by `rfl`; the three
  `map frame` sites by one lemma);
- `update`, `modify`, `updateRace`, `halt` and every `{ m with fibers/races/state/… }` keep
  both fields by `rfl`.

So user 1 threads no hypothesis: the existing ladder, `Keeps.comp` and the lifts of part 2
compose it, and `gap (Api.load …) = true` gives `Agrees` on every reachable machine.
`step_agrees` and `reachable_agrees` follow, and `TraceFacts.M1Trace` goes from 2 to 0.

Then R79.2: `forkedOf` and `Agrees` leave the library and become the control in `Test/`: the
theorem that the diagnostic log tells the truth about forks.

## 6. Part 4: the second user proves the tool is reusable

`Stores.MemoIdsOk m.state` on every reachable machine (`reachable_memoIdsOk`). Today it is proved
for each store operation (`syncOpStep_memoIdsOk`, `Laws/Machine/StoresLaws.lean:1437`) but not
carried through the machine. The memo deletion (`be15b062`) relied on the store operation being
the only writer of the memo map. This is a genuine `Preserves`: a name bump can turn a violating
state into a satisfying one, so no `Keeps` covers it. It closes the gap with the same lift and a
bank with one fact per hook, at the native instantiation, and gives an honest measure of how far
the tool reaches for a store-shaped invariant, which is what H needs.

## 7. Order and commits

| Step | What | Gate |
| --- | --- | --- |
| 0 | spike: the lifts, and the hand-written fact for seven functions across both users; the findings recorded in this note | none (no commit but the note) |
| 1 | the ledger and `fork` beside the fiber field; finite comparison check on the Lean side | narrow build, the lane |
| 2 | readers move, by the §3 checklist | narrow build of the touched laws |
| 3 | delete `RunFiber.origin`; regenerate; OCaml differential | `make check`, `make check-ocaml` |
| 4a | census owners extended; lift; bank; the hand-written list for user 1 | `lake build` of the tool and a fixture under `Test/` |
| 4b | the command, only if the stop rule of §4 says so; printing first | the fixture |
| 5 | trace agreement through the lift; `M1Trace` to 0 | ledger gate |
| 6 | `reachable_memoIdsOk` through the lift; hook facts | ledger gate |
| 7 | `forkedOf` to `Test/`; landing note; decisions rows 20 and 79 and R3; STATE; `make gen-architecture` | `make check` |

Each step is its own commit by explicit paths. Nothing is pushed.

## 8. Decisions for the owner

1. **Ledger shape.** Forks only, roots implicit, or births, every fiber with its origin
   (§3; the review leans to births).
2. **Justifying the reader switch.** Accept the census plus the finite check in slice 1 as
   the basis for moving readers (recommended), rather than first proving the old fiber labels
   agree, which is the route-A proof this plan exists to avoid.
3. **The command prints or adds.** The first version prints statements to paste
   (recommended by the review); adding kernel-checked theorems, as `#frame_rules` does, is the
   upgrade when reruns are routine.
4. **Where `forkedOf` goes after part 3.** Into `Test/` as the control (recommended), or deleted
   outright with its theorem.
5. **The register.** Row 79 says holder supervision "reads RunFiber.origin"; row 20 says the
   forks record their site on the fiber; R3 of the 2026-09-20 packet (§2.3) chose one origin
   field on the fiber and rejected a parent field as a second representation. The ledger
   replaces rather than duplicates, so R3's principle holds, but all three lines are rewritten
   by the coordinator at step 7.
6. **Is the agreement owed as a theorem?** Row 79 ruled it an obligation. The runtime never
   reads the trace (R79.2), and `Test/Api/SupervisionContract.lean:106` already holds the finite
   control. If the instrument is justified by H, the theorem is a cheap first user and the
   answer changes nothing; if the owner does not want the instrument yet, retiring the two
   obligations takes the gate to 0 with no machinery. Asked once, here.
7. **Build the command now or after the hand count** (the stop rule of §4).

## 9. Where this sits in the development plan

- **Slice 6, last item.** The codex packet lists slice 6 as the five source-site connectors,
  `step_agrees`/`reachable_agrees`, `observe_replace_trace` and the memo cleanup
  (`docs/research/2026-09-21-codex-packet-divergence-and-slice-5.md` §4). The first, third and
  fourth are landed (`40e3bfa3`, `be15b062`); this plan is the second.
- **Residue, not the critical path.** The synthesis places the trace/origin agreement among the
  residue proofs that proceed beside B–F, with the touched Supervision/TraceOrigin/Run laws and
  direct controls as the required builds, and says not to block the protocol design on a
  diagnostic proof (`post-phase-c-synthesis.md` §7). Parts 1 and 3 are that residue.
- **What it feeds.** Part 2 is a candidate instrument for H, transition preservation (M6/S2),
  whose families are to be landed in dependency order by the measured call graph rather than
  arm estimates, and which says "not necessarily a new tool" (§H). The census closure walk is
  the measured call graph; H's family order (frame and bookkeeping; delivery and interruption;
  store; fork, join, race; scopes; async, timer, due; outer driver) is the order the walk lands
  in. The indexed shape of §4 is H's frozen shape. The stop rule of §4 decides whether H gets a
  command or a hand list.
- **What it does not touch.** No protocol design, no run premise, no machine change beyond the
  ledger and the `fork` primitive, no change to the generated skeleton or the typed-state
  banks. `docs/core/decisions.md` is edited only at step 7 by the coordinator.
- **After it.** M5–M7 are briefed after the slice 5 receipt (packet §4); the instrument's
  outcome at step 0 is an input to the M6 brief. A decisions row for the step-invariant shape
  is proposed in the landing note at step 7, not before.
- **The pointer.** `docs/STATE.md` (current milestone, and the owner's decisions) names this
  note as slice 6's last item; this note is force-added when it lands, with the landing note.

## 10. Review record (2026-09-30, base `be15b062`)

Verified against the tree: the writer sets of the fork event, the origin label and the trace;
that nothing removes a fiber; the two runtime readers and the law readers named in §2; the
four update lemmas of §3; the census's owner rule and the source-less `writeSites` call; that
both existing commands add theorems through `ProofGraph.addTheorem` and that the axiom gate
walks the environment (`Test/Audit/AxiomGate.lean:433`); the gate's three-obligation scope;
that no frozen contract packet mentions the origin; the lane and guard sizes; R79.2, R79.3, R3
and rows 20 and 79.

Changed from the first draft: the reason route A is expensive (§2); the census owner fix named
(§2); the design rule stated and the `fork` primitive added (§3); births offered against forks
(§3, decision 1); the slice 2 checklist and the Lean-side probe (§3); the indexed shape, the
signature convention, the hook treatment, the scope of the claim, the print-first command and
the stop rule (§4); the agreement recognised as a `Keeps` (§5); the memo user as a genuine
`Preserves` with per-hook facts (§6); step 0 widened to both users and step 4 split (§7); R3
and decisions 6 and 7 added (§8); placement (§9). Arm counts corrected in §2's table.
