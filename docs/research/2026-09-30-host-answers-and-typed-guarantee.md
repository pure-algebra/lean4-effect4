# Host answers and the typed guarantee: the M6 repair, the external-reply slice, the typed API

Status: **proposed, for owner decisions (§6).** Base `be15b062` on `refactor/phase1-phase3`.
Research probes only; nothing is implemented or committed.

This note was split from the
[fork-ledger plan](2026-09-30-origin-ledger-and-step-invariants-plan.md) on 2026-09-30. It is
the short decision note for what to do now. The full external lane is specified in the
concurrent [external runtime contract](2026-09-30-external-runtime-contract.md). This note
carries:
- the three M6/API amendments of the
  [ratification conditions](2026-09-30-origin-plan-review/RemediationReview.md);
- the probe of the external-reply slice that the owner asked for;
- how that probe fits the contract.

## 1. The finding

The core promise is that every fiber of a type-checked program finishes with a value of its type.
It can only hold if the host's answers are right. Three places miss that today:

1. **M6's capstone** (`Typed/Assembly.lean:224-227`) counts every decision tape. A `sleep`
   answered with `42` finishes with `42`: a checked counterexample, `current_m6_capstone_false`
   in the [plan review's probe](2026-09-30-origin-plan-review/Probe.lean).
2. **The certificate-first API.** `Api.check` then `Typed.replay` runs that same tape to the end
   ([ratification probe](2026-09-30-origin-plan-review/RemediationProbe.lean); rechecked here).
3. **The runtime's own reply check** admits a host answer that names the wrong fiber. On the live
   host session a program checked at `nat` finishes with the string `"wrong"`
   ([probe](2026-09-30-host-answers-evidence/Probe.lean) §2). The path is:
   - `start`, which admits the program through `admitProgram`;
   - `bindCall`;
   - `submit`, whose `preflight` runs `acceptReply`, `admit` and `Val.hasTy`;
   - `applyReply`.

   A concurrent session's work-in-progress probe
   (`2026-09-30-external-runtime-contract/`) found the same through the checked replay.

The first two are gaps in a statement and a facade. The third is a hole in the live API.

## 2. How host answers flow today

- **The live session.** `advance` refuses an answer given as a plain decision
  (`Api/HostSession.lean:239-243`). A reply enters only through `submit` and `preflight`, and
  `applyReply` checks it again when it applies it (`:204-215`).
- **The check** (`Program/Admit.lean`). `admit` (`:77`) requires the fiber to be parked at that
  token on an external row (`requestOf`, `externalRow`). `admitAnswer` then checks the answer:
  - a success value goes through `externalValue` (`Program/Compile.lean:1354`). At a
    handle-typed row a number is an allocation request that becomes a new external handle; any
    other value must pass `Val.hasTy` and carry no external handle;
  - every handle in the answer must exist (`mintedIn`, `Admit.lean:25`);
  - typed failures must fit the row's error type (`errAdmits`);
  - a delayed cell read (`ofRefGet`) is checked by what the cell holds at that moment.
- **Preparation.** `prepareExternalAnswer` (`Compile.lean:1369`) turns the accepted reply into the
  code the fiber resumes with, allocating the external handle in the store.
- **Tape replays.** `Api.replayChecked` runs `admit` before each decision. `Api.replay`,
  `Typed.replay` and `replayAdmitted` do not: by their documentation the caller admits decisions
  (`Api.lean:278-284`, `:425-436`, `:471`).
- **The reference machine** ignores the host table. It has:
  - no external registration;
  - no conversion or allocation;
  - no prepared answer;
  - no way to take a table-aware interpreter.

  These are the four gaps filed with DI-57 (`Test/contracts/machine-scheduler-core.contract.md`,
  "Table-aware agreement"), whose scout B counterexample shows the two machines disagree on an
  external row. `run_eq_ref`'s docstring states the same boundary
  (`Laws/Program/RuntimeR.lean:203-210`).

## 3. Two layers, not two options

The runtime check is the public contract: it decides what a host may send, and a host can run
it. The typed condition (`AnswerOk`, `CompletionStrong` in the proof's world) is what the
preservation proof needs about the value the fiber actually receives.

The link between them must show that an admitted reply, after preparation, is a typed answer in
a world extended by whatever preparation allocated. "The incoming reply passes admission" is not
that statement:
- a number becomes a new handle, and the store grows;
- a delayed cell read is checked against the cell's present contents, while the typed condition
  uses the cell's declared type.

## 4. M6 within its current scope: small and exact

M6's reference runner ignores the host table, so the runs it can describe are those in which no
host answer is applied. At the empty table the runtime agrees: its check refuses every host
answer, whatever the machine holds. That is the theorem `emptyTable_refuses_every_answer`
([probe](2026-09-30-host-answers-evidence/Probe.lean) §1, `[propext, Quot.sound]`).

The repair makes the capstone count only runs whose tape applies no host answer. Proposed shape
(the predicate is new; no answer-detecting predicate exists on decisions today):

```lean
def RReachable (root : ProgramSource) (fuel : Nat) (m : RState) : Prop :=
  ∃ tape, (∀ d ∈ tape, d.isAnswer = false) ∧ m = (replayR root.program fuel tape).machine
```

- **`decision_preserves` keeps its `AnswerOk` premise.** It is the typed layer: every decision
  such a tape applies meets it trivially, and it is what the table-aware extension (§5) will use.
- **The statement catches up with its docstring.** The capstone's docstring already says "every
  state an admitted tape reaches"; the repair makes the statement say the same.
- **The counterexample gets registered** when the declaration changes: `E4-SCHED-CE-015` (the
  next free id), moving the plan review's probe into `Test/Counterexamples/`.
- **This is the premise the synthesis said must not be added silently** (§H). This note asks for
  it (§6, decision 1).

## 5. The external-reply slice, probed

The full external lane is specified in the concurrent
[external runtime contract](2026-09-30-external-runtime-contract.md) (2026-09-30, the survey
that places it in the lowering and runtime-structure plan). Its X0–X4 are the lane's order.
This section keeps what this probe found and what should happen now. It uses B-labels so the
two notes do not clash.

### B1. The boundary rule for handles: a live hole, to decide first

`Val.hasTy` checks a handle by its kind only (`Program/Typed.lean:34`):
- any fiber handle passes `fiberOf a e`;
- any cell handle passes `refOf`;
- any deferred handle passes `deferredOf`;
- anything that reads back as a context passes the context type.

What the fiber returns or the cell holds is typed only in the proof's world tables, which the
runtime does not have. `mintedIn` checks only that the handle exists. So a host can name any
live fiber of the wrong type, and the program goes wrong on the certified live path (probe §2,
proposed id `E4-HOST-CE-007`).

**How far it reaches today.**
- Fiber handles: exploitable now.
- Native cells and deferreds hold numbers only (`Native.lean:90`, `:98`). A wrong cell handle
  still delivers a number, but the generic cells of decisions row 44 would open the same gap.
- Contexts are the same class (not probed).
- **No host row in the tree answers an internal handle.** The SQLite and key-value packages
  answer data or their external client handles (`sqlTy`, `kvTy`, `Native.lean:103-106`); streams
  answer an external handle; the profile rows answer numbers, unit or an allocated resource
  handle.
- **Nothing refuses such a row.** An author can still write one (`Row.host`,
  `Authoring.lean:223`):
  - `checkTable` (`Native.lean:345`) checks only registration and kind;
  - `Table.lawful` checks names;
  - `admitProgram` (`Admission.lean:100`) adds only the int-free scans.

**The two notes differ here.** The contract (§3) proposes that a host may return an existing,
certified machine fiber, reference or deferred. It gets there through a registry: first-order
declarations derived from the checked creation sites, proved to agree with the proof's world.
That is a principled form of what this note first called "types at runtime". It is also a
proposed extension of decisions row 44's proof-only design, and a large piece of work.

The step that closes the hole now is compatible with it:
- **(A) now.** Refuse internal handle kinds in host rows' answer and error types when a table is
  admitted, with a located refusal. The contract's own first scope allows exactly this: an
  unsupported case is refused before execution and left out of the published profile.
  External handles, fresh or existing, stay supported, so this is not "reject every handle
  reply". It breaks nothing in the tree.
- **The registry later.** It lifts the refusal row kind by row kind, if the owner wants hosts to
  return machine capabilities at all. That is the real question for the owner.

Echo-only (a host may return only a handle it was given in the request) is a cheaper middle step
if a package needs one.

### B2. The typed replay route (API)

- **The two budgets.** `replayChecked` compiles with the execution fuel (`Api.lean:354-359`),
  while `Typed.replay` keeps two separate budgets (`:460-472`). A direct swap changes results:
  the ratification probe shows a run that stops at its compile budget completing instead.
- **Which route, revised after the finished contract (its ruling 6).** The public typed replay
  goes through the keyed session: a session header and a `Runner.Command` journal, with phases
  that can refuse and both budgets. It does not go through the decision-tape checker, as this
  note first proposed. A decision tape carries no call envelope, so it cannot show that host
  answers matched their calls.
- **What stays.** `replayChecked` stays as low-level evidence, with its budgets separated. Raw
  `Api.replay` and `replayAdmitted` keep their documented roles.
- **Owed theorem.** Erasing an accepted journal to its machine decisions agrees with the raw
  replay at corresponding budgets. The richer session facts are carried by the holder relation.
- **Order.** The checked session route closes the declaration and preparation gaps (B1, B3)
  before it carries the typed promise.

### B3. The proof's value predicate misses nested handles (affects M6, not only hosts)

The contract's predicate probe, rerun here with exit 0, shows `HandlesFit`
(`Typed/Admission.lean:39`) checks nothing inside:
- **products**, stored as two-element lists while the rule looks for a pair;
- **Result and successful-exit values**, which fall to a catch-all `True`;
- **unions**, where the shape and the handle evidence can come from different branches.

So the typed-state invariant does not carry a fiber's type through a pair. An M6 proof of
"project the pair, then await the fiber" would have nothing to stand on, and such a program
exists with no host involved. It forks a child returning 7, stores its handle in a pair with
`pair`, takes it back with `fst` and awaits it; it checks at `nat` with no host table and runs
to 7 ([path probes](2026-09-30-host-answers-evidence/PathProbes.lean) §D). This is the admission
audit's lesson again (validate a proof-side judgment against the actual representations before
freezing it). The contract (§4) proposes a constructor-complete membership judgment beside the
old one, with shape and handle evidence in one derivation, and the consumers migrated. That
belongs before M6 proof work, whether or not the external lane goes first.

### B4. The rest of the lane

These map onto the contract's order:
- the reference machine learning the table (DI-57's four gaps, `RunEqRefTableStatement`) is its
  X3;
- the typed connection at the boundary (preparation, allocation, the world extension, typed
  failures, delayed cell reads, oracle answers) is its X1 and X4;
- keyed lifecycle, cancellation and cleanup ownership are its X2;
- the checked application guarantee is its X4.

It also names the first vertical slice, run end to end: acquisition, prepared handle, stored in a
Ref and read, a second external operation, release, with the interrupted branch.

**A protocol note** (from the concurrent probe): an allocation reply is tied to the allocation
count at the moment it is applied. The live session checks again at application, which is the
rule to keep; the contract's §3 goes further and gives host resources a stable key separate from
the machine index.

## 6. Decisions for the owner

1. **M6's capstone counts only runs with no applied host answer** (§4), as its current-scope
   repair. Recommended.
2. **The value predicate is amended before M6 proof work**: a constructor-complete membership
   judgment beside the old one (B3; the contract's §4). Recommended.
3. **The handle rule at the boundary:** (A) refuse internal handle kinds in host rows now; decide
   separately whether hosts may ever return machine capabilities, which is the registry (B1;
   touches rows 44 and 7). Recommended. Note that (A) is stricter than row 7's open
   recommendation, which refuses a handle arriving from another process but admits one
   in-process. Under (A) an internal handle kind is refused from any host until the registry,
   or an in-process capability check, exists.
4. **One public typed host replay route:** `Typed.replay` consumes a session journal through
   the checked keyed session, keeps both budgets, and has refusal-bearing phases (B2; the
   contract's ruling 6). `replayChecked` stays low-level evidence. Recommended, as an explicit
   API migration.
5. **The external lane is required before the public guarantee is claimed**, as the contract's
   proposed ruling 1 says. M6 and M7 on programs without host answers are a first, provisional
   result, and are described that way. Recommended.

## 7. Evidence

- **This note's [probe](2026-09-30-host-answers-evidence/Probe.lean)**
  ([log](2026-09-30-host-answers-evidence/probe.log)). Command:
  `lake env lean -M6144 -DwarningAsError=true docs/research/2026-09-30-host-answers-evidence/Probe.lean`,
  exit 0. It contains:
  - the empty-table theorem, at `[propext, Quot.sound]`;
  - the forged fiber handle through the live session: phases progressed, bound, preflight,
    applied, progressed, then the root's exit is the string `"wrong"`;
  - the same through the checked replay;
  - what `Val.hasTy` sees.
- **The plan review's probe** (six theorems, the M6 capstone refuted): rerun, exit 0.
- **The ratification probe** (12 guards): rerun, exit 0.
- **The concurrent `2026-09-30-external-runtime-contract/` probe**, another session's work in
  progress. Its six-guard version showed the forged fiber through the checked replay and the
  allocation coupling. When I reran it, the file was mid-edit and one proof did not check; this
  note does not rely on it.

- **The contract's predicate probe** (five kernel facts about `HandlesFit`): rerun, exit 0.
- **The [path probes](2026-09-30-host-answers-evidence/PathProbes.lean)**
  ([log](2026-09-30-host-answers-evidence/path-probes.log)): the three design paths of §8, exit 0.

Everything above is a finite check except the kernel theorems. No implementation and no commit.

## 8. Review of the finished contract, and three design paths probed

The [external runtime contract](2026-09-30-external-runtime-contract.md) was finished the same
day (738 lines). Checked against the tree at `be15b062`:

**Reruns.** Its `verify_packet.py` passes (all 20 `Ty` constructors in the matrix, which I
confirmed against `Program/Ty.lean`; links and hashes agree). Its probe passes (11 guards) and
so does its predicate probe (five kernel facts).

**Its OCaml number claim holds.** It is verified at the translation table, not through a program
run (`src/OCaml5/Lcnf/Translate.lean`):
- natural addition lowers to raw `+` (line 162), and so does successor (line 175), so a large
  enough sum wraps;
- multiplication and powers saturate at the largest integer (lines 163, 182);
- subtraction floors at zero.

The profile's `natBound` (DI-56) bounds requests and answers, not intermediate values, which is
the contract's point. Its claim that the OCaml engine only runs with an empty table was not
checked here.

**Agreed:**
- external completion is required before the public guarantee is claimed;
- one checked, keyed host route, and the public typed replay over its journal;
- replies received and replies applied, separated;
- recovery that never repeats host work;
- the constructor-complete membership judgment;
- the six storage interfaces with every runtime family assigned;
- the compilation stages as named connections, each with its own evidence.

**Three design paths, tried side by side** ([path probes](2026-09-30-host-answers-evidence/PathProbes.lean)):
- **A. Refuse internal handle kinds in host rows at table admission.** It refuses the probe's
  fiber row and passes all 15 host rows in the tree (SQLite, key-value, streams, the profile
  rows). It is an interim profile with a located refusal, which the contract's first scope
  allows. It is not completion.
- **B. A fiber's declared type from its recorded creation site and the checker.** The recorded
  site is the fork action's path (`[0, 0]` in the probe). Typing the fork's body there gives
  `string` for the forged fiber, `nat` for the honest one, and the root's type for the root, with
  no type stored in any value. This is the contract's "registry derived from checked creation
  sites", shown workable for source forks. Two gaps it exposes:
  - no function yet computes the static environment at a path (the probe's fork is under no
    binder); a small fold would;
  - forks the runtime makes without a source point record the empty site (finalizer forks,
    `Machine/Fibers.lean:969`; races without a source site, `:1864`), so the ledger record needs
    the creating construct's kind for those.
- **D. A fiber handle inside a pair, with no host.** The program of B3 checks at `nat` and runs
  to 7: the amendment is needed for M6 itself.
- **C. Shape and handle declarations in one recursion over the actual encoding.** It refuses all
  four gaps the predicate probe shows (a pair, a Result, a successful exit, a union), accepts
  the same values when the declaration fits, and agrees with today's shape check on 21
  handle-free samples. B and C together refuse the forged reply and accept the honest one.

**What this adds to the contract:**
1. **The fork ledger of the origin plan is the fiber registry's evidence.** Its site field is
   what path B reads, and its lookup contract (unique, bounded, corresponding) is the fiber part
   of the contract's `RegistryAgrees`. The two tracks meet here; the ledger plan now says so
   (§3).
2. **A smaller first vertical slice exists.** The contract's first slice (acquisition, a handle
   stored in a Ref, a second call, release) needs generic cells first (its own prerequisite,
   decisions 42–43). A fiber slice needs none: the ledger's site, the static environment at a
   path, the one-recursion check, admission against the derived declaration, and the
   typed-replay route. It exercises the registry, the membership judgment and the boundary
   together. It fits before the Ref slice.
3. **The interim profile is explicit.** Until the registry lands, rows whose answers carry
   internal handle kinds are refused at admission (path A). The completeness converse the
   contract owes holds on that profile.
