# 2026-10-06 the law of a whole run for a module: what stands under it, and what does not

Status: a working note for a discussion with the owner (history, not authority). It proposes
and rules nothing. Part 1 is an inventory that a read-only scout made on 2026-10-06, at main
`9018a2aa`. The coordinator checked six of its facts in the source and marks them. Part 2 is
the coordinator's reading. Each statement of part 2 is a proposal until a slice places it.

## The question

Each module has laws of one store step and finite traces. No theorem speaks of a whole run of
a client that uses a module's operations. The owner asked on 2026-10-06 what that law needs,
and which base abstractions to complete first: typing, service handling, records.

## Part 1. The inventory

Evidence: read only, by a scout; "checked" marks what the coordinator read again.

| Base | What is proved today | Where it stops |
| --- | --- | --- |
| **Typed state along a run** | For every checked program and every admitted tape, each reached machine is typed in some world: `reachable_typed` (checked; `src/Effect4/Laws/Program/Typed/Commands/Clauses/All.lean`). An answer-free tape is admitted. Each cell's value is a member of its declared type (`CellsTyped`, `storeTyped_of_typedState`). The clauses cover forks, masks, scopes, `Ref` and `Deferred` rows | It is a law of `replayR` and `Api.replay`, at the empty row table. No statement is over a session or `Run.play`. With host answers the premise is the ghost `AdmittedTape` (R6, parked). It gives no progress |
| **A module's handle** | `Queue.bounded` is `Ref.make (empty A capacity)`, and it answers `.refOf (Queue.cellTy A)` (checked; `bounded_types`). Any term at that type types a `Ref.get` or a `Ref.modifyWith` | No handle type hides the cell. The Queue's own header says that a cell written by hand is outside every law of the module (checked). `Ty.handle` and `Ty.app` are opaque by name (checked), and only the mask's saved state uses one |
| **Handles along a run** | One step: an allocated key is fresh (`refMake_fresh`, `deferredMake_fresh`, `handle_identity_laws`). Declarations persist (`order_trans`, the world's extensions) | No theorem concludes `Table.Injective`, the premise of five attempt laws, and none builds a table from a reached machine (checked) |
| **`Deferred`, as behaviour** | One store step: an await of a completed cell answers the stored value and adds no waiter; a completion owes each waiter that value, in registration order (`deferredStore_register_done`, `deferredStore_complete_pending`). One command: a resume at the guard installs the answer, and a stale token is dropped (`drive_resume_guard`, `drive_resume_wrong_token`) | No theorem composes a completion with the awaiter's resumed value across commands. "Not lost before the park" is one store step and one finite trace |
| **Helpers and budgets** | An invariant lifts through each command, decision and replay (`Machine.Lift`). Dispatcher tasks keep the typed state. A run replays from its journal (`journal_replays`, `play_append`) | A task that exhausts its budget drops the rest of its snapshot (checked; `fireStep`). The only sufficient-budget theorem is on `Straight`. No law resumes after a cut |
| **Finalizers** | One scope value: a second close runs nothing, and the close order is the registrations reversed (`close_twice`, `closeOrder_eq`). One sequential close equals `Scope.closeExitsM` at every prefix (`runState_*`). The mask: a live fiber's flag is a function of its stack along a run | No finalizer theorem of a whole run. `releases_once` and `cleans_once` are planned goals, one program each |
| **Records** | Types with an optional-key flag; depth subtyping and no width (`Ty.sub`); membership (`Fits`, `NamedFit`); read, overwrite and their typing (`fieldType`, `setType`, with `record_fieldType_fits`, `record_setType_fits`); the TypeScript, Schema and wire images | No general equation of a read after an overwrite: each module proves its own, field by field, by `rfl`. Refused or open: equality at records (row 126), recursive types (row 124), number and integer fields in codecs (row 121), `catchTag`'s residual (row 130) |
| **Services** | `run_eq_ref` at the empty table; `run_eq_meaning` on `Straight`; `loopAgreement` on `Looped` | A client of service rows is outside all three, and it is typed only under `AdmittedTape` |
| **Agreement words** | `ReplayRel` and `BMeans` (two machines on one tape); `Projects` and `Refines` (one-step store projections) | No module uses them. "Agrees profile module expansion" and a stuttering simulation have no Lean definition. Row 230 says what a profile must define before it hides a cell |

The modules' own laws take as premises exactly what the middle column lacks at a run: a cell
that holds `cellVal tb msg s` for a state of the profile, that value's membership, an
injective table, and the captures (`take_attempt`, `src/Effect4/Laws/Modules/Queue/Ops.lean`).

## Part 2. The coordinator's reading

### The law has three layers, and they need different things

1. **The cell's invariant.** At every reached machine the module's cell encodes a state of
   the profile. It is the proposed claims `semaphore-accounting-preserved` and
   `pool-profile-preserved` (R4), and the Queue's has no name yet.
2. **A call's lifetime.** Each call's reply and its commits are the model's. A request that
   waits is notified once it is selected, and it withdraws when it is interrupted. These are
   R10's parts with `wait-registration-no-gap` (R12) and
   `waiting-request-obligation-preserved` (R11). They are invariants. None is liveness.
3. **Agreement.** The expansion's public observation equals the profile's (R10, "Agrees").
   It needs a client written against abstract operations and a machine that answers them.

Layer 3 needs the host boundary's open parts (R6). Layers 1 and 2 do not.

### What each layer stands on

| Need | Status | For |
| --- | --- | --- |
| The cell is written only by the module | **missing, and it is the first design choice** | layer 1 |
| The handle table stays injective along a run | missing; the one-step freshness lemmas are there | layer 1 |
| Typed state at every reached machine | proved, for closed programs | layers 1 and 2 |
| One law for an await and its notification across commands | missing; the one-step laws are there | layer 2 |
| A run in which no task was cut by its budget, as a named premise | missing as a name; the machine drops the work | layer 2 |
| The mask: the bracket of a region | proved, with the later cut's stack shape as its premise (`compiled_region_bracket`); a fiber that a pending command steps is live at each cut of a compiled command loop (`stepped_live`) | layer 2, under a masked caller |
| The stack's shape is kept along the fiber machine's commands while a fiber is inside a region (the carrying fact) | missing; seat BRACKET judges it a slice of its own, of the size of seat LIFT's second part. Its statement elaborates, and a finite probe on eight runs finds no counterexample. It is an until statement, which the lift does not carry as it stands (decisions row 280) | the same |
| A finalizer runs at most once for a registration, along a run | missing (R11's first whole-run clause) | the protected permit, Pool's `use`, two scenario goals |
| A general algebra of a record's read and overwrite | missing; it costs each module some lemmas and blocks nothing | every next module |
| An abstract client and its agreement relation | missing | layer 3 |

### The first design choice: how a client is known to leave the cell alone

Three ways, from the least change to the most.

- **A discipline on the checked program.** A decidable predicate: every `Ref` operation at
  the module's cell type is one of the module's steps, and every cell made at that type is
  the module's empty cell. The invariant then attaches to the cell's declared type in the
  world: every cell declared at `Queue.cellTy A` encodes a state of the profile. It lifts as
  typed state does, with the attempt laws as its steps. No syntax changes. The law's domain
  is "clients in the discipline", as `Straight` and `Looped` are domains.
- **An opaque handle type.** `Queue.bounded` answers a nominal type, and only the module's
  operations are typed at it. A client then cannot write the cell at all. It needs a sealing
  rule in the checker, so it is a change of the language (R3, row 124).
- **Abstract operations.** The client is written against operation rows, and the module's
  model answers them. It is the form of layer 3, and it waits for R6.

The coordinator would take the first for layers 1 and 2, and keep the second as the later
form in which the discipline holds by typing. The choice is the owner's: it fixes a supported
domain.

### Base work that pays before any module's law

In this order, each a slice of its own:

1. **The discipline and the type-indexed invariant**, on the Queue first. It also turns the
   attempt laws' premises into conclusions at a reached machine.
2. **The await and its notification**, as one invariant of the machine: a parked fiber is in
   its cell's waiters, or its delivery is owed, queued or accepted. It is module-free, and
   every module's waiting uses it. Seat POOLOPS found on 2026-10-06 what a module adds to
   it: at Pool a missing withdrawal loses a wake. Pool's helper selects by a count, so it
   takes a dead entry and resolves a hint that nobody awaits, and the item stays idle while
   the next borrower waits (tested: trace 2 of `Test/Program/PoolTraces.lean`, one
   schedule). Semaphore's helper scans the live waiters, and the same fault lost no wake
   there. So the law of a wake at Pool takes the withdrawal as a premise: every entry in
   the cell's waiters belongs to a fiber that still waits.
3. **A finalizer at most once along a run**, by registration identity. It is module-free
   too. It serves the protected forms and the scenarios' goals.
4. **The uncut run** as a named premise. Seat WORKQ found its right form on 2026-10-06: the
   tape of the run's own journal leaves no row unread, in the words of seat CUTS's laws "no
   stopped row". A journal's verdicts do not decide it. A reply application answers
   `applied` whatever fuel its step had left, so a cut can hide inside it (tested: one run of
   the crew at the command budget 60). Whether an application should report its sufficiency
   is a choice of the session's observation, for the owner.

   The seat then measured what a cut leaves (tested, finite:
   `docs/research/2026-10-06-seat-workq-evidence/left.out.txt` and `sweep.out.txt`). Where
   the fuel ends inside an answer decision, the command loop returns the commands that the
   fuel left, and `stepDecisionState` (`src/Effect4/Machine/Fibers.lean`) keeps the machine
   and the receipt `settled`, and drops them. The machine's own flag reads that the fuel
   was not enough, and the session does not show it. A cut has two kinds. One leaves a
   runnable fiber with no task (the budgets 60 and 100). The other leaves the machine at
   rest: no runnable fiber, no armed owner, no live call, and no exit of the root, so
   nothing will run the root (the named run `dropped`, at the budget 80). In a sweep of 22
   scripts at each command budget from 1 to 160, 1,937 runs are funded and 1,583 are cut;
   23 of the cut runs are at rest, and the root has no exit in 9 of them. So rest does not
   show that a run is funded. No goal's observation failed on any of the 23. The finding is
   evidence for the open parts `driver-continuation-split` and
   `driver-suspension-keeps-typed` (decisions rows 84 and 226): the driver's continuation
   is not kept. Whether the machine keeps it, or the session reports the cut, is the
   owner's.
5. **The record's read-and-overwrite laws**, as a bank. It shortens Pool's public slice's
   successors and Cache.

### What the question implicates elsewhere

- **Typing.** Nothing blocks layers 1 and 2. Two gaps are worth closing on the way: a theorem's
  premise that a caller's term has one type under both literal modes (Codex's review, friction
  3), and typed state stated over a session, which the scenarios' goals need.
- **Service handling.** Not on the path of layers 1 and 2. A scenario that takes host answers
  needs reply admission (R6, parked), so its goals wait for that and not for this law.
- **Records.** Sound for what the modules use. The missing piece is convenience, not meaning.

### Probes that would test this reading

`docs/research/2026-10-06-probe-questions.md`, group B: the exact premises of typed state
(B2), whether a client can write the cell (B3), references at record types (B4), and the
literature on a commit that a helper makes (B5).
