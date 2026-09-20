# The open design issues in order, and the first packet: observations, origin, connectors, the handshake

Written 2026-09-20 at `6dcfe79a` while Codex holds M1 (so nothing here was built; every
definition below is a statement to be probed when the compiler is free). The owner asked for
the open design issues tackled in order of importance to core stability, ergonomics and
utility. §1 is the order with the reason for each place. §2 is the first packet, row 79 with R3
and row 20, because it is what M1's memo condition, P2's `Arena` and every composed-module claim
need before they can be stated. §3 is what M1 can take from it today.

## 1. The order

The register at HEAD: decisions rows 78–85 open (78 is M1, underway), rows 48–53 recommended
and unruled, rows 2, 7, 10, 11, 14, 15, 19–24, 26–29, 31–33 open from the earlier groups,
rows 42/43 ruled but unlanded past L1/L3/L5, Config D1–D5 pending, DI-01/04/05/06/08/16/21
open, DI-24's repair half unstarted. Ranked by the owner's three criteria in that order.

### Core stability (blocks or de-risks M2–M7 and the correctness claims)

| # | item | why here | form |
| --- | --- | --- | --- |
| 1 | **Row 79 with R3 and row 20: the observation contract.** Three named views, the fiber's origin as state, the representation-connector shape | plan §3: observations precede representation changes. M1's memo condition needs the connector's statement now; P2's `Arena` needs the projection; `statusOf` reads the trace that `Obs` excludes (a consumer's semantics outside the theorems, stores map F3) | §2, this note |
| 2 | **The park-handshake invariant** stated as its own definition | stores map §2.1: S2 will otherwise discover it inside a proof; it is the machine-level twin of the skeleton's `ResumeOk` | §2.6 |
| 3 | **Row 85: `Arena`** | the lowering's trust seam; the interface exists in prose; needs #1's projection to say what the OCaml instance observes | next packet |
| 4 | **Rows 48, 51, 52** (existential typed stack; `ServiceOk` context-wide; progress as a claim) | milestone content, all "recommended"; ratify as one stroke into M3's brief rather than three rulings | ask |
| 5 | **DI-57** table-aware agreement | the host boundary's correctness; weeks; after M7 | later |

### Ergonomics (what an author or agent writes)

| # | item | why here |
| --- | --- | --- |
| 6 | **L4 of rows 42/43**: rows as templates over `var` (`Ref<A>`, `Deferred<A,E>`, `deferredMake` typed) and binder-term read-modify-write rows | ruled; plan §14 puts binder-term rows before M6's `refUpdate` family; `Ty.refOf`/`deferredOf`/`var` and the template calculus already exist, the store rows still spell `Ref.Ref<number>`; the kernel table is where a term kernel goes |
| 7 | **Row 2** records and variants (c now, b before the first foreign consumer); **DI-24's repair half** (one nominal class per full key on the printed face); **Config D1–D5**; **L6/L7** faces and the service table | each a short ruling packet; none touches the stores or the world |

### Utility (what programs can do)

| # | item | why here |
| --- | --- | --- |
| 8 | **Rows 84/80**: the embedded-attempt connector, then the first transaction profile | needs #1's semantic view to say what an attempt hides; P4 after M7 |
| 9 | **Row 81 Latch** with its four controls | the first scheduled-wake producer; DI-11's modules wake inline until it lands |
| 10 | **Row 82** behaviour values; **row 83** Clock/Random | owner decisions on the language's closed door |
| 11 | **Groups B and D** (digest, MCP; the lowering rules, rows 28/29) | the lowering-module API of the kickoff note §5 is row 28/29's content; after the milestone |

The placement moves are scheduled between M1 and M2 and are not a design issue.

## 2. Packet 1: observations, origin, connectors, the handshake (row 79, R3, row 20)

### 2.1 What exists, read at HEAD

- `Obs := ⟨exits : List (FiberId × Option ExitV), stores : Stores⟩`, `Obs.le` orders recorded
  exits and allocation (`Laws/Machine/Behaviour.lean:29-45`). `obs` forgets code, scheduling
  and the trace. `run_eq_ref` compares `outcome` and `obs` at the empty table
  (`RuntimeR.lean:211`). `E4-DEN-CE-003` and `E4-BEH-CE-001` are the rows that keep the trace
  out.
- `BookMeans C S` relates two instances field by field with **`m₁.state = m₂.state`** and no
  trace clause (`Book.lean:191-199`); `MachineOk StOk` carries a store predicate through the
  loop (`:236`); `StepAgrees` is the one-step obligation (`:622`).
- `Run.Observation` (the holder view, `Run.lean:220-240`): protocol state, outcome, root exit,
  awaits, pending and retired keys, applied count, frontier reasons, fiber statuses.
- `statusOf` (`Api/Supervision.lean:238-247`) reads machine state for `exited`, `child`
  (`parentOf` through `children`) and `pinned` (`pinOf` through the observer list), and reads
  **the trace** for the last distinction: `if (forkedIds m).contains f.id then .daemon else
  .root`, where `forkedIds` filters `RunEvent.forked` (`:167-181`). The module says it: "the
  `forked` events of the trace separate them, and only they can."
- `RunEvent` has 21 constructors (`Fibers.lean:360-384`). Host-visible: `exited`, `callback`;
  origin: `forked`, `started`; the rest scheduling and frame events, the frame part already
  erased on the reference (`η := Unit`).
- rc.112's fiber object holds no parent: the parent's `children` set tracks the child, and the
  forking closure's `parent` is used only for `interruptUnsafe(parent.id, …)` and annotations
  (`internal/effect.ts:879-910`). So `parentOf` is the transcription and only the
  forked-or-root bit is trace-derived.
- The critique's `Factors fine coarse := ∃ forget, ∀ s, coarse s = forget (fine s)` with
  `respects_eq` and `trans` (`2026-09-19-critique/Contracts.lean:33-45`), and
  `ObservationTx.lean`: two machines with equal `Obs` and different supervision because of fork
  history. That is F3 as a checked countermodel.
- The session ledger (`Api/HostSession.lean:84-93`) records accepted facts: a reply is pending
  until applied and consumed. The catalogue §1.5 draws the right conclusion from rc.112's own
  event log: the observable record is the ledger plus the exits, not a projection of the trace.

### 2.2 The three views, named

The rule: a view names what it retains, and every reader of the machine is one of the three.

| view | retains | who reads it | today |
| --- | --- | --- | --- |
| **semantic** `Obs` | every fiber's exit; the stores | the correctness theorems (`run_eq_ref`, `Beh`, the book) | exists, unchanged |
| **holder** `Run.Observation` | protocol state, outcome, root exit, awaits, pending/retired keys, applied count, frontier reasons, fiber statuses | the API, replay, supervision, the MCP face to come | exists; reads the trace through `statusOf` |
| **diagnostic** `RunMachine.trace` | the 21 events through the sink parameter `η` and the list | explanation, profiling, the truth harness's differential | exists; `η := Unit` on the reference |

**R79.1.** `Obs` stays the semantic view, unchanged. No four-event alphabet replaces it; a
composed module or a target that needs a coarser or finer view names a projection and proves
`Factors` to `Obs`, never redefines `Obs`.

**R79.2.** The holder view factors through machine state and the session ledger, never through
the trace. This is what R3 delivers (§2.3). After it, `Run.observe` does not mention `trace`.

**R79.3.** The diagnostic alphabet is every `RunEvent` but `exited` and `callback`; `forked`
and `started` join it once the origin is state. The erasure theorem, "replacing the trace
changes no semantic and no holder observation", is then definitional:
`obs { m with trace := t } = obs m` is `rfl` today, and `Run.observe` gets the same equation the
moment `statusOf` stops reading `forkedIds`. No sink refactor is needed for the theorem; the
sink parameter already exists for the cost.

### 2.3 R3, in its one-field form

The stores map proposed `parent : Option FiberId` and `daemon : Bool` on `RunFiber`. Reading
`statusOf`, `parentOf` already answers the parent from `children`, as rc.112 does, so a parent
field would be a second representation of a fact the machine holds. What the trace uniquely
carries is whether the fiber was forked at all, and with which flag. One field:

```
inductive Origin
  | root
  | forked (parent : FiberId) (daemon : Bool)     -- and, if row 20 is ruled yes, (site : List Nat)

structure RunFiber … where
  …
  origin : Origin
```

- Set once: `RunFiber.make` takes it; `spawn` (`Fibers.lean:908-923`) passes
  `.forked parent.id options.daemon`; the root's creation (`loadR`, `Api.run`'s start) passes
  `.root`. Nothing else writes it.
- `statusOf`'s last arm becomes `match f.origin with | .forked _ _ => .daemon | .root => .root`.
- `forkedOf`/`forkedIds`/`forkedEvents` become one control, "the trace agrees with the state":
  `forkedOf m.trace = m.fibers.filterMap (fun f => match f.origin with | .forked p d => some (p, f.id, d) | .root => none)`,
  proved once as an invariant of the loop (it is the stamp and the field being written by the
  same `spawn`), then the three functions leave the API.
- `Origin` carries a `parent` only as provenance; `parentOf` stays the tracking relation, since
  tracking is dropped when the child exits or the parent does, and provenance is not.
- Row 20's fork-site path: if ruled yes, it goes on `Origin.forked` as `site : List Nat`, not on
  the event, and `supervision_static`'s "at those paths" reads state. Both rows land as one edit.

Radius, by reading: `Machine/Fibers.lean` (`RunFiber`, `make`, `spawn`, the root start),
`Api/Supervision.lean` (`statusOf`, the three `forked*` functions to a control), `Laws/Machine/
Book.lean` (`FiberMeans` gains `origin` equality, one line), the frames (`#frame_rules
RunFiberOk` regenerates, so the frame count in `Typed/Frames.lean` moves), the supervision laws
that quantify over `forkedOf`, the OCaml regeneration (`RunFiber` is a generated record; the
`F.t` carrier holds it generically; `make gen-lcnf`, `gen-cas`, and the eff mirror since the
engine may not lag the source, row 70), and the batteries under `Test/Api` that pin fiber
statuses. The position census gains no row: `Origin` holds no value, exit, cause or program.
This is a small slice and should not run concurrently with M1's 38 files; it follows M1 with the
placement moves.

### 2.4 The representation connector: one shape, instantiated by M1 now and P2 next

`BookMeans` relates stores by equality and `Obs` holds the concrete `Stores`. A representation
change therefore cannot be an equality of observations, and plan §5 gives the two forms. The
contract, stated so a slice can instantiate it:

**Projection form** (an abstraction function exists). For a store family with concrete carrier
`C` and model `M`, `alpha : C → M`, the step functions `stepC` and `stepM` over the same
operation alphabet, and a well-formedness `WF` on the concrete side:

```
WF c → (stepC o c).map (fun (c', a) => (alpha c', a)) = stepM o (alpha c)
WF c → stepC o c = some (c', a) → WF c'
```

Every theorem stated on `M`'s observation transfers by `Factors` (`Factors.respects_eq`,
`Factors.trans`); nothing stated on `M` is re-proved.

**Relation form** (the representation quotients order or duplicates, so no `alpha` inverts):

```
Rel c m → stepC o c = some (c', a) → ∃ m' a', stepM o m = some (m', a') ∧ a = a' ∧ Rel c' m'
Rel c m → stepC o c = none → stepM o m = none
```

with `Rel` initial on the empties and, when the machine lifts it, a progress clause so that a
concrete step matching zero abstract steps cannot hide work forever (critique §4).

Where it lives: one module, `Laws/Machine/Refinement.lean` (name proposed), holding the two
shapes as structures `Projects alpha stepC stepM WF` and `Refines Rel stepC stepM`, each with
its lifting through `syncOpStep` to `Stores` and through `MachineOk`/`BookMeans` to the loop.
Instances: M1 (§3), P2's `Arena` (the list instance projects onto itself; the OCaml instance is
the relation form with `prop_store.ml` as finite evidence and no Lean theorem, by row 85).

**R79.4.** Adopt the two shapes as the only way a store representation may change; a slice that
changes a store's type names its instance in this module.

### 2.5 Agreement profiles per composed module (the second half of row 79)

DI-89 already requires one behaviour law per form on a named profile. What a profile is has
never been written as data. Proposed:

```
structure Profile where
  view       : semantic | holder                -- which observation the law is stated on
  handles    : HandleRel                          -- public-handle renaming; private helpers hidden by an identity world W
  decisions  : TapeRel                            -- how the expansion's tape relates to the module's (never "equal raw tape")
  direction  : equal | included | both            -- equality for deterministic related inputs; inclusion for a restricted profile
  progress   : none | measure                     -- what, if anything, is promised about ready operations
```

and the law of a catalogue row is `Agrees profile module expansion`. The retained finite
control (a scheduled and an inline wake returning different values) is the reason `decisions`
and `direction` are fields and not defaults: a module printed as its expansion agrees with
rc.112 on values relative to the tape (catalogue Q1's recommendation), and that is the profile
its law names.

**R79.5.** Profiles are data in one place; a composed module's law names its profile; the
default fidelity is values relative to the decision tape; a schedule deviation is a named
refusal row, as the atomic-transaction deviation will be.

### 2.6 The park-handshake invariant, stated

A waiting fiber is recorded twice: in the store's wake list as `(fiber, token, phase, payload)`
and on the fiber as `parked = withGuard token` plus a `Pending` entry. A resume for a token the
fiber is not parked on is inert (`drive_resume_wrong_token`, `Laws/Machine/Clauses.lean`). The
relation between the two sides is nowhere stated. Statement:

```
def ParkHandshake (m : RunMachine …) : Prop :=
  ∀ key phase, ∀ w ∈ (Stores.wakeList m.state key phase).waiters,
    ∀ f ∈ m.fibers, f.id = w.fiber →
      f.parked = Parked.withGuard w.token ∨ Inert m w.fiber w.token
```

where `Inert m fiber token` is the proposition `drive_resume_wrong_token` discharges: driving
`Cmd.resume fiber token _` on `m` changes nothing observable. Timers' waiters are covered by the
same quantification since `wakeList` addresses every family. Preserved by: `register` (adds the
waiter and parks the fiber in the same command), `cancel` (removes both), `complete`/`wakeBatch`
(moves waiters to `due`, whose drain is the one producer of `Cmd.resume`), and every other
command, which touches neither side. It is the machine-level statement the skeleton's `ResumeOk`
row assumes; it belongs in `Laws/Machine/Handshake.lean` beside `Clauses.lean`, stated at M3 and
proved at M4 with `Keeps.lean`.

### 2.7 Rulings asked

- **R79.1–R79.5** above.
- **R3 in the one-field form** (`Origin`), landing after M1 with the placement moves; the stores
  map's two-field form is withdrawn as a second representation of `children`.
- **Row 20**: yes or no on the fork-site path; if yes, on `Origin.forked`.
- **Row 4 of the order**: ratify rows 48, 51, 52 as M3 content in one stroke.

## 3. What M1 takes from this today

The memo deletion's second condition, "the representation connector" (`machine-state.md` §4),
is §2.4's projection form instantiated once. Under the old store invariant the completion
program of every cell is `completionPrim c` for exactly one `c` (`completionPrim` is injective:
its two arms land on different `Prim` heads), so the abstraction function exists on `StoresOk`
stores:

```
alpha : StoresOld → StoresNew       -- cells and owed resumes through completionPrim⁻¹; MemoEntry.effect dropped
theorem syncOpStep_alpha (o : SyncOp) (s : StoresOld) (h : StoresOk s) :
    (syncOpStepOld o s).map (fun (s', a) => (alpha s', a)) = syncOpStepNew o (alpha s)
```

by the case list of `syncOpStep` (every non-memo, non-deferred row is `rfl` after unfolding; the
deferred rows use the injectivity; the memo rows drop the field). Its corollary on the
observation, `obs_alpha : obsNew (mapStores alpha m) = projectObs (obsOld m)`, is the connector
the census witnesses of `layer.memo-build-once` restate through. One theorem, one corollary,
registered in the `Effect4.Stores` bank as the slice's first rules. It is the cheapest form the
condition can take, and it is the form every later store change will copy.

## 4. Receipts

Read at `6dcfe79a`: `Laws/Machine/{Behaviour,Book}.lean`, `Machine/Fibers.lean` (`RunEvent`,
`spawn`, `start`), `Api/Supervision.lean` (`forkedOf` through `daemonsQuiet`),
`Api/HostSession.lean` (the session record), `Run.lean` (`Observation`),
`vendor/effect-4.0.0-rc.112/src/internal/effect.ts` (`parent` uses), the critique response §4
and its `Contracts.lean`, the stores map §3, the catalogue §1.5, plan §3 and §5, decisions rows
20, 48–53, 78–85, `Test/Counterexamples/REGISTER.md` rows `E4-DEN-CE-003`, `E4-BEH-CE-001/002`.
Nothing built; every definition above is a statement for a probe once the compiler is free.
