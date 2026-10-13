# Semiotics of Contents States: One Inside Vocabulary for Every Object

Status: research note. 2026-10-13.
The code is `tools/Tools/View/Tube/`.
The prototype is `tools/view/out/proto/fills.html`.
The motion plan is `docs/research/2026-10-13-motion-everywhere/README.md`.
This review assesses contents states across the tube language.
In the dictionary (`docs/core/controlled-english.md` §3), a fill places a program at an address.
A body's inside displays a contents state (`docs/research/2026-10-13-motion-everywhere/README.md` words table).
This note uses "contents state" for what the lumen shows.
Zero-bore marks hold no contents state (`no lumen (strut)`).

---

## 1. The Objects

Every diagram in Effect4 renders objects from the semantics and the machine.
The visual grammar depicts fourteen distinct kinds of objects across their lifecycles.

```mermaid
flowchart TD
  Obj["Runtime Objects"] --> Data["Data Plane: Values, Stores, Handles"]
  Obj --> Control["Control Plane: Fibers, Frames, Scopes, Finalizers"]
  Obj --> Coord["Coordination: Promises, Queues, Semaphores, Streams"]
  Obj --> Boundary["Boundary: Failures, Interrupts, Host Calls, Frontiers"]
```

### 1.1 Values
- **What it is:** First-order evaluated data, defined in `Store.Val` (`src/Effect4/Store/Carrier/Val.lean`). It includes scalars, compound records, and references.
- **States over a run:** Uncomputed, present in a slot, moving in flight, and dereferenced.
- **States to tell apart:** A reader distinguishes an unwritten empty slot from an evaluated scalar and a compound collection.

### 1.2 Promises and Deferreds
- **What it is:** A synchronization cell defined in `Deferred` (`src/Effect4/Machine/Stores.lean`, `docs/core/machine-state.md` §2). A cell holds an optional completion and a list of waiting fibers.
- **States over a run:** Unfulfilled with no waiters, owed with waiting takers, fulfilled with a value, and failed with a cause.
- **States to tell apart:** A reader distinguishes an unfulfilled obligation from a fulfilled result and a broken promise.

### 1.3 Fibers
- **What it is:** A concurrent execution path defined in `RunFiber` (`src/Effect4/Machine/Fibers.lean`, `docs/core/machine-state.md` §1). It holds a continuation stack, status flags, and an origin.
- **States over a run:** Running, child forked, queued as a task, parked on a token, resting on yield, interrupt held, finalizing, and exited.
- **States to tell apart:** A reader distinguishes an active running fiber from a suspended waiter, a yielding turn, a finalizing exit, and an exited fiber.

### 1.4 Frames
- **What it is:** A stack frame continuation defined in `Prim` and `FrameEvent` (`src/Effect4/Machine/Frames.lean`, `docs/core/machine-state.md` §1). It forms an execution hole that receives a child result.
- **States over a run:** Pushed as an empty hole, popped with a result value, and skipped during a failure walk.
- **States to tell apart:** A reader distinguishes an open hole awaiting a return value from a filled hole and a skipped frame.

### 1.5 Scopes and Finalizers
- **What it is:** A lifetime boundary defined in `Scope` (`src/Effect4/Machine/Scope.lean`, `docs/core/semantics.md` concept 3). It tracks registered cleanup actions.
- **States over a run:** Open with no actions, open with registered actions, closing while running actions in reverse order, and closed.
- **States to tell apart:** A reader distinguishes an open scope from a closed scope. A reader distinguishes a registered finalizer from an executed finalizer and a cancelled finalizer.

### 1.6 Resources and Handles
- **What it is:** An allocated capability handle defined in `HandleKind` (`src/Effect4/Machine/Value.lean`, `docs/core/host-boundary.md` §4). Handles index fibers, cells, promises, and scopes.
- **States over a run:** Allocated and referenced, updated in place, released, and stale.
- **States to tell apart:** A reader distinguishes an active valid handle from a released handle and a stale handle.

### 1.7 Stores and Cells
- **What it is:** A mutable storage cell defined in `RefHeap` (`src/Effect4/Machine/Stores.lean`, `src/Effect4/Laws/Machine/Arena.lean`, `docs/core/machine-state.md` §7). It belongs to a dense memory arena.
- **States over a run:** Allocated empty, holding a value, updating atomically, and deallocated.
- **States to tell apart:** A reader distinguishes an empty cell from an occupied cell and an updating cell.

### 1.8 Queues
- **What it is:** A FIFO buffer defined in `Queue` (`src/Effect4/Library/Queue/Defs.lean`, `tools/Tools/View/Tube/Queue.lean`). It implements backpressure, sliding, and dropping strategies.
- **States over a run:** Empty, holding items below capacity, full at capacity, backpressured with waiting offers, and starved with waiting takers.
- **States to tell apart:** A reader distinguishes available capacity from stored items, waiting takers, and blocked offers.

### 1.9 Semaphores and Pools
- **What it is:** A permit coordinator defined in `Semaphore` and `Pool` (`src/Effect4/Machine/Stores.lean`, decisions row 330). It regulates concurrent access to resources.
- **States over a run:** Permits or items available, permits acquired or items leased, queued waiters, and closing or drained.
- **States to tell apart:** A reader distinguishes available permit capacity from acquired permits and waiting consumers.

### 1.10 Streams and Channels
- **What it is:** A discrete sequence pipeline defined in `Stream` and `Channel` (`src/Effect4/Program/Stream.lean`, decisions rows 331, 335, 367). It models asynchronous consumption.
- **States over a run:** Idle, transmitting a chunk in flight, continuous flow progress, gathered into a collection, completed with leftover, and failed.
- **States to tell apart:** A reader distinguishes moving data chunks from backpressure halts, normal completion, and failure halts.

### 1.11 Failures and Causes
- **What it is:** An error condition defined in `Reason` (`src/Effect4/Machine/Cause.lean`), `CauseTerm` (`src/Effect4/Program/Eff.lean`), and `Cause` (`src/Effect4/Machine/Cause.lean`). It separates typed errors, untyped defects, and interrupts.
- **States over a run:** Raised as a typed error, raised as a defect, raised as an interrupt cause, and combined in an ordered cause list.
- **States to tell apart:** A reader distinguishes a typed failure from an untyped defect, an interrupt cause, and an ordered cause sequence.

### 1.12 Interrupts
- **What it is:** An external stop signal defined in `ActionTerm.interrupt` (`src/Effect4/Program/Eff.lean`) and `RunEvent.interruptRecorded` (`src/Effect4/Machine/Fibers.lean`, decisions rows 350, 368). It forces fiber termination.
- **States over a run:** In flight, deferred behind an uninterruptible mask, and delivered to stop execution.
- **States to tell apart:** A reader distinguishes an in-flight interrupt surge from a deferred interrupt and an arrested stop.

### 1.13 Host Calls and Replies
- **What it is:** An external protocol exchange defined in `HostSession` (`src/Effect4/Api/HostSession.lean`, `docs/core/host-boundary.md` §4). It crosses the machine boundary.
- **States over a run:** Request dispatched, pending host execution, reply received behind a valve, reply admitted and applied, and reply refused or stale retired.
- **States to tell apart:** A reader distinguishes an outgoing request from an awaiting host state, an admitted reply, and a refused reply.

### 1.14 Decisions and Frontiers
- **What it is:** A scheduler choice or execution boundary defined in `RunDecision` (`src/Effect4/Machine/Fibers.lean`), `FrontierReason`, and `Api.Outcome` (`src/Effect4/Api/Runner.lean`, `docs/core/machine-state.md` §3). It drives execution steps.
- **States over a run:** Active step decision on tape, live frontier suspension, and abnormal machine halt.
- **States to tell apart:** A reader distinguishes an active step from a waiting frontier and an abnormal halt.

### 1.15 Mapping of Objects to Contents States
This table maps each state of the fourteen runtime objects to its visual figure, contents state, entering machine event or move, and simplification.
It compares each mapping with section 4 of the motion plan (`docs/research/2026-10-13-motion-everywhere/README.md`).

| Object | State to Tell Apart | Figure (`Kind`, `Shape`) | Contents State | Machine Event or Move | Simplification | Motion Plan §4 Comparison | Visual Encoding |
| --- | --- | --- | --- | --- | --- | --- | --- |
| Values | Uncomputed slot | `vessel` (`hole`) | `empty` | `FrameEvent.pushed` (`src/Effect4/Machine/Frames.lean`) | none | Agrees with §4.3 | motion `grow`; empty vessel on frame chain awaits return value. |
| Values | Evaluated scalar literal | `body` (`atom`) | `full` | `Frame.current := .val v` (`src/Effect4/Machine/Frames.lean`) | none | Agrees with §2.4 | motion `keep`; solid ink denotes immutable scalar literal. |
| Values | Compound collection | `container` (`cells`) | `units` | `Frame.current := .val (.list xs)` (`src/Effect4/Machine/Frames.lean`) | none | Agrees with §4.1 | motion `carry`; discrete pills depict collection items. |
| Promises | Unfulfilled, no waiters | `vessel` (`hollowDot`) | `promised` | `deferredMakeOf` (`src/Effect4/Machine/Stores.lean`) | none | Agrees with §4.1 | motion `grow`; hollow bubble denotes unfulfilled promise. |
| Promises | Owed with waiters | `vessel` (`hollowBox`) | `promised` | `RunEvent.parkedOn` (`src/Effect4/Machine/Fibers.lean`) | omits waiter fiber IDs and tokens | Agrees with §4.1 | motion `grow`; vessel fed by pipe denotes blocked waiter. |
| Promises | Fulfilled with value | `vessel` (`filledDot`) | `promised to units` | `RunEvent.resumedWith` (`src/Effect4/Machine/Fibers.lean`) | none | Agrees with §4.1 | motion `keep`; hollow bubble contracts to solid unit in place. |
| Promises | Failed with cause | `vessel` (`hollowDot` + `cross`) | `failed` | `deferredFail` (`src/Effect4/Machine/Stores.lean`) | omits cause error payload | Agrees with §4.1 | motion `keep`; cross marks broken synchronization cell. |
| Fibers | Running turn | `cadence` (`enter`) | `units` | `RunEvent.started` (`src/Effect4/Machine/Fibers.lean`) | omits fiber continuation stack | Agrees with §4.1 | motion `carry`; unit on staff denotes active execution turn. |
| Fibers | Child forked | `bond` (`arrow`) | `units` | `RunEvent.forked` (`src/Effect4/Machine/Fibers.lean`) | omits daemon flag | Agrees with §4.1 | motion `grow`; descending arrow spawns child staff. |
| Fibers | Queued task | `vessel` (`hollowBox`) | `promised` | `RunEvent.scheduledTask` (`src/Effect4/Machine/Fibers.lean`) | omits task priority level | Agrees with §4.1 | motion `carry`; task waits in dispatcher queue line. |
| Fibers | Parked on token | `vessel` (`hollowBox`) | `promised` | `RunEvent.parkedOn` (`src/Effect4/Machine/Fibers.lean`) | omits park token number | Agrees with §4.1 | motion `grow`; hollow bubble holds fiber execution. |
| Fibers | Yielding turn | `wire` (`rest`) | `empty` | `RunEvent.yieldInjected` (`src/Effect4/Machine/Fibers.lean`) | omits atOp step index | Agrees with §4.1 | motion `parting`; conduit parted across yield beat. |
| Fibers | Interrupt deferred | `container` (`rail`) | `empty` | `RunEvent.interruptDeferred` (`src/Effect4/Machine/Fibers.lean`) | none | Agrees with §4.1 | motion `swell`; wall swell stands at start of double rail. |
| Fibers | Finalizing exit | `vessel` (`hollowDot`) | `promised to units` | `RunEvent.finalizerProgram` (`src/Effect4/Machine/Fibers.lean`) | omits nominal finalizer ID and exit value | Agrees with §4.1 | motion `keep`; finalizer bubbles keep in reverse order. |
| Fibers | Exited with value | `cadence` (`exitBar`) | `units` | `RunEvent.exited` (`src/Effect4/Machine/Fibers.lean`) | none | Agrees with §4.1 | motion `grow`; exit bar ends staff with success value. |
| Fibers | Exited with cause | `cadence` (`exitBar` + `reasons`) | `failed` | `RunEvent.exited` (`src/Effect4/Machine/Fibers.lean`) | omits cause structure and annotations | Agrees with §4.1 | motion `grow`; exit bar followed by ordered reasons. |
| Frames | Pushed open hole | `vessel` (`hole`) | `empty` | `FrameEvent.pushed` (`src/Effect4/Machine/Frames.lean`) | omits frame operator payload | Agrees with §4.1 | motion `grow`; empty vessel on frame chain awaits return value. |
| Frames | Popped with return | `vessel` (`hole`) | `empty to units` | `FrameEvent.popped` (`src/Effect4/Machine/Frames.lean`) | none | Agrees with §4.1 | motion `carry` then `shrink`; value enters hole before hole shrinks. |
| Frames | Skipped on failure walk | `vessel` (`hole`) | `failed` | `FrameEvent.ranContAll` (`src/Effect4/Machine/Frames.lean`) | omits passed frame primitive payload | Agrees with §4.1 | motion `carry`; failure cross passes through skipped hole. |
| Scopes | Scope open awaiting close | `container` (`openBracket`) | `open` | `scopeMake` (`src/Effect4/Machine/Scope.lean`) | omits parent scope pointer | Agrees with §4.1 | motion `grow`; single opening hook awaits closing hook. |
| Scopes | Finalizer registered | `vessel` (`hollowDot`) | `promised` | `RunEvent.scopeLinked` (`src/Effect4/Machine/Fibers.lean`) | omits finalizer registration key | Agrees with §4.1 | motion `grow`; sealed hollow bubble enclosed by bracket. |
| Scopes | Scope closed normally | `container` (`bracket`) | `promised to units` | `closeScope` (`src/Effect4/Machine/Scope.lean`) | none | Agrees with §4.1 | motion `grow` then `keep`; second hook completes bracket. |
| Scopes | Scope closed by failure | `container` (`bracket` + `reasons`) | `failed` | `closeScope` on failure (`src/Effect4/Machine/Scope.lean`) | omits cause composition tree | Agrees with §4.1 | motion `grow`; bracket encloses abnormal failure exit. |
| Resources | Active valid handle | `body` (`tag`) | `units` | `refMake` (`src/Effect4/Machine/Stores.lean`) | omits cell index Nat | Agrees with §4.1 | motion `none`; collar tag identifies valid capability. |
| Resources | Updating handle | `body` (`tag` collar) | `units` | `SyncOp.refModify` (`src/Effect4/Machine/Stores.lean`) | none | Agrees with §4.1 | motion `carry`; unit transits through collar during write. |
| Resources | Released handle | `body` (`tag` vacated) | `empty` | `FrameEvent.ranFinalizer` (`src/Effect4/Machine/Frames.lean`) | none | Agrees with §4.4 | motion `carry`; unit drains from handle tag. |
| Resources | Stale invalid handle | `none (internal); wire (relief exhaust, external)` | `empty` | `Refusal.staleCall` (`src/Effect4/Api/HostSession.lean`); none in machine for internal cells | omits refusal call record | Differs from §4.3 (settled by row 371 point 3) | motion `carry` to relief exhaust for external stale calls; no figure for internal cells (no machine event or refusal exists). |
| Stores | Allocated empty | `vessel` (`slot`) | `empty` | `refMake` unwritten (`src/Effect4/Machine/Stores.lean`) | none | Agrees with §2.1 | motion `grow`; empty shelf awaiting first written value. |
| Stores | Occupied cell | `body` (`tag` + value) | `units` | `refSet` (`src/Effect4/Machine/Stores.lean`) | none | Agrees with §4.1 | motion `carry`; discrete value pill resides in cell. |
| Stores | Updating atomically | `body` (`tag` collar) | `units` | `SyncOp.refModify` (`src/Effect4/Machine/Stores.lean`) | none | Agrees with §4.1 | motion `carry`; old unit exits and new unit enters in one beat. |
| Queues | Empty buffer | `vessel` (`Layout.vessel`) | `empty` | `Queue.bounded` (`src/Effect4/Library/Queue/Ops.lean`) | none | Agrees with §4.2 | motion `none`; vessel lumen holds ground tone. |
| Queues | Holding items | `vessel` (`Layout.vessel`) | `units` | `Queue.offer` (`src/Effect4/Library/Queue/Ops.lean`) | none | Agrees with §4.2 | motion `carry` with `swell`; discrete pills occupy slots. |
| Queues | Saturated at capacity | `vessel` (`Layout.vessel`) | `units` (packed) | `Queue.offer` at cap (`src/Effect4/Library/Queue/Ops.lean`) | none | Differs from proposal (settled by row 371 point 3) | motion `none`; packed units preserve discrete message counts. |
| Queues | Backpressured offers | `wire` (`Layout.inlet`) | `units` behind parting | `Queue.offer` blocked (`src/Effect4/Library/Queue/Ops.lean`) | omits waiting offer fiber IDs | Agrees with §4.2 | motion `carry` then `morph`; units form backwater behind closed valve. |
| Queues | Starved takers | `wire` (`Layout.outlet`) | `promised` | `Queue.take` waiting (`src/Effect4/Library/Queue/Ops.lean`) | omits waiting taker fiber IDs | Agrees with §4.2 | motion `grow`; hollow bubble waits at outlet nozzle. |
| Semaphores | Permits or items free | `wire` (circuit loop) | `units` | `Semaphore.release` / `Pool.make` (`src/Effect4/Library/Semaphore/Ops.lean`, `src/Effect4/Library/Pool/Ops.lean`) | none | Differs from proposal (settled by row 371 point 3) | motion `carry`; discrete permit pills circulate in closed loop. |
| Semaphores | Permits acquired / leased | `wire` (holder branch) | `units` | `Semaphore.take` / `Pool.use` (`src/Effect4/Library/Semaphore/Ops.lean`, `src/Effect4/Library/Pool/Ops.lean`) | none | Agrees with §4.2 | motion `carry`; unit translates from circuit to borrower staff. |
| Semaphores | Queued permit waiters | `wire` (inlet line) | `promised` | `Semaphore.take` waiting (`src/Effect4/Library/Semaphore/Ops.lean`) | omits waiting fiber IDs | Agrees with §4.2 | motion `grow`; hollow bubble waits before circuit valve. |
| Semaphores | Closing / drained pool | `wire` (circuit valve) | `units` to `promised` | `Pool.close` (`src/Effect4/Library/Pool/Ops.lean`) | none | Agrees with §4.2 | motion `parting` then `keep`; valve parts and finalizers run. |
| Streams | Idle opened pipeline | `wire` (`series`) | `empty` | `Source.opened` (`src/Effect4/Library/Stream/Source.lean`) | none | Agrees with §4.2 | motion `grow`; clear conduit with no units in transit. |
| Streams | Transmitting chunk | `wire` (`series`) | `units` | `Stream.drain` (`src/Effect4/Library/Stream/Ops.lean`) / `Source.pull` (`src/Effect4/Library/Stream/Source.lean`) | none | Agrees with §4.2 | motion `carry`; discrete pills travel along pipeline. |
| Streams | Continuous progress | `wire` (`series`) | `level` | `Stream.drain` continuous step (`src/Effect4/Library/Stream/Ops.lean`) | abstracts discrete pull elements into continuous level | Differs from §4.2 (settled by row 371 point 3) | motion `carry`; level indicates fractional progress. |
| Streams | Gathered items | `container` (`cells`) | `units` (coalesced) | `Effect4.Stream.collectGain` (`src/Effect4/Library/Stream/Model.lean`) | none | Agrees with §4.2 | motion `coalescence`; units fuse under fold summation. |
| Streams | Completed with leftover | `cadence` (`exitBar` + units) | `units` | `Cursor.finish` (`src/Effect4/Library/Stream/Model.lean`) | none | Agrees with §4.2 | motion `grow`; exit bar seals conduit with leftover items. |
| Streams | Failed stream | `wire` (`hash` or `cross`) | `failed` | `Pull.matchEffect` on error (`src/Effect4/Library/Pull/Ops.lean`) | omits cause payload | Agrees with §2.2 | motion `morph`; conduit severed by failure mark. |
| Failures | Raised typed error | `body` (`cross`) | `failed` | `Cause.fail` (`src/Effect4/Machine/Cause.lean`) | omits error value payload | Agrees with §4.1 | motion `keep`; diagonal cross marks typed error. |
| Failures | Raised untyped defect | `body` (`hash`) | `failed` | `Cause.die` (`src/Effect4/Machine/Cause.lean`) | omits defect value payload | Agrees with §4.1 | motion `keep`; sheared fracture marks unhandled defect. |
| Failures | Interrupt cause | `force` (`blockedArrow`) | `failed` | `Cause.interrupt` (`src/Effect4/Machine/Cause.lean`) | omits interruptor fiber ID | Differs from Q3 (settled by row 371 point 3) | motion `keep`; blocked arrow marks cancellation. |
| Failures | Combined cause sequence | `body` (`reasons`) | `failed` | `Cause.both` (`src/Effect4/Machine/Cause.lean`) | omits cause tree branching structure | Agrees with §4.1 | motion `keep`; ordered beads show cause composition. |
| Interrupts | In-flight recorded surge | `force` (`surgeOf`) | `empty` | `RunEvent.interruptRecorded` (`src/Effect4/Machine/Fibers.lean`) | omits interruptor fiber ID | Agrees with §4.1 | motion `swell`; pressure wave deflecting wall. |
| Interrupts | Deferred behind mask | `container` (`rail`) | `empty` | `RunEvent.interruptDeferred` (`src/Effect4/Machine/Fibers.lean`) | none | Agrees with §4.1 | motion `swell`; surge held at double rail boundary. |
| Interrupts | Delivered stop | `cadence` (`exitBar`) | `no lumen (strut)` | `RunEvent.exited` under interrupt (`src/Effect4/Machine/Fibers.lean`) | none | Agrees with §4.1 | motion `grow`; solid structural bar terminates fiber staff. |
| Host Calls | Request dispatched | `bond` (`port` outbound) | `units` | `HostSession.bindCall` (`src/Effect4/Api/HostSession.lean`) | omits call ID and native operation | Agrees with §4.3 | motion `carry`; unit exits canvas through outbound hairpin. |
| Host Calls | Pending host answer | `bond` (`port` inbound) | `promised` | `HostProtocol.State.awaitingAsync` (`src/Effect4/Api/HostProtocol.lean`) | omits guard token number | Agrees with §4.3 | motion `grow`; hollow receiver waits at port inlet. |
| Host Calls | Reply received at valve | `bond` (`port` mouth) | `units` | `HostSession.submit` (`src/Effect4/Api/HostSession.lean`) | omits call ID number | Agrees with §4.3 | motion `carry` then hard stop; unit stands behind valve. |
| Host Calls | Reply admitted and applied | `bond` (`port` inbound) | `promised to units` | `HostSession.applyReply` (`src/Effect4/Api/HostSession.lean`) | none | Agrees with §4.3 | motion `parting` then `keep`; valve fuses and promise keeps. |
| Host Calls | Reply refused / retired | `wire` (relief exhaust) | `units to empty` | `HostSession.retire` (`src/Effect4/Api/HostSession.lean`) | omits refusal reason constructor | Agrees with §4.3 | motion `carry`; unit drains through relief exhaust. |
| Decisions | Step decision on tape | `cadence` (`barLine`) | `no lumen (strut)` | `RunDecision.fire` (`src/Effect4/Machine/Fibers.lean`) | omits decision tape cursor index | Agrees with §4.1 | motion `grow`; thin solid strut carries no fluid. |
| Decisions | Live frontier suspension | `cadence` (`fermata`) | `promised` | `FrontierReason` (`src/Effect4/Api/Runner.lean`) | omits fuel deficit amount | Agrees with §4.1 | motion `grow`; fermata marks pause awaiting fuel or choice. |
| Decisions | Abnormal machine halt | `cadence` (`caesura`) | `failed` | `Stuck` marker (`src/Effect4/Machine/Fibers.lean`) | omits stuck identifier payload | Agrees with §4.1 | motion `grow`; caesura marks abnormal machine stoppage. |

---

## 2. The Contents States

The proposal in `tools/view/out/proto/fills.html` names seven states for body interiors.
In the dictionary (`docs/core/controlled-english.md` §3), a fill places a program at an address.
This document names what the lumen shows as its contents state.

### 2.0 Zero-Bore Marks Hold No Contents State
A cadence strut (`barLine`, stop bar) has zero bore (`THIN = 0`) and zero clearance.
It draws as solid structural ink (`Fill.ink`), but carries no lumen (`no lumen (strut)`).
Zero-bore marks hold no contents state.
They provide structural framing and time punctuation, distinct from fluid-carrying conduits.

```mermaid
flowchart LR
  Empty["empty (○ absent)"] --> Promised["promised (○ hollow)"]
  Promised --> Units["units (● filled)"]
  Units --> Full["full (● whole)"]
  Units --> Level["level (◐ half)"]
  Empty --> Open["open (◌ dashed in proposal; cut mouth in practice)"]
  Empty --> Failed["failed (× cross)"]
```

### 2.1 The Seven Contents States
1. **empty (○ absent):** The lumen holds ground tone. It signifies unoccupied space, an idle conduit, or free capacity. Sign class: Icon.
2. **units (● filled):** The lumen holds solid ink circles or pills. Each pill represents one discrete value or message. Sign class: Icon and Index.
3. **promised (○ hollow):** The lumen holds an ink rim enclosing ground tone. It represents an active obligation or waiting taker. Sign class: Symbol and Index.
4. **level (◐ half):** The lumen holds ink filling from one boundary to a continuous mark. It shows a continuous share or fractional progress. Sign class: Index.
5. **full (● whole):** The lumen holds solid ink throughout. It indicates an immutable literal, a saturated capacity, or a shut barrier. Sign class: Icon and Symbol.
6. **open (◌ dashed in proposal; cut mouth in practice):** The conduit boundary remains unsealed. It represents an unclosed scope or external host boundary. Sign class: Icon.
7. **failed (× cross):** The lumen contains an ink cross or shear mark. It represents an execution failure, defect, or broken promise. Sign class: Symbol.

### 2.2 Audit of the Proposal Family Table
The table in `tools/view/out/proto/fills.html` maps the seven contents states across the seven families of `tools/Tools/View/Glyph.lean`.
Every cell is audited below against the fourteen runtime objects.

| Contents State | Family | Proposal Text | Verdict | Semiotic Analysis and Correction |
| --- | --- | --- | --- | --- |
| `empty` | `body` | a box: a place for a value | Kept | Icon of empty evaluation container (`box`, `Shape.box`). |
| `empty` | `vessel` | free capacity: a slot not held | Kept | Icon of available storage capacity in queue or accumulator. |
| `empty` | `container` | every container: a membrane, its contents the figure | Kept | Container tubes have fine bores (`FINE = 4 px`); lumen is neutral envelope. |
| `empty` | `wire` | an idle wire | Kept | Passable conduit with no fluid in transit. |
| `empty` | `bond` | a tap not yet filled | Kept | Unlinked connection or uncalled callback tap. |
| `empty` | `force` | — | Kept | A force does not exist before its impulse is triggered. |
| `empty` | `cadence` | — | Kept | Cadence struts have zero bore (`THIN = 0`); they carry no lumen (`no lumen (strut)`). |
| `units` | `body` | a value | Kept | Discrete evaluated scalar or data unit in `value` (`Shape.value`). |
| `units` | `vessel` | held units, by count | Kept | Integer count of stored items inside queue vessel (`unitLen`). |
| `units` | `container` | — | Changed | Change to: held items in a data lane (`cells`, `Shape.cells`). |
| `units` | `wire` | values in flight | Kept | Kinetic transit of messages along process piping (`series`). |
| `units` | `bond` | a copy in each tap | Kept | Duplicated broadcast units in manifold takeoff taps (`spider`). |
| `units` | `force` | the surge's unit | Changed | Change to: —. A force is a shockwave, not a moving unit. |
| `units` | `cadence` | — | Kept | Cadences never transport fluid units. |
| `promised` | `body` | a value promised | Kept | Evaluated slot owed by a continuation. |
| `promised` | `vessel` | a waiting taker | Kept | Unresolved deferred or consumer demand bubble (`hollowBox`, `hollowDot`). |
| `promised` | `container` | — | Changed | Change to: unclosed scope with close owed (`openBracket`). |
| `promised` | `wire` | a demand travelling back | Kept | Upstream pull signal traveling against process direction. |
| `promised` | `bond` | a waiter on a completion | Kept | Awaiting subscriber registered on completion manifold. |
| `promised` | `force` | — | Kept | Interrupts are immediate impulses, not deferred promises. |
| `promised` | `cadence` | — | Changed | Change to: live frontier awaiting resolution (`fermata`). |
| `level` | `body` | — | Kept | A discrete body holds discrete scalar data, not partial fluid. |
| `level` | `vessel` | a measure: permits taken, a pool's share | Kept | High-capacity permit utilization where drawing individual pills is unreadable. |
| `level` | `container` | — | Kept | Container perimeters do not hold fill levels. |
| `level` | `wire` | a stream's progress | Kept | Fractional progress along an active transmission conduit. |
| `level` | `bond` | — | Kept | Relational bonds convey topological connections, not levels. |
| `level` | `force` | the surge's pressure | Dropped | Hydrostatic pressure is drawn by wall deflection (`SWELL`), not by lumen level. A swell is wall motion, and lumen remains empty. |
| `level` | `cadence` | — | Changed | Change to: timer countdown elapsed on staff line. |
| `full` | `body` | a literal, a constant | Kept | Immutable scalar value completely occupying lumen (`atom`). |
| `full` | `vessel` | full: at capacity, the valve shut | Kept | Maximum buffer capacity reached; float valve closes. |
| `full` | `container` | — | Kept | Jacketed casings do not fill solid. |
| `full` | `wire` | — | Changed | Change to: backwater lock behind closed valve. |
| `full` | `bond` | — | Kept | Cross-lane bridges do not hold stationary solid fills. |
| `full` | `force` | a stop (solid, an air gap short) | Changed | Change to: impact barrier. A stop is structural framing, not a full lumen. |
| `full` | `cadence` | a strut: thin and solid, it carries nothing | Changed | Clarify: Structural solid bar (`Fill.ink`), carrying zero bore (`THIN = 0`); holds no lumen (`no lumen (strut)`). |
| `open` | `body` | a value from the host | Changed | Change to: host-provided parameter socket. |
| `open` | `vessel` | a deferred not yet made | Changed | Change to: unsealed receiver socket (`hole`). |
| `open` | `container` | a scope still open | Kept | Open bracket awaiting second closing hook (`openBracket`). |
| `open` | `wire` | a wire to the world | Kept | Conduit with square cut end crossing canvas boundary (`OFF`). |
| `open` | `bond` | a port | Kept | Bulkhead penetration looping into external environment (`port`). |
| `open` | `force` | — | Kept | An interrupt does not hold an open state. |
| `open` | `cadence` | — | Kept | Temporal punctuation markers remain closed and intact. |
| `failed` | `body` | a failure on its wire | Kept | Typed failure mark × (`cross`) or defect mark # (`hash`). |
| `failed` | `vessel` | a promise broken | Kept | Vessel holding a rejected completion cause. |
| `failed` | `container` | a scope closed by failure | Kept | Scope bracket bounding an abnormal exit. |
| `failed` | `wire` | a defect | Kept | Conduit fractured by sheared break (`hash`). |
| `failed` | `bond` | — | Changed | Change to: severed fork link or cancelled race entrant. |
| `failed` | `force` | an interrupt | Changed | Change to: unhandled interrupt cause deposited at boundary. |
| `failed` | `cadence` | — | Changed | Change to: abnormal machine halt on untyped state (`caesura`). |

---

## 3. Consistency

A semiotic notation prevents symbol overload and symbol redundancy.
One visual contents state must not signify conflicting concepts.
One runtime state must not require conflicting contents states.

```mermaid
classDiagram
  class SemioticRule {
    +fillMeaning(fill, family)
    +stateFill(object, state)
  }
  class NoOverload {
    One contents state has one meaning per family
  }
  class NoRedundancy {
    One semantic state has one representation
  }
  SemioticRule <|-- NoOverload
  SemioticRule <|-- NoRedundancy
```

### 3.1 Resolving Overloads (One Contents State with Multiple Meanings)
1. **Solid Ink: Literal versus Structural Strut**
   - *Conflict:* Solid ink currently represents both an immutable scalar literal (`atom`) and a cadence strut (`barLine`).
   - *Rule:* A literal fills a non-zero lumen (`PIPE = 10 px`). A cadence strut has zero bore (`THIN = 0`) and zero clearance. The pen draws it as a 10 px solid structural bar (`Fill.ink`), distinct from fluid-filled conduits. It carries no lumen (`no lumen (strut)`).

2. **Full Lumen: Constant Value versus Queue Backpressure Lock**
   - *Conflict:* A solid lumen denotes an immutable constant in `body`, but saturated backwater in `wire`.
   - *Rule:* In process conduits, backwater is drawn as discrete packed pills touching menisci (`unitOf`). Only atomic literals without internal structure take solid full ink lumens.

3. **Open Mark: Broken Line versus Missing Cap**
   - *Conflict:* The proposal suggests dashed lines for open states, conflicting with cut conduit mouths.
   - *Rule:* The pen never draws openness with dashed line strokes. Openness is drawn as an unsealed conduit mouth with a cut square end (`round := false`) or an unclosed hook (`openBracket`).

4. **Failure: Blocked Plug versus Error Cross**
   - *Conflict:* Drawing an error as an obstructing plug confuses normal backpressure with fatal failure.
   - *Rule:* An air-gap plug indicates normal control stoppage (`plugOf`). A failure must feature an explicit cross (×) or sheared fracture (#).

### 3.2 Resolving Redundancies (One Meaning with Multiple Representations)
1. **Unfulfilled Obligations**
   - *Conflict:* A waiting promise is drawn as a hollow dot (`hollowDot`) or a hollow box (`hollowBox`).
   - *Rule:* Both marks use the exact same fill: an ink rim around a ground lumen (`hollowOf`, `RIM = 2 px`). Their external casing geometry conveys whether the promise is sealed (`Dot`) or fed by a pipe (`Box`).

2. **Defect versus Typed Failure**
   - *Conflict:* Both typed failure and defect represent error states.
   - *Rule:* Typed failure uses the diagonal 4-way cross fitting (`cross`, ×). Untyped defect uses the sheared fractured conduit (`hash`, #). Both keep ground lumens obstructed by ink marks.

---

## 4. Change as Motion

State transitions in the visual language must correspond to lawful physical movements.
All animations occur in response to discrete machine commands or host decisions (decisions row 354 point 5).
Transitions are staged in causal order, using the kit's spring (`settle`, omega = 7.4 in `tools/Tools/View/Tube/Draw.lean`).

```mermaid
sequenceDiagram
  autonumber
  participant Machine as Machine Command
  participant Casing as Conduit Casing
  participant Lumen as Lumen Fill
  Machine->>Casing: 1. Actuate Valve / Open Spool (0ms - 180ms, OPENING = 180)
  Machine->>Lumen: 2. Kinetic Flow / Fill Transition (180ms - 560ms, IMPACT = 560)
  Machine->>Casing: 3. Impact and Critically Damped Settling (560ms - 1000ms, settle)
```

The phase boundaries map to declarations in `tools/Tools/View/Tube/Queue.lean` and `tools/Tools/View/Tube/Draw.lean`:
- **Phase 1 (0 to 180 ms):** The inlet valve actuates (`OPENING = 180` in `tools/Tools/View/Tube/Queue.lean`).
- **Phase 2 (180 to 560 ms):** Kinetic transit along the inlet conduit until impact (`IMPACT = 560` in `tools/Tools/View/Tube/Queue.lean`).
- **Phase 3 (560 to 1000 ms):** The unit arrests at the shut valve. The inlet span deflects and settles under the critically damped spring (`settle`, omega = 7.4 in `tools/Tools/View/Tube/Draw.lean`).

### 4.1 The Nine Motion Primitives
The motion plan (`docs/research/2026-10-13-motion-everywhere/README.md` §4) defines nine motion primitives.
Each primitive maps to a current declaration in the tree or a planned kit slice:

| Motion | What Moves | Declaration Today | Planned in Kit |
| --- | --- | --- | --- |
| `grow` | A tube from its root to its length, in length and width at once. | `GlyphPage.hidden` (`tools/Tools/View/Tube/GlyphPage.lean`) | `Tube.root` (slice S23) |
| `shrink` | A tube back to its root. | `GlyphPage.hidden` reversed (`tools/Tools/View/Tube/GlyphPage.lean`) | `Tube.root` (slice S23) |
| `morph` | A kept tube's pieces by the intrinsic mix, through a pose where given. | `Stroke.bend` (`tools/Tools/View/Tube/Motion.lean`), proved by theorem `bend_ok` (`tools/Tools/View/Tube/Glyphs.lean`) | `Change.bend` (slice S23) |
| `carry` | A unit along a line of tubes, governed by the unit law. | `Picture.carry` (`tools/Tools/View/Tube/Motion.lean`), `Law.carries` (`tools/Tools/View/Tube/Physics.lean`) | Stays in Effect4 |
| `swell` | A body's width round a carried unit, or round a pressure surge. | `swellOf` (`tools/Tools/View/Tube/Motion.lean`), `surgeOf` (`tools/Tools/View/Tube/Glyphs.lean`) | `Change.swell` (slice S23), `Join.bulb` (slice S24) |
| `parting` | An air gap that opens in a body, or closes and fuses its ends. | `plugOf` (`tools/Tools/View/Tube/Draw.lean`), `partCubics` (`tools/Tools/View/Tube/Outline.lean`) | `Tube.parting` (slice S23) |
| `blend` | A junction's notch, closed by a G2 corner or a rolling ball. | `crotch`, `fork` (`tools/Tools/View/Tube/Outline.lean`) | `Notch.blendIn`, `Join.fork`, `Join.wye` (slice S24) |
| `coalescence` | Two units that fuse into one of their joint area. | None today | `Coalesce.film`, neck grows as square root of time (slice S24) |
| `keep` | A promise kept: a hollow's inside leaves, and its rim stays as the unit. | `hollowAt` (`tools/Tools/View/Tube/Glyphs.lean`) | Stays in Effect4 |

### 4.2 State Transitions and Their Motions

#### 4.2.1 Promise Kept
- **Motion:** `keep`.
- **Implementation:** `hollowAt` (`tools/Tools/View/Tube/Glyphs.lean`).
- **Mechanism:** The inner ground circle (`hollowOf:in`) leaves the picture while the outer rim remains as the unit (`unitAt`).
- **Evidence:** Construction: bistable fulfillment. The transition keeps the outer boundary intact while removing the hollow interior (`hollowAt`, `tools/Tools/View/Tube/Glyphs.lean`).

#### 4.2.2 Scope Closed
- **Motion:** `grow` then `keep`.
- **Implementation:** `GlyphPage.hidden` (`tools/Tools/View/Tube/GlyphPage.lean`) and `containerFigure.bracket` (`tools/Tools/View/Tube/Glyphs.lean`).
- **Mechanism:** The second hook (`bracket:b`) extrudes from its anchor to complete the bracket. Registered finalizer hollows then keep in reverse registration order.
- **Evidence:** Construction: enclosure keeping: the scope remains closed while finalizers discharge.

#### 4.2.3 Failure Raised
- **Motion:** `morph` and `swell`.
- **Implementation:** `Stroke.bend` (`tools/Tools/View/Tube/Motion.lean`) and `surgeOf` (`tools/Tools/View/Tube/Glyphs.lean`).
- **Mechanism:** The conduit fractures into a sheared break (`SHEAR = 23066` in `bodyFigure.hash`, `tools/Tools/View/Tube/Glyphs.lean`) or deposits an ink cross (`bodyFigure.cross`). Arrest creates a reverse pressure surge via `surgeOf`.
- **Evidence:** Theorem: `bend_ok` (`tools/Tools/View/Tube/Glyphs.lean`) proves that every mixed pose satisfies the bend law.

#### 4.2.4 Resource Released
- **Motion:** `carry`.
- **Implementation:** `Law.carries` (`tools/Tools/View/Tube/Physics.lean`).
- **Mechanism:** The solid fluid pill translates downstream through the discharge port and leaves the canvas.
- **Evidence:** Construction: `Law.shape` (`tools/Tools/View/Tube/Physics.lean`) preserves pill area `c · len + PI_M · c² / 4000000` by construction using integer square roots, verified by guards.

#### 4.2.5 Unit Taken from Queue
- **Motion:** `carry`.
- **Implementation:** `Law.run` and `Law.stepAll` (`tools/Tools/View/Tube/Physics.lean`).
- **Mechanism:** Units move by the Intelligent Driver Model (`Physics.Law.accel`), not by a fixed uniform stagger. The head unit departs, and trailing units accelerate based on the headway to the unit ahead. Initial start delays use `STAGGER = 70` (`tools/Tools/View/Tube/Queue.lean`).
- **Evidence:** Construction: kinematic wave propagation: each following unit accelerates only after the lead unit leaves sufficient headway (`Law.least = 2000` in `tools/Tools/View/Tube/Physics.lean`).

#### 4.2.6 Unit Offered to Full Queue
- **Motion:** `carry` followed by hard stop and span deflection.
- **Implementation:** `Queue.picture` and `Layout.inletAt` (`tools/Tools/View/Tube/Queue.lean`).
- **Mechanism:** An incoming unit arrives at a closed float valve, stopping hard at `IMPACT = 560` (`tools/Tools/View/Tube/Queue.lean`). The inlet span sags under backlog weight, overshooting its rest pose by `OVERSHOOT = 35` per cent (`tools/Tools/View/Tube/Queue.lean`).
- **Evidence:** Construction: clamped span deflection. `Layout.inletAt` sags in three arcs with slope proportional to backlog (`slope n`, `tools/Tools/View/Tube/Queue.lean`).

#### 4.2.7 Units Merged under Aggregation
- **Motion:** `coalescence`.
- **Implementation:** Planned in kit slice S24 (`Coalesce.film`).
- **Mechanism:** Two units meet and fuse into one unit whose area equals their sum (`Law.shape`). The neck between drops grows as the square root of time sampled at `keyTimes`.
- **Evidence:** Construction: area conservation: the merged pill keeps the exact sum of the input units' areas by construction.

---

## 5. Unity of the Design Language

The visual system spans three media:
1. Tube figures in the view tool (`tools/Tools/View/Tube/`).
2. Tree and graph figures in the docs (`docs/core/`, generated site).
3. Status glyphs in text and tables (decisions row 354 point 2: ● ◐ ○ ◌ ×).

```mermaid
flowchart TD
  subgraph SharedRules ["Shared Invariant Rules"]
    Tones["Two Tones Only: Ink and Ground"]
    Shapes["Shape-Based Semantics: ● ◐ ○ ◌ ×"]
    NoNoise["Smooth Outlines, Zero Default Noise"]
    NoColor["Zero Arbitrary Hues; Hue Reserved for 4 Agents"]
  end
  SharedRules --> Tubes["Tube Figures (Hydraulics)"]
  SharedRules --> Graphs["Docs Graphs (Topology)"]
  SharedRules --> Status["Status Marks (Evidence)"]
```

### 5.1 Where They Share Rules
- **Two Tones Alone:** All three media use ink (`--e4-color-ink`) and ground (`--e4-color-ground`). No greys or gradients appear.
- **Status Alignment:** Decisions row 354 point 2 rules status by shape in the promise-and-keeping family:
  - Proved: filled (●).
  - Modulo: half filled (◐).
  - A planned goal: hollow (○).
  - Open: a dashed outline (◌).
  - Refuted: the cross (×).
- **Geometric Rigor:** Straight runs align to whole pixels (`crisp`, `onPixel`). Bends follow fixed minimum radii (`BEND = 24 px`).
- **Hue Restriction:** Hue is strictly forbidden for status or meaning. Hue belongs exclusively to the four agents (machine, host, failure, resource).

### 5.2 Where They Differ on Purpose
- **Topological Continuity:** Tube figures enforce continuous fluid conduits with physical walls and clearances. Graph figures use thin abstract connection rules.
- **Text Placement:** Graph figures place text labels inside nodes. Tube figures never place text inside fluid conduits. Typography stands strictly outside casings or on collar tags (`tag`).
- **Proportions:** Tubes use the radio-button proportion 2 : 3 : 10 (`LINE`, `MARGIN`, `UNIT`). Graph figures use 1 px structural dividers.
- **Motion Physics:** Tube motion models fluid dynamics, mass balance, and beam deflection. Graph diagrams animate by simple node translation and edge reveal.

### 5.3 The Documentation Node as a Contents State
The motion plan (`docs/research/2026-10-13-motion-everywhere/README.md` §5.2, §8 question 7) proposes this.
Decisions row 371 point 1 rules that a docs node shows its status as a contents state in a small vessel.

1. **Unification into One Sign:**
   A small vessel (`vesselFigure.sealed`, `tools/Tools/View/Tube/Glyphs.lean`) beside a node unifies evidence status marks and contents states into one sign:
   - Proved becomes a solid unit (●) in the vessel.
   - Modulo becomes a level fill (◐) in the vessel.
   - A planned goal becomes a hollow promise (○) in the vessel.
   - Open becomes an unsealed cut mouth or open hook (◌ / `openBracket`).
   - Refuted becomes a failure cross (×) in the vessel.

2. **Potential Symbol Overload:**
   This unification introduces three potential symbol overloads:
   - *Operational state versus proof status:* A reader might mistake proof status for runtime status on active constructs. The status text ("proved", "modulo", "goal", "open", "refuted") stands beside the vessel. Proof vessels appear strictly on documentation graph nodes.
   - *Modulo versus continuous progress:* Level fill (◐) represents continuous stream progress in runtime conduits, but represents "proved modulo goals" in proof nodes. The text word "modulo" prevents conflation.
   - *Refuted versus runtime failure:* The cross (×) represents runtime error in operational piping, but counterexample refutation in proof nodes. The text word "refuted" prevents conflation.

---

## 6. Recommendations for the Design Questions

The proposal in `tools/view/out/proto/fills.html` asks four design questions.
Here are the recommendations grounded in semiotics, runtime semantics, and the decisions register.

### 6.1 Question 1: Full versus Strut
- **Proposal Question:** Today a thin strut is solid ink and carries nothing. A full lumen would mean a literal. Keep both, told apart by width, or give the strut a ground lumen?
- **Recommendation:** Keep both, told apart by width and structure.
- **Reason:** A strut represents structural punctuation (measure bars, final exit gates, barrier stops). It has zero bore (`THIN = 0`), giving a solid 10 px bar (`body THIN = 10 px`). Giving the strut a ground lumen would turn it into a passable hollow pipe. That would invite category confusion between time framing and process conduits. A full lumen occurs only in conduits with non-zero bore (`PIPE`, `VESSEL`), representing an evaluated literal or saturated vessel.

### 6.2 Question 2: Level versus Units
- **Proposal Question:** Is a level (continuous) worth having beside counted units? It suits a semaphore's permits, a pool's share and a stream's progress.
- **Recommendation:** Retain `level` strictly for continuous fractional progress and large populations. Retain `units` for all discrete runtime queues.
- **Reason:** Effect4 execution steps in discrete whole commands (README.md §5, decisions row 369). Semaphore permits, queue capacities, and memory cells are discrete natural numbers. Drawing a continuous fluid level for small counts destroys integer exactness (`AREA = 120 px²`). Level is justified only for continuous progress bars (streams, timer elapsed fractions) or high-capacity connection pools where discrete pills cannot fit.

### 6.3 Question 3: Open as a Dashed Line (Row 354 and Row 371 Ruling)
- **The Conflict:** Decisions row 354 point 2 explicitly rules status "open" as a dashed outline (◌). Conversely, section 6.3 of round two and decisions row 370 point 3 refuse dashed outlines on solid tube bodies.
- **The Two Answers:**
  1. *Tubes follow the docs' dashed mark:* Tubes adopt dashed outlines when depicting open boundaries or host sockets.
     *Cost:* Breaks the solid tube casing model (row 370 point 1). Creates rendering artifacts and broken seams at filleted elbows and crotches. Requires complex dash-array mathematics along offset cubic curves.
  2. *Docs keep ◌ and tubes draw open by a square cut end on purpose:* Documentation graph nodes use ◌ (dashed circle) for textual status. Hydraulic tube figures draw openness indexically by an unsealed cut mouth (`OFF`, `port`) or an unclosed hook (`openBracket`).
     *Cost:* Retains two distinct signs for openness across different media (symbolic dashed circle in topology versus indexical cut mouth in hydraulic tubes).
- **Recommendation:** Adopt Answer 2. Tubes keep solid casings and draw open by square cut ends and open hooks. Docs graphs keep ◌.
- **Ruling:** The owner ruled in decisions row 371 point 2. The documentation status mark keeps row 354 point 2's dashed outline. A tube draws open by a cut end or an open hook, never by a dashed line.

### 6.4 Question 4: Failure
- **Proposal Question:** A cross in the lumen, or a plug across it with an air gap (as the force family's stop)?
- **Recommendation:** Retain the explicit cross (×) or sheared fracture (#) in the lumen. Never replace failure with an air gap plug.
- **Reason:** An air gap plug signifies normal flow stoppage, such as backpressure behind a closed float valve (`plugOf`). A failure is an abnormal or fatal error condition. Collapsing failure into an air gap conflates a paused queue with a crashed fiber. The cross directly aligns with the docs' status mark × (decisions row 354 point 2).

---

## 7. Settled Decisions for the Owner

The owner ruled on 2026-10-13 in decisions row 371.
The questions of rounds two and three take their rulings as follows:

1. **Saturated Queue Under Backpressure:**
   A saturated queue keeps packed units (`units`), keeping discrete message identities and integer accounting (decisions row 371 point 3).
2. **Resource Pool Permit Representation:**
   A resource pool renders discrete permit pills on a closed circuit (`units`). This keeps natural number capacity without switching to continuous fill levels (decisions row 371 point 3).
3. **Cancelled Fiber Conduit:**
   A cancelled fiber takes a pressure surge and terminates with the blocked arrow (`blockedArrow`, ⊣). This distinguishes interruption from typed errors and defects (decisions row 371 point 3).
4. **Unclosed Scope Hook Boundary:**
   An unclosed scope hook receives no terminal flange. The plain open hook (`openBracket`) conveys that a close is owed (decisions row 371 point 3).
5. **Open Boundary Representation:**
   Documentation graph nodes keep row 354 point 2's dashed outline (◌). Tube figures draw open states with a cut square mouth or an open hook, never a dashed line (decisions row 371 point 2).
6. **Proof Status Vessels on Documentation Nodes:**
   A docs node displays evidence status as a contents state in a small vessel beside its status word. Runtime vessels in operational tubes never display proof status metadata (decisions row 371 points 1 and 3).
7. **Stream Transmission Progress:**
   Continuous progress meters use a level fill (`level`). Discrete chunked stream pulls use unit pills (`units`, decisions row 371 point 3).
