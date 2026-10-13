# Visual Semantics Review: Vocabulary of Marks and Motion Physics

This document reviews the thirty marks of Effect4.
It classifies each mark by physical kind and provides motion grammars.
It delivers proposals for marks that fail semiotic clarity or physical congruence.

## The Five Findings That Matter Most

1. **The direction of causality is inverted in `arrow`.**
The fork arrow currently points northeast from bottom-left to top-right.
Parent fiber lanes sit above child lanes in allocation order.
Time moves from left to right across the score.
A fork arrow that ascends into the past contradicts the reading order.
The arrow must descend southeastward from parent lane to child lane.

2. **`CauseTerm.both` commits a category error by using `series`.**
The mark `series` depicts two operational program boxes linked by a wire.
The design language establishes that a cause is a flat list of reasons.
A cause is never an execution graph or a syntactic tree.
Drawing `CauseTerm.both` as `series` misrepresents list combination as sequential program execution.
Cause combination must be drawn as list aggregation rather than sequential bind.

3. **`ScopeState` collapses all five lifecycle states into `bracket`.**
The constructors `empty`, `openEmpty`, `openInline`, `openMap`, and `closed` share the identical glyph `bracket`.
A closed scope holds an immutable exit value and is sealed.
An open scope holds active finalizers and owes a closing execution.
An empty scope holds no finalizers.
Collapsing all five states into one static mark hides the scope state machine.

4. **`Eff.service` is falsely conflated with `port`.**
The mark `port` represents the row protocol across the host boundary.
`Eff.service` reads a capability from the fiber's ambient typed context.
It executes no external request and awaits no host reply.
Drawing `Eff.service` as `port` misleads the reader into seeing an external communication.
Context lookup belongs to the environment container rather than protocol ports.

5. **Key marks collapse or mislead at small scales.**
The mark `probe` uses a desktop search magnifying glass rather than an instrumentation test point.
The marks `call` and `library` crowd 1.5-pixel strokes within 3 pixels of borders, blurring at 16 pixels.
The mark `enter` is drawn hollow in `Shape.parts`, contradicting its role as a committed loop entry event.
The mark `rest` uses a 1-pixel dash that vanishes at 12 pixels.
Each mark must survive 12-pixel monochrome rendering without distortion.

---

## Part A: Review of the Thirty Marks

| Mark | Transparency | Confused With | Rows That Do Not Fit | Verdict | Reason |
| --- | --- | --- | --- | --- | --- |
| `box` | High. Borrows standard flowchart and process box conventions. | `call`, `library`, `bracket` at 12 pixels. | None. Fits single-step computations. | Keep | The basic process box is clear and stable. |
| `value` | High. Borrows string-diagram output token convention. | None. The wire-and-terminal dot is distinct. | None. Fits values on the success wire. | Keep | The token on the wire reads unambiguously. |
| `series` | Moderate. Two boxes with a connecting wire resemble dumbbells. | `parallel`, `box` at low resolution. | `CauseTerm.both` does not fit. Cause combination is not sequential execution. | Adjust | Add a forward flow chevron and reassign `CauseTerm.both`. |
| `parallel` | Moderate. Stacked rectangular slabs look heavy and static. | `series`, `rail`, `bracket` at 12 pixels. | None. Fits concurrent layer merge. | Adjust | Draw as parallel conduit wires with alignment guides. |
| `block` | High. Borrows typographic convention for text lines inside code. | `box`, `library` at 12 pixels. | None. Fits statement block generation. | Keep | The code block metaphor is immediately recognizable. |
| `alternative` | Moderate. Dashed lower arm incorrectly suggests that the second arm is subordinate. | `rest`, `loop` at 12 pixels. | `Stmt.ifElse` and `Eff.matchCause` have two primary arms. | Adjust | Draw symmetric solid arms for coordinate alternatives. |
| `loop` | High. Borrows circular flow return arrow. | None. The curved return contour is unique. | None. Fits iteration and loops. | Keep | The return loop arrow is universally understood. |
| `region` | Moderate. Dashed rounded rectangle looks like a faint process box. | `box`, `hole` at 12 pixels. | None. Fits environment providers. | Adjust | Draw corner bounds `⌜ ⌟` matching text glyph. |
| `bracket` | High for syntax, low for lifecycle. Borrows square brackets. | `hollowBox`, `call` at 12 pixels. | `ScopeState.closed` does not fit an open enclosure. | Adjust | Widen hooks and distinguish open versus closed states. |
| `rail` | High. Borrows railway double-track convention for protected corridors. | `parallel` at 12 pixels. | `Eff.restore` restores state rather than defining a span. | Keep | The double rail barrier is authoritative. |
| `arrow` | Low. Points northeast into the past and upward. | `enter` at 12 pixels. | All fork rows. Forks descend to child lanes. | Redraw | Direct arrow southeastward from parent to child lane. |
| `blockedArrow` | High. Borrows Talmy's force-dynamic Antagonist barrier `⊣`. | `barLine` if horizontal stroke is lost. | None. Fits interrupt commands and reasons. | Keep | The blocked arrow clearly conveys interruption force. |
| `spider` | Moderate. Frobenius spider has inputs on left and outputs on right. | `value` at 12 pixels. | None. Fits one-to-many completion wakes. | Adjust | Place completion input on left and waiter legs on right. |
| `rest` | Low. The 1-pixel dash vanishes at 12 pixels. | `rail`, empty space at small scales. | None. Fits fiber yield. | Adjust | Use distinct dash spacing with a centered rest block. |
| `hollowBox` | High. Hollow square indicates an unfilled promise. | `bracket` at 12 pixels. | None. Fits park tokens and queued tasks. | Keep | Part of the core promise-and-keeping pair. |
| `filledBox` | High. Filled square indicates a kept event. | Solid glyphs at 12 pixels. | None. Fits resume tokens and ran tasks. | Keep | Part of the core promise-and-keeping pair. |
| `hollowDot` | High. Hollow circle indicates registered promise. | `hole` at 12 pixels. | `Eff.onExit` is an enclosing program wrapper. | Keep | Clean registration mark; re-examine `Eff.onExit` assignment. |
| `filledDot` | High. Filled circle indicates fulfilled action. | Terminal dot of `value`. | None. Fits executed finalizers. | Keep | Completes the hollowDot promise pair. |
| `port` | Moderate. Line and arc look disconnected. | Stray punctuation at 12 pixels. | `Eff.service` reads context rather than external ports. | Adjust | Draw mated plug-socket pin and reassign `Eff.service`. |
| `probe` | Low. Magnifying glass is a consumer search metaphor. | None, but conveys text search. | `ActionTerm.context` is ambient context access. | Redraw | Replace with instrumentation test point reticle matching `⌕`. |
| `call` | Moderate. Flowchart subroutine bars blur into borders at 12 pixels. | `box`, `bracket` at 12 pixels. | `LayerTerm.ref` is a shared reference, not a call. | Adjust | Widen sidebar margins to prevent stroke fusion. |
| `library` | Moderate. Asymmetric L-bracket looks like a broken border. | `block`, `box` at 12 pixels. | None. Fits definition blocks. | Redraw | Draw clean double-offset rounded module cards. |
| `cross` | High. Universal error cross `×`. | `hash` if strokes blur. | None. Fits typed failures. | Keep | Universal typed error convention. |
| `hash` | High. Typographic octothorpe `#` for untyped defect. | `cross` at 12 pixels. | None. Fits defects. | Keep | Distinct from typed failures. |
| `exitBar` | High. Musical final bar line `‖`. | `barLine` in monochrome print. | None. Fits terminal exits and completion. | Keep | Standard conclusion of a musical movement. |
| `hole` | Moderate. Circle clashes with rectangular operation boxes. | `hollowDot` at 12 pixels. | None. Fits continuation frames. | Adjust | Draw as dashed rectangular receptacle matching box syntax. |
| `enter` | Moderate. Hollow triangle suggests uncommitted state. | `arrow` at 12 pixels. | None. Fits fiber loop entry. | Adjust | Fill triangle solid `▶` matching design language. |
| `barLine` | High. Musical measure bar line across staves. | `exitBar` in monochrome. | Overloaded across all decisions without distinction. | Keep | Serves as structural measure boundary on score. |
| `fermata` | High. Musical fermata `𝄐` for live pause. | None. Unique silhouette. | None. Fits live frontiers awaiting host answers. | Keep | Musical metaphor perfectly models held live state. |
| `caesura` | High. Musical caesura `//` for abrupt pause. | None. Clean parallel slash marks. | None. Fits machine halt on untyped state. | Keep | Authoritative stoppage glyph. |

---

## Part B: Behaviour and Imagined Physics

### 1. The Seven Physical Kinds

The visual semantics grounds marks in seven physical kinds:

1. **Body**: An entity with mass, identity, and spatial position.
It persists across steps and moves along continuous trajectories.
Examples: `value`, `enter`, `probe`.
2. **Vessel**: A bistable state carrier governed by promise and fulfillment.
It is hollow when promised and filled when kept.
Examples: `hollowBox`, `filledBox`, `hollowDot`, `filledDot`, `hole`.
3. **Container**: A spatial enclosure bounding scopes, regions, or environments.
It establishes boundaries that must open, enclose, and close.
Examples: `box`, `block`, `region`, `bracket`, `rail`, `library`, `call`.
4. **Wire**: A conduit transmitting continuous execution flow or data.
It routes values and establishes causal sequences.
Examples: `series`, `parallel`, `loop`, `alternative`, `rest`.
5. **Bond**: A topological junction relating multiple concurrent lifelines.
It forms directed bridges across fibers and staves.
Examples: `arrow`, `spider`, `port`.
6. **Force**: A transient directed impact that acts upon an Agonist and is spent.
It delivers an impulse, deposits a reason, and ceases kinetic travel.
Examples: `blockedArrow`, `cross`, `hash`.
7. **Cadence**: A stationary temporal boundary or holding mark on the score.
It cuts the runtime wire and organizes logical beats.
Examples: `barLine`, `exitBar`, `fermata`, `caesura`.

#### Theoretical Justification
- **Talmy's Force Dynamics**: Differentiates Agonist entities in motion (`Body`, `Wire`) from Antagonist vectors (`Force`), barriers (`Container`, `rail`), and releases (`Vessel`).
- **Tversky's Congruence Principle**: Graphic structures must correspond directly to mental models. Containment models scopes, conduits model flow, vectors model interrupts.
- **Heer and Robertson's Staged Transitions**: Separates layout transitions into discrete semantic phases. Maintains object constancy across steps.
- **Lasseter's Physical Principles**: Entities with mass follow arcs and settle without artificial overshoot (`settle` critically damped, ω = 7.4).
- **Bertin's Visual Variables**: Maps position to reading order and lanes, shape to physical kind, value to state progression, and hue strictly to agents.

---

### 2. Motion Grammar in Four Primitives

Every animated transition is expressed via four first-order CSS primitives: `translate`, `scale`, `clip-path: inset`, and `opacity`.

| Kind | Enters | Changes | Leaves |
| --- | --- | --- | --- |
| **Body** | Scales up from center (`scale(0)` to `scale(1)`) or translates from emitting node. | Translates along a shallow arc with critically damped settling (`settle`). | Translates into target receptacle or scales to zero upon consumption. |
| **Vessel** | Outer boundary appears via clip inset; fill opacity is zero. | Fulfills by transitioning fill opacity from 0% to 100% while boundary remains invariant. | Collapses inward via scaling about center or fades to zero opacity. |
| **Container** | Reveals via directional clip inset opening along flow from leading edge. | Scales along axes about anchor point to accommodate internal contents; borders transition. | Contracts via clip inset toward trailing edge or fades boundary opacity. |
| **Wire** | Reveals along transmission direction via expanding clip inset (`inset(0 100% 0 0)` to `inset(0)`). | Displays opacity pulse along path segment during active data transfer. | Clips out along flow direction following tail or fades opacity. |
| **Bond** | Central node establishes via scale; connecting legs extend via directional clip inset. | Connecting legs transition fill state as endpoints finish and arrive. | Dissolves connecting legs via opacity fade when relation concludes. |
| **Force** | Translates rapidly along vector toward target coordinate. | Impacts boundary with settling compression, deposits reason glyph, and halts. | Absorbed into cause record; active vector fades to zero opacity. |
| **Cadence** | Reveals as stationary vertical stroke via top-to-bottom clip inset. | Entirely stationary during beat; holds frame without translation. | Recedes in tone and value as reading cursor advances past it. |

---

### 3. Physical Kinds of Marks and Divergent Rows

#### Classification of All Thirty Marks
- **Body**: `value`, `enter`, `probe`.
- **Vessel**: `hollowBox`, `filledBox`, `hollowDot`, `filledDot`, `hole`.
- **Container**: `box`, `block`, `region`, `bracket`, `rail`, `call`, `library`.
- **Wire**: `series`, `parallel`, `loop`, `alternative`, `rest`.
- **Bond**: `arrow`, `spider`, `port`.
- **Force**: `blockedArrow`, `cross`, `hash`.
- **Cadence**: `exitBar`, `barLine`, `fermata`, `caesura`.

#### Rows Whose Semantic Kind Differs from Mark Kind
- `CauseTerm.both`: Assigned `series` (Wire). Its true kind is Body aggregation. Combining causes is list concatenation, not program wiring.
- `Eff.service`: Assigned `port` (Bond). Its true kind is Container lookup. It reads ambient context, not external protocol ports.
- `ActionTerm.closeScope`: Assigned `bracket` (Container). Its true kind is Force. It executes scope termination and releases finalizers.
- `ActionTerm.runIn`: Assigned `bracket` (Container). Its true kind is Wire redirect. It routes program execution into an existing scope.
- `ScopeState.closed`: Assigned `bracket` (Container). Its true kind is Cadence or sealed Vessel. A closed scope is a terminal outcome.
- `RunEvent.scopeLinked`: Assigned `bracket` (Container). Its true kind is Bond. It attaches a child fiber to a scope as a finalizer.
- `Observer.dropScopeFinalizer`: Assigned `hollowDot` (Vessel). Its true kind is Force cancellation. It removes a registered finalizer.
- `Eff.onExit`: Assigned `hollowDot` (Vessel). Its true kind is Container hook. It installs an exit cleanup enclosure.
- `Prim.asyncFinalizer`: Assigned `hollowDot` (Vessel). Its true kind is Force cancellation. It cancels a host registration.

---

### 4. Storyboards

#### Scene 1: Fork, Join, Await, and Race
- **Beat 1 (`ActionTerm.fork`)**:
  - Parent lane issues fork.
  - Mark `arrow` (Bond) enters: reveals via `clip-path: inset(0 0 0 0)` descending southeast from parent lane to child lane.
  - Mark `enter` (Body) on child lane enters: scales up via `scale(0)` to `scale(1)` with fill opacity 100%.
- **Beat 2 (`Eff.awaitFiber`)**:
  - Waiting fiber registers on child completion.
  - Mark `spider` (Bond) enters: hub appears on child lane via `scale(0)` to `scale(1)`.
  - Leg extends to parent lane via horizontal clip inset.
  - Parent fiber transitions to rest: mark `hollowBox` (Vessel) appears on parent lane.
- **Beat 3 (`Exit.success` and wake)**:
  - Child completes: mark `exitBar` (Cadence) reveals vertically via clip inset on child lane.
  - Child exit token: mark `value` (Body) translates from child exit along spider leg into parent lane.
  - Mark `spider` leg fills: opacity transitions from 0% to 100%.
  - Parent `hollowBox` transitions to `filledBox` (Vessel): fill opacity transitions from 0% to 100% via `settle`.
- **Beat 4 (`ActionTerm.raceAll`)**:
  - Multiple entrants execute concurrently.
  - Winner reaches exit: winner displays `exitBar` (Cadence).
  - Losers receive cancellation: mark `blockedArrow` (Force) translates sharply into losing entrant lanes.
  - Losing entrant lanes close: mark `blockedArrow` settles; losing lanes terminate with `exitBar`.

#### Scene 2: Interruption Outside and Inside an Uninterruptible Region
- **Beat 1 (Interrupt outside mask, `ActionTerm.interrupt`)**:
  - Host decision issues interrupt command.
  - Mark `blockedArrow` (Force) enters: translates horizontally into target fiber lane.
  - Target fiber is unmasked: `blockedArrow` impacts lane, halting active wire.
  - Mark `exitBar` (Cadence) reveals with reason `blockedArrow` appended.
- **Beat 2 (Enter mask, `Eff.uninterruptible`)**:
  - Target fiber enters protected region.
  - Mark `rail` (Container) reveals: double horizontal rails expand via clip inset along reading axis.
- **Beat 3 (Interrupt arrives inside mask, `RunEvent.interruptRecorded`)**:
  - Interrupt arrives while rail is active.
  - Mark `blockedArrow` (Force) translates to coordinate directly above the double rail.
  - Antagonist cannot penetrate: `blockedArrow` halts above rail; horizontal translate ceases; opacity holds at 100%.
- **Beat 4 (Interrupt deferred, `RunEvent.interruptDeferred`)**:
  - Target continues evaluation under rail.
  - Hovering `blockedArrow` translates synchronously with reading cursor along top edge of rail.
- **Beat 5 (Exit mask and delivery, `FrameEvent.deferred`)**:
  - Rail terminates: mark `rail` ends with vertical boundary clip inset.
  - Deferred interrupt drops: `blockedArrow` translates vertically downward across fiber lane with settling impact.
  - Fiber halts and exits: mark `exitBar` reveals with delivered interrupt reason.

#### Scene 3: Frame Pushed, Frame Popped, and Failure Walk
- **Beat 1 (`FrameEvent.pushed`)**:
  - Evaluation encounters `bind`.
  - Continuation frame is pushed: mark `hole` (Vessel) enters program canvas via `scale(0.8)` to `scale(1)`.
  - Receptacle contour is dashed rectangular socket with fill opacity 0%.
- **Beat 2 (`FrameEvent.popped`)**:
  - Inner computation produces result: mark `value` (Body) translates from inner box into `hole`.
  - Value docks into socket: socket fill opacity transitions from 0% to 100%.
  - Mark `hole` dissolves: dashed border fades out via opacity; computation proceeds to subsequent frame.
- **Beat 3 (Failure occurs, `Eff.fail`)**:
  - Typed error occurs: mark `cross` (Force) enters with sharp settling impact.
  - Active execution halts; cursor R begins failure walk.
- **Beat 4 (Failure walk skipping frame, `FrameEvent.ranContAll`)**:
  - Cursor passes frame lacking failure handler.
  - Mark `hole` (Vessel) remains unfilled: cursor translates backward past hole; hole fades out via opacity with zero fill.
- **Beat 5 (Failure caught, `Eff.catchCause`)**:
  - Cursor encounters matching handler frame.
  - Mark `cross` (Force) translates into handler input port; failure is absorbed.
  - Handler subprogram reveals via clip inset.

#### Scene 4: Scope Closure with Finalizers in Reverse Order
- **Beat 1 (Register finalizer A, `Eff.acquireRelease`)**:
  - Scope enclosure: mark `bracket` (Container) reveals leading hook.
  - Mark `hollowDot` A (Vessel) enters resource staff via `scale(0)` to `scale(1)` at position 1.
- **Beat 2 (Register finalizer B, `Eff.acquireRelease`)**:
  - Mark `hollowDot` B (Vessel) enters resource staff at position 2 to the right of A.
- **Beat 3 (Initiate close, `ActionTerm.closeScope`)**:
  - Closing exit arrives: scope boundary trailing hook `bracket` reveals.
  - Finalizer run queue is established in strict LIFO order: [B, A].
- **Beat 4 (Execute finalizer B, `RunEvent.finalizerProgram`)**:
  - Finalizer B executes first: mark `hollowDot` B transitions to `filledDot` B via fill opacity 100%.
  - Execution completes: `filledDot` B settles with slight pulse.
- **Beat 5 (Execute finalizer A, `RunEvent.finalizerProgram`)**:
  - Finalizer A executes second: mark `hollowDot` A transitions to `filledDot` A via fill opacity 100%.
  - All registered finalizers are fulfilled.
- **Beat 6 (Scope closed, `ScopeState.closed`)**:
  - Enclosure seals: both brackets join with solid terminal seal; resource release concludes.

#### Scene 5: Queue Offer and Take
- **Beat 1 (Queue offer into empty buffer)**:
  - Buffer container is active on canvas.
  - Incoming message: mark `box` (Container/Body) enters left boundary via `translate(-20px, 0)` with `settle`.
  - Box docks at index 0 of buffer.
- **Beat 2 (Queue second offer)**:
  - Second message: second mark `box` enters via translate.
  - Docks at index 1 to the right of first box.
- **Beat 3 (Queue take)**:
  - Consumer issues take command.
  - First message at index 0 departs: translates rightward out of buffer container into taker lane.
  - Remaining elements maintain object constancy: second box at index 1 translates horizontally to index 0 via shallow arc with `settle`.
- **Beat 4 (Queue take from empty buffer with wait)**:
  - Buffer is empty; consumer calls take.
  - Taker cannot be served: mark `hollowBox` (Vessel) appears in waiters compartment with token identity.
- **Beat 5 (Queue offer fulfilling waiter)**:
  - Producer offers value.
  - Offer bypasses buffer: translates directly toward waiting taker.
  - Waiter mark `hollowBox` transitions to `filledBox` via fill opacity 100%; taker lane resumes.

#### Scene 6: Frontier Under Fermata
- **Beat 1 (Fuel exhausted or host reply owed, `Outcome.frontier`)**:
  - Machine executes final step under available budget.
  - Further execution is paused awaiting external decision or host event.
  - Mark `fermata` (Cadence) enters: reveals via vertical clip inset over the terminal rest position.
- **Beat 2 (Quiescence hold)**:
  - Absolute stationary hold: zero translation, zero scaling, zero opacity transitions.
  - Reading cursor R rests directly beneath fermata.
  - Concurrency lanes remain static; no speculative motion occurs.
- **Beat 3 (Host decision arrives, `RunDecision.answerAsync`)**:
  - Host answers registration: mark `barLine` reveals at next measure.
  - Mark `fermata` recedes in value: opacity reduces to 55%.
  - Execution resumes as answer body flows across the score.

---

## Part C: Redraw Proposals and SVG Code

Proposals are defined on the standard 24x24 grid with `fill="none"`, `stroke="currentColor"`, `stroke-width="1.5"`, `stroke-linecap="round"`, and `stroke-linejoin="round"`.
Filled parts use `fill="currentColor"`.

### 1. `arrow` (REDRAW)
- **Reason**: Invert northeast trajectory to southeast descending vector.
A parent forks a descending child lane forward in time.
```xml
<path d="M5 5 L17 17 M10 17 H17 V10" />
```

### 2. `probe` (REDRAW)
- **Reason**: Replace desktop search magnifying glass with an instrumentation test point reticle matching text glyph `⌕`.
```xml
<circle cx="12" cy="12" r="5" />
<path d="M12 2 V5 M12 19 V22 M2 12 H5 M19 12 H22" />
<circle cx="12" cy="12" r="1.5" fill="currentColor" />
```

### 3. `library` (REDRAW)
- **Reason**: Replace asymmetric broken L-bracket with clean double-offset rounded module cards.
```xml
<rect x="4" y="6" width="13" height="14" rx="1.5" />
<path d="M8 6 V4 A1.5 1.5 0 0 1 9.5 2.5 H18.5 A1.5 1.5 0 0 1 20 4 V14 A1.5 1.5 0 0 1 18.5 15.5 H17" />
```

### 4. `enter` (ADJUST)
- **Reason**: Fill wedge solid. Loop entry is a committed event, matching text glyph `▶` and the design language.
```xml
<path d="M8 6 L18 12 L8 18 Z" fill="currentColor" />
```

### 5. `call` (ADJUST)
- **Reason**: Widen sidebar margins from x=6 and x=18 to x=8 and x=16. Prevents stroke fusion at 16 pixels.
```xml
<rect x="3" y="5" width="18" height="14" rx="1.5" />
<path d="M8 5 V19 M16 5 V19" />
```

### 6. `port` (ADJUST)
- **Reason**: Draw explicit contact pin mating with receptor socket, eliminating disconnected appearance.
```xml
<path d="M3 12 H10 M14 6 C18 6 20 8.5 20 12 C20 15.5 18 18 14 18" />
<circle cx="10" cy="12" r="1.5" fill="currentColor" />
```

### 7. `series` (ADJUST)
- **Reason**: Replace static dumbbell shape with directed forward flow chevron connecting balanced stages.
```xml
<rect x="2" y="7" width="7" height="10" rx="1.5" />
<path d="M9 12 H15 M12 9.5 L14.5 12 L12 14.5" />
<rect x="15" y="7" width="7" height="10" rx="1.5" />
```

### 8. `parallel` (ADJUST)
- **Reason**: Draw concurrent conduit tracks rather than heavy stacked slabs.
```xml
<path d="M3 7 H21 M3 17 H21" />
<rect x="7" y="5" width="10" height="4" rx="1" />
<rect x="7" y="15" width="10" height="4" rx="1" />
```

### 9. `alternative` (ADJUST)
- **Reason**: Draw symmetric solid fork arms for coordinate alternatives, avoiding false impression of subordination.
```xml
<path d="M3 12 H8 L14 6 H21 M8 12 L14 18 H21" />
```

### 10. `region` (ADJUST)
- **Reason**: Use corner bracket bounds `⌜ ⌟` matching text glyph and preventing blur into solid boxes at 16 pixels.
```xml
<path d="M4 9 V5 A1 1 0 0 1 5 4 H9 M15 4 H19 A1 1 0 0 1 20 5 V9 M20 15 V19 A1 1 0 0 1 19 20 H15 M9 20 H5 A1 1 0 0 1 4 19 V15" />
```

### 11. `bracket` (ADJUST)
- **Reason**: Reinforce hook corners to avoid confusion with hollowBox at 16 pixels.
```xml
<path d="M8 4 H4 V20 H8 M16 4 H20 V20 H16" />
```

### 12. `spider` (ADJUST)
- **Reason**: Align with causality: one completion input on left fans out to multiple waiter legs on right.
```xml
<path d="M3 12 H11 M11 12 L20 6 M11 12 H21 M11 12 L20 18" />
<circle cx="11" cy="12" r="2.5" fill="currentColor" />
```

### 13. `rest` (ADJUST)
- **Reason**: Strengthen dash pattern to 3 3 and center a solid musical rest block so mark remains visible at 16 pixels.
```xml
<path d="M3 12 H21" stroke-dasharray="3 3" />
<rect x="10" y="10" width="4" height="4" fill="currentColor" />
```

### 14. `hole` (ADJUST)
- **Reason**: Draw as dashed rectangular socket receptacle matching the rectangular process boxes that dock into it.
```xml
<rect x="5" y="5" width="14" height="14" rx="2" stroke-dasharray="3 2" />
```

---

## Changes to the Table

1. `Effect4.Program.CauseTerm.both`: Change mark from `series` to `block` (variant `"reasons"`, word `"combine"`, means `"a list of reasons, combined in order"`).
2. `Effect4.Program.Eff.service`: Change mark from `port` to `region` (variant `"service"`, word `"ask"`, means `"a service resolved from the ambient context"`).
3. `Effect4.ScopeState.closed`: Change variant from `"closed"` to `"sealed"` with a sealed enclosure mark to differentiate from open scopes.
4. `Effect4.Machine.RunEvent.started`: Update SVG drawing of `enter` from hollow to filled `▶`.
5. `Effect4.Program.ActionTerm.fork`: Update SVG drawing of `arrow` to southeast descending vector.
6. `Effect4.Program.ActionTerm.forkIn`: Update SVG drawing of `arrow` to southeast descending vector.
7. `Effect4.Program.ActionTerm.forkScoped`: Update SVG drawing of `arrow` to southeast descending vector.
8. `Effect4.Machine.RunEvent.forked`: Update SVG drawing of `arrow` to southeast descending vector.
9. `Effect4.Machine.RunEvent.raceLaunched`: Update SVG drawing of `arrow` to southeast descending vector.
10. `Effect4.Program.Eff.withFiber`: Update SVG drawing of `probe` to instrumentation test point reticle.
11. `Effect4.Program.ActionTerm.snapshotChildren`: Update SVG drawing of `probe` to instrumentation test point reticle.
12. `Effect4.Program.ActionTerm.getId`: Update SVG drawing of `probe` to instrumentation test point reticle.
13. `Effect4.Program.ActionTerm.getInterruptible`: Update SVG drawing of `probe` to instrumentation test point reticle.
14. `Effect4.Program.ActionTerm.context`: Update SVG drawing of `probe` to instrumentation test point reticle.
15. `Effect4.Prim.withFiber`: Update SVG drawing of `probe` to instrumentation test point reticle.

---

## Questions for the Owner

1. **Meaning**: Should cause combination in `CauseTerm.both` possess its own dedicated list concatenation glyph, or should it use an aggregated horizontal list format?
2. **Representation**: Should `ScopeState.closed` visually clasp its outer brackets together, or should it embed an exit glyph between the brackets?
3. **Domain**: Should service context reads (`Eff.service`) share the corner bracket glyph of `provideService`, or should they take a distinct context tag glyph?
4. **Representation**: Should continuation frame holes be rectangular receptacles matching operation boxes, or must they strictly remain circular combining placeholders?

---

## Sources

The following authority documents in this repository were read:
- `docs/research/2026-10-12-visual-semantics/README.md`
- `docs/core/decisions.md` (rows 354, 365, 366, 367)
- `docs/design/design-language.md` (§2, §3, §4, §5.1, §7, §9)
- `docs/research/2026-10-09-visual-language-theory.md` (§1, §2, §3, §4, §5, §6)
- `tools/Tools/View/Glyph.lean`
- `tools/Tools/View/GlyphSheet.lean`
- `docs/research/2026-10-12-visual-semantics/review-input/marks.png`
- `docs/research/2026-10-12-visual-semantics/review-input/sheet.png`

The following theoretical literature was recalled:
- Talmy, Leonard (1988, 2000), Force Dynamics in Language and Cognition (recalled).
- Tversky, Barbara; Morrison, Julie Bauer; B&eacute;trancourt, Mireille (2002), Animation: Can It Facilitate? (recalled).
- Heer, Jeffrey; Robertson, George (2007), Animated Transitions in Statistical Data Graphics (recalled).
- Lasseter, John (1987), Principles of Traditional Animation Applied to 3D Computer Animation (recalled).
- Bertin, Jacques (1967, 1983), Semiologie Graphique (recalled).
- Moody, Daniel (2009), The "Physics" of Notations: Toward a Scientific Basis for Creating Cognitive Effective Visual Notations (recalled).

Review complete.
