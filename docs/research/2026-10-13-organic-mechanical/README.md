# Tissue and metal: a review of the living picture's math, and the composition primitives for the whole machine

Status: research note (history, not authority). 2026-10-13. The owner asked for two things: "a
basic math and abstractions review", then "a deeper dive into the organic composition primitives
we'd need to generalize to the whole machine as well as mix with mechanical semantics w/ a machine
/ metal aesthetic to create different operational semantics for flows and invariants/vessels etc
for deeper aesthetic beauty and semantic fidelity". The PC is off the seat for now; development of
the package moves to the Mac worktree `~/Dev/lean4-whatwg-svg` (branch `html/svg`, at `80bb06b`,
which Effect4 pins).

Part I reviews what exists: Effect4's `tools/Tools/View/Living/` and the package's `Scene` modules
that serve it. Part II proposes the primitives: two materials, each with its own operational
semantics, and the algebra that composes them over the whole machine. Part III is the plan and the
owner's questions.

---

## Part I. The math and the abstractions, reviewed

### I.1 Findings, the most serious first

| # | Finding | Where | Kind | Remedy |
| --- | --- | --- | --- | --- |
| 1 | **Conservation breaks in pixels.** A core's width is truncated to whole pixels one branch at a time, so at three to one the daughters draw `5 + 1 = 6` pixels against a trunk of `7`. The law the picture claims (the branches of a split sum to the trunk) is false of the picture | `Totals.picture` (`(unit * q) / 1000).toNat`) | defect | draw the cores as the package's bands (`Scene/Network`, W18): bands are what lies between rounded edges, so they tile and sum exactly (`Network/Laws`) |
| 2 | **A discrete counter is drawn as a continuous curve.** The level of the run interpolates the counts between commands with the monotone curve. The counts change only at commands; between them nothing is held "half". The curve suggests a flow that does not exist | `Level.level` | semantic error | a counter's history is a step: flat between commands, a riser at each (Part II, §II.4: the operational semantics chooses the interpolation). The monotone curve stays for what does relax continuously: a conductivity, an eased position |
| 3 | **The spacing search can stop without its law.** `Phyllotaxis.spacing` tries 400 spacings and returns the last one tried whether or not it keeps the units apart | `Phyllotaxis.spacing` | defect (latent) | return `Option`, or prove a bound: Vogel's nearest neighbours stand about `c·√π·0.9` apart, so a start from `gap / (√π · 0.9)` and a bound on the steps make the search total and its result lawful |
| 4 | **The golden turn drifts 0.0088° a step.** The convergent `7/18` gives 137.499°; over 89 units the last stands 0.78° off, enough to bend the parastichies that make the pattern read as a sunflower | `Phyllotaxis.TURN_*` | precision | the next convergent `278/715` gives the triple `(433941, 397540, 588509)`, an error near `10⁻⁵`° a step; the law `turn_norm` holds of any triple |
| 5 | **A disc's place is recomputed from the start for every slot.** `Plan.slotAt` builds `directions (a + 1)` for each age `a`: quadratic in the units per frame | `Organism.Plan.slotAt`, `roomAt` | speed | compute the directions once per plan and index them |
| 6 | **Units in a disc travel through one another.** In a beat a unit moves on a straight line between two spiral places; an offer moves every unit one age outward, and the straight paths cross | `Beat.at_` | motion defect | move along the spiral (each unit's angle and radius interpolated, which keeps the order of radii), or use the package's patch (`Scene/Patch`) with paths per move |
| 7 | **The wall's width reads one source's slope.** At a junction several sources add and the slope no longer gives the local radius, so a neck's wall is too thick or too thin | `Soft.Grid.walls`, `Organism.wallOf` | approximation | read the local radius from the medial axis (the distance to the contour across the normal, two samples), or clamp by the nearer source's radius; documented as an approximation until then |
| 8 | **Catmull-Rom through thinned crossings can leave the band.** The spline through every fourth crossing may cut inside a tight neck or cross a unit; nothing checks it | `Soft.closed`, `thin` | unchecked | a check like the composition grammar's: every point of the smoothed contour within a pixel of the field's level (sampled), refused otherwise; or the package's `Geometry/Through` with its laws |
| 9 | **The answer of a beat is drawn by hand.** The cores light the channels a beat crossed, but the arcs of motion in a sampled beat are straight; a unit that leaves through a channel does not follow the channel's curve | `Beat.along` | fidelity | travel along the channel's own curve (its cubic), at the settle ease |
| 10 | **Two pictures of the same quantities are drawn twice.** The lane form of slots duplicates the package's `Scene/Units` (W20); the totals duplicate `Scene/Network` (W18); the level duplicates `Geometry/Stack/Layers` (W19); the beat's join duplicates `Scene/Join` and `Scene/Patch` | `Organism`, `Totals`, `Level`, `Beat` | duplication | move each onto the package's value (§I.3) |

### I.2 What is right, and why

| Piece | The law | Checked by |
| --- | --- | --- |
| Physarum's adaptation | `dD/dt = f(|Q|) − D`, `f(q) = q²/(1 + q²)` (Tero et al. 2010, p. 441, `γ = 2` here against the paper's 1.8), one explicit beat a command | `gain_lt`, `adapt_le`, `adapt_idle`, `conductivity_le`, proved |
| A tube's radius from its conductivity | `D = π r⁴ / 8η` (Hagen–Poiseuille, the paper's equation 1): `r ∝ D^(1/4)` | `Organism.channelR` by `root4`; a definition |
| Wyvill's kernel | `C(s) = 1 − 4/9 s³ + 17/9 s² − 22/9 s`, `s = r²/R²`: one at the source, one half at half the radius, zero at the radius, with a zero slope there (`C'(1) = (−12 + 34 − 22)/9 = 0`), so a sum of kernels is smooth | three guards in `Soft.lean`; the slope by hand here |
| Marching squares | a crossing on an edge by linear interpolation; a saddle by the cell's centre; loops by edge keys, each interior crossing met twice | the probe of one segment's loop; closed loops need a border below the level, which `MARGIN` gives |
| Laplace with Hooke | a thin elastic tube's strain `ΔR / R = (R / E h) ΔP`, linear; the pressure the signed count over the capacity | a definition, with the compliance and the collapse named as the tissue's constants |
| Murray's radii | at the optimum the flow goes as `r³`, so the cubes of a split add | `flows_add`; `radius` as the integer cube root |
| Murray's angles | at the optimum a tube's cost per length goes as `r²` (both of Murray's terms, `8μQ²/πr⁴` and `bπr²`, scale as `r²` when `Q ∝ r³`). Minimising `Σ cᵢ Lᵢ` over the junction point (the weighted Fermat point) gives `Σ cᵢ ûᵢ = 0`: a closed triangle of forces with sides `r₀²`, `r₁²`, `r₂²`. The law of cosines then gives `cos θ₁ = (r₀⁴ + r₁⁴ − r₂⁴) / (2 r₀² r₁²)` | derived here; guarded at an even split (37.5°) and at three to one (0.923, by hand) |
| Vogel's spiral | `θ_k = k φ`, `r_k = c √k`: equal area per floret | the golden turn as a Pythagorean triple; `turn_norm` (exact, by `grind`); the least spacing guarded |
| The scales | counts down a linear scale that falls, beats across a point scale | the package's laws (`linear_height`, `Band.fit_inside`) |

### I.3 The abstractions: what is Effect4's, what is the package's

The rule: the package holds what is true of pictures whatever they draw, with its laws; Effect4
holds what the Queue's semantics says, and nothing that draws.

| Abstraction | Today | Where it belongs | Its law |
| --- | --- | --- | --- |
| a soft field, its contours, walls of a width | `Living.Soft` | the package (generalises W22, a vessel's hull) | the contour separates the samples above the level from those below; a wall's inner edge lies inside; the field of a moved source is the field moved |
| units in a lane | `Organism.Plan.heldAt` | the package's `Scene/Units` (W20), landed | count, order and front kept; one slot over is one move |
| units in a disc | `Living.Phyllotaxis` | `Scene/Units` as a second form, beside the row | count and order kept; no two closer than the gap; area in proportion to the count |
| a split's geometry | `Living.Murray` | the package, with `Scene/Network` (W18): a link's angle at a node | the cubes add; the force triangle closes |
| a flow network | `Living.Totals` | the package's `Scene/Network`, landed | conservation at each node; bands tile with no gap |
| adaptive conductance | `Living.Physarum` | the package: a fold over a run's fluxes, generic in the network | bounded; idle decay; monotone in the flux |
| the run's level | `Living.Level` | the package's `Geometry/Stack/Layers` (W19), landed, as steps | a layer's height at a beat is its value |
| a beat's motion | `Living.Beat` | the package's `Scene/Patch` and `Scene/Reel`, landed | a thing that only moved is one move; the reel's frames in order |
| the marking, the flux of a step, the plan | `Living.Organism` | Effect4: they read the Queue's cell | the flux is the keyed join of two markings |
| the roles of a module | `Organism.Place`, by hand | Effect4, `Library/Queue/View.lean` (row 367, point 5) | none: data |

So Effect4 keeps three things: the module's roles, the reading of a cell into a marking, and the
choice of which primitive draws which construct. Everything that draws moves to the package.

---

## Part II. Tissue and metal: the primitives for the whole machine

### II.1 Two materials, two operational semantics

The living picture draws state as tissue: soft, continuous, deforming, eased. It has no material
for what never deforms: the bound a queue never passes, the order a scope's finalizers must keep,
the step a command takes and cannot take back. A machine draws those. The proposal is one rule:

> **An invariant is metal; state is tissue.** What the program fixes, or a theorem proves, is
> drawn as a rigid machined part: exact, quantised, moving only by rigid steps. What the run
> accumulates, carries or adapts is drawn as tissue: soft, continuous, moving by flow and
> settling. A part's material says which kind of fact it is.

Living things are built so. A cell is a tensegrity: compressed struts (microtubules) and a
tensed network (actin) under prestress, its shape held by the balance (Ingber; Stamenović; the
microtubule-disruption traction experiments, PMC2614693). Its motors are machines: kinesin walks a
rigid track in discrete 8 nm steps, one ATP a step, hand over hand (Asbury et al., *Science* 2003);
the F1 rotor of ATP synthase turns in discrete 120° steps, three catalytic events a turn (Yasuda et
al., *Nature* 410, 2001). A skeleton is levers and pulleys, its tendons tissue. The two materials
are not a style: they are two kinds of fact, and biology already draws with both.

| | Tissue | Metal |
| --- | --- | --- |
| what it is | state: a quantity, a pressure, a history | an invariant, a bound, a protocol, a commitment |
| its source | the run (the marking, the join, the fold of fluxes) | the program's text, a module's roles, a proved claim |
| its geometry | a field's contours: smooth, no corner | circles, lines, involutes: exact, with the corners a machinist cuts |
| how it changes | continuously in form, settling (critically damped) | by rigid steps: a tick, an index, a click; no deformation |
| how a count is drawn | units that flow | teeth, slots, notches: a count is a number of discrete places |
| its interpolation between commands | none for a count (a step); a curve for what relaxes (a conductivity) | a step, always |
| its tone | the ink at a low value, its walls at a middle value | the ink at a high value, crisp, thin and thick lines 1:2 (ISO 128) |

### II.2 The machine's constructs, each with its primitive

Each row gives the construct, the primitive that draws it, its material, the law the primitive
obeys, and how it moves. The constructs are the machine's (`src/Effect4/Machine/*`) and the
library's (`src/Effect4/Library/*`).

| Construct | Primitive | Material | Law | Motion |
| --- | --- | --- | --- | --- |
| a fiber | a motor on a track: the track is its lane, a tie on it each command | metal track, tissue motor | one step a command (kinesin: one step an ATP) | the motor steps one tie a beat; parked, it stands off the track |
| a fiber's stack of frames | sockets in a rigid frame, each a hole its result returns to (VS-4) | metal | last in, first out | a socket clamps on when pushed, releases when popped |
| a scope | a bracket frame holding loaded springs, one a finalizer | metal frame, spring energy | the springs release in the reverse order of their loading | at close, each spring releases in turn, the last loaded first |
| a mask (uninterruptible) | a clutch disengaged: the brake's force is not transmitted | metal | an interrupt is held, never dropped, until the mask lifts | the clutch plate separates; the held pawl rests on its guard |
| an interrupt | a pawl or a brake shoe | metal | it lands, or is held by the guard | travels to its target; stops at the guard or lands |
| a deferred | a latch: open (hollow) until tripped, then closed (filled) | metal | trips once | one rigid snap |
| the waiters on a deferred | pawls resting on the latch | metal | all release at the trip (the spider) | release together |
| a ref | a dial with a needle | metal dial, a value | the needle points at the value | the needle turns to the new value |
| a queue's buffer | a vessel of tissue in a machined frame whose rim is its capacity | tissue in metal | the count never passes the rim (the profile's bound) | tissue flows; the frame never moves |
| a queue's offer strategy | a valve at the inlet: closed (suspend), relief (dropping), spill at the rim (sliding) | metal | one way; the relief vents what passes its setting | the valve's gate indexes |
| a semaphore | a ratchet wheel with one tooth a permit | metal | permits held never exceed the teeth | acquire indexes one tooth; release returns it |
| a pool | a rack of tools, an empty peg a borrowed item | metal rack, tissue items | an item is on its peg or out, never twice | an item leaves its peg and returns |
| a pubsub | a manifold: one inlet, many outlets | metal body, tissue flow | what enters reaches every outlet subscribed | flow divides at Murray's angles |
| a stream | a conveyor whose sprocket is driven by the demand at its end | metal sprocket, tissue chunks | pull: nothing moves without demand | the sprocket indexes a chunk a pull |
| a fork | a gear that drives a second shaft | metal | the child's track begins at the parent's tie | the new gear meshes and the child's motor starts |
| a join, an await | a differential: two shafts into one | metal | the output waits for both | it turns once both inputs have turned |
| a race | a release: the first arrival trips it and the others are braked | metal | one winner; the losers take ⊣ | one snap; brakes land on the rest |
| time, a schedule | an escapement and its wheel: one tick a beat; a Geneva drive for a dwell between indexes | metal | 360°/n an index; nothing moves during the dwell | tick, dwell, tick |
| a host's decision | a lever thrown from outside the machine | metal | it selects one position | one throw |
| the journal | a punched tape behind a ratchet and pawl | metal | a command punched is never unpunched | the tape advances one row a command |
| a proved invariant | a rail, a guide, a frame member: machined | metal | the part exists only where a claim is proved | it never moves |
| a planned goal | the same part as a rough casting, not yet machined (hollow: promised) | metal, rough | the casting is replaced by the machined part when the claim is proved | none; it is promised |

The last two rows tie the picture to the proof graph: a reader sees which invariants are proved by
which parts are machined. This is semantic fidelity in the strict sense: a rail is drawn only where
a theorem holds the thing on it.

### II.3 The composition algebra

Parts compose by six operations. Each says which materials it joins and what it transmits.

| Operation | Joins | What passes | Example |
| --- | --- | --- | --- |
| **mount** | tissue in metal | the bound: the frame holds the tissue in | the queue's buffer in its rim; a pool's items on their rack |
| **mesh** | metal to metal | a ratio of steps, exact in whole teeth | a fork's gears; a semaphore's ratchet driving a gate |
| **pump** | metal to tissue | a command moves a unit: a piston, a valve opening | an offer's piston pushing a message through the inlet valve |
| **sense** | tissue to metal | a pressure trips a part: a float valve, a gauge | a full vessel closing the inlet valve (suspend's backpressure) |
| **channel** | tissue to tissue | a flow, conserved | the Physarum channels between places; a pubsub's branches |
| **nest** | either in either | containment that closes | scopes in scopes (frames in frames), compartments in a cell (membranes in membranes) |

With a seventh, **feedback**, which closes a loop through a sense and a pump: a governor. A stream
with backpressure is one: demand at the end is sensed, and the sprocket is pumped.

Reuleaux's kinematic pairs (a revolute joint, a prismatic slide, a screw; a gear's teeth as a higher
pair) are the metal joints of the algebra: each says how many degrees of freedom the joined parts
keep, so a mechanism's motion is fixed by its joints and not drawn case by case.

### II.4 Operational semantics by material

The two materials move differently because their facts change differently.

- **Metal moves by index.** Every metal motion is a rigid step from one exact position to the next:
  a tooth, a tie, a row of tape. Between commands a metal part is still. A step takes the beat and
  stops dead, at most with a critically damped stop; it never overshoots, since an overshoot would
  draw a position the machine was never in. A count kept by metal draws as a step function.
- **Tissue moves by flow.** A unit travels inside its channel along the channel's curve; a vessel
  distends and relaxes by its pressure; a conductivity rises and decays. These interpolate, and the
  interpolation is honest because the quantity it draws is continuous: a position in flight, a
  conductivity's relaxation. A count is never interpolated.
- **A mixed part moves both ways at once.** A pump's piston indexes (metal) while the unit it
  pushes flows (tissue); a valve's gate snaps while the pressure behind it relaxes.

This settles finding 2: the run's level is a counter, so it is drawn by metal, a step at each
command; the lives of the channels are conductivities, so they stay curves.

Row 354 (point 4) names the motion primitives translate, scale, clip and opacity. Metal needs one
more: **rotation about a point** (a gear's index, a needle, a ratchet's tooth), which CSS states
exactly (`rotate`). Its addition is an owner's ruling (§III.3, question 1).

### II.5 The look of metal, under the rules

No hue is added (hue stays the four agents'), and no mark is ornament. Metal's look comes from
engineering drawing, whose every convention carries a meaning (ISO 128):

- **Two line weights, thin and thick, 1:2.** A machined edge is a thick continuous line; a hidden
  edge a dashed thin line; a centre line, the axis of a rotating part, a thin long-dash dotted line.
- **Section hatching at 45°**, thin, on a part cut through: the solid material of a proved invariant
  where the picture cuts it.
- **Dimension lines** for a bound: a thin line with terminators and the number, so a queue's
  capacity is a dimension on its rim, the way a drawing states a tolerance.
- **Exact geometry**: circles, straight lines, the involute of a gear's teeth (its ratio is the
  ratio of the tooth counts, exact; its centre distance may vary without changing the ratio), the
  slots of a Geneva wheel (`360° / n` an index).
- **Tone by value only**: machined metal at a high value of the ink, its faces flat; tissue at a
  low value, its walls at a middle value. The contrast between the crisp and the soft is the
  material's meaning.

### II.6 Generalising to the whole machine

The machine's state is a set of stores (fibers, frames, scopes, deferreds, refs, timers, the
journal) and its steps are commands. The picture of the whole machine is then:

1. **A scene of parts**, one per live store entry, each the primitive of its construct (§II.2),
   placed by the composition algebra (§II.3): mounted, meshed, nested, channelled.
2. **A motion per command**: the parts the command touches (the step's footprint, which the
   machine already computes: `machine-from-the-base`, moves and footprint), each moving by its
   material's semantics (§II.4).
3. **A proof layer**: for each claim of the registry that holds a part, the part machined or cast
   (§II.2, the last two rows).

The organism of the Queue is the first instance: its vessel is tissue mounted in a rim, its
channels tissue, its inlet a valve. The next instances are the semaphore (a ratchet), the scope (a
spring frame) and the fiber (a motor on a track): each tests a different operation of the algebra.

---

## Part III. Plan

### III.1 Repairs to what exists (Effect4, then the package)

1. The totals' cores as the package's network bands (finding 1).
2. The run's level as steps (finding 2).
3. The spacing search total, the finer golden turn, the directions computed once (findings 3–5).
4. A disc's units along the spiral; a channel's units along its curve (findings 6, 9).
5. Move the lane slots, the totals, the level and the beat's join onto `Scene/Units`,
   `Scene/Network`, `Geometry/Stack/Layers` and `Scene/Patch` (finding 10).

### III.2 New abstractions, in the package (`~/Dev/lean4-whatwg-svg`), each with its laws

| Ask | Abstraction | Laws |
| --- | --- | --- |
| W23 | a soft field: sources, the grid, contours, walls of a width (from `Living.Soft`) | separation at the level; the field of moved sources is the field moved |
| W24 | units in a disc (Vogel), a second form of `Scene/Units` | count and order kept; no two closer than the gap |
| W25 | a junction's geometry (Murray) for `Scene/Network`'s links | the cubes add; the force triangle closes |
| W26 | adaptive conductance (Physarum) as a fold over a network's fluxes | bounded; idle decay; monotone |
| W27 | metal parts: a gear (involute, ratio by teeth), a ratchet (a monotone index), a Geneva wheel (`360°/n`, a dwell), a spring stack (LIFO), a valve (one way, relief), a latch | each part's step is exact; a ratchet never goes back; a stack releases in reverse |
| W28 | kinematic pairs (revolute, prismatic) as the joints of `Layout`, so a mechanism's motion follows from its joints | a joint keeps its degrees of freedom |
| W29 | rotation about a point as a motion primitive, beside translate, scale, clip and opacity | the end frame is the target; reduced motion shows it |

### III.3 Questions for the owner

1. **Rotation.** May rotation about a point join the motion primitives (row 354, point 4)? Gears,
   ratchets, needles and latches need it; CSS states it exactly.
2. **The rule of materials.** Is "an invariant is metal; state is tissue" the rule, with a part
   machined only where a claim is proved and cast where it is planned?
3. **The look of metal.** Engineering drawing's flat conventions (two weights, centre lines,
   hatching, dimensions), or a rendered metal with value bands for its faces? The first keeps every
   mark a meaning; the second is richer and risks ornament.

### III.4 What this note does not establish

The mapping of §II.2 is a proposal: no picture yet draws a metal part, and no part is tied to a
claim of the registry. The biology is cited as a precedent for the two materials, not as a model the
picture simulates. The Geneva and escapement figures come from a single engineering site and are
used only for the index angle, `360° / n`, which is geometry.

## Sources

Read in this session's searches: Tero et al., *Science* 327:439 (2010), the paper's p. 441 and its
equation 1 (pdodds.w3.uvm.edu copy); Ingber's cellular tensegrity, via Stamenović's review and
PMC2614693; Asbury et al., "Kinesin moves by an asymmetric hand-over-hand mechanism", *Science*
2003 (faculty.washington.edu copy); Yasuda et al., *Nature* 410 (2001), doi 10.1038/35073513, F1's
120° steps; Feynman's ratchet and pawl and the Brownian ratchet (arXiv cond-mat/0504610; Wikipedia,
flagged); Reuleaux's kinematic pairs (Wikipedia, "Kinematic pair", "Mechanism (engineering)");
the Geneva drive and the escapement (firgelliauto.com, secondary); ISO 128 line types (ISO 128-2
preview; ISO 128-23); involute gears (cnc25d gear profile theory) and the differential as a summing
mechanism (US4509390). Recalled: Murray's two papers of 1926; Vogel 1979; Wyvill et al. 1986.
