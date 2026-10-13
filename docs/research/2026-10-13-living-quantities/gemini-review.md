# Visual Semantics Review: Living Quantities Language

This document reviews Effect4's living-quantities language for numbers and flows.
It evaluates the manual sketch in `sketch.html` and the computed implementation in `tools/Tools/View/Living/Organism.lean`.
It ranks nature-inspired algorithms for exact execution in Lean.
It details motion storyboards and concrete improvements to the drawing code.

## The Five Findings That Matter Most

1. **Continuous scalar field summation produces dishonest swelling.**
`tools/Tools/View/Living/Soft.lean` samples a continuous field by summing polynomial kernels.
`tools/Tools/View/Living/Organism.lean` assigns field sources to `held`, `offers`, and `takers`.
These sources merge into one undivided contour in `living.png`.
Waiting offers at the inlet and waiting takers at the outlet fuse with the vessel.
A reader cannot tell the vessel's fixed capacity of two from parked requests.
Most critically, a waiting taker holds no message and represents a deficit.
`Organism.lean` gives each taker a source of weight 900.
This weight creates a large outward bulge at the outlet in Frame 7.
Drawing empty demand as an outward swelling misrepresents negative quantity as positive mass.

2. **Channel width conflates historical conductivity with step flux.**
`tools/Tools/View/Living/Physarum.lean` models tube conductivity $D$ via Tero et al.'s adaptation rule.
In `Organism.lean`, channel radius follows $D^{1/4}$ from Hagen–Poiseuille's law.
This single width draws the entire channel segment.
A channel carrying no messages in the current step remains wide if past steps used it.
In Frame 7 of `living.png`, the outlet channel appears dilated after three prior takes.
The current step performs no message transfer, yet the channel displays high conductance.
A reader cannot distinguish structural conductance from active transfer.
The visual language lacks a separate mark for instantaneous step flux.

3. **Motion trajectories bypass the channels.**
`Organism.lean` generates an airborne quadratic bezier curve (`arc`) for each moved message.
In Frame 4 and Frame 6 of `living.png`, these curves span up to 340 pixels across the canvas.
They leap high above the central axis and land outside the conduits.
The Physarum channels sit underneath as inactive lines while messages travel through empty space.
This contradiction undermines the living transport network.
Units belong to `Kind.body` and must translate through the channel lumen.

4. **Contrast inversion suppresses the foreground data payloads.**
In `Organism.lean`, the membrane renders with 52% ink opacity (`.shape .ink 520`).
The held droplet renders with only 30% ink opacity (`.shape .ink 300`).
The ambient vessel wall commands higher contrast than the held message payload.
In `sketch.png`, droplets use 100% ink fill with dark numerals.
The low contrast in `living.png` makes held units resemble hollow promises rather than committed values.
Primary visual contrast belongs to the data payload rather than the container hull.

5. **Static diagrams etch transient motion paths into persistent geometry.**
`Organism.lean` draws transient step transitions as static lines on small-multiple frames.
In `tools/Tools/View/Glyph.lean`, no `arc` constructor exists in `Shape`.
Decisions row 354 and row 368 restrict motion to four CSS primitives: translate, scale, clip, and opacity.
Etching ballistic trajectory curves directly onto static frames violates semiotic clarity.
Static frames must show discrete before and after states with directional vectors inside the lumen.
Curvilinear travel belongs strictly to animated playback tracks.

---

## Part A: Review of What Is Drawn

### 1. Capacity, Held, Offers Waiting, and Takers Waiting
In `sketch.png`, a reader reads capacity directly from the geometry.
The vessel is an explicit capsule containing two discrete circular slots.
A hollow slot marks promised room.
A filled droplet marks a committed message.
Waiting offers sit in parked boxes to the left of the inlet.
Waiting takers sit in parked boxes to the right of the outlet.
The spatial separation maintains an unambiguous boundary between inside and outside.

In `living.png`, this clarity disappears.
Wyvill's soft field in `Soft.lean` sums influence across all sources.
When an offer arrives in Frame 3, the inlet swells into a wide organic pouch.
The pouch coalesces with the vessel body.
The contour suggests an expanded buffer holding three items rather than a bounded buffer holding two.
When the buffer empties in Frame 6, the vessel waist deflates.
The outline changes shape continuously across frames.
A reader cannot perceive a constant capacity without counting hollow rings.

### 2. Channel Width: History of Use versus Step Flux
`Physarum.lean` implements $dD/dt = f(|Q|) - D$.
Conductivity accumulates with traffic and decays with an idle rate of 40%.
`Organism.lean` computes channel radius as $r \propto D^{1/4}$.
This geometry represents accumulated conductivity, not step flux.

In Frame 3, offer 30 arrives while the vessel is full.
Offer 30 cannot enter the vessel and parks at the inlet.
No message crosses from the inlet to the vessel.
Yet the channel between the inlet and vessel appears thick because requests 1 and 2 traversed it.
In Frame 7, take 7 arrives while the vessel is empty.
Take 7 cannot consume a message and parks at the outlet.
No message crosses the outlet channel.
Yet the outlet channel appears dilated from earlier takes.
A reader cannot tell whether a channel is actively transferring messages or sitting idle.

A dual-layer ribbon resolves this ambiguity.
The outer wall represents accumulated conductivity $D$.
An inner core represents instantaneous flux $Q$.
When flux is zero, the inner core stays dark and the outer wall shows resting conductivity.
When flux occurs, the inner core lights up and expands to fill the lumen.

### 3. Honesty of the Membrane
The membrane in `living.png` fails physical and semantic honesty.
In `Organism.lean`, held units receive a field source with radius 26 and weight 450.
Waiting offers and waiting takers receive a field source with radius 30 and weight 900.
A waiting item exerts twice the weight of a held item.
This parameter choice produces excessive swelling at the margins.

The treatment of waiting takers is especially misleading.
A taker is an unsatisfied consumer request.
It holds no data payload and consumes zero buffer space.
In `docs/research/2026-10-13-living-quantities/README.md`, takers waiting represent a deficit below zero.
In Frame 7 of `living.png`, taker 7 produces a massive outward protrusion at the outlet.
Drawing negative demand as positive physical mass violates visual integrity.
A deficit must appear as an empty receptacle or an inward tension line, never an outward swelling.

Furthermore, field contours do not preserve linear area scaling.
Two sources placed close together produce a combined area larger than the sum of their individual areas.
The visual volume expands non-linearly.
A reader cannot infer discrete item counts from the contour area.

### 4. Hierarchy, Contrast, Density, Rhythm, Arcs, and Captions
- **Hierarchy and Contrast**: In `living.png`, droplets use fill opacity 0.30 (`.shape .ink 300`).
The membrane boundary uses fill opacity 0.52 (`.shape .ink 520`).
The container overpowers the contents.
Numerals printed inside faint droplets suffer from low legibility against the dark ground.
- **Density and Canvas Allocation**: The frame canvas measures 640 by 140 pixels.
All structural features cluster along the central horizontal line at $CY = 70$.
The regions above $y = 40$ and below $y = 100$ sit completely empty.
This creates poor spatial utilization.
- **The Arcs**: Arcs in Frame 4, 5, 6, and 8 reach heights of 26 pixels and widths up to 340 pixels.
They dominate the entire upper half of the image.
They disconnect message motion from the channel conduits.
- **Rhythm**: The static frames repeat an identical horizontal bar from left margin to right margin.
This unbroken horizontal line imposes a rigid, monotonous cadence.
It flattens the distinction between active and blocked steps.
- **Captions**: Captions appear at the bottom left in faint serif italic text.
They sit far below the marks and fail to label spatial parts.
Labels for inlet, vessel, and outlet are absent.

### 5. Compliance with Decisions and Design Rules
- **Decisions Row 354 (Point 2)**: Evidence status follows shape: hollow promised, filled kept.
In `living.png`, droplets use 30% opacity, which dilutes the solid appearance of kept values.
The monochrome dark ground (`#14110d`, ink `#ece6dc`, rule `#48433c`) adheres strictly to the rule of hue.
- **Decisions Row 354 (Points 4 and 5)**: Motion uses only translate, scale, clip, and opacity.
Nothing loops and nothing pulses.
The ballistic arcs in `Organism.lean` attempt to draw motion inside static SVGs.
This creates ad-hoc curves outside the four primitives.
- **Decisions Row 366 (Point 3)**: No ornament without meaning.
`Organism.lean` inserts dummy point sources at `inletX` and `outletX` with weight 700.
These dummy points create artificial lumps in the channels even when no units are present.
- **Decisions Row 368 (Point 4)**: Physical kinds govern mark behavior.
In `Glyph.lean`, a message value is a `Kind.body`.
A body changes position via `.translate`.
Airborne bezier curves bypass this grammar.

---

## Part B: Nature-Inspired Algorithms

The table below ranks eleven nature-inspired algorithms for living quantities in Effect4.
Rankings prioritize semantic fidelity to Effect primitives, integer-only computation speed, and formal provability in Lean.

| Rank | Algorithm | Target Effect Construct | Visual Semantics | Fast & Exact in Lean | Trustworthy Law | Source |
|---|---|---|---|---|---|---|
| 1 | **Murray's Law & da Vinci Pipe Model** | Queue totals, PubSub, Stream forks | Channel branching where trunk width equals branch sum ($w_0 = \sum w_i$) | Exact integer addition and list folds | Conservation of flow: $\sum w_{\text{in}} = \sum w_{\text{out}}$ | Recalled |
| 2 | **Horton–Strahler Stream Ordering** | Stream pipelines, Fiber supervision trees | Hierarchical channel capacity and conduit thickness | Recursive tree fold with integer `max` and `+ 1` | Path monotonicity: order never decreases downstream | Recalled |
| 3 | **Vogel's Phyllotaxis** | Semaphore permits, Connection Pool, high-capacity Queue | Optimal 2D spiral packing inside round vessels | Precomputed fixed-point trigonometric table and integer square root | Non-overlap: minimum pairwise distance $\ge 2r$ | Recalled |
| 4 | **Constructal Law (Bejan)** | Work-stealing dispatchers, Tree scheduling | Tree networks minimizing flow resistance between points and areas | Hierarchical bisection and integer coordinate scaling | Global access resistance minimization | Recalled |
| 5 | **Physarum Network Adaptation** | Route traffic history, RPC channels | Channels dilating with usage and withering when idle | Fold over integer flux list using integer sigmoid | Boundedness: $D \le 1$; withering: $D_{t+1} \le D_t$ | Read (`Physarum.lean`) |
| 6 | **Space Colonization (Runions)** | Demand-driven resource allocation | Dendritic branches growing toward active consumer requests | Grid bucket hashing with integer Manhattan distance | Acyclicity and tree connectivity | Recalled |
| 7 | **Centroidal Voronoi / Lloyd Relaxation** | Memory pool partitions, Multi-fiber boundaries | Organic cell territories dividing shared capacity | Discrete jump-flooding on coarse integer grid | Complete spatial tiling: $\bigcup V_i = \Omega$ | Recalled |
| 8 | **Differential Growth** | Queue backlog pressure, Overfill warnings | Wrinkled, buckling membrane boundaries under strain | Polyline edge subdivision with integer spring relaxation | Boundary non-self-intersection | Recalled |
| 9 | **Reaction–Diffusion (Gray-Scott)** | None (Refused: purely ornamental) | Turing spot and labyrinth textures | Slow 2D grid PDE integration requiring floating-point values | Maximum principle bounds | Recalled |
| 10 | **L-Systems (Lindenmayer)** | Static AST syntax trees | Fractal self-similar branching trees | Pure string rewriting | Formal grammar preservation | Recalled |
| 11 | **Flocking / Boids (Reynolds)** | None (Refused: violates deterministic queueing) | Swarms of steering particles | $O(N^2)$ neighbor searches | Velocity bounding | Recalled |

### Detailed Analysis and Justifications

#### 1. Murray's Law and the da Vinci Pipe Model (Rank 1)
- **What it draws**: Channels that split and merge without discontinuity.
Branch widths sum exactly to trunk widths.
- **Semantics in Effect4**: Represents total volume conservation in the Queue, PubSub fan-out, and Stream merges.
In `sketch.html` Section 4, 4 offered units split into 3 direct admissions and 1 queued offer.
Every pixel of ribbon width represents an actual unit.
There is zero ornament.
- **Fast and exact in Lean**: Arithmetic uses exact natural numbers.
The trunk width is simply the sum of branch widths: $w_0 = \sum w_i$.
It requires no square roots or floating-point numbers.
Execution is an $O(N)$ list fold.
- **Trustworthy law**: Conservation of channel width across every junction.
Lean proves `sum (branches) = trunk` by induction on lists.

#### 2. Horton–Strahler Stream Ordering (Rank 2)
- **What it draws**: Stream network hierarchies where tributary streams merge into larger rivers.
- **Semantics in Effect4**: Models topological depth in `Stream.merge`, PubSub topic trees, and fiber supervision hierarchies.
A channel's Strahler number determines its structural capacity and visual stroke weight.
- **Fast and exact in Lean**: Defined as an inductive function on trees:
```lean
def strahler : Tree → Nat
  | .leaf => 1
  | .node l r => if strahler l == strahler r then strahler l + 1 else max (strahler l) (strahler r)
```
This computation runs in linear time with integer arithmetic.
- **Trustworthy law**: Monotonicity along directed stream paths.
Lean proves that downstream order is strictly greater than or equal to upstream order.

#### 3. Vogel's Phyllotaxis (Rank 3)
- **What it draws**: Concentric spiral arrangements of items inside a circular container.
Points follow $\theta = n \times 137.508^\circ$ and $r = c \sqrt{n}$.
- **Semantics in Effect4**: Solves the spatial scaling problem for `Semaphore`, `Pool`, and large queues.
When capacity exceeds 8 units, a linear horizontal array causes excessive sprawl.
Vogel's spiral packs dozens of permits organically into a compact round vessel.
Hollow rings mark available permits.
Filled dots mark acquired permits.
- **Fast and exact in Lean**: Uses a fixed-point sine and cosine lookup table in thousandths.
Radii compute via integer square root `Grow.isqrt`.
Placement evaluates in a single deterministic pass.
- **Trustworthy law**: Preservation of minimum pairwise distance ($\forall i \neq j, \text{dist}(p_i, p_j) \ge 2r_{\text{unit}}$).
Guarantees zero overlap between unit discs.

#### 4. Constructal Law (Bejan) (Rank 4)
- **What it draws**: Tree networks that minimize resistance between a point and an area.
- **Semantics in Effect4**: Models work distribution from a shared dispatcher to a worker pool.
Channel tapering reflects throughput resistance and routing bottlenecks.
- **Fast and exact in Lean**: Computed via recursive quadtree bisection and integer coordinate scaling.
- **Trustworthy law**: Flow resistance minimization under fixed volume bounds.

#### 5. Physarum Network Adaptation (Tero et al.) (Rank 5)
- **What it draws**: Tubes that dilate with usage history and wither when idle.
- **Semantics in Effect4**: Visualizes route traffic history across long-running pipelines.
- **Fast and exact in Lean**: Already proven in `Physarum.lean`.
Computes via integer thousandths with the gain function `q * q * ONE / (q * q + ONE * ONE)`.
- **Trustworthy law**: `gain_lt`, `adapt_le`, `adapt_idle`, and `conductivity_le` are already machine-checked in Lean.
- **Refinement**: Must be decoupled from instantaneous flux and restricted to outer lumen boundaries.

#### 6. Space Colonization Algorithm (Rank 6)
- **What it draws**: Organic branching networks directed toward attraction markers.
- **Semantics in Effect4**: Visualizes demand-driven resource allocation.
Waiting takers act as attraction points; supply conduits grow toward them.
- **Fast and exact in Lean**: Discretized on an integer grid using spatial bucket hashing.
Heavier than direct tree folds.
- **Trustworthy law**: Acyclicity and structural tree reachability.

#### 7. Centroidal Voronoi Tessellation & Lloyd Relaxation (Rank 7)
- **What it draws**: Organic cell territories dividing shared space.
- **Semantics in Effect4**: Partitions memory buffers and thread pools among competing fibers.
- **Fast and exact in Lean**: Classical Lloyd relaxation requires continuous integration.
A discrete jump-flooding algorithm (JFA) on an integer grid operates in $O(\log N)$ passes.
Still computationally heavy.
- **Trustworthy law**: Partitions form a complete tiling without voids or overlaps.

#### 8. Differential Growth (Rank 8)
- **What it draws**: Buckling, undulating membrane contours.
- **Semantics in Effect4**: Visualizes queue overfill pressure when incoming offers exceed capacity.
- **Fast and exact in Lean**: Requires iterative edge splitting and collision avoidance.
Heavy compute overhead.
- **Trustworthy law**: Polyline self-avoidance.

#### 9. Reaction–Diffusion (Rank 9 - Refused)
- **What it draws**: Turing spots and labyrinthine stripes.
- **Semantics in Effect4**: Purely decorative texture with no semantic counterpart in Effect.
Violates Decisions row 366 (Point 3).
- **Fast and exact in Lean**: Requires floating-point PDE numerical integration.
Slow and non-exact.

#### 10. L-Systems (Rank 10)
- **What it draws**: Rigid fractal plant structures.
- **Semantics in Effect4**: Suited for static AST representation, but poor for dynamic state transitions.
- **Fast and exact in Lean**: Fast string rewriting, but generates static geometric ornaments.

#### 11. Flocking / Boids (Rank 11 - Refused)
- **What it draws**: Swarms of autonomous particles steering together.
- **Semantics in Effect4**: Contradicts deterministic, ordered queue semantics.
Messages in Effect4 do not flock autonomously; they obey strict FIFO ordering.
- **Fast and exact in Lean**: Expensive neighbor search queries.

---

## Part C: Storyboards and Proposals

### 1. Storyboard of Three Beats on the Organism

All motion complies with Decisions row 354, row 367, and `Glyph.lean` (`Kind.grammar`).
Motion occurs within exactly one beat per command.
Transitions use only the four CSS primitives: translate, scale, clip, and opacity.
No motion loops, and no motion pulses.

#### Beat 1: `offer 30, request 3` (Buffer Full: 20 and 10 Held)
- **Bodies that move**: Droplet 30 moves. Droplets 20 and 10 remain still inside the vessel.
- **Path and Primitives**:
  - Droplet 30 (`Kind.body`) translates eastward along the center of the left channel lumen from $x = 0$ to $x = 192$.
  - Parked box 3 (`Kind.vessel`) clips open from left to right at $x = 175$ in the inlet vestibule.
  - Droplet 30 settles inside box 3 and comes to rest.
- **Easing**: Cubic ease-out without velocity overshoot.
- **Membrane and Channels**:
  - The inlet collar remains closed.
  - The vessel hull remains completely stationary.
  - The left channel outer lumen dilates slightly via `.scale` under Physarum adaptation.
  - The inner core displays active flux ($Q = 1$) during transit, then dims.

#### Beat 2: `take, request 4` (10 Exits · 20 Advances · Waiting 30 Enters)
- **Bodies that move**: Droplets 10, 20, and 30 move simultaneously.
- **Path and Primitives**:
  - Answered box 4 (`Kind.vessel`) clips open at $x = 420$ in the outlet channel.
  - Droplet 10 translates eastward from slot 0 ($x = 305$) through the outlet collar into box 4 ($x = 437$).
  - Droplet 20 translates eastward from slot 1 ($x = 257$) to slot 0 ($x = 305$) inside the vessel lumen.
  - Droplet 30 translates eastward from inlet box 3 ($x = 192$) through the inlet collar into slot 1 ($x = 257$).
  - Parked box 3 fades out via `.opacity` from 1.0 to 0.0 as its promise is fulfilled.
- **Easing**: Linear velocity within the beat, settling cleanly at target coordinates.
- **Membrane and Channels**:
  - Both inlet and outlet collars open during transit and reseal upon arrival.
  - Both inlet and outlet channels show active inner flux cores ($Q = 1$).
  - The outlet channel outer lumen dilates via `.scale` as its Physarum conductivity increases.

#### Beat 3: `offer 40, request 8` (Wakes Waiting Taker 7)
- **Bodies that move**: Droplet 40 moves. Taker 7 wakes.
- **Path and Primitives**:
  - Taker 7 sits parked in box 7 at $x = 420$.
  - Droplet 40 translates eastward along the inlet channel from $x = 0$ into slot 0 ($x = 257$).
  - A wake indicator dot inside taker box 7 scales up from 0 to 1 (`.scale`).
  - An organic wake bond vector highlights between droplet 40 and box 7.
- **Easing**: Cubic ease-out.
- **Membrane and Channels**:
  - The outlet collar relaxes outward to signal pending delivery.
  - In the subsequent atomic beat, droplet 40 translates eastward into box 7 and exits.

---

### 2. Proposals Drawn in `gemini-proposals.html`

The self-contained file `docs/research/2026-10-13-living-quantities/gemini-proposals.html` renders all proposals.
The page adheres strictly to the dark look (`#14110d` ground, `#ece6dc` ink, `#48433c` rule) with zero ornamental hue.
The screenshot at `review-input/proposals.png` verifies the complete visual layout.

The proposals include:
1. **The Improved Organism (Figure 1)**: Contrasts the flawed soft-object swelling with the honest capsule lumen.
Features organic valve collars separating boundary vestibules from vessel capacity.
Introduces dual-layer channels separating Physarum conductance from instantaneous flux.
Restores 100% ink contrast to data droplets.
2. **Storyboard of the Three Beats (Figure 2)**: Visualizes the exact motion paths of Beat 1, Beat 2, and Beat 3.
All motion maps directly to the four CSS primitives.
3. **The Run as One Level (Figure 3)**: Extends Section 3 of `sketch.html`.
Projects the run onto a bounded baseline stratum $[0, 2]$.
Traces the level using a Fritsch–Carlson monotone cubic spline with zero overshoot.
Shades pressure above capacity and deficit below zero.
4. **Totals as Conserved Channels (Figure 4)**: Extends Section 4 of `sketch.html`.
Draws the run's aggregate flow using Leonardo da Vinci's pipe model and Murray's law.
Branch widths sum exactly to trunk widths ($40 = 30 + 10$).
5. **Scaled Living Representations (Figure 5)**:
- Left: Implements Vogel's phyllotaxis algorithm for Semaphore permits and connection pools.
Arranges 21 units along a golden-angle Fermat spiral, preventing horizontal sprawl.
- Right: Implements Horton–Strahler stream ordering for concurrent stream merging and PubSub pipelines.

---

## Changes Proposed to Lean Source Modules

### Proposed Changes to `tools/Tools/View/Living/Organism.lean`
1. **Remove taker soft field sources**:
   - *Location*: Line 165 (`Soft.Source.point (takerX cap j) CY 30 900`).
   - *Action*: Delete this field source entirely.
   - *Reason*: Takers waiting represent deficits. Emitting a positive field source creates a false physical swelling.
2. **Decouple waiting offers from the vessel membrane**:
   - *Location*: Line 164 (`Soft.Source.point (offerX j) CY 30 900`).
   - *Action*: Move the offer vestibule further west and isolate it behind a collar boundary.
   - *Reason*: Prevents waiting offers from merging into the vessel hull and visually altering capacity.
3. **Replace ballistic arcs with lumen conduits**:
   - *Location*: Lines 198–202 (`def arc`) and lines 225–232.
   - *Action*: Route message transit through the channel spine coordinates.
   - *Reason*: Units belong to `Kind.body` and must travel inside the transport tubes.
4. **Restore primary contrast to kept droplets**:
   - *Location*: Line 186 (`droplet`: `.shape .ink 300`).
   - *Action*: Change fill opacity from 300 to 1000 (`.shape .ink 1000`), with numerals in ground `#14110d`.
   - *Reason*: Kept data must command primary contrast over structural borders.
5. **Implement dual-layer channel rendering**:
   - *Location*: Lines 141–145 (`channelR`) and line 160.
   - *Action*: Render outer sheath from conductivity $D$ and inner core from flux $Q$.
   - *Reason*: Disentangles historical conductance from active step transfer.

### Proposed Changes to `tools/Tools/View/Living/Soft.lean`
1. **Replace 2D grid marching squares with analytic ribbon hulls**:
   - *Location*: Lines 84–179 (`Grid.of`, `Grid.cell`, `Grid.loops`).
   - *Action*: Replace raster grid sampling with closed Catmull-Rom capsule outlines (W17, W22).
   - *Reason*: Eliminates marching squares rasterization artifacts and speeds up computation.
2. **Increase grid step if rasterization is retained**:
   - *Location*: Line 89 and `Organism.lean` Line 169 (`STEP : Nat := 2`).
   - *Action*: Increase step size from 2 to 4 or 8 pixels, using linear edge interpolation.
   - *Reason*: Reduces grid evaluation points by a factor of 4 to 16, speeding up generation.

### Proposed Changes to `tools/Tools/View/Living/Physarum.lean`
1. **Separate conductance from active flux core**:
   - *Location*: Lines 34–43.
   - *Action*: Export both accumulated conductivity $D$ and step flux $Q$ in the history record.
   - *Reason*: Allows the visual renderer to draw both the structural lumen and the active transport stream.
2. **Prove branch flow conservation theorem**:
   - *Location*: Add downstream theorem.
   - *Action*: Prove $\sum Q_{\text{in}} = \sum Q_{\text{out}}$ across multi-branch junctions.
   - *Reason*: Establishes mathematical trustworthiness for Murray ribbon splits.

---

## Questions for the Owner

1. **Representation**: In the dual-layer channel, should an idle channel with high historical conductivity display its resting lumen outline at a faint opacity, or should it fully collapse to a hairline until new flux arrives?
2. **Domain**: When Queue or Semaphore capacity exceeds a threshold such as 8 units, should the visual language automatically switch from linear slot arrays to 2D Vogel phyllotaxis discs?
3. **Meaning**: How should waiting takers (deficits) be symbolized outside the outlet collar? Should they appear as parked hollow boxes on an external tether line, or as an inward indentation in the vessel wall?

---

## Sources Used

### Read Sources (Cited by Path or URL)
- `docs/research/2026-10-13-living-quantities/README.md`
- `docs/research/2026-10-13-living-quantities/sketch.html`
- `tools/Tools/View/Living/Physarum.lean`
- `tools/Tools/View/Living/Soft.lean`
- `tools/Tools/View/Living/Organism.lean`
- `tools/Tools/View/CellSheet.lean`
- `tools/Tools/View/Glyph.lean`
- `docs/core/decisions.md` (Rows 354, 366, 367, 368)
- `docs/design/design-language.md` (§2, §5.1, §7, §9)
- `docs/research/2026-10-12-visual-semantics/gemini-review.md`
- `docs/research/2026-10-12-whatwg-requests.md` (Asks W16 to W22)
- Tero, Takagi, Saigusa, Ito, Bebber, Fricker, Yumiki, Kobayashi, Higashi, Nakagaki, "Rules for Biologically Inspired Adaptive Network Design", *Science* 327:439–442, 2010. Read via citation in `Physarum.lean`.
- Wyvill, McPheeters, Wyvill, "Data Structure for Soft Objects", *The Visual Computer* 2:227–234, 1986. Read via citation in `Soft.lean`.

### Recalled Sources
- Murray, C. D., "The Physiological Principle of Minimal Work", *PNAS* 12(3):207–214, 1926. (recalled)
- Leonardo da Vinci, *The Notebooks of Leonardo da Vinci* (Pipe Model and Branching Conservation). (recalled)
- Horton, R. E., "Erosional Development of Streams and Their Drainage Basins", *GSA Bulletin* 56(3):275–370, 1945. (recalled)
- Strahler, A. N., "Hypsometric (Area-Altitude) Analysis of Erosional Topography", *GSA Bulletin* 63(11):1117–1142, 1952. (recalled)
- Vogel, H., "A Better Way to Construct the Sunflower Head", *Mathematical Biosciences* 44(3–4):179–189, 1979. (recalled)
- Bejan, A., *Shape and Structure, from Engineering to Nature*, Cambridge University Press, 2000 (Constructal Law). (recalled)
- Runions, A., Lane, B., Prusinkiewicz, P., "Modeling Trees with a Space Colonization Algorithm", *Eurographics Workshop on Natural Phenomena*, 2007. (recalled)
- Lloyd, S., "Least Squares Quantization in PCM", *IEEE Transactions on Information Theory* 28(2):129–137, 1982. (recalled)
- Fritsch, F. N., Carlson, R. E., "Monotone Piecewise Cubic Interpolation", *SIAM Journal on Numerical Analysis* 17(2):238–246, 1980. (recalled)
- Turing, A. M., "The Chemical Basis of Morphogenesis", *Philosophical Transactions of the Royal Society of London B* 237(641):37–72, 1952. (recalled)
- Lindenmayer, A., "Mathematical Models for Cellular Interactions in Development", *Journal of Theoretical Biology* 18(3):280–299, 1968. (recalled)
- Reynolds, C. W., "Flocks, Herds and Schools: A Distributed Behavioral Model", *ACM SIGGRAPH Computer Graphics* 21(4):25–34, 1987. (recalled)

Review complete.
