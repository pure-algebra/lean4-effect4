# Anatomy for the renderer: every measure of the living picture from a law

Status: research note (history, not authority). 2026-10-13. The owner: "there is math for how an
organism is laid out. You don't have to guess… outlines, padding… we can map all those semantics…
it's the reason you study anatomy, so that you can render properly, as a matter of course, not by
guessing." This note maps each measure of the living Queue (`tools/Tools/View/Living/`) to the
physiological law that sets it and to the quantity of the Queue that drives it. It also records
which of Gemini's findings (`gemini-review.md`) the laws answered.

## 1. The measures and their laws

| Measure | Law | Equation | The Queue's quantity | Where | Source |
| --- | --- | --- | --- | --- | --- |
| a channel's sheath | Hagen–Poiseuille, and Physarum's adaptation | `Q = D Δp / L`, `D = π r⁴ / 8η`; `dD/dt = f(|Q|) − D`, `f = |Q|^γ / (1 + |Q|^γ)` | the messages that crossed the channel, over the run | `Physarum.lean`, `Organism.channelR` | Tero et al., *Science* 327:439, 2010, eq. 1 and p. 441 (read) |
| a channel's core | the flux of this step | `Q` of the beat | the messages that crossed it in the step | `Organism.cores` | the keyed join of two markings |
| the vessel's distension | Laplace's law with Hooke's, a thin elastic tube | `T = P r` (wall tension); strain `ΔR / R = (R / E h) ΔP` | the transmural pressure: held less takers waiting, over the capacity | `Organism.Body.vesselR` (`COMPLIANCE`, `COLLAPSE`) | Laplace's law in vessels (lgross.utk.edu, NCBI NBK534265; read in search); the strain step is recalled |
| the deficit | the same law, under negative pressure | `ΔP < 0`: the tube draws in, down to the share it keeps | takers waiting on an empty vessel | `Body.vesselR` | as above |
| the wall's thickness | Laplace at a constant wall stress | `σ = P r / h`, so `h ∝ r` at one stress; youthful arteries keep `r / h` constant | the local radius, read from the field's slope at the wall | `Soft.Grid.walls`, `Organism.wallOf` (`WALL_RATIO`) | PMC5823157 (coronary radius / wall thickness with age; read in search) |
| a unit's room | the cell-free layer (Fåhræus) | a plasma layer of a few microns between the cells and the wall | a waiting offer holds a message: its size and the layer; a waiting taker holds nothing: no room | `Organism.CLEARANCE`, `Body.sources` | the Fåhræus–Lindqvist effect (Wikipedia; a CFL measurement paper, SPIE JBO 21(4) 040501; read in search) |
| a unit in a narrow channel | single-file flow | a cell wider than the tube distends it | a message in transit outside the vessel | `Body.transit` | single-file flow in capillaries up to about 8 μm (read in search) |
| the membrane and its lamellae | an iso-contour of one field; collagen parallel to the surface in cartilage's tangential zone | the contours of the soft field at three levels | none: structure | `Organism.body`, `Soft.Grid.walls` | Wyvill et al. 1986 (soft objects); Benninghoff's arcades (PMC2906441, read in search) |
| junction angles (not yet used) | Murray's optimum | `r₀³ = r₁³ + r₂³`; `cos θ₁ = (r₀⁴ + r₁⁴ − r₂⁴) / (2 r₀² r₁²)` (reconstructed, not checked against Murray 1926) | a split: PubSub's fan-out, the run's totals | not built | arXiv adap-org/9909003, Artery Research (read in search) |
| walls that meet (not yet used) | Plateau's laws | three walls at 120° | compartments that touch: a scope's children | not built | Plateau's laws (Wikipedia, TCD foams; read in search); D'Arcy Thompson, *On Growth and Form*, "Forms of Cells" (recalled) |
| units in a round place (not yet used) | Vogel's phyllotaxis | `θ_n = n · 137.5°`, `r_n = c √n` | a Semaphore's permits, a Pool's items, a large capacity | not built | MathWorld, Vogel 1979 (read in search) |

What stays a constant of the tissue, chosen once and named: the vessel's rest radius, its
compliance (the share of the rest radius it gains at full pressure) and the share it keeps under
suction, the cell-free layer, and the wall's ratio. Each is a property of the material, as `E h`
and `σ` are; none is set picture by picture.

## 2. Gemini's findings, and the law that answered each

| Finding | Answer |
| --- | --- |
| a waiting taker drew an outward swelling: a deficit as mass | a taker holds nothing, so it takes no room; the deficit is negative pressure on the empty vessel, which draws in |
| waiting offers fused with the vessel: three held in a vessel of two | the inlet stands behind a narrow neck, and an offer's room is its size and the cell-free layer |
| a channel's width conflated history with the step | the sheath is the history (Physarum); the core is the step's flux |
| droplets fainter than the walls | a kept message is solid ink, its value above it; the wall's tone is below it |
| motion arcs in the static frames | the static frames draw no arc; motion is the sampled beat, inside the channels |
| node sources with nothing in them: ornament | removed: a place with nothing in it has no field of its own |

Gemini's three questions for the owner stand (`gemini-review.md`, "Questions for the Owner"): an
idle channel's resting lumen faint or collapsed to a hairline; the switch to phyllotaxis above a
capacity of eight; and the takers' mark outside the outlet.

## 3. What this note does not establish

The laws are applied as their equations say, at constants of the tissue chosen once; no constant is
measured from an organism. Murray's angle formula is reconstructed and not checked against the 1926
paper. The strain of an elastic tube is recalled. The picture is a view: no theorem relates its
shapes to the Queue's semantics beyond the marking, the join's flux and the Physarum laws of
`Physarum.lean`.
