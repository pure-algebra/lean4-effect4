# Literature read and its project use

Status: source-grounded research, not imported proof evidence.
Sources were read on 2026-10-10.
No upstream theorem is claimed as an Effect4 theorem.
The implementation and probes have separate receipts.

## Huet: The Zipper

Primary source: [author PDF](https://gallium.inria.fr/~huet/PUBLIC/zip.pdf), sections 1.1, 1.2, and 2.2.
The location retains a subtree and its surrounding context.
Section 2.2 derives context forms from constructor arities.
Section 1.2 explicitly bounds upward movement by the number of older siblings.

Application: derive typed editor contexts from `LayerView` and reconstruct the existing `Eff` tree.
Do not promise constant-time movement for arbitrary variadic lists.
The project needs its own reconstruction and replacement connectors.
The program-graph note's blanket movement claim needs this qualification.

## Cai, Giarrusso, Rendel, and Ostermann: A Theory of Changes

Primary source: [paper](https://arxiv.org/pdf/1312.0658), definition 2.4 and section 4.3.
The update law relates a changed output to fresh evaluation after an input change.
The differentiation result relies on the chosen primitives meeting its change interface.
Correctness and performance are separate claims.

Application: require the same commuting square for page and table updates.
`Sketch.table_fill` already supplies a concrete part of that structure.
Retain the old calculation as the independent reference for each optimized consumer.
No general differentiator or higher-order stored syntax is introduced here.

## Acar, Blume, and Donham: Self-Adjusting Computation

Primary source: [paper](https://arxiv.org/pdf/1106.0478), consistency and correctness results.
The semantics combine dependency traces, memoization, and change propagation.
The authors machine-check the metatheory in Twelf.
Their store and primitive-operation premises belong to their language.

Application: record the inputs each retained view reads before implementing selective invalidation.
Compare propagation with a fresh calculation on the same updated input.
An arbitrary digest cache does not satisfy that obligation.
Effectful host calls must not be replayed merely because a display dependency changed.

## Plotkin and Power: Tensors of Comodels and Models

Primary source: [paper](https://homepages.inf.ed.ac.uk/gdp/publications/Tensors_Comodels_Models.pdf), definition 3.1 and theorem 4.4.
A comodel supplies the dual interpretation of the operation theory.
Theorem 4.4 describes interaction with a free model through the comodel state and returned value.
It assumes the stated Lawvere theory and comodel structure.

Application: reuse Effect4's comodel interpretation and its composition laws for host interaction.
Keep the syntax graph and the session transition graph distinct.
A drawing is an observation of that interaction, not its semantic definition.
The result supplies no scheduler fairness or physical-host theorem.

## Xia et al.: Interaction Trees

Primary source: [paper](https://www.cis.upenn.edu/~stevez/papers/XZHH%2B20.pdf), figure 11 and the discussion of silent divergence.
The interpreter respects return, operation triggering, and monadic composition.
The coinductive account retains potentially infinite interaction and internal steps.

Application: organize host interpretation proofs around shared composition laws.
Keep live frontiers as unfinished observations when computing finite prefixes.
Do not import function-valued continuations as canonical Effect4 syntax.
The existing first-order programs and explicit decision inputs remain the representation.

## Morin: Open Data Structures, adjacency lists

Primary source: [section 12.2](https://opendatastructures.org/versions/edition-0.1e/ods-java/12_2_AdjacencyLists_Graph_a.html).
Incoming-edge queries otherwise scan many unrelated adjacency lists.
A second index exchanges retained data and construction work for cheaper incoming queries.

Application: retain stable incoming edge occurrences for the existing placement calculation.
Effect4's payloads and duplicate occurrences must survive indexing.
The sparse natural-key implementation also retains out-of-range positions permitted by the current theorem.
Its receipt measures actual Lean execution separately from edge-visit counts.

## MCP 2026-07-28

Primary sources: [base protocol](https://modelcontextprotocol.io/specification/2026-07-28/basic),
[tools](https://modelcontextprotocol.io/specification/2026-07-28/server/tools),
and [wire schema](https://github.com/modelcontextprotocol/modelcontextprotocol/blob/main/schema/2026-07-28/schema.json).
The base protocol requires self-contained requests and explicit identifiers for state spanning requests.
Connection identity supplies no authoring context.

Application: every prototype call carries canonical program and hole bytes.
The cache changes no answer and grants no implicit previous snapshot.
The driver returns preview bytes without publishing a shared root.
The protocol schema hash and independent validator version appear in `mcp/protocol-results.json`.
This finite probe establishes no compatibility with every MCP requirement.

## Additional sources read by the independent session reviewer

[Ahman and Bauer, Runners in Action](https://arxiv.org/pdf/1910.11629), definition 2 and proposition 3,
relate effectful runners and monad morphisms.
Their finalization guarantees require their calculus's conditions.
They suggest reuse of `Comodel.run_bind` and routing laws, not automatic guarantees for physical hosts.

[Foster et al., lenses](https://www.cis.upenn.edu/~bcpierce/papers/newlenses-popl.pdf), section 3.2,
gives the familiar GetPut, PutGet, and PutPut laws.
Existing replacement laws supply the relevant structural counterparts.
Undo alone does not establish disjoint edit commutation or omission renumbering.

[Hinze and Paterson, finger trees](https://ora.ox.ac.uk/objects/uuid%3A4083c1c6-0c3a-4505-8319-d80bb4033d88)
provide measured persistent sequence operations.
They are a candidate for later table split and concatenation work.
This packet does not introduce them or claim a performance result from them.
