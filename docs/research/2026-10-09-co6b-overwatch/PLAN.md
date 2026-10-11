# CO-6b work-in-progress review plan

Review the committed plan and row 339 at `c2288f02`.
Freeze the current TypeScript printer and its law changes separately from that commit.
The implementation remains work in progress until its author commits it.

## Placement

| Probe | Concept and requirement | Claim and consumer | Reach and limit |
| --- | --- | --- | --- |
| Generated declaration names | exact-codecs, R2/R3 | `printed-modules`, service printer refusal | finite positive and negative controls; target typing separate |
| Service formation | exact-codecs, R5 | proposed formation judgment in the CO-6b plan; printer domain | existing roles and declared requests; no client execution claim |
| Module round trip | exact-codecs, R5/R8 | `module-defs-round-trip`; service reader | readable blocks with services; no target execution claim |
| Shared authoring | translation-simulation, R2/R8 | plan's role-inertness obligation; Queue and Semaphore exports | declaration roles stay separate from execution and handles |

Keep all production files, owner rulings, and the Claude session unchanged.
Use read-only scouts and isolated probes.
Run one narrow Lean process at a time, with `LEAN_NUM_THREADS=3`.
Check TypeScript only with the pinned tsgo 7.
No full sweep, merge, push, or message to Claude belongs to this review.

## Finish criteria

- Distinguish the ruled design from the current uncommitted implementation.
- Reproduce any reported defect with a positive control.
- Record exact source hashes and the limits of an extracted probe.
- Recommend the smallest repair without expanding the author interface.
- Save a checkpoint without repeating unchanged host findings.
