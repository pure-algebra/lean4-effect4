# Literature read for this design

These are primary sources read during this review.
The mappings below propose Effect4 work.
They do not import a runtime theorem from another system.

## Random descent

Vincent van Oostrom and Yoshihito Toyama, *Normalisation by Random Descent*, FSCD 2016.
[Publisher PDF](https://drops.dagstuhl.de/storage/00lipics/lipics-vol052-fscd2016/LIPIcs.FSCD.2016.32/LIPIcs.FSCD.2016.32.pdf).

Read scope: abstract, introduction, measured rewrite systems, and the distinction between local diagrams and global reduction properties.
The paper generalizes length to a measure and discusses macro steps alongside micro steps.
It supports separating scheduler observations from a chosen step-count measure.
Our strict 0/0-or-1/1 diamond remains a separate sufficient criterion.

The original note's remembered RTA 2007 citation is not verified here.
Use this verified source with its actual title and scope.
No theorem about Effect4 follows until the machine relation satisfies the required premises.

## Deterministic parallel access

Robert L. Bocchino Jr. and colleagues, *A Type and Effect System for Deterministic Parallel Java*, OOPSLA 2009.
[Author PDF](https://rob-bocchino.net/Professional/Bocchino-OOPSLA-2009.pdf).

Read scope: region and effect noninterference, aliases, and commutativity annotations.
The paper separates read/write effects by regions.
Its commutativity annotations require verification outside the compiler's check.

The useful adaptation is inferred origin-based access summaries.
Effect4 should prove a closed update family's answer-and-store law once.
A Boolean supplied by an author is not that evidence.
This proposal neither reuses Java's region language nor adds a second Eff representation.

## Monotonic state and reads

Lindsey Kuper and Ryan R. Newton, *LVars: Lattice-based Data Structures for Deterministic Parallelism*, FHPC 2013.
[Author PDF](https://users.soe.ucsc.edu/~lkuper/papers/lvars-fhpc13.pdf).

Read scope: monotonic writes, threshold reads, the determinism theorem, and the termination discussion.
The determinism theorem compares irreducible configurations.
The paper treats termination transfer as a separate unresolved issue there.

The useful lesson is to restrict what a concurrent read can reveal.
Our first fragment uses a join barrier before observing cells with shared addition updates.
The fragment separately accepts shared read-only cells.
A future monotonic data type would need its own read semantics and proof.
This paper does not establish Effect4 callback counts or R12.

## Local sources remain the implementation authority

`NativeOp.row` and `Stores.refStep` define the supported operations in this checkout.
`Program.interpOf` and `Program.evaluatorFor` supply the concrete machine interpretation.
`Machine.obs` defines the observation used in the new controls.

The literature suggests proof structure.
The local definitions determine every premise and observation of the proposed theorems.
