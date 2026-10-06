# Tree, graph, binding and replay techniques

The useful direction is a set of typed views and connecting proofs over the existing program data.
The literature does not justify replacing `Eff` with a universal graph representation.
The immediate opportunities are shared path induction and shared handling of environments under binders.

This review reads frozen source `cbd2ec5793006fd1279121c5104bfdbdc065ea40`.
It reads the owner's TYPES 2003 volume, not *Types and Programming Languages*.
It also reads selected primary papers listed below.
It runs no Lean, compiler, generator, build or runtime probe.
Existing theorem declarations below are source evidence, not a new proof or axiom receipt.

## The book and the selection

The volume is *Types for Proofs and Programs*, TYPES 2003, LNCS 3085, edited by Berardi, Coppo and Damiani, published in 2004.
The [publisher record](https://link.springer.com/book/10.1007/b98246) confirms the identity.
The local PDF has 417 pages and SHA-256 `c96a2965756f8388b1bfc4d8ddf890a415e32b219dc1a7ac9eed7ef6af1c7dfe`.
Printed page 210 is PDF page 218, counting from one.

The whole contents lists 25 chapters.
`contents-and-read-status.json` records every chapter and the actual reading extent.
The previous scout read Adams, Ballarin and Wiedijk.
This pass reads Gambino–Hyland and Brady–McBride–McKinna in full.
It reads the named sections of Momigliano–Tiu and the concurrent logical framework chapter.
It screens six further chapters through their abstracts and opening sections.
Extracting a chapter's text does not mean reading its entire argument.

## Six connections

### 1. Generate indexed tree views, then reuse structural induction

**Literature.** Gambino and Hyland, *Wellfounded Trees and Dependent Polynomial Functors*, printed pages 210–225.
Section 2.3 describes constructors by labels and input positions.
Section 5 indexes both constructor outputs and their children.
Theorem 12, page 220, gives initial algebras in a locally cartesian closed category with W-types.
Lemma 13, pages 220–221, isolates the trees whose children have the required indices.
The paper omits the final initiality argument and refers to an earlier proposition.
It is not a Lean proof receipt.
The [chapter record](https://link.springer.com/chapter/10.1007/978-3-540-24849-1_14) provides its DOI.

**Existing consumer.** `Node`, generated children, and `PathYield` already provide the relevant structural boundary.
`yieldAt_subset_of_at` in `src/Effect4/Laws/Program/PathFold.lean` lifts local child inclusion along any successful address.
`layerRefsWF_at` supplies a reference target fact consumed by `Typed/LayerArm.lean`.
Do not create another graph walk for those facts.

**Placement and proposed work.** Concept `initial-algebras-folds`; existing `hom-eq-cata-eff` and the addressed reference consumers serve R8.
For a new consumer, derive its local child facts from the existing constructor signature.
Instantiate the existing path theorem before proposing another induction principle.

**Premises and observation.** Fix the root, successful address lookup, node sort and the local child property.
The conclusion concerns addressed syntax, not machine reachability.
Closed layer bodies and operation-carried terms need their own declared traversal routes.

**Proposed controls and prerequisite.** A nested valid address is the positive control.
A wrong child index and an omitted operation term are separate negative controls.
First name the consumer and confirm which sort owns its fields.
Arbitrary cyclic references are outside this well-founded tree result.

### 2. Consolidate binder-aware proofs around related environments

**Literature.** Allais et al., [*A Type and Scope Safe Universe of Syntaxes with Binding*](https://bentnib.org/binding-universe.pdf), 2018, article 90.
Section 6 gives a semantics interface with environment transport, variables and constructor interpretation.
Section 8.1, Figures 41–44, derives simulation from related environments and compatible constructor cases.
Section 8.2 needs additional environment, quotation and binder conditions for traversal fusion.
Section 9.2 explicitly leaves a richer cross-sharing cyclic representation outside its completed framework.
Semantic functions in this method do not require storing host functions in program syntax.

**Existing consumer.** `Node.binders`, `closedChild` and `childLevel` in `src/Effect4/Program/Binders.lean` already own binder placement.
`PointTyped` and `CaptureTyped` in `Typed/Admission.lean` attach environments to addressed code.
`termMaps_of_typed` in `Typed/Denotation.lean` already combines environment extension, future-world transport and term evaluation.
Its consumer is `syncRow_typed`.

**Placement and proposed work.** Concept `store-typing`, claim `term-typed-maps`, R4.
Use the existing environment lemmas when a new binder term reaches a state operation.
Extract a shared interface only when two actual consumers repeat the same premises.

**Premises and observation.** Preserve the native atom table, typed captures, accepted term type and every later world.
The result maps members of input type A to members of result type R.
It does not admit refused terms or justify arbitrary traversal fusion.

**Proposed controls and prerequisite.** Retain an outer capture through a nested fold as the positive control.
Dropping one binder extension is a negative control.
A closed layer body tests scope reset separately.
The immediate prerequisite is the exact binder census for the new consumer.

### 3. Keep graph typing, reference validity and sharing behavior separate

**Literature.** Kahl, [*Dependently-Typed Formalisation of Typed Term Graphs*](https://arxiv.org/pdf/1102.2653), EPTCS 48, 2011, pages 38–53.
Section 4 types each operation's input and output ports.
Its general graph structure still needs extra constraints to cover all nodes with producers.
Section 5 distinguishes sharing an operation's output from duplicating that operation.
Sections 6–7 use scoped node declarations and fresh names for composition.
The conclusion leaves further algebraic proofs and a fully verified generation toolchain as future work.

**Existing consumer.** `Eff.layerRefsWF` in `src/Effect4/Program/Refs.lean` checks earlier targets, excludes ancestor targets, and requires actual non-reference layers.
The same module states that a layer's path supplies its identity.
`expandRefs` supplies copies for typing; compilation redirects references.
These are different uses of the representation.

**Placement and proposed work.** Concepts `store-typing` and `translation-simulation`; R5 layer behavior and R8 named connections.
A graph display can expose typed reference edges over the existing tree.
Its edge certificate should retain target existence and the existing reference-validity evidence.
An execution claim additionally needs the layer identity and memo observation.

**Premises and observation.** Fix the admitted root and each target path.
Typing a graph edge does not prove reachability, acyclicity, allocation behavior or memo identity.
Lexicographic descent alone is not a global well-foundedness proof over all natural-number lists.
A termination argument needs its finite admitted address domain or another explicit measure.

**Proposed controls and prerequisite.** Compare two references to one allocating layer with two separate allocating layer definitions.
Observe allocation and shared handles, not merely final scalar values.
This is a proposed distinction control, not an executed runtime witness.
The prerequisite is a named layer consumer and its observation.

### 4. Induct on reachable histories with the invariant in the motive

**Literature.** Brady, McBride and McKinna, *Inductive Families Need Not Store Their Indices*, pages 115–129.
Section 7.3, page 126, uses an accessibility witness to justify recursive calls on computed arguments.
Section 7.4, page 127, uses an indexed witness connecting a typed view to its raw expression.
Section 5 distinguishes closed execution from the stronger requirements of reduction under open contexts.
Erasure requires the paper's conditions; it is not permission to discard arbitrary certificates.

Momigliano and Tiu, *Induction and Co-induction in Sequent Calculus*, Section 2.2, pages 297–298, distinguishes inductive invariants from coinductive simulations.
Their rules retain the chosen fixed-point interpretation.
A cycle in a graph does not choose that interpretation for us.

**Existing consumer.** `Reached` in `src/Effect4/Laws/Run.lean` constructs a run from opening and applying commands.
`journal_replays` proves exact reconstruction by induction on that history.
The result includes the run's bookkeeping, not only its final machine.

**Placement and proposed work.** R13 already names `journal_replays` as its top node.
For future restore or typed-reachability claims, strengthen the induction motive with the required world, environment and session properties.
Reuse `Reached.play` and the existing journal action.
This supports Concept `translation-simulation`; new claims still need their own registry placement.

**Premises and observation.** Keep the original program, signature, profile, budgets and a reachable history.
A constructed state with matching final values need not satisfy `Reached`.
Reachability alone does not establish typing; admission and reply premises remain necessary.
Lean already erases propositions, so this is not a proposal for a new certificate eraser.

**Proposed controls and prerequisite.** A reached multi-command run is the positive control.
A hand-modified ledger with the same machine tests the omitted-history premise.
First state whether the desired observation includes the session ledger or only the machine.
Neither finite induction nor an accessibility certificate proves fairness.

### 5. Prove independence before identifying replay orders

**Literature.** Watkins, Cervesato, Pfenning and Walker, *A Concurrent Logical Framework: The Propositional Fragment*, pages 355–377.
Section 2.3, Figure 4, page 364, allows commuting monadic steps only under dependency side conditions.
Page 365 relates the resulting concurrent traces to a Petri-net interpretation with individual tokens.
This gives a method for reasoning about independent steps, not a rule that all adjacent effects commute.

**Existing consumer.** `Run.play_append` in `src/Effect4/Laws/Run.lean` is an action of ordered command lists.
`tape_replays` in `Test/Dogfood/Scenario.lean` connects progressed controls and applied replies to raw replay.
Its theorem is already present at this freeze.
Its premise requires the extracted tape to be fully read.
Its observation is machine equality, excluding the session ledger and lowered engine correctness.

**Placement and proposed work.** Concept `translation-simulation`, existing claim `run-tape-replay`, R8; journal data also serves R13.
Keep the ordered journal as the reference.
If trace reduction becomes a measured need, state one adjacent-swap theorem for a named independence predicate and observation.
Do not quotient the stored journal as a convenience.

**Premises and observation.** Different request keys alone do not prove independence.
Shared store cells, fresh identifiers, scheduler state and ordered logs can couple the steps.
Commutation needs both execution orders admitted and the chosen observations equal.

**Proposed controls and prerequisite.** Two operations with a proved disjoint footprint form a candidate positive control.
A write followed by a read of the same cell is a negative control.
Receiving and applying a reply are another deliberately ordered pair.
The prerequisite is a demonstrated trace-reduction consumer and a proved independence interface.
No general concurrency, fairness or host-call reordering follows.

### 6. Add focused tree views only for a concrete editing consumer

**Literature.** Huet, [*The Zipper*](https://gallium.inria.fr/~huet/PUBLIC/zip.pdf), especially Section 2.2, author PDF pages 5–6.
A focus carries its surrounding constructor context and siblings.
The fixed-arity version reconstructs the containing tree while preserving constructor arity.
It does not prove scoping, typing or execution preservation.
The author's [bibliography](https://gallium.inria.fr/~huet/bib.html) records JFP 7(5), 1997, pages 549–554.
The linked author draft has a placeholder publication header; its section locators are used here.

**Existing consumer.** `Node.replaceAt` already edits the addressed tree.
`replaceAt_spec`, `replaceAt_exists`, `replaceAt_self` and `replaceAt_overwrite` are in `src/Effect4/Laws/Program/References.lean`.
`at_replaceAt_disjoint` preserves lookup below a different child of a common ancestor.
The module explicitly excludes ancestor replacement from this independence property.

**Placement and proposed work.** Concept `initial-algebras-folds`, existing claim `addressed-replacement`, R8 module reconstruction.
If an editor repeatedly changes one focus, derive a temporary context view from the existing signature.
Connect its reconstruction to `replaceAt_spec`; keep `Eff` as the stored program.
Do not introduce a second editable program representation now.

**Premises and observation.** A successful lookup and same-sort replacement justify structural reconstruction and undo.
They do not justify rebinding or relocation of layer references.
An edit can retain shape while invalidating typing or the reference graph.

**Proposed controls and prerequisite.** Lookup after replacement, undo and a disjoint sibling lookup are positive controls.
A same-sort subtree with an out-of-scope variable is a negative control for a proposed typing-preservation extension.
The prerequisite is an actual repeated-focus editing consumer, followed by explicit scope and reference-validity obligations.

## Chapters that do not supply the desired graph theorem

Honsell–Lenisa's graph-like lambda models concern semantic models of lambda calculus and geometry of interaction.
The opening pages 242–244 do not present a finite program-graph reachability theorem.
The title is not evidence for replacing the program tree.

Berghofer's opening pages 66–67 concern Higman's lemma and word embeddings.
That technique could serve a future termination argument with a matching consumer.
It does not establish replay fairness or acyclicity here.

Honsell–Scagnetto's opening pages 324–326 study mobility typing and incremental inference.
Their higher-order binding representation conflicts with this project's stored first-order syntax if copied directly.
They explicitly omit structural congruence and reduction semantics from that encoding.

Baro's pages 51–52 provide a useful separation between program terms, proof engine and interface.
They do not provide the graph or runtime connection sought here.
Soloviev–Chemouil's pages 338–339 concern added conversion rules and algebraic structures over inductive types.
They do not license unrestricted new equations over effectful computations.
Xi's pages 394–396 distinguish static reasoning from dynamic programs.
That is a relevant design comparison, not a replacement for the existing admission and runtime judgments.

## Recommended order

First, map new structural and binder consumers to the existing path and environment lemmas.
Second, make any graph view expose reference-validity and sharing premises explicitly.
Third, use history induction for replay and restore obligations with a precisely named observation.
Keep zipper editing and trace permutation conditional on a real consumer.

Do not prioritize a universal graph theorem, a new stored IR, unrestricted sharing equations, or a general trace quotient.
Do not treat a syntax fold as a scheduled interpreter.
Do not claim a complete compiler proof, infinite-run result or performance improvement from this reading.

## Evidence retained

`source-hashes.json` binds fifteen project files to the frozen commit and hashes the owner's book.
`contents-and-read-status.json` records all chapters and reading scope.
`sources.json` records primary URLs, bibliographic versions and locators.
The `web-*.json` files retain tool-returned reading excerpts and metadata, not downloaded PDF bytes.
The shell download attempt failed because DNS was unavailable.
The browser tool supplied the external readings.
No external PDF hash or complete external download is claimed.
