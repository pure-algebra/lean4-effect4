# Reference faults use the module table

The one thing to know first: partial table placement cannot update a whole-document reference refusal.

Status: implementation plan and receipt for the documents seat.
Base: `cd2cea0de813ed2e22ecf53f1c0eb6c20468b131`.
Branch: `codex/abstractions-documents`.

## Finishing criteria

- Keep `SourceSession.Coherent` equal to the exact `Sketch.sourceTable`.
- Splice only when the old sketch and candidate have no ill-formed reference.
- Recheck all other candidates through the existing module oracle.
- Check the retained draft, kept edit, document, replay, undo and subtree controls.
- Build the touched modules, audit their declarations and run `make check-ocaml`.
- Exercise the generated fix through the native tool.

## Placement and scope

Concept: `initial-algebras-folds`.
Requirement: R14.
Claim: `source-feed-coherent`, whose pointer is `SourceSession.feed_coherent` in `src/Effect4/Laws/Program/SourceTable.lean`.
Consumer: `Doc.coherent`, document replay and undo.
Reach: accepted source edits from coherent sessions, every feed policy and certified checker oracles.
This slice repairs the two false planned statements, `feed_draft` and `feed_keepExact`.
Their reasons cite the retained counterexamples.
It proves no new theorem and leaves the coherence statement unchanged.
The proof seat owns the proof work and the retained counterexamples.
The invariant remains exact table equality, including malformed drafts and refused roots.
Finite controls establish only their concrete observations.
The native gate tests generated behavior within the existing LCNF lowering trust boundary.

## The repair

Add `SourceSession.canSplice` beside `expandedEditAgrees` in `src/Effect4/Program/Typing/SourceSession.lean`.
It requires expansion agreement and no reference fault in either sketch.
Both fast paths use this predicate.
A draft with an invalid reference accepts the rechecked source table.
A kept edit with an invalid reference refuses through the existing module check.
The document and fill set keep their existing representations.

## Before the repair

`python3 /private/tmp/seams-lean-one.py lake build Test.Program.SourceFeedControls` fails.
The six failed guards cover draft coherence, kept refusal, unrelated kept edit, undo, document coherence and replay coherence.
Log: `/private/tmp/documents-red-build.log`.
The control that removes a reference fault and the wide-subtree control already pass.
The historical kernel counterexamples remain at `git:84f88cf6f:src/Effect4/Laws/Program/SourceTable.lean`.

## Verification

The first narrow run fails six concrete guards before the repair.
The focused repaired build passes with the document controls.
The final law build includes the corrected planned statements.
Its audit reports `269 declarations within [propext, Quot.sound], 2 of them modulo planned goals; 8 planned goals`.
The core and focused-control audit alone reports `210 declarations`, without planned goals or declarations that rest on them.
The audit driver is temporary and imports the document controls plus `ProofGraph.AxiomAudit`.
Its command is:

```lean
#axiom_audit Effect4.Program.Typing.SourceSession Effect4.Laws.Program.SourceTable Test.Program.SourceFeedControls
```

The exact narrow commands are:

```sh
python3 /private/tmp/seams-lean-one.py lake build Test.Program.SourceFeedControls
python3 /private/tmp/seams-lean-one.py lake build Effect4.Program.Typing.SourceSession Test.Program.SourceFeedControls Test.Program.SourceDocumentControls
python3 /private/tmp/seams-lean-one.py lake build Effect4.Laws.Program.SourceTable Test.Program.SourceFeedControls Test.Program.SourceDocumentControls Test.Program.SourceFeedAudit
```

`make check-ocaml` regenerates the native file and passes the new N5 controls.
N5 checks kept refusal, refused-root drafts, module rechecking, the edited source entry, fault removal and a wider subtree.
The final gate command routes nested Lake calls through the prescribed wrapper:

```sh
PATH=/private/tmp/abstractions-lean-bin:$PATH make check-ocaml LAKE=lake
```

The initial cold gate calls its nested Lake processes without that shim.
The final command checks the same inputs with the shim selected.
`documents-validation.txt` retains the before/after controls, audit and native result excerpts.

This landing does not prove `feed_coherent` or the document laws that rest on it.
It does not import the proof seat's work.
The planned statements remain planned, with their existing consumers.
Native tests remain finite evidence under the LCNF translation trust boundary.
No full battery, whole-tree axiom gate, semantics generation or TypeScript gate runs.

The final wrapped gate exits with code zero and reports `PASS ocaml: shared result d2cb13c4df0c`.
The initial execution records the same key after running the native controls.
`git diff --check` passes.
The targeted controlled-English check reports no finding in the research note or receipt.

## Commits and changed files

Base: `cd2cea0de813ed2e22ecf53f1c0eb6c20468b131`.
Implementation head: `7d4987dbdd2611329f8ecc3c05d2514536bcfaa3`.
Core repair: `f94116005e52047837ddccb06d615fb77a836350`.
Planned-statement repairs: `7d4987dbdd2611329f8ecc3c05d2514536bcfaa3`.

The changed implementation files are:

- `src/Effect4/Program/Typing/SourceSession.lean`
- `src/Effect4/Laws/Program/SourceTable.lean`
- `Test/Program/SourceFeedControls.lean`
- `ocaml/engine/test/kit/test_tool.ml`
- `ocaml/gen/api_gen.ml`
- `ocaml/gen/closure-api_gen.tsv`

The research note, this receipt and `documents-validation.txt` carry the written results.
No file on the proof seat's branch changes.
The parent must update its stronger proof-seat route lemmas to use `canSplice` when it integrates that work.

## Exact splice address statement

The existential splice clause does not specify which addresses the step reports.
Replace it with the source addresses below the edited path, in source order.
The expression is independent of the cached verdict and its table.
It includes the edited address and every descendant that remains in the source program.
It excludes descendants introduced only by reference expansion.

Placement: `initial-algebras-folds`, `source-feed-keep-exact`, R14.
The required property remains exact kept editing, with document commits and fill certification as consumers.
The reach remains coherent sessions, accepted kept edits below the root and `canSplice = true`.
This strengthens a planned goal and proves no new theorem.
Wider-subtree and reference-bearing finite controls check the exact expression.
The runtime, generated code and existing native gate result remain unchanged.

The exact clause in `feed_keepExact` is:

```lean
(s.canSplice next.sketch e = true → step.delta =
  .spliced ((Node.addresses (.eff next.sketch.program)).filter (Table.under e.path)))
```

The follow-up command is:

```sh
python3 /private/tmp/seams-lean-one.py lake build Effect4.Laws.Program.SourceTable Test.Program.SourceFeedControls Test.Program.SourceDocumentControls Test.Program.SourceFeedAudit
```

The temporary driver imports the document controls and `ProofGraph.AxiomAudit`.
It audits `Effect4.Laws.Program.SourceTable` and `Test.Program.SourceFeedControls`.
The build passes, including the wider-subtree and valid-reference controls.
The audit reports `92 declarations within [propext, Quot.sound], 2 of them modulo planned goals; 8 planned goals`.
The existing runtime gate receipt remains valid because this follow-up changes only a planned proposition, finite controls and documentation.
