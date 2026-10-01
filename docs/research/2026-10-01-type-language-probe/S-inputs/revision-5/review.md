# Reconciled Schema scout: annotation repair verified

**Ready to brief the narrow readable-Schema addition.** The annotation defect from revision 4 is repaired in the supplied prototype, the previous fixes still pass, and this review found no new blocker in the changed policy. This is readiness for a scoped implementation brief, not acceptance of a completed production compiler or a general preservation proof.

Reviewed main: `c007d0eff6b0e6961c0097c61afda88f12aa9dc3`. Reviewed [report](gemini-report.md) and exact probe snapshots are pinned by [input hashes](inputs.json). All review work and results are in this temporary directory; no active repository, worktree, branch, UI or Claude seat was changed or contacted.

## What now holds

**Behavior-changing annotations are refused before code is emitted.** The object policies that reject extra fields or retain them, and the filter policy that disables integer checks, now return located refusals. Two independent Lean equations establish those results; the object equation covers any option string. The new validator, filter processor, property processor, emitter and six reviewer equations use only `[propext]` in the printed axiom reports.

**Validation reaches the accepted positions.** In addition to the supplied 16 guards, the review exercises all 16 accepted node constructors with both unsupported annotations and passing documentation/empty-bag neighbors. Separate controls cover property bags, tuple-element bags, filter bags, child schemas, array rest schemas, union members, check-child schemas, nested paths, mixed bags, and the excluded `brands` key. The tests do not merely replace the previous bad outputs with an always-refusing implementation.

**The allowlist matches the stated observation.** An independent [static source review](annotation-review.md) checked all eight allowed keys against the pinned parser, reconstruction and metadata consumers. `default` is documentation here, not the separate runtime constructor-default mechanism. Identifier/reference presentation and error messages can change, and remain outside the claimed observation. Metadata payload shapes are not generally validated; this is an emission profile, not a general annotations checker.

**Allowed metadata passed the host controls.** The harness reconstructs source schemas through JSON persistence and compares them with actual Lean-emitted expressions. There are 144 acceptance/decoded-value comparisons: all eight documentation keys separately, their combined bag, and documentation on properties, tuple elements and integer filters, with passing and rejecting values under both default and strict excess-property options. They agree on these cases. The three previously unsafe annotation examples now have no emitted expression.

The existing number-boundary, nested-record, modifiers, escaped-key, tuple, array and union controls still pass. TypeScript accepts the generated supported examples and their type assertions, with rejecting controls for wrong types and modifiers. Historical duplicate-key output remains an explicitly historical compiler rejection (TS1117); the current prototype refuses that source before generation.

Evidence: [audit source](DefinitiveSchemaAudit.lean), [Lean output](schema.log), [runtime harness](runtime.mjs), [runtime output](runtime.log), [type controls](inference.ts), [host results](host-results.json).

## Boundaries to retain in the implementation brief

1. **One narrow addition.** Reuse `Representation` and its existing fold, keep the document export unchanged, and add the readable export without a second schema AST. Carry the exact refusal profile, annotation allowlist, rc.112 pin and observation into the brief.
2. **Finite target evidence remains finite.** The host controls exercise the stated examples; they do not prove every admitted representation preserves acceptance, decoded values or inferred types. Diagnostics, tooling metadata and nominal branding are excluded. `Schema.Natural` covers the target's safe non-negative integers, not all Lean naturals.
3. **Record execution and read-back remain separate work.** Recursive canonical environments, general checker/evaluator agreement, the typed printer/reader relation, and row 128's production exactness proofs are still owed. The revised status matrix now says this. The whole-union model is evidence for the needed check, not the production codec theorem.
4. **Static-layout preparation is still proposed.** The generic sort/map theorem is a useful ingredient. The supplied evaluator still sorts dynamically. Preparing a layout once needs its implementation and an evaluator-agreement argument, including evaluation/refusal order. Read the prose about eliminating runtime sorting as the intended optimization, not a completed result.

There is no need for another broad scouting rewrite before drafting this bounded brief. One small report correction: the unchanged projection file has ten guards, not seven. Its comparator and insertion/map lemma have no axioms; its sorting/map law uses `[propext]`, as the detailed audit already states.

## Verification receipt

- [verify-lean.py](verify-lean.py): sequential Lean 4.33.1, one thread, 1,536 MiB, 30-second limit per command. Original schema, projection and union probes pass with the added controls; no forbidden axiom appears in the printed audits. The supplemental equations retain the reviewer's local recursion-depth setting from revision 4; original probe bytes are unchanged.
- The verifier rechecked 1,372 source/artifact hashes. All 49 imported non-toolchain source hashes were also rechecked against the reviewed main/package sources. The two previously inspected differences from the isolated import snapshot remain document-key naming in `Bridge` and comment-only fiber labels; neither changes the definitions exercised here. [Import provenance](import-provenance.json).
- [verify-host.py](verify-host.py): Node v22.23.2, Effect 4.0.0-rc.112, TypeScript 5.9.2, sequential processes with a 1,024 MB heap and 30-second limit. The five relevant installed Effect source files match the vendor hashes, including `SchemaParser.ts`. [Host pins](host-pins.json).
- Commands, process limits, exits and elapsed times: [Lean results](lean-results.json), [host results](host-results.json). Expected outcomes are exit 0 for the current probes and positive type checks, and exit 2 with TS1117 for the historical malformed TypeScript control. The TypeScript checks are independent controls, not the project's separate TypeScript 7 gate.

No full build, generator, installation or scheduled campaign sweep was run.
