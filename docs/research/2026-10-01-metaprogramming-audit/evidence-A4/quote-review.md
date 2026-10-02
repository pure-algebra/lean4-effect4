# ProofGraph quotation and axiom-policy review

Reviewed source at `198dd5331eb6607e1e94f3abad39ebbda90c86dc`, Lean `v4.33.1`. The three reviewed files match that revision byte for byte; see `quote-provenance.json`. Read-only review; **no compiler or build was run**, so proposed changes/tests below remain proposals. No active repository files were written.

## Recommendation

Keep the specialized closed-expression quotation for this slice. There is no ready-made `ToExpr Expr`, `ToExpr Level`, or `ToExpr BinderInfo` instance in the pinned Lean source or installed Batteries. Consolidate the three identical semantic axiom filters in `ProofGraph.Proof` instead. This is a small, useful change with already strong tests and does not change the proof boundary.

## Quotation: the bespoke code has a real contract

`tools/ProofGraph/Proof.lean:30–68` implements **Expr-as-data** quotation, not pretty printing or an Expr-to-Syntax delaborator. It preserves binders, constructor fields, literal values, all constant universe arguments, `letE`'s nondependent flag, and projection data. It explicitly erases `mdata` wrappers (line 65), refuses expression free/metavariables (line 68), and has a panic arm for universe metavariables (line 36). `checked_theorem%` first validates the kernel theorem (lines 70–75), so the latter branch is protected by `ProofRef.validate`'s closedness check (line 21).

The pinned `Lean/Expr.lean:567–569` confirms `Expr.hasMVar` includes **both** expression and universe metavariables. This is not a missing universe check. Do not replace it with only `hasExprMVar`.

`Lean/ToExpr.lean:27–33` describes the correct abstraction—values to expressions denoting them—but the available instances do not cover Expr, Level, or BinderInfo. They do cover Name (228), lists (243), literals (262), and FVarId (268). `Lean/ToLevel.lean:22–27` is a different operation: an elaboration-time universe parameter becomes a `Level` value; it is not `Level → Expr` and does not replace `quoteLevel`.

Lean's generic `deriving ToExpr` mechanism exists (`Lean/Elab/Deriving/ToExpr.lean:224–235`). It synthesizes constructor applications and calls `toExpr` for the fields (79–111). It therefore does not impose the existing closedness/refusal policy or erase metadata. For Expr it would also require a chain of field instances (e.g. MVarId, MData/KVMap, Level/LMVarId), and would expand the instance surface for Lean-owned types. The handler can emit partial definitions for nested/mutual types (114–175). Blindly deriving the entire tree is not a drop-in cleanup under the repository's policy.

A locally scoped derived BinderInfo instance could replace four arms, and a derived Level instance plus list ToExpr could replace more code only after providing LMVarId support and preserving the precondition. Neither is a compelling first slice: it installs additional instances to save a few simple constructor lines. A later measured refactor could compare generated declarations/axioms and exact quoted values, but should not claim existing support that is absent from this toolchain.

Do not route `ProofRef` freezing through `ppExpr` or delaboration/re-elaboration. Those are presentation APIs, whereas this field is the proposition inspected by `isDefEq`. A clearer docstring should explicitly say that metadata is erased and that the validated declaration guarantees closure; current “preserving all type arguments” does not explain those boundaries.

## Axiom policy: a safe narrow seam

The same literal policy is repeated at:

- `Proof.lean:26` — named theorem validation;
- `Ledger.lean:54` — named placeholder validation;
- `Search.lean:132–133` — prospective theorem validation before publication.

A single pure helper in Proof.lean, e.g. `disallowedAxioms (xs : Array Name) : Array Name := xs.filter ...`, is enough. Both consumers already import Proof.lean, so there is no new module or dependency direction. Preserve ordering and existing caller-specific errors. Keep the caller's name/kind, universe, type, and closure checks exactly where they are.

**Do not consolidate collection itself without a separate reason.** Existing named declarations use Lean.collectAxioms; unpublished terms have no name, so Search.axiomsOfTheorem collects from both the proposition and proof (`Search.lean:110–125`). The explicit unknown-constant check at 114–115 is significant: Lean's collector silently returns on an unknown constant (`Lean/Util/CollectAxioms.lean:67`). Search's pre-publication check also rejects a forbidden axiom occurring only in the statement, even if definitional reduction discards it. Both behaviors have rejecting controls and must survive.

Do not absorb the full `Test/Audit/AxiomGate.lean` policy into this helper. That gate distinguishes semantic declarations from specifically admitted audit implementation and rendering declarations (`AxiomGate.lean:66–91` and onward), and performs additional declaration-kind/trust checks. Matching the two-name ceiling is not equivalent to passing the full gate. ProofGraph sits below Laws/Conform and currently depends only on Lean/Batteries (see commit `7ab022a6` and `tools/Tools/ArchitectureRoles.lean:101,190`).

## Existing controls and useful additions

Existing controls that should be rerun for a changed policy helper:

- `Test/Audit/ProofGraph.lean:23–73`: proved/wanted counts; missing/stale evidence; ceiling; wrong proposition; non-theorem; mismatched placeholder; dependency cycle; rejection of Classical.em.
- `Test/Audit/ProofGraphSearch.lean:76–190`: rollback portability, fresh polymorphic declaration closure, temporary axiom rejection, kernel type mismatch, unknown constants, statement-only forbidden axiom before publication, preservation of existing theorem references.
- `Test/Audit/Obligations.lean:128–134`: explicit publication of Classical.em rejects with the expected ceiling error.
- `tools/Conform/Cli/BoundaryControls.lean:12–24`: actual `checked_theorem%` client plus theorem/type/axiom reference controls.

Two focused additions make the filter seam reviewable without implementation-mirroring tests:

1. A named placeholder whose proposition contains Classical.choice in an unused let must reject in Ledger.check, while the corresponding ordinary closed ProofWanted accepts. The existing ledger suite tests placeholder type mismatch but not its axiom path. Use an existing Classical constant, not a newly declared axiom.
2. A passing named theorem genuinely depending on the allowed `propext` or `Quot.sound`, plus a rejected Classical theorem, ensures the helper neither accidentally forbids the ceiling nor broadens it. The existing good examples mainly have no axioms.

If quotation is touched despite the recommendation, add permanent controls through the public `checked_theorem%` client for a universe-polymorphic theorem and binder/projection/let shapes, verifying the frozen proposition still validates against the environment and its universe parameter list is unchanged. Metadata erasure and refusal behavior need a deliberately exposed narrow test seam or an elaborator fixture; a pretty-printed equality is insufficient. Do not assert that a handful of shapes proves an all-Expr quotation law.

Suggested narrow validation order (root executes serially with its limits): build ProofGraph; then compile Test.Audit.ProofGraph and the affected direct consumers/fixtures. No full Test sweep is justified by this review alone.

## History and evidence limits

`7ab022a6` introduced this code as the one evidence seam below Laws/Conform, replacing older Conform duplication. `3aa1a9f1` later made Obligation a Prop marker and fixed theorem binder handling; it did not change this quoter. The three reviewed files remain exactly as at the stated base. This review is source evidence, not a fresh passing build, axiom audit, or performance result.
