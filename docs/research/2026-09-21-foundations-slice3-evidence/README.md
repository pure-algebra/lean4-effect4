# Slice 3 verification evidence

`statements.log` is the declaration checkpoint (15 open obligations).
`targeted.log` checks all slice 3 modules and the preflight counterexamples.
`make-build.log` and `make-check.log` are the final passing full checks for this slice.
`final-audit.log` is a fresh declaration-backed unique ledger and axiom report, emitted
by `lake env lean -DwarningAsError=true FinalAudit.lean` at this folder's path.
`source-sha256.json` pins the touched Lean sources at verification.

`interrupt-inputs.log` additionally checks the proposed catch premises and handler result.
All retained commands returned exit 0. The initial attempts exposed a type annotation,
record layout, an opaque subtype reduction, and an import below the Test root gate;
these were corrected before the retained passing runs. No failed elaboration is proof
of its attempted statement. The input review's old probes remain historical evidence
at their own source hashes; this folder is the evidence for the implementation.
