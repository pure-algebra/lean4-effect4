# Independent slice 4 evidence

All retained command logs finish with exit 0. `targeted.log` checks the independent laws,
their new batteries and the unchanged scheduler/defect counterexamples. `make-build.log.gz`
checks the full proof/test closure and trust ceiling. `make-check.log.gz` additionally checks
fresh root elaboration and generated-byte drift.

The two full logs and four statement snapshots are deterministic gzip archives. Their
decompressed bytes are exactly the original output/source, including diagnostic trailing
tabs and the checkpoint's trailing blank line; no evidence text was trimmed to satisfy a
whitespace check. The statement manifest hashes refer to decompressed source bytes.

`statements.log`, `statement-snapshot/` and `statement-sha256.json` retain the eleven-obligation
checkpoint before payload filling and checked-reference registration. The seven adapted
generic protocol proofs are already present in that snapshot; the ledger still reports
them open. The checkpoint is architecture/declaration evidence, not eleven proved payloads.
The final C2 implementation adds one checked lookup helper, giving twelve closed obligations.

`FinalAudit.lean` emits `final-audit.log`: the fresh binder audit, unique production ledger,
nine remaining names and transitive axiom report for every backing proof in this landing.
It runs as:

```sh
lake env lean -DwarningAsError=true docs/research/2026-09-21-foundations-slice4-evidence/FinalAudit.lean
```

`VendorInterruptProbe.ts` calls the actual pinned continuation selector, failure/success
evaluators and run loop. `vendor-probe.json` records six passing finite controls;
`vendor-sha256.json` pins the two implementation files. Run it from the repository root:

```sh
bun docs/research/2026-09-21-foundations-slice4-evidence/VendorInterruptProbe.ts
```

Those manually constructed host states establish neither source reachability nor a
whole-machine simulation. The findings and the held-contract boundaries are in
`../2026-09-21-foundations-independent-probe-disposition.md`.

`source-sha256.json` pins the touched Lean sources and the unchanged held contracts,
evaluator and earlier counterexamples. `source-check.json` checks the snapshot hashes,
unchanged main obligation statements, nine unchanged open names, and the runtime/source fence.
Run `python3 docs/research/2026-09-21-foundations-slice4-evidence/verify-receipt.py` to repeat it.
No failed elaboration attempt is proof evidence; local type-inference/rewrite issues and
the expected-message fixture were corrected before the retained passing runs.
