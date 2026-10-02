# A4 receipt — shared evidence readers

**Before merging:** Gemini can call `ProofGraph.readGoal` from `ProofGraph.Ledger` instead
of copying the private reader. The reader discovers a goal; `ProofGraph.check` and
`ProofRef.validate` still validate evidence. This does not replace the whole-library gate.

Base `198dd5331eb6607e1e94f3abad39ebbda90c86dc`; audit commit `b7f2a10b`;
implementation is the commit containing this receipt, on `codex/metaprogramming`.
A subsequent closing receipt records the implementation's full hash.

Changed files: `tools/ProofGraph/{Proof,Ledger,Search}.lean`,
`src/Effect4/Laws/Auto/Obligations.lean`, `Test/Audit/ProofGraph.lean`, and this research folder.
The goal reader moves verbatim into the generic evidence library. Three identical axiom
filters use one policy function. Statements, diagnostics and collector order are unchanged.
Different inventory universes and the axiom gate's implementation exceptions remain separate.

## Verification

Exact commands, exits, timing and output are in `evidence-A4/`. Lean 4.33.1; every compiler
ran serially with `-j1 -M4096 -DwarningAsError=true` and a 120-second process bound.
Changed modules compiled, followed by Conform.Core.Proof, Auto.Census, Auto.Frames,
Auto.Obligations and the ProofGraphSearch, ProofGraph and Obligations batteries. All passed.
The first new-test run rejected the deliberately malformed definition at the defProp linter;
the fixture now scopes the same linter exception used by the existing legacy-definition test.
No existing expected diagnostic changed.

New controls preserve a polymorphic goal's identity, universes and quantified statement;
refuse a definition posing as a goal and a nested marker; admit propext evidence; and reject
Classical.choice hidden in a placeholder proposition. A separate check confirms the temporary
rejected declaration did not escape the test environment. The helper and new elementary
witnesses use no axioms; the deliberately propext-backed witness uses exactly propext.

The private cache is an APFS copy, never a shared symlink. Before these controls, 920 source
and compiled-file hashes for 301 relevant project/package modules were checked against their
Lake receipts; zero mismatches. Recompiled modules are recorded by their commands instead
of treating their old trace as fresh. No full build, generator, installation or whole-tree
gate ran. Other consumers of Auto.Obligations have not all been recompiled; this is a narrow
receipt, not a sweep or a machine-safety claim.

Independent source review found no change in the goal reader, axiom policy, binders or
universe handling. Retained closed-expression quotation: the pinned Lean has no appropriate
ToExpr Expr/Level/BinderInfo instances; general derivation is not the same boundary.

## Held work

DI-18 requires an owner ruling before adding Lean.Parser.Do to Sugar; the experimental
patch is held outside this branch. Macro fallback policy, global unexpanders and module moves
remain proposals. No authority register, root import, gate, generated artifact, Claude file
or Gemini-owned file was edited. No new semantic proof obligation was introduced.
