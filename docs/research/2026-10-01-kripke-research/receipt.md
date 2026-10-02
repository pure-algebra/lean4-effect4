# Kripke research receipt

The research supports the existing world-based proof design, with a precise boundary: persistence of selected typing facts does not establish valid machine transitions. No production contract was changed and no new reachable failure was found. Documentation wording and a focused transition-premise investigation are proposed for coordinator integration.

Base implementation: `26c7be34e6fea61fe2d13c4fa80d9bcd80d414d5`, branch `codex/metaprogramming`, isolated worktree `/Users/pooks/.codex/worktrees/metaprogramming-audit/lean4-effect4`. This receipt is retained in the research-only commit following that base; the commit containing it supplies the research head without a self-referential stamp. Main and Gemini's active files were not edited. No push or merge was performed.

## Evidence and limits

- Two focused GPT-6.1 Sol reviewers independently inspected architecture and primary literature. Their notes are retained alongside the synthesis. Their results are source review, not compiler runs.
- The parent compiled `KripkeProbe.lean`, importing the actual `Effect4.Laws.Program.Typed.Residual` graph. Fifteen declarations have printed axiom receipts: twelve use only `propext` and `Quot.sound`; three use no axioms. Supporting declarations were checked transitively. There is no `sorry`, `native_decide`, new axiom or production-file change.
- The checked controls cover world-box laws, existing membership/program persistence, valid-origin and invalid-extension stores, shared versus per-world witnesses, and generic protocol continuation obligations. The generic protocol example is not a refutation of production `TypedProg` or its handlers.
- The no-build freshness preflight reported all 393 prepared jobs up to date; the reused checker verified 1,051 saved artifact hashes and resolved project/package imports against this worktree. The compiler toolchain is pinned to `leanprover/lean4:v4.33.1`. Preflight output includes replayed historical elaboration messages; those are not newly executed ledger or axiom checks.
- The probe used one compiler thread, Lean's 4,096 MB memory setting and a 180-second external timeout. Final Lean exit was zero in 5.182 seconds. No full build, generator, TypeScript compiler or runtime test was run.
- The existing broader Laws build remains outside this check; earlier Bookkeeping errors and the owner's separate repairs are unchanged by this work. No performance improvement or complete machine safety claim follows from this research.

## Recorded execution

Working directory: `/Users/pooks/.codex/worktrees/metaprogramming-audit/lean4-effect4`.

The scratch harness reused `scripts/check-semantics.py`'s `require_artifacts` for freshness, import resolution and saved-output verification. Its Lake command was:

```sh
lake --no-build --no-cache --rehash build Effect4.Laws.Program.Typed.Assembly Test.Program.TypedProgBindRed Test.Audit.SemanticsCensus Drivers.Semantics Drivers.SemanticsControls
```

The isolated proof command was:

```sh
LEAN_NUM_THREADS=1 lake env lean -j1 -M4096 -DwarningAsError=true /private/tmp/codex-second-eyes-2026-10-01/kripke-research/KripkeProbe.lean
```

The copied probe's SHA-256 is `cd9a00fac8c5cffd6a87e852245b798a72b2b7b52df3f7b7598210c8b2faec22`. The complete command record and saved-output hashes are in `probe-receipt.json`; compiler diagnostics and axiom output are in `probe.log`. `source-snapshot.json` binds reviewed source and vendored text bytes. `recorded-runner.py` preserves the exact historical scratch harness, including its fixed paths; its JSON `probe.exit` and `result` fields carry the outcome rather than the Python process exit status. It is an execution record, not a new project check command.

The initial sandboxed preflight could not update local Lake hash caches. An approved rerun in the isolated worktree passed. The first actual compile found two unused binder warnings, treated as errors. Renaming those unused binders fixed the probe; the second compile passed. The first diagnostic log is retained as `attempt-1-probe.log`. No statement changed between attempts. Larger permission/failure records remain outside repositories under the scratch research directory.

For a fresh reproduction, use the retained probe path in the proof command after checking the same source/artifact boundary; refuse stale imports instead of silently building a different revision. The source-only review of `Bookkeeping`, historical test files and literature is not promoted to fresh proof evidence by this preflight.

## Finishing checks

The final file check verifies the probe against its receipt hash, all source snapshot hashes against current files, every copied evidence file byte-for-byte, fifteen printed axiom records, local Markdown file targets, and the exact new-file allowlist. `git diff --check` covers the staged research packet. No tracked implementation changes are part of this research commit.
