# Semantics freshness repair

Before merging: the first requested semantics run after adoption intentionally ignores
an older receipt and performs the existing preflight. It never prepares artifacts or
installs dependencies. An unchanged successful run remains cached. No proof statement,
registry entry or generated report changes in this slice.

Base: `c60c2f7c41634ae5166ec30335a80873d70ff0a8` (`claude/proofs`).
Branch: `codex/proof-infra-freshness`. This receipt belongs to the same commit as its
repair; resolve its head with
`git log -1 --format=%H -- docs/research/2026-10-02-proof-infra-audit/freshness-receipt.md`.

## Contract and finishing criteria

The consumer is `make gen-semantics` / `make check-semantics`. A prior successful
marker must not suppress the existing validator after a build-configuration edit,
deleted source/import/trace, or missing report. The change is finished when the real
Makefile's cache decisions have passing and rejecting controls, unchanged input still
skips, and failed final validation leaves the maintained reports intact. This is a
cache contract, not a new semantic obligation or a claim of proof soundness.

## Reproduction and change

At the base, isolated `make -q` controls returned 0 after changing `lakefile.toml` or
`lake-manifest.json`, deleting an imported `.olean`, or deleting the report before
generation. The check target rejected the missing report as a missing Make prerequisite,
before the existing checker could give its located diagnostic. The prior graph slice
had already repaired source edits and imported-artifact replacement; this repair does
not repeat that earlier finding.

The successful run receipt now remembers input filenames. Make reads that metadata
without loading Lean and fails closed to its existing preflight when a remembered file,
report or valid receipt is missing. It also watches the Lake configuration, package
manifest, Makefile, package sources/configuration and resolved import traces. Live
discovery still detects additions. A changed inventory during generation refuses
publication. The actual artifact/hash checks, proof validation, decoder and staging
mechanism retain their existing owners.

Independent review caught two initial omissions: imported traces and package sources.
Both are repaired and have regression controls. A receipt is internal cache metadata;
the preflight, not the filename inventory, validates prepared artifacts. Existing
files use Make timestamps; this is not a content-addressed build system or an audit of
arbitrary timestamp-preserving filesystem changes.

Changed paths: `Makefile`, `scripts/check-semantics.py`,
`scripts/test-semantics-freshness.py`, `docs/GENERATED.md`, and this receipt.

## Verification

- `python3 scripts/test-semantics-freshness.py`: **16 tests passed**. They use the real
  Makefile with temporary timestamps/files and `make -q`; no recipes, Lean, Bun,
  TypeScript compiler or full build run. Cases cover unchanged success, configuration
  edits, modified/deleted prepared imports and traces, package inputs, source additions
  and removals, nested TypeScript removal, missing/modified reports, old/failed/malformed
  receipts and invalid saved paths. The two publication controls substitute only the
  external producer and preflight: successful generation records the inventory; a
  changing inventory refuses and preserves existing report bytes.
- Python `compile(...)` checks for both scripts: passed.
- `git diff --check`: passed.

No new Lean axiom output applies: this slice changes Python/Make cache behavior only.
It does not rerun or re-certify the broader semantic proof report. No production file
in Claude's worktree, seat L or the nested-extras seat was edited; no push or merge.

Logs and original controls:
`/private/tmp/codex-second-eyes-2026-10-01/proof-infra-audit/freshness-tests.log`,
`make-before.json`, and the independent review's cache controls in the same directory.
