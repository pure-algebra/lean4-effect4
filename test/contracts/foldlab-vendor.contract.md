# Foldlab evidence-vendor contract

Status: IMPLEMENTED / GREEN, 2026-08-31

Implementation fence: `vendor/foldlab/**`, `scripts/*vendor-foldlab.sh`, and
the dedicated CI step.

## Source boundary

The tracked evidence source is exactly Foldlab commit
`feb29321fd50204aa338209d313e84a3f8b71c66` at the eight entries in
`vendor/foldlab/SCOPE.txt`. Extraction uses `git archive` at that commit, so
dirty or untracked working-tree bytes cannot enter the pinned bundle.

The late evidence is a different class. It consists of exactly:

- 39 `workshop/s1/*.lean` probes;
- 24 `workshop/s2/*.lean` probes;
- 16 `workshop/layer/*.lean` probes;
- three `workshop/layer/ground-*.md` research notes; and
- the final S1, S2, and Layer reports in `.staging/agent-reports/`.

Those 85 files were uncommitted or ignored in the source worktree. Their
manifest therefore records `-` rather than inventing a Git blob. They remain
evidence-only under `vendor/foldlab/late/tree/` and are never imported.

The frozen payload totals are 826 pinned files (9,456,751 bytes) and 85 late
files (2,484,232 bytes): 911 files and 11,940,983 bytes altogether.

## Closed manifest

Each manifest row has four tab-separated fields:

```text
source_path    bytes    sha256    git_blob
```

For pinned rows, `git_blob` is the exact 40-digit Foldlab blob identifier and
is recomputed from the vendored bytes. For late rows it is `-`. The internal
checker rejects an unsafe path, duplicate or unsorted row, wrong byte count,
wrong SHA-256, wrong Git blob, missing file, or extra file. It also fixes the
pin, extraction scope, late category counts, and absence of a Foldlab Lake
dependency.

## Required attacks

`scripts/test-vendor-foldlab.sh` uses three independent disposable copies:

1. delete one manifested file — the file-set gate must fail;
2. add one unmanifested file — the file-set gate must fail; and
3. mutate one manifested file — the byte or digest gate must fail.

The source vendor is checked again after all attacks. A self-test that edits
the source vendor, depends on an external Foldlab checkout, or accepts any of
the three planted defects does not satisfy this contract.

## Claim boundary

Passing this gate establishes byte identity and closed inventory only. It
does not make Foldlab a dependency, promote a workshop proposal, prove a Lean
theorem, or show semantic preservation. Those remain per-declaration and
per-type obligations.
