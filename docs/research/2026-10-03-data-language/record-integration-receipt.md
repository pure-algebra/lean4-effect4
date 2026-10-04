# Record integration receipt

## Merge note

Record construction, field reads and overwrite reach the checked TypeScript boundary.
The record-tag operation and collection operations remain separate slices.
The OCaml mirrors still require their producer refresh and focused checks.
No JSON or Schema record codec is claimed here.

Base: `d69a28da` on `codex/data-language-wave`, descended from `82d34358`.
The commit containing this receipt supplies the resulting head.

## Changes

The refusal generator includes `RecordTypingReason`, `RecordTermRefusal` and `RecordCauseRefusal` before their consumers.
Its controls check recovery, extra-byte refusal, truncated-byte refusal and generated shape membership.
`Codegen.codesOf` claims no unmeasured TypeScript diagnostic for the new record reasons.

`FormationContract` checks malformed record declarations at the public entry points.
`BlameContract` covers instantiated formation errors.
The core and test roots import their new modules.
The normalization fixture supplies the existing two control flags explicitly.

The case policy follows the measured compiled branches.
The three new type classifiers refuse non-record types.
Literal, pair-request and pair-tag classifiers continue to reject the new record term forms.
Generated term equality includes every appended constructor.
The policy retains its notes and refuses unlisted case sites.

## Commands and results

| Command | Result |
| --- | --- |
| `LEAN_NUM_THREADS=3 python3 scripts/generate.py --only derived` | Passed; final generated-module build reports 327 jobs |
| `LEAN_NUM_THREADS=3 python3 scripts/generate.py --only derived --output-dir /private/tmp/effect4-record-derived-repeat` | Passed; every generated file matches byte-for-byte |
| `LEAN_NUM_THREADS=3 lake build Effect4 Test.Program.FormationContract Test.Program.BlameContract Test.Program.RecordRefusals Test.Program.FoldFamilySelection Effect4.Codegen.Diagnostics Conform` | Passed; 428 jobs |
| `make check-cases` | Passed; the fresh case report exits zero |
| `python3 scripts/check-docs.py` | Passed; every reference in 71 authority documents resolves |
| `git diff --check` | Passed |

The case seed was reviewed before installation.
It adds three type classifiers and updates nine existing term consumers.
No unrelated policy family changes.
The retained generated-output comparison establishes deterministic regeneration for this run.

## Proof placement and trust

The public formation checks serve `raw-formation` and `instantiated-formation`.
The record diagnostics serve `denote-typed` through the unchanged checker acceptance projections.
Their exact judgments and limits remain in the source and diagnostic receipts.

The formation fixture reports thirteen axiom queries.
The record refusal fixture reports seven axiom queries.
Each reports only `propext` and `Quot.sound`.
The fold selection fixture also checks the selected connectors within that ceiling.
These are focused axiom queries, not a whole-library axiom sweep.

The generated refusal controls and case audit are finite checks.
They establish neither target execution agreement nor machine liveness.
