# Feature and proof view receipt

Before integration: regenerate the two semantics projections and the architecture
page on the merged proof head. This branch measures `0f1f878b`; Claude's later M6
and load proofs are deliberately not copied into it. No status is inferred from
an adjacent green node. The view is selected, not a complete obligation census.

Base: `0f1f878bb21201e52740577c46327b63e7cebc5a`.
Branch: `codex/proof-feature-graph`, in the independent `proof-feature-graph`
worktree. The containing commit is the implementation head. No push or merge.

The [method](method.md) records the acquired TYPES 2003 chapters read for this
work, their printed page numbers, the adaptation limits and the shared notation.
The v2 semantics report reuses `ProofGraph` evidence validation, carries actual
statement/body references from Lean expressions and keeps authored prerequisites
separate. The architecture page and Markdown read the same report. The display
uses Lean's pretty printer with fixed display options; its constant-only loader
retains canonical names when imported notation is unavailable. No unsafe
initializer execution, global notation change or new runtime theorem was added.

At this base the selection has 9 features and 120 declarations: 74 proved as
stated, 33 definitions, 13 wanted. It records 396 proof-body, 26 definition-body,
236 statement-reference and 7 authored ledger-prerequisite edges. Full
quantification, propositional premises, structure constructor signatures, exact
names, source locations, evidence and axiom lists remain inspectable. Proposed
work is not a proof. `step_resume` is the transport task's consumer, not a
prerequisite assumed completed.

Changed surfaces: `Tools.ProofMap`, `ProofMapSelection`, `ProofMapHtml`,
`ProofMapFixture`, `SemanticsDisplay`; the semantics and architecture producers;
the existing Lean controls; the strict Effect Schema consumer and fixtures;
the Makefile and semantics check script; architecture/generated/semantics prose;
the three generated projections; this research method and receipt.

Verification (all final commands exited 0):

- `lake build Tools.Architecture Drivers.Semantics Drivers.SemanticsControls`.
- `python3 scripts/check-semantics.py --generate generated`, followed by
  `python3 scripts/check-semantics.py`: two fresh reports equal maintained bytes;
  1,219 prepared artifacts match saved hashes; source freshness before/after;
  12 graph refusals, existing 28 report refusals and 18 register controls;
  removal of the real CE-030 row refuses without replacing old outputs.
- The script ran pinned tsgo `7.0.0-dev.20260629.1`, Effect `4.0.0-rc.112`,
  Bun `1.4.2`: 110 tests passed, including a wanted placeholder falsely labeled
  as a proved goal. The HTML reader independently passed 3 accepting and 21
  rejecting local controls. It is a local reader, not a replacement for the
  complete host schema.
- `lake env lean -j1 -M6144 -DwarningAsError=true --run
  tools/Tools/Architecture.lean`, then the same command with `--check`: current.
- 34 synthetic and 56 actual-report DOM controls passed. Final embedded JSON
  equals the checked report, and final graph JavaScript equals the tested source.
  Static exports of the actual feature, denotation and replay layouts were
  rendered and visually inspected. Browser preview was explicitly blocked; no
  browser-based rendering or interaction verification is claimed.
- 13 isolated Make question-mode freshness controls passed. Transitive Lean
  edits, replaced artifacts and nested TypeScript/JSON edits trigger checks;
  unchanged inputs skip. Modifying installed Effect implementation bytes while
  leaving its package metadata unchanged is outside these timestamp triggers.
- `git diff --check`; final named-input and generated-output SHA-256 comparison.

Compiler runs were serialized, one thread, bounded memory and time. Preparation
used private copy-on-write artifacts, repaired stale copied dependencies, then
required exact freshness; no complete battery, trust-gate sweep, installation or
code generator outside these projections ran. The report's proof references are
validated at `[propext, Quot.sound]`; this is not a new whole-estate gate receipt.
Earlier failed elaboration/pretty-printing probes are retained as failures.

Evidence and exact command logs:
`/private/tmp/codex-second-eyes-2026-10-01/proof-graph-book/`, especially
`gen-final-receipt.json`, `check-final-receipt.json`, `html-decoder-final.log`,
`architecture-check.log`, and `renderer/actual-controls-final.log`.

Final generated hashes:

| File | SHA-256 |
| --- | --- |
| `generated/semantics.json` | `b6598ed0ecb475b19e8f89c01ad37e8905ad9ececbdcd8912072abf6dcf83006` |
| `generated/semantics.md` | `7f637ed53ccf064c6b64ae8288d6d0ca77036d480d0a4b75c6ca28bfa88539a4` |
| `docs/core/architecture-map.html` | `b5b03b817c5204785e82bb5496e8f30caa315350557846818274eed20a959cdf` |

Still separate: full coverage, conservative extension, proof-plan entailment,
general M5, M6/M7 inputs, target execution and compiler lowering. The existing
`Api/RunnerDerived → Effect4.Run` direction issue remains visible and unchanged.
