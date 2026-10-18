# S3a receipt: the tool serves requests over one action interpreter

The one thing to know first: the five tool laws are proved, not placed as goals.
`serve_appends`, `serve_refuses`, `serve_query`, `serve_transparent` and `transcript_replays` follow from the definitions.
The frozen sources had never compiled; four compile repairs and one control repair were needed, all listed below.

## Commits and source ownership

- Base: `a25d899f7555ae42964bd312db94a7b6cfb95b91`.
- Implementation: `23f710f2873083ba762c3b9bd03df499b7a35814`.
- Branch: `refactor/phase1-phase3`. Sources: Codex's frozen S3a drafts (`/private/tmp/seams-s3a-sol/overlay`), documented and repaired by the coordinator.

| Module | Owns |
| --- | --- |
| `Effect4.Tool.Protocol` | `Action`, `Query`, `Request`, `Answer`, `Refusal`, `Reply`, the views, `Request.method`, `supportedMethods` |
| `Effect4.Tool.Actions` | `Internal.Raw` and `Internal.action`, the one action interpreter |
| `Effect4.Tool.Replay` | `State`, sealed by the replay of its transcript; `replayAccepted`; `State.accept` |
| `Effect4.Tool.Queries` | `Internal.query`: document views, inspection, history, fills, suggestions, runs, previews, `dry`, `discover` |
| `Effect4.Tool.Serve` | `serve` |
| `Effect4.Laws.Tool.Serve` | the five laws |

The interpreter reuses each owner: `Doc.step`, `FillSet.add` and `publication`, `Api.Built.ofSketch` with `Live.open`, `LiveRecord.restore`, `CheckCache.suggestPage` and `Run.Preview`.
It adds no second document, edit interpreter or run language.
The core root reaches no Laws module.

## Acceptance rows and controls

| Plan row | Positive evidence | Red control |
| --- | --- | --- |
| Loops 1 to 3 through `serve` | `Test/Program/SeamsS3a.lean` opens, starts a run with its snapshot origin, plays to `success 7`. | — |
| Three outcome kinds | A refused play leaves the transcript and the run's journal unchanged; a played refused phase stays in the journal. | An apply before any reply records a refused phase inside an accepted play. |
| Event rollback | A resolved `flush` followed by an unresolved selector refuses the whole play. | The successful prefix is discarded: the run's journal equals the one before. |
| `dry` | A dry start answers `started`. | The transcript stays at one action and the run list stays empty. |
| Inspection | `Test/Program/SeamsS3aInspection.lean`: every field of an inspection at the root matches the table. | An address with no node, and each statement address of a generator, refuse `noProgram`. |
| Suggestion environments | `Test/Program/SeamsS3aDifferentEnv.lean`: a candidate from another environment answers `differentEnv` with its module key. | It asks no check: its trace is empty. |

These are finite Lean evaluations; the laws below are the general statements.

## Proof placement

| Claim | Pointer | Role | Status |
| --- | --- | --- | --- |
| `tool-serve-appends` | `Tool.serve_appends` | compatibility | Proved. |
| `tool-serve-refuses` | `Tool.serve_refuses` | preservation | Proved. |
| `tool-serve-query` | `Tool.serve_query` | preservation | Proved. |
| `tool-serve-transparent` | `Tool.serve_transparent` | compatibility | Proved, from `Oracle.transparent`: the whole checked answer, its trace included. |
| `tool-transcript-replays` | `Tool.transcript_replays` | compatibility | Proved, from the sealed `State.replayed`. |

Concept `host-session-protocol`, the tool-transition property; requirements R6 and R13.
The laws observe `serve`'s state and reply; they establish no native execution, external-effect rollback or host progress.
The placement proposed `characterization` for two claims; the registry has no such role, so they use `compatibility`.
`serve_answers` (the request and reply pairing) stays S3b's, with the generated pairing.

## Repairs to the frozen sources

| Repair | Evidence |
| --- | --- |
| `Row` resolved to another declaration inside `Effect4.Tool`; `HoleView.row` names `Program.Row`. | First compile: "type expected". |
| `Option.toExcept` does not exist; `Internal.requireDoc` answers `noDocument`. | Second compile: unknown field. |
| `Live` has no `save`; the record query calls `LiveRecord.save`. | Third compile. |
| `State`'s constructor is private to `Replay.lean`; `State.accept` moves there, and `replayStep` uses explicit matches so its proof rewrites through them. | Fourth compile: private constructor, then a failed `rfl`. |
| The draft's third inspection control searched `succeed (lit 7)` for a node that holds no program; that program has none, so the control could never pass. It now searches a generator, whose statements are such nodes. | A probe printed the addresses of both programs. |

## Cuts

The plan's §2.2 assigns `Tools.Query` as a protocol source, `fillPremises` and `omitPremises` to S3a.
Their consumer is the stateless JSON driver `tools/Drivers/Query.lean`, which reads requests from JSON lines.
Moving it onto `Tool.Request` needs the generated Tool codecs, so the cut lands with S3b's driver migration.

## Current commands and trust evidence

```text
#axiom_audit: 722 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals
```

| Check | Exit | Seconds | Exact command |
| --- | --- | --- | --- |
| [versions](evidence/S3a/versions.json) | 0 | 0.609 | `python3 /private/tmp/seams-lean-one.py python3 /private/tmp/seams-runtime-versions.py` |
| [narrow](evidence/S3a/narrow.json) | 0 | 11.568 | `python3 /private/tmp/seams-lean-one.py lake build Effect4.Laws.Author.Explain Effect4.Laws.Tool.Serve Effect4.Tool.Actions Effect4.Tool.Protocol Effect4.Tool.Queries Effect4.Tool.Replay Effect4.Tool.Serve ProofGraph.Registry ProofGraph.Why Test.Audit.AxiomGate Test.Audit.ClosureAudit Test.Program.SeamsS3a Test.Program.SeamsS3aDifferentEnv Test.Program.SeamsS3aInspection Tools.LoadPaths Tools.Semantics Tools.View.Glyph` |
| [audit](evidence/S3a/audit.json) | 0 | 2.069 | `python3 /private/tmp/seams-lean-one.py lake env lean -DwarningAsError=true /private/tmp/seams-s3a-audit.lean` |
| [batteries](evidence/S3a/batteries.json) | 0 | 1.749 | `python3 /private/tmp/seams-lean-one.py make batteries-touched BASE=a25d899f7555ae42964bd312db94a7b6cfb95b91` |
| [check-ocaml](evidence/S3a/check-ocaml.json) | 0 | 6.485 | `python3 /private/tmp/seams-lean-one.py make check-ocaml` |
| [generate-semantics](evidence/S3a/generate-semantics.json) | 0 | 35.505 | `python3 /private/tmp/seams-lean-one.py make gen-semantics` |
