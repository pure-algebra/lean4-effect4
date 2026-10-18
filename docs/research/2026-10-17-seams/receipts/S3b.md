# S3b receipt: generated wire codecs, the JSON driver, and the old dispatcher retired

The one thing to know first: the codec generator changed. Its new opt-in flag, `--arm-lemmas`,
proves each round trip through one `rfl` equation per reader arm, because the old template's proof
of the 57-arm `EffName` timed out in `whnf` even at 800,000 heartbeats. Every existing group
regenerates byte-identically; the flag is used by the two new groups only. Whether it becomes the
default is logged for a second look (`docs/research/2026-10-18-codec-generator-large-recursive-sums.md`).

## Commits and source ownership

- Base: `d2994ed0144977d5c65a04aa1f1659b0f6483ff1`.
- Part 1 (codecs, profile, wire): `3969699e4`. Part 2 (driver, view, batteries, retirement): `bc40095bbdaa6cc21e2df281250373bced2fef98`.
- Branch: `refactor/phase1-phase3`. Codex's frozen S3b drafts (`/private/tmp/seams-s3b-sol`) supplied the
  generator's qualified-names flag, the JSON profile and its law, the wire drafts and the view drafts.

| Owner | What it holds |
| --- | --- |
| `tools/Effect4Gen/Main.lean` | `--qualified-names` (now also for foreign identifiers) and `--arm-lemmas` |
| `src/Effect4/Tool/CheckDerived.lean` (generated, group `Check`) | the checker's public data: keys, verdicts, sites, explanations |
| `src/Effect4/Tool/ToolDerived.lean` (generated, group `Tool`, 85 carriers) | every carrier of a request and a reply, through `Live.View` and the preview tree |
| `src/Effect4/Store/Domain/ContextCanonical.lean` | the hand-written exact codec of the machine's service context (a `Nodup` proof field and a dependent value) |
| `src/Effect4/Tool/CodecProfile.lean` | the JSON profile: refuses an option whose item can print null, and a write that does not read back |
| `src/Effect4/Tool/WireTypes.lean`, `src/Effect4/Tool/Wire.lean` | the envelope, the connection, `responds`, `decode`, `serveJson` |
| `tools/Tools/WireText.lean` | one request or reply per text line |
| `tools/Drivers/Session.lean` | the JSON-lines driver over `serveJson`, with a learned checker memo |

The Tool protocol families' wire tags are pinned in `tools/Effect4Gen/wire-tags.json` at their
declaration positions; no existing tag moved.

## Acceptance rows and controls

| Plan row | Positive evidence | Red control |
| --- | --- | --- |
| Unknown tags, missing fields (R8, R12) | `Test/Program/SeamsS3bWire.lean`: a `CheckInput` round-trips through bytes and JSON. | An unknown tag and a missing field read as none. |
| The `Option Unit` profile refused | — | `Option Unit` and JSON `null` refuse the profile; a natural that binary64 rounds refuses to write. |
| Wire framing | A request reads back at the selected version; an accepted request appends one action. | An unselected method, a wrong version, a disagreeing method, a malformed message and a connection that selects a method twice each refuse, with the state unchanged. |
| Loop 4 (the view builds a program as frames) | `Tools.View.LiveChecks`: every build's requests are accepted through `serve`; the incremental lines and flow agree with fresh ones at every step. | The first fill at a stale snapshot refuses, and the state stays. |
| Both drivers | `tools/Drivers/Session.lean` answers the translated session fixture: ten replies, all accepted. `tools/Drivers/Live.lean build pFork`: seven requests accepted, 650 patch rows. `tools/Drivers/View.lean session …`: six frames, every graph check passes. | A line that does not parse prints a refusal and changes nothing. |
| Old dispatcher deleted | `tools/Tools/Session.lean`, `tools/Tools/Session/Snapshot.lean` and `JsonBridge.valueFrom?` are gone; no source names them. | — |

The six batteries that drove the old dispatcher now drive `Tool.serve`: `SessionToolControls`,
`SketchAdmissionControls`, `LiveRecordControls`, `PreviewControls`, `CheckCacheControls` and
`FillSetControls`. Each keeps its control's meaning; three change form:

- A restore adds a run rather than replacing the live one; the restored view still waits on the
  one call left, with its checked instance.
- The dispatcher's full-anchor check guarded a document with the same identity and revision but
  another base. In the tool that state cannot arise: each open allocates a fresh generation and
  clears the pending fills. The control now shows that a fill at the earlier snapshot refuses as
  foreign.
- The dispatcher's `syncExit` field and per-answer law names have no counterpart in the protocol;
  the view's frames no longer print a law line.

These are finite Lean evaluations and finite host runs.

## Proof placement

| Claim | Pointer | Status |
| --- | --- | --- |
| `codec-profile-retains-value` | `Tool.CodecProfile.write_read` | Proved. |
| `tool-serve-answers` | `Tool.serve_answers` | Planned goal. Two of eight action branches were proved in a probe; `split` cannot generalize past `Checked`'s trace proof, so each branch needs its discriminant named. |

## Departures and proposed decisions

| Correction | Evidence and control | Proposed decision |
| --- | --- | --- |
| The recursive template's proofs do not scale past about fifty arms. | `EffName` timed out at 800,000 heartbeats; with arm lemmas the Tool group compiles at the default budget, in 6.3 seconds. | Keep `--arm-lemmas` opt-in until a measured comparison decides the default. |
| `--qualified-names` left foreign identifiers short, so two foreign `Refusal`s collided. | The duplicate `lift_Refusal` declaration. | Qualify foreign identifiers under the flag. |
| The machine's service context is outside the generator. | Its `Nodup` field and dependent value. | One hand-written exact codec; reading refuses a duplicate key (control in the module). |
| The pairing was planned as generated. | An exhaustive match refuses to compile when a constructor is added. | Keep `responds` as one exhaustive match. |
| `Tools.Query` holds reads the tool lacks (`slots`, the full `table`, `addresses`). | Its battery `Test/Program/QueryControls.lean`. | Keep `Tools.Query` and its driver until those reads join the tool's queries; then delete it with `fillPremises` and `omitPremises`. |
| `tools/Tools/View/Run.lean` passed a list where `finishBuild` takes an application. | The view driver did not compile before this slice. | Pass the empty application. |
| The session request fixture used the old format. | `tools/view/make_videos.py` reads it. | Translate it by serving each request; every one is accepted. |

## Current commands and trust evidence

Part 1's runs are kept under `evidence/S3b/part1/`. The table below covers the whole slice.
The audit covers every module the slice changed, including Laws modules whose docstrings now name
the tool as their consumer. `Laws/Program/SourceTable.lean` holds S1's placed goals, so the audit
counts them; this slice adds one goal, `serve_answers`.

```text
#axiom_audit: 3357 declarations within [propext, Quot.sound], 2 of them modulo planned goals; 9 planned goals
```

| Check | Exit | Seconds | Exact command |
| --- | --- | --- | --- |
| [versions](evidence/S3b/versions.json) | 0 | 0.613 | `python3 /private/tmp/seams-lean-one.py python3 /private/tmp/seams-runtime-versions.py` |
| [narrow](evidence/S3b/narrow.json) | 0 | 23.933 | `python3 /private/tmp/seams-lean-one.py lake build Drivers.Live Drivers.Session Drivers.View Effect4.Laws.Api.LiveRecord Effect4.Laws.Api.Preview Effect4.Laws.Author Effect4.Laws.Author.Explain Effect4.Laws.Program.FillSet Effect4.Laws.Program.SketchAdmission Effect4.Laws.Program.SourceDocument Effect4.Laws.Program.SourceTable Effect4.Laws.Tool.CodecProfile Effect4.Laws.Tool.Wire Effect4.Store.Domain.ContextCanonical Effect4.Tool.CheckDerived Effect4.Tool.CodecProfile Effect4.Tool.ToolDerived Effect4.Tool.Wire Effect4.Tool.WireTypes Effect4Gen.Exe Effect4Gen.Main ProofGraph.Registry ProofGraph.Why Test.Audit.AxiomGate Test.Audit.ClosureAudit Test.Program.CheckCacheControls Test.Program.FillSetControls Test.Program.LiveRecordControls Test.Program.PreviewControls Test.Program.SeamsS3bWire Test.Program.SeamsS4 Test.Program.SessionToolControls Test.Program.SketchAdmissionControls Test.Program.SourceFeedControls Test.Run.LiveContract Test.Schema.DocumentJson Tools.Catalogue Tools.JsonBridge Tools.LoadPaths Tools.Query Tools.Semantics Tools.View.Build Tools.View.Glyph Tools.View.Live Tools.View.LiveChecks Tools.View.Run Tools.WireText` |
| [audit](evidence/S3b/audit.json) | 0 | 3.433 | `python3 /private/tmp/seams-lean-one.py lake env lean -DwarningAsError=true /private/tmp/seams-s3b-audit.lean` |
| [batteries](evidence/S3b/batteries.json) | 0 | 2.667 | `python3 /private/tmp/seams-lean-one.py make batteries-touched BASE=d2994ed0144977d5c65a04aa1f1659b0f6483ff1` |
| [check-ocaml](evidence/S3b/check-ocaml.json) | 0 | 63.38 | `python3 /private/tmp/seams-lean-one.py make check-ocaml` |
| [generate-semantics](evidence/S3b/generate-semantics.json) | 0 | 25.769 | `python3 /private/tmp/seams-lean-one.py make gen-semantics` |
