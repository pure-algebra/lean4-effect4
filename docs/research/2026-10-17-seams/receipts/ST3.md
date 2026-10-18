# ST3 receipt: the result envelope, one result per query, the read face and the gate key

The one thing to know first: every node entrance now applies one result rule, in Lean and in the
native store. A result node must read as the common envelope (`badEnvelope`), and no other node
may answer its designated query (`poisoned`, naming the query and both results). The shape
alphabet gained `Shape.value` (wire tag 14) for the raw output, so this slice rebuilds most of the
tree once.

## Commits and source ownership

- Base: `025df9b346e901e0165a0d9b8e6c251de1030e5d`. It holds the two merged follow-ups (below).
- Implementation: `2062a13aafd8afbe8d6017e77be426ee6c64090b`, on `refactor/phase1-phase3`. Codex's frozen scout
  (`/private/tmp/seams-st3-scout`) supplied the raw-value shape, the carriers' readers, the conflict
  search's helpers, the gate key and its tests, and the placement analysis.

| Owner | What it holds |
| --- | --- |
| `src/Effect4/Store/Domain/Shape.lean`, `Schema/OfShape.lean`, `Derived/Value.lean` (generated) | `Shape.value`: any value tree fits; the schema renders it as unknown; its JSON reader refuses it |
| `src/Effect4/Store/Domain/Document.lean` | the one `Content Document` instance, moved below the store |
| `src/Effect4/Store/Domain/Action.lean` | `ActionId`, `Query κ` (kind `query`), `Answered κ` (kind `result`), `Node.resultQuery?` |
| `src/Effect4/Store/Domain/Store.lean` | `resultConflict`, `resultFault`, `ResultOnce`; `Admission.badEnvelope`, `Admission.poisoned`; the rule in `putNode`; `Store.Sound.results` |
| `src/Effect4/Store/Domain/Word.lean` | the rule in `Binding.admissibleAfter` and `Store.verifyResult`; `apply_resultOnce`; closure completeness kept |
| `src/Effect4/Store/Domain/Cas.lean` | the read face: `Read`, `Store.read`, `Cas.read` |
| `src/Effect4/Laws/Store/Results.lean` | `Cas.sound`, `Cas.result_once` |
| `src/OCaml5/Lcnf/Gallina.lean`, `rocq/StoreCode.v` (generated), `rocq/StoreLaws.v` | the printed rule; the reader as a `Prim` parameter |
| `src/OCaml5/Store/Facts.lean`, `ocaml/engine/cas/e4_result.ml{,i}` (generated), `e4_admission.ml{,i}` (generated) | the envelope's specification bytes; the two refusals |
| `ocaml/engine/cas/e4_cas.ml{,i}` | `result_query`, the by-query table, `check_result` at every entrance |
| `src/OCaml5/Tools/CasGoldens.lean`, `ocaml/engine/cas/goldens/` (generated), `test/test_cas.ml` | golden families G8 and G8word, two G7 rows |
| `scripts/lib/gate_cache.py`, `scripts/test-gate-cache.py`, `Makefile` | the command-aware gate key |
| `Test/Store/SeamsResults.lean` | the finite controls |

## Acceptance rows and controls

| Plan row | Positive evidence | Red control |
| --- | --- | --- |
| §4.7 ordinary row 7: `q`, `r1`, then `r2`, no moves | `Test/Store/SeamsResults.lean`; golden `g8-result-poisoned`: fresh, fresh, then `poisoned q r1 r2`. A duplicate result is admitted. | One transaction holding both results refuses at its sixth node. |
| Malformed envelopes, unknown versions, wrong query kinds | — | A non-envelope payload, envelope version 1 and a wrong specification refuse `badEnvelope`. A query field naming a schema node refuses `wrongKind`, because edges precede the envelope. Goldens `g8-result-*`. |
| Incidental references | A result for `qb` whose output mentions `qa` is admitted beside `qa`'s result; a results read for `qa` does not return it. | — |
| Varying output | A run identity in the query's input names a new query; its result is admitted beside the first. | — |
| Raw output keeps its edges | An output reference that names no node refuses `dangling`. | The generated `Canonical Val` frames a reference as data: its refs are empty. |
| Every entrance (insertion, word, verification; recovery and commit through insertion) | `Word.wf` admits one result; `verify` passes a sound store. | The pre-envelope checker admitted a malformed result at all three (Codex's `OldAdmissionControl`); each now refuses it. Two results refuse at `Word.wf`, `Word.apply` and `verify`, in Lean and natively (G7, G8, G8word). |
| Read face | `Cas.read`: node, root, results, closure; a typed `Cas.get` returns the exact envelope. | A missing node and a missing root answer nothing. |
| Repeated gate commands | Two commands over identical inputs keep two pass records, each keyed by its command (`scripts/test-gate-cache.py`, 17 tests). | The former command-free key fails that test (`gate-cache-red`). A forged record whose command differs reruns. |

The native store agrees with Lean on every new row: G8 9/9 admission rows through `put`, both
words through `word_wf` and `apply_word`, and G7 9/9 verify rows. These are finite evaluations
and finite native runs.

## Proof placement

| Claim | Pointer | Concept, role | Reach | Not established | Status |
| --- | --- | --- | --- | --- | --- |
| `cas-result-envelope` | `Node.resultQuery?_eq_some_iff` (`Store/Domain/Action.lean`) | exact-codecs, compatibility | a node answers a query exactly when it is the node of a version-0 envelope of it | result truth, hash injectivity | Proved. |
| `cas-result-once` | `Cas.result_once` (`Laws/Store/Results.lean`) | exact-codecs, preservation | every store the event interpreter reaches: commits, cuts, restoration | result truth, host determinism, progress | Proved. |

Helpers, each serving `cas-result-once` under R13: `resultConflict_none_iff`,
`resultConflict_some`, `resultConflict_none_subset`, `resultFault_none_iff`, `resultOnce_subset`,
`resultOnce_append_of`, `ResultsOnce.unique`, `resultsOnce_append`, `putNode_ok_result` (consumed
by `putNode_sound`), `admissibleAfter_result`, `apply_added` and `apply_resultOnce` (consumed by
`apply_idempotent`), `verifyNode_result` (consumed by `verify_sound`), `stageNodes_sound`,
`commit_sound`, `interrupted_sound`, `restore_sound`, `eventStep_sound`, `replayEventsFrom_sound`
and `Cas.sound`.

Kept statements: `putNode_ok` (the accepted-new-to-old connector), `wf_apply`, `apply_idempotent`,
`closure_closed` and `verify_sound`. `putNode_fresh`, `putNode_duplicate`, `put_duplicate` and
`admissibleAfter_of` gained one premise each, the result rule; their consumers supply it.
`Store.Sound` gained the field `results`, over every binding, shadowed ones included, because the
conflict scan reads them all.

Rocq: `Node.resultQuery?` is a parameter of `Prim`, so `StoreLaws.v` holds over every reader.
Two proofs gained one case split each. No Rocq claim about results is made; one would need an
adequacy premise for the reader.

## Departures and proposed decisions

| Correction | Evidence and control | Proposed decision |
| --- | --- | --- |
| The scout gave `Query κ` a common specification. It follows `Annotation τ` instead: the input field takes the input carrier's shape and table. | `specOf (Query Nat) ≠ specOf (Query String)`; the envelope keeps one specification, because `κ` is a phantom there. | A query's specification names its input's shape. |
| The result output needs a shape that fits every value tree. | `Shape.value`, appended at tag 14; existing tags unchanged; the JSON reader refuses it. | Adopt `Shape.value` for raw outputs only. |
| `Content Document` lived above the store. | Admission computes `specOf (Answered Unit)`; `Document.lean` holds the one instance; `Genesis` keeps its theorems. | Keep the instance below the store. |
| Three entrances needed one rule. | `resultFault` is one operation; insertion, word admission and verification adapt its answer. | One result operation per store. |
| The printed word projection is a tail-recursive loop. | The Gallina printer maps `List.reverse` to Rocq's `rev`. | Add the row. |
| The native word check lacked M2's handle test, which Lean's has. | `admissible_after` now applies it with the result rule. | Close the gap here. |
| The native store had no result index. | The by-query table is a cache with a rebuild, as the by-Cid index is, with a staged half. | Keep results indexed by query. |
| GNU Make 3.81 writes short options after long ones, and reuses same-second stamps. | The flag reader reads every short-option word; gate stamps are phony, so the shared-result reader alone decides; the Makefile no longer computes `--force`. | Adopt the scout's correction. |

Follow-ups merged before this slice (base above): `Tool.serve_answers` proved (`1621d212b`), and
arm lemmas as the codec generator's only template (`025df9b34`). Their merged tree built 980 jobs,
and `#axiom_audit` over the follow-ups' twelve modules gave 7,076 declarations within
`[propext, Quot.sound]`, with no planned goals.

Outside the repository, the shared Lean runner now locks per worktree, and the two machine slots
take 5 threads alone and 3 beside another build (owner, 2026-10-18).

## Not done

No producer stores results yet: the gate cache keeps its file records, now keyed by command. ST4's
session chains and S6's shell are the first consumers of `Cas.read`.

## Current commands and trust evidence

The semantics report (`make gen-semantics`) was not regenerated: the owner retired it from
landings on 2026-10-18. `generated/semantics.md` therefore does not yet list
`cas-result-envelope` and `cas-result-once`; the registry and `docs/core/semantics.md` do.

`landed-source-paths.txt` lists every implementation path, and `landed-source-hashes.json` pins
their bytes at the implementation commit.

```text
#axiom_audit: 2305 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals
```

| Check | Exit | Seconds | Exact command |
| --- | --- | --- | --- |
| [versions](evidence/ST3/versions.json) | 0 | 0.764 | `python3 /private/tmp/seams-lean-one.py python3 /private/tmp/seams-runtime-versions.py` |
| [narrow](evidence/ST3/narrow.json) | 0 | 0.479 | `python3 /private/tmp/seams-lean-one.py lake build Effect4.Api Effect4.Api.RunnerDerived Effect4.Codegen.Schema Effect4.Laws.Author.Explain Effect4.Laws.Program.Simulation.Evaluate Effect4.Laws.Store.Folds.Val Effect4.Laws.Store.Recovery Effect4.Laws.Store.Results Effect4.Schema.OfShape Effect4.Store.Domain.Action Effect4.Store.Domain.Canonical Effect4.Store.Domain.Cas Effect4.Store.Domain.ContextCanonical Effect4.Store.Domain.Derived.Value Effect4.Store.Domain.Document Effect4.Store.Domain.Genesis Effect4.Store.Domain.PayloadCanonical Effect4.Store.Domain.Shape Effect4.Store.Domain.Store Effect4.Store.Domain.Traits Effect4.Store.Domain.Word OCaml5.Lcnf.Gallina OCaml5.Store.DiskOracle OCaml5.Store.Facts OCaml5.Tools.CasDiskCuts OCaml5.Tools.CasDiskOracle OCaml5.Tools.CasFacts OCaml5.Tools.CasGoldens OCaml5.Tools.GallinaGen ProofGraph.Registry ProofGraph.Why Test.Audit.AxiomGate Test.Audit.ClosureAudit Test.Codegen.ModeledLane Test.Schema.DialectContract Test.Schema.DocumentJson Test.Store.NodeContract Test.Store.ProbeContract Test.Store.ProgramContent Test.Store.SeamsAdmission Test.Store.SeamsHeadPrinter Test.Store.SeamsRead Test.Store.SeamsResults Test.Store.SeamsTransactions Test.Store.WordContract Tools.Catalogue Tools.JsonBridge Tools.LoadPaths Tools.Query Tools.Semantics Tools.View.Glyph Tools.WireText` |
| [audit](evidence/ST3/audit.json) | 0 | 6.197 | `python3 /private/tmp/seams-lean-one.py lake env lean -DwarningAsError=true /private/tmp/seams-st3-audit.lean` |
| [generate-derived](evidence/ST3/generate-derived.json) | 0 | 50.963 | `python3 /private/tmp/seams-lean-one.py python3 scripts/generate.py --only derived` |
| [generate-cas](evidence/ST3/generate-cas.json) | 0 | 12.494 | `python3 /private/tmp/seams-lean-one.py python3 scripts/generate.py --only cas` |
| [generate-store-rocq](evidence/ST3/generate-store-rocq.json) | 0 | 6.146 | `python3 /private/tmp/seams-lean-one.py python3 scripts/generate.py --only store-rocq` |
| [rocq](evidence/ST3/rocq.json) | 0 | 3.479 | `python3 /private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/9702bd4d-c422-4d7e-85c6-6052708a5ba3/scratchpad/seams-st3-rocq-production.py` |
| [native-store](evidence/ST3/native-store.json) | 0 | 3.968 | `opam exec --switch=effect4 -- dune runtest --force --root ocaml engine/cas/test` |
| [gate-cache](evidence/ST3/gate-cache.json) | 0 | 1.276 | `python3 scripts/test-gate-cache.py` |
| [gate-cache-red](evidence/ST3/gate-cache-red.json) | 0 | 0.058 | `python3 /private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/9702bd4d-c422-4d7e-85c6-6052708a5ba3/scratchpad/st3-gate-red.py` |
| [batteries](evidence/ST3/batteries.json) | 0 | 6.546 | `python3 /private/tmp/seams-lean-one.py make batteries-touched BASE=025df9b346e901e0165a0d9b8e6c251de1030e5d` |
| [check-ocaml](evidence/ST3/check-ocaml.json) | 0 | 24.706 | `python3 /private/tmp/seams-lean-one.py make check-ocaml` |
