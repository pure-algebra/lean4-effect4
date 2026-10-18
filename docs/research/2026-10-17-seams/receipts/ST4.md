# ST4 receipt: session chains and the exchange

The one thing to know first: a session now persists as a chain of `SessionEntry` nodes under the
journal root `session/<name>`, and `load_own` is proved. Each action entry carries its transcript
index, a field the plan did not have: it makes parent order checkable and the loader's walk
structural, with no fuel and no hash premise.

## Commits and source ownership

- Base: `909390c5b37eee458f4d44c1c845d7b54c534c92`. Implementation: `6bb098a245591c0e2f69ca1807f8bb4f16387cb6`, on `refactor/phase1-phase3`.
- Codex's ST4 preparation was placement only (`/private/tmp/seams-st4-scout/PLACEMENT.md`); the code
  is new.

| Owner | What it holds |
| --- | --- |
| `src/Effect4/Tool/Session.lean` | `SessionEntry` (kind `entry`): `origin` and `action parent index a after`; its exact codec |
| `src/Effect4/Tool/Exchange.lean` | `LoadRefusal`, `Chain`, the walk, `stepped`, `replay`, `load`; `Base`, `Envelope`, `Refusal`, `resolve`, `publication`, `finish`, `apply`; `applied` |
| `src/Effect4/Laws/Tool/Exchange.lean` | `load_own`, `apply_commits_once`, `apply_refuses` and their helpers |
| `src/Effect4/Store/Domain/Cas.lean` | `Cas.commit_store`, the reached commit as the store's; the entry's designated parent read at four fields |
| `ocaml/engine/cas/e4_cas.ml` | the native designated parent read at four fields |
| `Test/Program/SeamsExchange.lean` | the controls |

## Acceptance rows and controls

| Plan row | Positive evidence | Red control |
| --- | --- | --- |
| Loop 5: persist, stop, resume | Open, edit and start under `Base.head "demo"`: generations 1, 2, 3. A new load at the head has three actions, and run 0 waits on `ask`. | — |
| Loop 6: two writers | The second writer reloads at the new head; a fork starts `session/demo-b` at generation 1. | Its act at the old head refuses `staleBase demo h2 h3`; its edit at the old snapshot is the tool's `stale`, inside an accepted exchange. |
| `load_own` | Proved; the loop 5 load reads it. | — |
| A refused stored action, a false `after`, versions, parents | — | `refused 0 noDocument`, `after 0`, `version 2 1`, `parent`, `noOrigin`, and `unreadable … missing`. |
| Engine changes | A chain whose origin records another engine loads. | — |
| Both stalenesses | `staleBase` from the exchange; `stale` from the tool. | — |
| A lost acknowledgement | `Exchange.applied` finds the start at the head after head 2. | Another action is not found there. |
| Exact-entry bases | A query there changes no node. | An action there refuses `readOnly`. |

These are finite Lean evaluations (20 guards).

## Proof placement

| Claim | Pointer | Concept, role | Reach | Not established |
| --- | --- | --- | --- | --- |
| `session-load-own` | `Exchange.load_own` | host-session-protocol, compatibility | after an exchange commits an accepted action, loading the head it reports gives the state `serve` reached from the resolved base | repeated host effects, host progress, hash injectivity |
| `session-commits-once` | `Exchange.apply_commits_once` | host-session-protocol, compatibility | one transaction; its last node is the entry; its one move publishes it | a host acknowledgement, exactly-once host effects |
| `session-refuses` | `Exchange.apply_refuses` | host-session-protocol, preservation | a query or a refused request returns the store it was given | IO rollback |
| `session-entry-exact` | `SessionEntry.ofVal_exact` | exact-codecs, compatibility | an entry's reader answers only its own tree | action acceptance |

All four are proved; no planned goal is added. Helpers, each serving `session-load-own`:
`apply_ok`, `Keeps`, `keeps_commit`, `entryAt_committed`, `originAt_keeps`, `walk_keeps`,
`originAt_acc`, `walk_acc`, `originAt_steps`, `walk_length`, `replay_cons`, `stepped_ok`,
`replay_append`, `replay_transcript`, `chainAt_extend`, `load_extend`, `installRoot_root?`,
`root?_name`, `move_root`, `commit_move_root`, `loaded_ok`, `resolve_publish`, `load_origin`.

## Departures and proposed decisions

| Correction | Evidence | Proposed decision |
| --- | --- | --- |
| An action entry carries its transcript index. | The walk is structural in it; `parent` and `noOrigin` refuse an out-of-order chain; `load_own` needs no fuel bound and no hash premise. | Entries record their index; the designated parent stays field 0. |
| `apply` serves, then hands the reply to a pure `finish`; replay's step is a pure `stepped`. | `split` cannot generalize past the checked writer (the `serve_answers` finding); the laws read plain values. | Keep decisions outside the writer. |
| The plan's standalone Job and Tape exports have no carrier in the tree; only their kinds are registered. | No `Job` or `Tape` declaration exists. | Nothing to retain until a carrier lands. |
| The Tools.Query cut (`909390c5b`) removed `JsonBridge.toHex`, which `ocaml/engine/test/kit/write.lean` still called; check-ocaml failed. | The writer spells the same bytes, `hexString (Canonical.encode p)`; check-ocaml passes. | Repaired here. |
| ST1b's journal fixtures built three-field entries. | `Test/Store/SeamsTransactions.lean` and the native `test_cas.ml` now write the index. | Updated with the readers. |
| The engine an origin records is not compared on load. | The engine control loads. | As the plan says: replay re-establishes the history. |

The semantics report was not regenerated (owner, 2026-10-18); the registry and
`docs/core/semantics.md` carry the four claims.

## Current commands and trust evidence

`landed-source-paths.txt` lists every implementation path, and `landed-source-hashes.json` pins
their bytes at the implementation commit.

```text
#axiom_audit: 1051 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals
```

| Check | Exit | Seconds | Exact command |
| --- | --- | --- | --- |
| [narrow](evidence/ST4/narrow.json) | 0 | 6.725 | `python3 /private/tmp/seams-lean-one.py lake build Effect4.Laws.Author.Explain Effect4.Laws.Store.Recovery Effect4.Laws.Store.Results Effect4.Laws.Tool.Exchange Effect4.Store.Domain.Cas Effect4.Store.Domain.Traits Effect4.Tool.Exchange Effect4.Tool.Session OCaml5.Store.DiskOracle OCaml5.Tools.CasGoldens ProofGraph.Registry ProofGraph.Why Test.Audit.AxiomGate Test.Audit.ClosureAudit Test.Program.SeamsExchange Test.Store.ProgramContent Test.Store.SeamsRead Test.Store.SeamsRecovery Test.Store.SeamsResults Test.Store.SeamsTransactions Test.Store.WordContract Tools.LoadPaths Tools.Semantics Tools.View.Glyph` |
| [audit](evidence/ST4/audit.json) | 0 | 5.664 | `python3 /private/tmp/seams-lean-one.py lake env lean -DwarningAsError=true /private/tmp/seams-st4-audit.lean` |
| [check-ocaml](evidence/ST4/check-ocaml.json) | 0 | 231.684 | `python3 /private/tmp/seams-lean-one.py make check-ocaml` |
