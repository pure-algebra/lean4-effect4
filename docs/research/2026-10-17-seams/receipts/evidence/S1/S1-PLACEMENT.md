# S1 placement packet

All proposed claims serve R14 under `initial-algebras-folds`.
The required properties are source-session coherence, typed replacement, and accepted-action replay.
The coordinator registers these pointers before production compilation.
Every row excludes admission, progress, liveness, and native execution.
A conditional row establishes no missing premise.

| Pointer | Proposed question and role | Exact reach | Consumer |
| --- | --- | --- | --- |
| `SourceSession.open_coherent` | source-session-coherent; helper | Every application/sketch and certified oracle; exact source table | feed coherence and Doc opening |
| `SourceSession.feed_coherent` | source-feed-coherent; compatibility | Successful feed, coherent initial source, every policy | `Doc.coherent` |
| `SourceSession.feed_keeps` | source-feed-edit; compatibility | Successful feed; exact application, edit, candidate sketch, invalid-edit no-op | replay draft transport |
| `SourceSession.feed_draft` | source-feed-draft; compatibility | Coherent source; every edit; old expanded EditSession observation and exact source projection | `replay_drafts_view` |
| `SourceSession.feed_keepExact` | source-feed-keep-exact; compatibility | Successful nonroot keepExact; root/local types, exact guarded splice or recheck | Doc commit and FillSet certification |
| `SourceSession.feed_root` | source-feed-root; compatibility | Root edit with candidate; equality of the entire Checked module recheck computation | root edits and root suggestion key |
| `SourceSession.feed_undo` | source-feed-undo; compatibility | Coherent source, actual original node, successful draft fill, exact immediate inverse | document revert |
| `Doc.coherent` | source-document-coherent; invariant | Every sealed Doc; no hidden coherence premise | `SourceSession.reached_view` |
| `SourceSession.replay_drafts_view` | source-session-draft-transport; compatibility | Every old application/sketch/edit-list; canonical draft replay, exact edited sketch, table/refusals/root | old reached-state transport |
| `SourceSession.reached_view` | source-session-coherent; compatibility | Every sealed Doc; exact table, refusal list, and root observation | tool view and inspection |
| `Doc.step_replay` | source-document-replay; compatibility | Every origin/history/action; exact canonical replay through the history ledger | validating action replay |
| `Doc.step_refuses` | source-document-atomic; helper | Refused step; caller keeps original Doc | atomic tool wrapper |
| `Doc.step_coherent` | source-document-step; invariant | Successful step, coherent initial Doc; exact snapshot, origin/history, application/coherence | document reach |
| `Doc.commit_sound` | source-document-commit; compatibility | Successful commit with keepExact/recheck; initial positive root for keepExact | batch publication |
| `Doc.commit_one_keepExact` | source-document-local-keep; compatibility | One nonroot kept change, coherent initial source; exact root/local observations | local edit explanations |
| `Doc.commit_single_sound` | source-document-single-transport; compatibility | Exact old single-edit observations with the necessary initial positive-root premise | old commit claim transport |
| `Doc.revert_program` | source-document-revert; compatibility | Successful action and immediate selected-entry revert; coherent source | revert and pending publication controls |

Names carry the prefix `Effect4.Program`.
The exact statements in `s1-laws` define every premise and observation.
The conditional `SourceSession.view_eq` is a helper of the reached-state claim.
It is not the reached-state claim's replacement.

Thirteen rows remain planned goals, as listed in `S1-RECEIPT-SOL.md`.
`open_coherent` is proved modulo V1's `combine_deps` through exact `Checked.ask_value`.
`reached_view` is proved modulo `Doc.coherent`.
The other helpers are proved within the recorded axiom ceiling.

## Root and native integration

The existing SourceSession and SourceDocument core imports reach the new representation.
Keep the existing Laws imports for SourceTable and SourceDocument.
Add `Test.Program.SourceFeedControls` through the existing SourceDocumentControls battery import.
The existing test root already reaches SourceDocumentControls.
No new global dispatcher or program representation is introduced.
The current native roots do not export Doc or reach SourceDocument.
S1 therefore adds no native Doc wrapper or export.
S3a must seal Doc if its actual protocol roots make Doc reachable.
The coordinator owns reached roots, their generation, and the native gate.
The temporary Lean audit establishes no native sealing result.

`RETIREMENTS.md` records the version-2 section-2.2 cuts.
`REACHED-VIEW-TRANSPORT.md` preserves the old reached-state statement and explicit proof-status regression.
The keepExact initial-positive correction retains its finite counterexample.
