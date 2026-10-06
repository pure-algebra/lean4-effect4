# Proposed acceptance controls

**Status:** proposed controls for future implementation. None below ran against a new API, because no such API was implemented.
The research checks performed here verify frozen source and packet references only.

| Consumer | Positive control | Refusal or deliberate failure control | Exact observation |
| --- | --- | --- | --- |
| Bundle loader | Existing admitted program and its actual ordered table load | Same program bytes with a swapped table cannot reuse the old checked handle | Program, table and computed type bound to the loaded handle |
| Bundle format | Current generated signature and supported profile load | Retired operation tag, unknown schema revision and unsupported service extension refuse | Named decode/profile refusal; no default constructor/type |
| Selection | Read a loop body at its actual Node path | Reuse the selection after replacing its base; use a term-field index as a Node child | Exact node or stale/missing-path refusal |
| Selection identity | Two handles resolving to identical bundle bytes permit equivalent lookup | Stub digest resolver maps two distinct bundles to one digest | Exact bytes still distinguish them; no assumed digest injectivity |
| Local type view | Bind continuation, Ref current value and loop body show their correct environments | Remove one binder or reverse fold accumulator/element in a mutant view | Local judgment at the exact environment refuses the mutant |
| Reference occurrence | Reference-free selection has one source occurrence | Two references to one layer cannot reuse one undistinguished expanded path | Explicit occurrence mapping or named initial-profile refusal |
| Checked edit | Replace with a same-sort, well-scoped admitted subtree | Same-sort replacement captures a different variable; a changed layer invalidates another reference | Whole rebuild accepts only the exact valid candidate |
| Edit result | Existing admitted candidate reuses rebuild_admitted | Equal old/new root types are presented as a behavior certificate | Admission succeeds independently; behavior claim remains unproved/refused |
| Prefix replay | Split a journal and use play_append | Drop a refused decoded command, or change compileFuel only | Exact run/journal/phase reconstruction differs or identity check refuses |
| Byte replay | Canonical command bytes return the existing phase | Append trailing bytes to a canonical command | Unreadable-row verdict; runner unchanged |
| Observation schema | Decode existing session-state and Run.Observation under their own schema | Label session-state as run-observation | Schema/operation mismatch refuses |
| Mixed target evidence | OCaml machine projection compares against Lean's same projection | Fill absent OCaml session fields with Lean ledger data | Provenance check refuses an independent-measurement claim |
| Clock | Canonical decimal 0 and a supported larger millisecond value round trip | Leading zero, negative, wrong unit and target out-of-range value | Existing decoder/profile refusal; no silent number conversion |
| Straight/loop bridge | Completed Looped meaning agrees at sufficient fuel; straight case uses existing bridge | Low budget returns none with changed stores | Frontier/unfinished result retains stores; no typed error or completion claim |
| Proof application | Correct theorem, universes, subject and discharged premises validate | Same theorem name with changed proposition; open premise; modulo-goal dependency | Existing refusal or unresolved result, never proved |
| JSON values | Current admitted codec value round trips | Unsupported handle or incompatible subtype layout | Codec refusal; membership/support alone is insufficient |

A finite acceptance battery does not prove the general API laws.
The future slice should retain exact inputs, compiler identity where relevant, output and deliberate-failure result.
Use the existing generated-group freshness check and existing Conform report, rather than a parallel gate or ledger.
