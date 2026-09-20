Phase B build evidence

This bundle retains 52 diagnostic logs and six input/runner metadata files in a lossless archive. It records 44 compile attempts or finite instrument controls. The serial runner records 19 successful module builds and two failed attempts, each followed by a separately retained successful retry. Standalone failures and repairs also remain separate. 14 outer process exit codes are unknown; their recorded output and any child exit are retained without promoting them to exact process status.

Both Test.All runs returned 0. The earlier audit checked 469 modules and 66,141 declarations; the latest checked 469 modules and 66,142 declarations. Both reported semantic/test axioms [propext, Quot.sound] and the same explicit implementation allowance: 14 modules, 29 declarations, additionally admitting Classical.choice. These results establish the recorded build/audit scope; they are not a claim that the Phase B wanted statements are proved.

Forms compiled directly with the confirmed command and returned 0. The two direct driver compiles (Truth and Keyed) also returned 0 through the retained sequential set -e script. Their empty diagnostic logs are kept. These are completed prerequisites for the next census, not census results. Later census and ledger-status output is excluded.

The original serial plan is retained verbatim, including stale plan-only wording and planned counts. It is not execution metadata. The runner RESULT records, exact commands where retained or coordinator-confirmed, and fresh Built lines supply the execution evidence. Every one of the 26 planned statement-build targets has a fresh Built line somewhere in this retained set; planned-module-coverage.json gives each location and excludes Replayed lines.

The instrument controls are finite checks. Search and zero-theorem-census failures, the initial missing-import setup failure, successful repairs, and the ordinary dead-tactic refusal remain distinguished. The separate phase-b-instrument-evidence bundle contains the detailed source/diff review.

All original bytes were read back from the compressed archive and compared with their source and SHA256. Archive header timestamps are normalized only for deterministic packaging; no execution timestamps are inferred. Packaging started no Lean process and changed no repository files.
