# Protocol retirement map

This map follows interfaces version 2, section 2.2.
V1 is validated and frozen.
S1 and S2 complete their temporary builds, batteries, and audits.
Production integration and gates remain the coordinator's.

| Required retirement | Packet and replacement | Status |
| --- | --- | --- |
| `CheckCache.lookup` | V1 `Memo.oracle` with exact and certified extension rules | Deleted; caller and battery pass |
| `CheckKey`, CheckCache `Entry`, `insert` | V1 `CheckInput`, `Memo`, checked traces | Deleted; caller and battery pass |
| `Evidence.fromCache`, `SuggestResult.cache` | V1 semantic evidence and `Checked` result | Deleted; caller and battery pass |
| Operational tool `Sketch.check`, Kit's second checker | V1 `Check.run`; Kit restricts the module key to no holes | Caller builds pass |
| `Doc` free revision field, `undo`, `fork`, own commit checks | S1 sealed origin/history/session; derived revision; sole `Doc.step` interpreter | Core, caller, battery, and audit pass |
| `certifiedB` operational owner | S2 same keepExact feed; old observation moved into Laws `FillReference` | Core, caller, battery, and audit pass |
| `CheckCache.evaluateCandidate` | S2 `suggestOne` through same keepExact feed | Core, caller, battery, and audit pass |
| `FillSet.empty`, `ofDoc`, `materializeDoc` | S2 sealed `open_`, checked add, one publication commit | Core, caller, battery, and audit pass |
| `Program.materialize` | S2 publication; Laws-only `FillReference.materialize` retains exact old observation | Core, caller, battery, and audit pass |

S1 keeps the old pending-fill interface through an interim caller migration.
That migration routes its publication through `Doc.step` and introduces no second edit interpreter.
S2 removes that interim owner and moves all original D1–D9 observations into the Laws reference.

The current `Snapshot` is a preview-input cache, not Doc persistence.
It stays until its S3b callers move.
No format migration or fabricated history is introduced in S1.

The request dispatcher, legacy Query premises, Snapshot, and wire encoding retire in S3a and S3b.
They are outside these three packets and remain assigned to their named slices.
