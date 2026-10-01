# Ingest census

Pinned projects: 34. Files: 26145; candidate files: 15866.

v4: **44 / 69447** corroborated lifts. V3 and pre-v3 are input data only and excluded from this score.

Every one of 3320 file disagreements has a copied source fixture and a defects.jsonl entry; 0 include declaration-enumeration differences.

| Generation | Candidates | Corroborated lifts | Unit disagreements |
| --- | ---: | ---: | ---: |
| v4 | 69447 | 44 | 8376 |
| v3 | 5087 | 56 | 516 |
| pre-v3 | 38 | 0 | 5 |

## V4 refusal codes

- E-PARAM-SHAPE: 28374
- E-IMPORT-OPAQUE: 10954
- E-SPINE-ESCAPE: 8058
- E-NODE: 6634
- E-OP-UNKNOWN: 5209
- E-TYPE-PARAM: 4109
- E-ARG-DYNAMIC: 2938
- E-PROGRAM: 2529
- E-OP-RECEIVER: 1955
- E-NODE-SHAPE: 938
- E-REF-UNBOUND: 931
- E-BIND-SHAPE: 718
- E-YIELD-POSITION: 126
- E-ARG-CLOSURE: 116
- E-BRANCH: 61
- E-STMT-SHAPE: 28
- E-RETURN-SHAPE: 23
- E-FAIL-NOT-DOCUMENTED: 15
- E-LOOP: 3
- E-HANDLER: 2
- E-REF-FORWARD: 1

## V4 unknown heads

- "Schema.Struct": 2032
- "Schema.decodeUnknownEffect": 547
- "Schema.Union": 265
- "Schedule.max": 237
- "unstable/reactivity/Atom.make": 201
- "Schema.Literals": 138
- "Schedule.exponential": 92
- "Schema.decodeUnknownSync": 92
- "unstable/cli.Command.make": 88
- "Schema.Array": 79
- "Function.dual": 56
- "Schema.brand": 55
- "Schema.decodeUnknownOption": 50
- "unstable/httpapi.HttpApiBuilder.group": 50
- "Schema.Record": 48
- "Schema.TaggedStruct": 44
- "Schema.check": 35
- "Schedule.min": 32
- "Config.string": 29
- "unstable/cli/Command.make": 28
- "Schema.fromJsonString": 26
- "Schema.String.check": 26
- "unstable/ai/Tool.providerDefined": 25
- "Semaphore.makeUnsafe": 22
- "Context.Reference": 20
- "Schema.encodeSync": 20
- "Schema.TaggedUnion": 20
- "Schema.decodeUnknownResult": 19
- "unstable/ai.Tool.make": 18
- "unstable/cli.Flag.string": 16

Code and head histograms count a unit once per distinct engine answer; disagreements can therefore contribute two different answers. Full counts by project and generation are in summary.json. File rows, unit rows, dependency provenance and source pins are retained alongside this report.
