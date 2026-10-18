# Seams implementation receipts

K0 lands from `c752e565b4e1afac95d1258b0a4a570b81bcdf81` on `codex/seams`.
The table records landed slices. Every unlanded slice remains open. This receipt claims no completed goal.
The coordinator merges; this branch is never pushed.

The owner pauses work after V1.
[The pause checkpoint](../preparation/paused-2026-10-18/README.md) retains prepared sources, evidence, and resume instructions.

| Slice | Implementation commit | Receipt | State |
| --- | --- | --- | --- |
| K0 | `66f292a095e57e7c94586434aab9c5c597f82d6e`; receipt `faa7d0122bd550186e4c622517509ac001763a35` | [K0](K0.md) | Required checks pass. |
| S0 | `d46b1e6d6f184764a7ee1a00b01a800a45f35d33`; receipt `489e127a8b94f4796ff40ef4200080b5e83a94f2` | [S0](S0.md) | Required checks pass. |
| V1 | `d6ad9482303a1998bfbcc826bf0d12ab4f6aa3c9`; receipt `6406fa8d47b99e1b6224dffac5025f622235893c` ; receipt `6406fa8d47b99e1b6224dffac5025f622235893c` | [V1](V1.md) | Required checks pass; two placed goals remain. |
| S1 | `2e71c9dc69b1d06e2b2241f8374e0600daa90a0f` ; receipt `4de971df3ecce776ec1cc914aa326adcf88ec333` | [S1](S1.md) | Required checks pass; thirteen placed goals remain. |
| S2 | `e15394b0934f14158970b21abf65d6b391c61fe4` | [S2](S2.md) | Required checks pass; three new placed goals remain. |
| S4 | Pending | Pending | Open |
| S3a | Pending | Pending | Open |
| S3b | Pending | Pending | Open |
| ST1a | `637fd14686343632378427190c9a4ed9142a0fc7` ; receipt `0bb42e37d4fa99fd84979df03beb3dd0391a4e98` | [ST1a](ST1a.md) | Required checks pass. |
| ST1b | `79acf8fbbd74a8cee46c0dc919a8b16ff77aa959` ; receipt `709f9f10a9401150af66870a8665860e45cc63d3` | [ST1b](ST1b.md) | Required checks pass. |
| ST2 | Pending | Pending | Open |
| ST3 | Pending | Pending | Open |
| ST4 | Pending | Pending | Open |
| S6 | Pending | Pending | Open |

## Departures from the plan

| Slice | Correction and control |
| --- | --- |
| K0 | The shared launcher admits two slots and resets the thread count. An outer lock serializes this goal; the command overrides the count. |
| K0 | Split generated constructor headers need a reader repair. Current generated-file controls retain the failing baseline. |
| K0 | Deleting Cascade exposes an implicit Store import in the evaluator proof. The explicit import restores its unchanged proof. |
| K0 | `generate.py` has no semantics family. `make gen-semantics` owns that report. |
| K0 | The reader tool's String and JSON operations exceed the library proof ceiling at baseline. Library and fixture audits keep the required ceiling. |
| K0 | The native compile script names the deleted numeric interface. Removing that input repairs its retained failing command. |
| K0 | Pending nursery allocations distort immediate counters. Flushed readings pass a known-list calibration; earlier measurements are superseded. |
| S0 | The certified checker packages land in S0 to test the actual sealed boundary; V1 retains decomposition and caller migration. |
| S0 | A generated annotation leaf reader removes a dependent-child lowering refusal; its connector proves the exact ordered annotation sequence. |
| S0 | Source nominal ascriptions recover erased package types. A concrete verdict accessor replaces the refused generic mono root. |
| S0 | The stable step recomputes its source interpreter and ignores the adapter's former argument; mismatched-interpreter controls bound this change. |
| S0 | Fresh typed trees determine interfaces; final duplicate bindings win. Stale-interface and hostile-alias clients retain their refusals. |
| S0 | Explicit roots include observed inherited instance operations and Todo callers. The kit renderer now matches real kinds. |
| S0 | Generated warnings 30 and 32 are suppressed; warning 55 remains an error. The hidden-helper refusal is retained. |
| S0 | Todo placeholders remain outside the tested Live/start/restore closure, which contains no unknown type or placeholder. |
| S0 | Output alias checks cover all generated extensions and cross-artifact aliases before publication or comparison. |
| S0 | The report explicitly imports Check for its new claim. Its retained first attempt refuses the unloaded pointer. |

| ST1a | Typed reads use the per-value genesis specification; the universal-spec comparison is retained as a rejecting control. |
| ST1a | The reached-store interpreter stays explicit until ST1b; typed reading claims exact resident payloads only. |
| ST1a | Checked construction uses no_expose because an exposed definition cannot call the private constructor; the compiler refusal is retained. |
| ST1a | A store-only Rocq producer avoids the full route's compiler mismatch, compares unchanged Skeleton, and compiles every current store proof. |
| ST1a | M2 uses list constructors because Gallina refuses the polymorphic emptiness call; the failed export is retained. |
| ST1a | The native byte library is unwrapped; the fixture uses its actual module names. |
| ST1a | Cross-artifact output aliases refuse before generation; the red control overwrites only a disposable victim, and the repaired control preserves it. |
| ST1a | The old M2 mismatch tripwires fail after regeneration in both native fixtures. Both replacements require every admission row to agree with Lean. |

| ST1b | Duplicate targets retain generation; the changed-target increase law and duplicate-retention law keep ordinary row five. |
| ST1b | Version 2 retains exact UTF-8 names; legacy byte decoding keeps its original name domain and maps old planes explicitly. |
| ST1b | Checkpoint roots use journal policy and their canonical fourth parent field; incidental references refuse ancestry. |
| ST1b | Gallina prints generic Head through explicit type parameters; value parameters refuse and the type name avoids a projection collision. |
| ST1b | The audit input remains receipt evidence; acceptance fixtures stay under Test. |

| V1 | Actual dependency asks enter traces; the unchanged ask-value law now depends on the exact decomposition goal. |
| V1 | Pure signature support moves into core; exact attributed Laws wrappers retain their existing names and statements. |
| V1 | Semantic traces remain equal under certified oracle substitution. Cache cost is outside that trace observation. |
| V1 | The ask-value placement attribute follows its host-session obligation table; moved owners receive current source citations. |
| V1 | Extension and explanation exports use explicit roots and nominal ascriptions; S0 package abstraction remains checked. |
| V1 | A specialized wrapper retains a stale source recursion flag; emitted self-reference now determines recursive singleton bindings. |

| S1 | Initial root positivity is required only by positive keepExact commit claims; the local-edit counterexample remains. |
| S1 | Replay retains the undo ledger; equal source sessions can require different selected inverses. |
| S1 | Sealed runtime state retains that ledger with its replay equation; revert performs no earlier action again. |
| S1 | Reached-state observations retain their exact scope through placed goals and explicit proof-status changes. |
| S1 | Module asks retain actual dependency traces; native Doc sealing waits for the actual exported protocol closure. |

| S2 | Certification and publication agreement retain reference-free premises; publication also requires a positive base. |
| S2 | The complete anchor includes source and application; equal identity/revision alone does not authorize publication. |
| S2 | Missing nonroot focus refuses before candidate construction, without an invented key or item index. |
| S2 | Original certification and materialization algorithms move to Laws-only observations; D1–D9 retain their exact premises. |

## Proposed decisions rows

| Slice | Proposed text |
| --- | --- |
| K0 | Update `E4-CAS-CE-006` to resident node identity. Keep both own-address lookup premises and equal addresses; retain the arbitrary-content collision alternative. |
| S0 | Adopt typed-tree interface inference, explicit roots, source nominal ascriptions, and whole-package sealing for this generated family. |
| S0 | Record the exact annotation connector and the stable closed step; retain interpreter recomputation as an unmeasured cost. |

| ST1a | Adopt typed version, kind, per-value specification, and exact payload checks; preserve the genesis exception. |
| ST1a | Keep the accepted-new-to-old connector when admission gains M2, and generate native kind and refusal facts from the Lean owners. |
| ST1a | Keep semantic naturals exact and native capacity outside modeled admission. |

| ST1b | Adopt full expected heads, unchanged duplicate generations, generated policy data, and stale-first root checks. |
| ST1b | Retain explicit legacy root-byte mapping and exact version-2 names. |
| ST1b | Count fresh durable nodes only after full transaction validation; keep model cuts distinct from host crash observations. |

| V1 | Adopt the common checker, certified exact and extension reuse, and actual dependency traces. |
| V1 | Keep full verdict equality, including tables; retain placed decomposition and explanation goals and the exact ask-value dependency. |
| V1 | Keep pure support connectors in core, existing attributed wrappers in Laws, and host cost outside semantic traces. |
| V1 | Derive singleton recursion from actual emitted references; keep mutual dependency components unchanged. |

| S1 | Adopt one policy feed and one accepted-action interpreter for commit, draft, revert, and document replay. |
| S1 | Derive revision from history; preserve atomic refusal and exact snapshot checks. |
| S1 | Retain derived undo entries only in sealed memory; reconstruct them from accepted actions on load. |
| S1 | Retain initial-positive premises and full reached-state goals, with proof status measured by the report. |

| S2 | Adopt witnessed pending fills, keepExact certification, and one address-ordered publication commit. |
| S2 | Reset only after successful publication; retain full-anchor checks and precise feed refusals. |
| S2 | Keep three placed connections and the original D1–D9 observations on their explicit fragments. |

The individual receipts retain commands, exit statuses, audit output, red controls, and evidence limits.
