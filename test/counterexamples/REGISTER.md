# Effect4 counterexample register

Stable IDs in this file are never reused. A row closes only when its witness
is retained and the repaired declaration or theorem mechanically rejects the
attack. `PINNED` means the witness already exists at the named immutable source
revision; `SEEDED` means the packet has frozen the attack but no immutable
provenance pin for its Effect4 witness has yet been recorded.

| ID | Status | Attacked statement | Witness / evidence | Forced repair |
| --- | --- | --- | --- | --- |
| `E4-ALG-CE-001` | SEEDED | Handler sum can be characterized by one arm or by examples | `Effect4Test/Algebra/ExtractionContract.lean`, `swappedSum`, differs on both arms | require both projection equations and `Handler.sum_unique` |
| `E4-ALG-CE-002` | PINNED | Monad-morphism laws alone pin an interpreter | Foldlab `Universal.lean:701–714`, `pinned_needs_op_agreement`, at commit `feb29321fd50204aa338209d313e84a3f8b71c66` | require agreement with the supplied handler on every one-operation program |
| `E4-ALG-CE-003` | PINNED | Operation agreement alone pins an interpreter; or `Program S` is initial among bare monads | Foldlab `Universal.lean:716–727`, `pinned_needs_the_morphism_law`, plus its two distinct state morphisms, same pin | require both pure/bind preservation and operation agreement; state initiality only in the category of `S`-models |
| `E4-ALG-CE-004` | PINNED | All handler towers form one monoid | Foldlab `Universal.lean:739–790`: composition changes source/target signatures; only `Handler S (Program S)` is closed | state a category across signatures and a monoid only on endomorphisms |
| `E4-ALG-CE-005` | SEEDED | Program result universes may vary independently of the signature answer and handler input universe | guarded rejection of `Program SmallSignature Type` in the algebra battery | align the three universes; add only explicit, law-carrying lifts later |
| `E4-ALG-CE-006` | PINNED | A fixed-fuel evaluator admits a bind/composition law | Foldlab `Universal.lean:894–910`, `run_has_no_composition_law`, same pin | state composition at `interpret`/big-step, never at one fixed fuel |
| `E4-ALG-CE-007` | PINNED | The higher-order proof carrier is canonical first-order program content | Foldlab `Prog.lean:12–15`: continuations are host functions and are not serializable | keep `Program` as proof syntax; introduce a distinct checked first-order flow with an explicit embedding |
| `E4-ALG-CE-008` | SEEDED | Inductiveness makes every `Program` a globally finite tree | `Effect4Test/Algebra/ExtractionContract.lean`: a `Nat`-indexed injective continuation has distinct children of unbounded finite depth | describe `Program` as a well-founded higher-order W-tree; claim only selected-branch well-foundedness, not finite branching or a uniform depth bound |
| `E4-FLOW-CE-001` | SEEDED | Duplicate block identifiers may be resolved by first-row/last-row lookup or normalization | `Effect4Test/Flow/AdmissionContract.lean`, `duplicateBlockFlow` | reject with `.duplicateBlockId` before canonical-order checking; preserve one unambiguous block table |
| `E4-FLOW-CE-002` | SEEDED | All dangling references can share a clause-only or block-only diagnostic | `Effect4Test/Flow/AdmissionContract.lean`, `danglingRootFlow` and `danglingSuccessorFlow` | distinguish exact root-row and successor-slot sites and retain the missing target payload |
| `E4-FLOW-CE-003` | SEEDED | Resolved block references imply operation closure | `Effect4Test/Flow/AdmissionContract.lean`, `unknownOperationFlow` | check every `perform` against the supplied closed alphabet before local term typing |
| `E4-FLOW-CE-004` | SEEDED | A known operation and resolved target suffice for term typing | `Effect4Test/Flow/AdmissionContract.lean`, `answerTargetMismatchFlow` | require the target block input to equal the operation answer type and report expected/actual types |
| `E4-FLOW-CE-005` | SEEDED | Admission must reject cycles to retain an inductive meaning | `Effect4Test/Flow/AdmissionContract.lean`, `selfCycleFlow` | admit locally typed closed cycles; define divergence later in relational semantics rather than graph admission |
| `E4-FLOW-CE-007` | SEEDED | Soundness/completeness pins which of several defects is reported | `Effect4Test/Flow/AdmissionContract.lean`, `firstDiagnosticFlow` | freeze packet-owned clause order and prove the returned diagnostic is the first condemning clause |
| `E4-FLOW-CE-013` | SEEDED | A raw first-order branch may store a Lean continuation | compile-negative in `Effect4Test/Flow/AdmissionContract.lean` | require nominal child `BlockId`s only; keep host functions outside canonical content |
| `E4-FLOW-CE-014` | SEEDED | Reference closure may ignore unreachable blocks, or admission may require every block reachable and acyclic | `Effect4Test/Flow/AdmissionContract.lean`, `unreachableClosedCycleFlow` and `unreachableDanglingFlow` | allow unreachable closed cycles but reject every dangling successor in the whole raw document |

Area-specific attack shapes are in
[`algebra/ATTACKS.md`](algebra/ATTACKS.md) and
[`flow/ATTACKS.md`](flow/ATTACKS.md). Fired implementation attacks add a
`BROKE / LAW / WITNESS / CLASS / FIXED-BY` record to the owning contract packet
without deleting the stable row.
