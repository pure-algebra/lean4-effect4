# ST1a proof placement

The node admission change must also govern word validation and verification.

| Claim or helper | Concept and property | Reach | Exclusions | Consumer |
| --- | --- | --- | --- | --- |
| `Node.read_exact` | exact-codecs; stored byte exactness; compatibility | Success equals the existing decoder's image, with payload formation and version zero. | Admission, hashing, capacity, persistence. | Raw byte entrance; R13. |
| `Node.readContent_exact` | exact-codecs; typed stored-carrier reading; compatibility | Version, kind, per-value spec, and canonical payload reading imply the exact node. | Hash injectivity, graph closure, native refinement. | `Cas.get_exact`; R13. |
| `Cas.get_exact` | exact-codecs; typed stored-carrier reading; compatibility | A successful typed read names its exact resident node. The reached-store replay parameter stays explicit. | Atomic commits or admission of an arbitrary replay parameter. | ST4 session loading; R13. |
| `putNode_ok_handleFree` | exact-codecs; stored node admission; preservation | Every successful node insertion passes M2 before edge and resident checks. | Liveness, host persistence, cryptographic assumptions. | `Store.Sound.handles`, word replay; R13. |
| `admissibleAfter_handleFree`, `verifyNode_handleFree` | exact-codecs; stored node admission; helper steps | Accepted words and verified residents pass M2. | Native crash behavior. | `wfFrom_apply`, `verify_sound`; R13. |

Existing `putNode_ok` keeps its accepted-operation conclusion.
Fresh and duplicate introduction laws require the new M2 premise.
The old premise set accepts a content node containing a handle; retain that counterexample.
`Store.Sound` gains M2 because it states that each resident passes current node admission.
The receipt records this strengthening and its controls before claiming the changed invariant.

The generic `CasOf replay` is the probe's reached-store package.
ST1b fixes its replay parameter to the transaction event interpreter.
No theorem claims that an arbitrary replay parameter performs admission or atomic commit.
