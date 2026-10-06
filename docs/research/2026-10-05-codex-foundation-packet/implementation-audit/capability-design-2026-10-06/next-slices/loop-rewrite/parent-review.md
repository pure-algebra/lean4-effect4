# Independent review of the parent synthesis

**Role:** source-grounded review. **Status:** no substantive codec or proof overclaim found in the reviewed synthesis.
`parent-review-source.json` binds the exact copy reviewed here.
The independent source freeze for this follow-up is `c22f908def0c2a881ae46040d0dbaaaa57991352`.

## Confirmed precise

- The report keeps first-order `Eff`, existing `Run` and the seven judgments.
- Its `Built` signature caveat, ordered table identity and program-bytes limitation match source.
- `RunnerBytes.observeBytes` is `HostProtocol.State`, while the larger `Run.Observation` has a separate canonical instance.
- The latter omits complete stores and traces. Raw OCaml replay omits the session ledger.
- New wrapper codecs are proposed only for a real boundary. Decoding does not imply admission.
- Proof application reconstructs an expected proposition, preserves universes and premises, and distinguishes transitive goals from proved status.
- The suspension transformation and all-budget relation are proposals, not existing checked results.
- The text separates synchronous `Looped` from asynchronous modules, and separates semantic budgets from sufficient machine fuels.

## Two small clarifications worth carrying forward

1. The prefix-reconstruction row says that stopped commands remain separate.
   Keep every attempted decoded command, including refused or frontier commands, in the `Run` journal.
   Only the raw-machine tape projection and its stopped-command mapping have the narrower boundary.
   Returned phases can be validated as an observation; they are reconstructed by replay rather than trusted as an independent input.
   A malformed byte row remains in `RunnerBytes`' transport transcript and never becomes a decoded `Command`.

2. The finished-loop theorem has a narrower root than the all-budget meaning relation.
   `LoopAgreement` uses `meaningB k e [] Stores.empty` and default-table `Api.run e fuel`.
   Name that empty-table root when proposing a machine corollary for a `Built` consumer.
   The general semantic rewrite law still quantifies every value environment and initial store.
   A nonempty table needs its own connector before that machine statement describes `Built.typed.run`.

The public facade can remain under `Api`, while the initial Looped-certified operation executes through tooling that loads Laws.
This preserves the synthesis's existing instruction against importing Laws into core.
The new brief makes that implementation boundary explicit.

## Codec and proof caveats retained in the detailed packet

Canonical byte retraction needs well-formed framing lengths.
JSON exactness uses the named `Codec.normJ` rather than unqualified byte equality.
Subtype codec reuse needs `Codec.Compatible`.
Digest equality alone proves no input identity.
`ProofRef.validate` checks the theorem and frozen proposition, but an application still requires its exact arguments and premises.
These details are already retained in `interop/report.md`; no additional framework is needed.

No parent file was edited by this review.
