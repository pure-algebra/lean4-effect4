import Effect4.Api
import Effect4.Program.Profile

/-!
Fresh kernel dependency report for the host specification (`src/Effect4/Program/Profile.lean`)
and the recorded-reply section of `src/Effect4/Program/Admit.lean`; plan
`docs/research/2026-09-09-foundation-settlement-v2.md` §3 row S6a, contract
`Test/Program/HostSpecContract.lean`.

Coordinator-owned, appended from the `#print axioms` output at each landing. Every declaration
below is expected at the ceiling `propext`/`Quot.sound`; the gate
(`Test/Audit/AxiomGate.lean`) is what enforces it, this file is the human-readable receipt.
-/

-- PROFILE/data: the serialisable half, and the pinned rc.112 profile.
#print axioms Effect4.Program.InvocationForms
#print axioms Effect4.Program.CallClass
#print axioms Effect4.Program.ProfileData
#print axioms Effect4.Program.ProfileData.formsOf
#print axioms Effect4.Program.ProfileData.adapterOf
#print axioms Effect4.Program.ProfileData.admitsNat
#print axioms Effect4.Program.ProfileData.admitsNat_iff
#print axioms Effect4.Program.rc112

-- PROFILE/spec: the relations and the three laws.
#print axioms Effect4.Program.HostSpec
#print axioms Effect4.Program.LawfulHostSpec
#print axioms Effect4.Program.Profile.graphOf
#print axioms Effect4.Program.Profile.graphOf_snd
#print axioms Effect4.Program.Profile.graph_functional

-- PROFILE/scalar model: the pure row, its laws, and its three transitions.
#print axioms Effect4.Program.Profile.Scalar.waitRow
#print axioms Effect4.Program.Profile.Scalar.profile
#print axioms Effect4.Program.Profile.Scalar.refusal
#print axioms Effect4.Program.Profile.Scalar.Rep
#print axioms Effect4.Program.Profile.Scalar.RelatedState
#print axioms Effect4.Program.Profile.Scalar.observe
#print axioms Effect4.Program.Profile.Scalar.after
#print axioms Effect4.Program.Profile.Scalar.outcome?
#print axioms Effect4.Program.Profile.Scalar.step?
#print axioms Effect4.Program.Profile.Scalar.spec
#print axioms Effect4.Program.Profile.Scalar.lawful
#print axioms Effect4.Program.Profile.Scalar.outcome_in_profile
#print axioms Effect4.Program.Profile.Scalar.outcome_out_of_profile
#print axioms Effect4.Program.Profile.Scalar.in_profile
#print axioms Effect4.Program.Profile.Scalar.out_of_profile
#print axioms Effect4.Program.Profile.Scalar.no_step_of_wrong_shape

-- PROFILE/allocating model: acquire, use, release, and the rollback refutation.
#print axioms Effect4.Program.Profile.Resource.State
#print axioms Effect4.Program.Profile.Resource.State.isOpen
#print axioms Effect4.Program.Profile.Resource.HostVal
#print axioms Effect4.Program.Profile.Resource.Rep
#print axioms Effect4.Program.Profile.Resource.RelatedState
#print axioms Effect4.Program.Profile.Resource.observe
#print axioms Effect4.Program.Profile.Resource.after
#print axioms Effect4.Program.Profile.Resource.outcome?
#print axioms Effect4.Program.Profile.Resource.step?
#print axioms Effect4.Program.Profile.Resource.spec
#print axioms Effect4.Program.Profile.Resource.lawful
#print axioms Effect4.Program.Profile.Resource.acquire_extends
#print axioms Effect4.Program.Profile.Resource.use_fails_after_mutation
#print axioms Effect4.Program.Profile.Resource.use_failure_mutated
#print axioms Effect4.Program.Profile.Resource.release_after_failure
#print axioms Effect4.Program.Profile.Resource.no_use_after_release
#print axioms Effect4.Program.Profile.Resource.no_double_release
#print axioms Effect4.Program.Profile.Resource.failing
#print axioms Effect4.Program.Profile.Resource.rollbackStep?
#print axioms Effect4.Program.Profile.Resource.rollbackSpec
#print axioms Effect4.Program.Profile.Resource.rollback_steps
#print axioms Effect4.Program.Profile.Resource.rollback_not_lawful

-- ADMIT/envelope (DI-58): the recorded reply, its envelope, and the one-completion law.
#print axioms Effect4.Program.RecordedReply
#print axioms Effect4.Program.Envelope
#print axioms Effect4.Program.acceptReply
#print axioms Effect4.Program.acceptReply_envelope
#print axioms Effect4.Program.acceptReply_decision
#print axioms Effect4.Program.acceptReply_of_envelope
#print axioms Effect4.Program.acceptReply_none_of_table
#print axioms Effect4.Program.acceptReply_none_of_request
#print axioms Effect4.Program.acceptReply_none_of_admit
#print axioms Effect4.Program.acceptReply_none_of_unparked
#print axioms Effect4.Program.steppedBy
#print axioms Effect4.Program.AcceptedOnce
#print axioms Effect4.Program.acceptedOnce_of_unparked
