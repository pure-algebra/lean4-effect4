import Effect4

/-!
Finite representation controls for accepted-action persistence.
Concept: host-session-protocol, typed replay.
Consumer: proposed Tool.State.transcript in S3a and its ST4 serializer.
The red case checks that erased reachability cannot supply runtime history.
The green case retains history as data. Neither case proves Tool replay or host agreement.
The edge controls compare raw digests and reference frames using the existing store codec.
-/
namespace SeamsTranscriptCarrierControl

structure WitnessOnly where
  raw : Nat
  reached : ∃ actions : List Nat, actions.length = raw

/-- error: Tactic `cases` failed -/
#guard_msgs(error, substring := true) in
def lostTranscript (s : WitnessOnly) : List Nat :=
  match s.reached with
  | ⟨actions, _⟩ => actions

structure Retained where
  transcript : List Nat
  raw : Nat
  replayed : transcript.length = raw

def retainedExample : Retained := ⟨[4, 9], 2, rfl⟩
#guard retainedExample.transcript == [4, 9]
#guard retainedExample.raw == 2

open Effect4.Store

-- A digest encodes bytes, so the node edge traversal sees no reference.
#guard (Canonical.toVal zeroDigest).refs = []
-- An explicit reference frame exposes its kind and digest to that traversal.
#guard (Canonical.toVal (AnyRef.mk .entry zeroDigest)).refs =
  [AnyRef.mk .entry zeroDigest]

end SeamsTranscriptCarrierControl
