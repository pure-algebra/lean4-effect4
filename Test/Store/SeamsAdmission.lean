import Effect4.Store.Domain.Word

/-!
# M2 admission controls

The old premise set admits the handle genesis in the retained baseline probe.
This fixture checks the new refusal, its precedence, and the callers that share it.
These are finite evaluations. The invariant proofs remain `putNode_ok_handleFree` and `verify_sound`.
-/

set_option autoImplicit false
namespace Test.Store.SeamsAdmission
open Effect4.Store

/- The baseline counterexample satisfies every old local admission premise. -/
def handleGenesis : Node := ⟨0, .schema, zeroDigest, .handle 2 7⟩

#guard handleGenesis.payload.wf
#guard handleGenesis.version = 0
#guard !handleGenesis.malformedRef
#guard handleGenesis.checkedEdges = []
#guard handleGenesis.handleInContent
#guard refusedWith (Store.empty.putNode handleGenesis) .handleInContent

/- A forged resident cannot bypass admission through the duplicate branch. -/
def forged : Store := ⟨[(sha256 handleGenesis.encode, handleGenesis)], []⟩
#guard refusedWith (forged.putNode handleGenesis) .handleInContent
#guard match forged.verify with
  | .error (.handleInContent d) => decide (d = sha256 handleGenesis.encode)
  | _ => false

/- Content handles refuse before the missing spec edge. -/
#guard refusedWith (Store.empty.putNode ⟨0, .«export», zeroDigest, .handle 2 7⟩) .handleInContent

/- Version and malformed-reference checks still precede M2. -/
#guard refusedWith (Store.empty.putNode ⟨1, .«export», zeroDigest, .handle 2 7⟩) .badVersion
#guard refusedWith (Store.empty.putNode
  ⟨0, .tree, zeroDigest, .pair (.ref 127 zeroDigest.bytes) (.handle 2 7)⟩) .malformedRef

/- Only run-relative kinds admit the handle when their spec resolves. -/
#guard ([Kind.tape, .log, .exits, .checkpoint].all fun k =>
  outcomeIs (probeStore.putNode ⟨0, k, probeSchemaAddress, .handle 2 7⟩) .fresh)
#guard (Kind.all.filter Kind.isContent).all fun k =>
  refusedWith (probeStore.putNode ⟨0, k, probeSchemaAddress, .handle 2 7⟩) .handleInContent

/- The word checker and replay agree on the same counterexample. -/
def badWord : Word := [⟨sha256 handleGenesis.encode, handleGenesis⟩]
#guard !(Word.wf badWord)
#guard match Word.apply badWord Store.empty with
  | .error .handleInContent => true
  | _ => false

/- Shared passive kind facts preserve the native classifications. -/
#guard (Kind.all.filter Kind.tombstoned) = [.fiber]
#guard (Kind.all.filter Kind.isInterior) = [.chunk]

/- Parse diagnostics retain their distinct admission constructors. -/
#guard Admission.ofRead (.unknownTag 253) = .unknownTag 253
#guard Admission.ofRead .trailing = .trailing
#guard Admission.ofRead .badFrame = .badFrame
#guard Admission.ofRead .shortSpec = .shortSpec
#guard Admission.ofRead (.unregisteredKind 127) = .unregisteredKind 127
#guard Admission.ofRead (.badVersion 4) = .badVersion

end Test.Store.SeamsAdmission
