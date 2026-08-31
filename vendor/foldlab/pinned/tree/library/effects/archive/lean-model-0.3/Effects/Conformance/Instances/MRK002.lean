import Effects.Conformance.Schema.TraceExcludes
import Effects.Merkle.Laws

/-!
# MRK-002 — the decoder emits only verified chunks

TRACE-EXCLUDES over the verified-streaming decoder at the decision-tag
projection, the state paired with its pending input: the guarded mode
is "not entitled to emit" — the machine is not active on an in-range
leaf frame whose expected address the input chunk's leaf pre-image
hashes to — and the excluded decision is the emission tag. The
run-level half against a committed list, with the collision witness in
the consumed prefix and the decoder under no obligation to detect it,
is the named theorem `drun_emissions_sound`. The negative kit is a
correct chunk for its frame, which does emit — the gate is not
vacuous.
-/

namespace Effects.Conformance

open Effects.Merkle
open Effects.Cas (Bytes)

/-- The kit address function: an injective-enough structural encoder
over byte-list addresses. Vectors use the declared toy digest; kits
need only computability.

An address here carries its whole pre-image, so it is as long as the
subtree beneath it. Every kit below decides address equality by kernel
evaluation of these lists, and the cost grows with both chunk width and
tree depth. -/
def mrkKitH : HP Bytes :=
  ⟨fun p => match p with
    | .leaf i b => 0 :: UInt8.ofNat i :: b
    | .parent l r => 1 :: UInt8.ofNat l.length :: (l ++ r)⟩

/-- The kit decoder environment: two chunks, full range. Two one-byte
chunks is a bound the kits depend on, not an arbitrary sample — the
entitlement kits decide `dstep` over this environment by kernel
evaluation, so widening it lengthens every address compared. -/
def mrkKitD : DParams Bytes :=
  ⟨mrkKitH, 2, mrkKitH.H (.parent (mrkKitH.H (.leaf 0 [7]))
    (mrkKitH.H (.leaf 1 [8]))), 0, 2⟩

private abbrev DStI := DState Bytes × DInput Bytes

private def leafFrame0 : DState Bytes :=
  ⟨[⟨mrkKitH.H (.leaf 0 [7]), 0, 1⟩], .active⟩

/-- MRK-002: a chunk is emitted only after it verifies. -/
def mrk002 : TraceExcludes DStI Unit DTag Bool where
  id := "MRK-002"
  sentence := "When the pending input is not entitled to emit — the decoder is not active on an in-range leaf frame whose expected address the input chunk's leaf pre-image hashes to — no step ever emits: emission IS verification, and against a committed list every emission matches the committed chunk at its index or a hash-collision witness exists in the consumed prefix, the decoder being under no obligation to detect the collision."
  modeOf := fun p => emissionEntitled mrkKitD p.1 p.2
  guarded := false
  decisions := fun p _ =>
    ((dstep mrkKitD p.1 p.2).decisions).map DDecision.tag
  bad := .emitted
  law := fun p _ h => dstep_emits_only_entitled mrkKitD p.1 p.2 h
  posState := (leafFrame0, .chunkNode [9])
  posInput := ()
  pos_mode := by decide
  negState := (leafFrame0, .chunkNode [7])
  negInput := ()
  neg_mode := by decide
  neg_bad := by decide

end Effects.Conformance
