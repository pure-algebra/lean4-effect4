import Effects.Cas.Value

/-!
# The CAS node carrier

The ratified node object: versioned kind, canonical payload bytes, and
ordered **typed** references — each reference declares the kind tag it
expects, which is what makes the wrong-kind admission clause (CAS-002)
expressible. Addresses are full 32-byte digests (ruling D3: full digest
width, never truncated); the address FUNCTION stays abstract until
`Address.lean` — nothing in the carrier or codec mentions a hash.

`Node.WF` is the byte-bound well-formedness the codec quantifies over:
payload length and reference count below `2^32`, matching the fixed-width
scalar fields. Store-level admission (dangling and wrong-kind references
against a store) is a separate judgment in `Admission.lean`.

`Addr32` and `AdmittedNode` are `abbrev`s deliberately: they are
transparent names for subtypes, not new semantic carriers, and keeping them
reducible keeps every proof surface working at one transparency level.
-/

namespace Effects.Cas

/-- A full-width 32-byte address value. The subtype carries the width
invariant; no hash appears anywhere in this file. -/
abbrev Addr32 := { b : Bytes // b.length = 32 }

/-- A typed reference: the kind tag the referencing node expects at the
target, and the target address. -/
structure Ref where
  expectedTag : UInt8
  addr : Addr32
  deriving DecidableEq

/-- The node carrier: scheme version byte, kind tag byte, canonical payload
bytes, ordered typed references. -/
structure Node where
  version : UInt8
  tag : UInt8
  payload : Bytes
  refs : List Ref
  deriving DecidableEq

/-- Byte-bound well-formedness: the domain of the codec's round trip,
matching the fixed-width scalar fields. -/
def Node.WF (n : Node) : Prop :=
  n.payload.length < 4294967296 ∧ n.refs.length < 4294967296

instance (n : Node) : Decidable n.WF := by
  unfold Node.WF; infer_instance

/-- The admitted-node carrier: a node together with its byte-bound
well-formedness. The codec's public laws quantify over this subtype — "per
admitted node" is a statement about these values. -/
abbrev AdmittedNode := { n : Node // n.WF }

end Effects.Cas
