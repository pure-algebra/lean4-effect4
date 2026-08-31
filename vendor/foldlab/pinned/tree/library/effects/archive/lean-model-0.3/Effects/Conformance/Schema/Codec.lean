import Effects.Conformance.Ledger

namespace Effects.Conformance

/-- SCHEMA CODEC. Sentence template: "Canonicalization is idempotent,
canonical values round-trip, the encoding is injective on canonical
forms, and a successful decode's input is exactly the canonical
encoding of its result — <domain gloss>." Kit template: a value
exercising the round trip, and bytes the decoder rejects, proving the
decoder is not constantly accepting. The exactness field is the
direction a lax codec omits: round-trip plus injectivity does NOT
imply it, so it is carried structurally, never by prose. -/
structure Codec (α Bytes : Type) where
  id : String
  sentence : String
  canon : α → α
  encode : α → Bytes
  decode : Bytes → Option α
  law_canon_idem : ∀ x, canon (canon x) = canon x
  law_roundtrip : ∀ x, decode (encode (canon x)) = some (canon x)
  law_inj : ∀ x y, canon x = x → canon y = y → encode x = encode y → x = y
  law_exact : ∀ b x, decode b = some x → b = encode x
  posVal : α
  negBytes : Bytes
  neg_rejects : decode negBytes = none

def Codec.entry {α Bytes : Type} (b : Codec α Bytes) : LedgerEntry :=
  { id := b.id, family := "CODEC", sentence := b.sentence }

end Effects.Conformance
