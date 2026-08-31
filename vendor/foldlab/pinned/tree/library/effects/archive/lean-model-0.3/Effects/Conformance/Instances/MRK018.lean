import Effects.Conformance.Schema.Codec
import Effects.Merkle.Manifest

/-!
# MRK-018 — the blob-manifest codec, recipe-gated

CODEC over bounded manifest contents: the canonical sixteen-byte
payload commits the recipe identity, the total byte length, and the
leaf count. The decoder is closed, exact, and RECIPE-GATED — an
unknown recipe identifier fails closed at decode, so a reader never
guesses semantics; changing any identity-affecting recipe parameter
changes the manifest id because the recipe id is inside the committed
payload. The rejection kit is a registered-looking prefix that is not
a canonical document.
-/

namespace Effects.Conformance

open Effects.Merkle

/-- Manifest contents with representable fields and a registered
recipe. -/
abbrev BoundedManifest :=
  { m : ManifestContent // knownRecipes.contains m.recipeId ∧
      m.recipeId < 4294967296 ∧ m.totalBytes < 18446744073709551616 ∧
      m.leafCount < 4294967296 }

/-- The closed decoder at the bounded carrier. -/
def decodeManifestBounded (b : List UInt8) : Option BoundedManifest :=
  (decodeManifest? b).bind fun m =>
    if h : knownRecipes.contains m.recipeId ∧ m.recipeId < 4294967296 ∧
        m.totalBytes < 18446744073709551616 ∧ m.leafCount < 4294967296
    then some ⟨m, h⟩ else none

theorem decodeManifestBounded_encode (x : BoundedManifest) :
    decodeManifestBounded (encodeManifest x.val) = some x := by
  obtain ⟨hr, hrb, ht, hl⟩ := x.property
  unfold decodeManifestBounded
  rw [decodeManifest_encodeManifest x.val hr hrb ht hl]
  simp only [Option.bind_some]
  rw [dif_pos ⟨hr, hrb, ht, hl⟩]

theorem decodeManifestBounded_exact (b : List UInt8) (x : BoundedManifest)
    (h : decodeManifestBounded b = some x) : b = encodeManifest x.val := by
  unfold decodeManifestBounded at h
  match hd : decodeManifest? b with
  | none =>
    rw [hd] at h
    exact nomatch h
  | some m =>
    rw [hd] at h
    simp only [Option.bind_some] at h
    split at h
    · injection h with h
      subst h
      exact (decodeManifest_exact b m hd).1
    · exact nomatch h

/-- MRK-018: blob manifests parse fail-closed, exactly, and
recipe-gated. -/
def mrk018 : Codec BoundedManifest (List UInt8) where
  id := "MRK-018"
  sentence := "Blob-manifest contents parse fail-closed and exactly: the canonical sixteen-byte payload commits the recipe identity, the total byte length, and the leaf count; truncation, trailing content, and UNKNOWN RECIPE IDENTIFIERS are all rejected at decode, so a reader selects semantics from the registered recipe id and never guesses, and changing any identity-affecting recipe parameter changes the manifest identity."
  canon := id
  encode := fun m => encodeManifest m.val
  decode := decodeManifestBounded
  law_canon_idem := fun _ => rfl
  law_roundtrip := fun x => decodeManifestBounded_encode x
  law_exact := fun b x h => decodeManifestBounded_exact b x h
  law_inj := fun x y _ _ henc => by
    have hx := decodeManifestBounded_encode x
    rw [henc, decodeManifestBounded_encode y] at hx
    injection hx with hx
    exact hx.symm
  posVal := ⟨⟨1, 5, 1⟩, by decide⟩
  negBytes := encodeManifest ⟨9, 5, 3⟩
  neg_rejects := by decide

end Effects.Conformance
