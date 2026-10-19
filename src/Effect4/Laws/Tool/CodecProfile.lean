import Effect4.Tool.CodecProfile
import Effect4.Laws.Store.ShapeRead
import Effect4.Laws.Auto.Semantics
/-!
# Laws.Tool.CodecProfile — the tool's JSON profile, located and exact

## Placement

Concept `exact-codecs` (`docs/core/semantics.md` §2.5): write/read retraction on an admitted
JSON profile, and exactness of its reader modulo a named normaliser. Requirements R8, R12, R14.

- **`codec-profile-retains-value`** (claim, role compatibility; pointer `write_read`): a
  successful guarded write reads back as the original carrier. Reach: every Canonical carrier and
  each successful guarded write. Not established: total writing, raw JSON text identity, the native
  parser. Consumer: the Tool driver emits only a JSON value that reads as the original carrier.
- **`json-read-located`** (proposed claim, role compatibility; pointer `profileLocated_exact`):
  whatever the profile's located reader reads from a tree is the carrier whose canonical print is
  the tree's binary64 image, normalised by `ShapeDoc.order`; every refusal names a site of the
  input (`profileLocated_site`); the located reader erases to the codec's reader
  (`profileLocated_erases`), and a guarded write reads back through it (`write_readLocated`).
  Reach: the explicit JSON profile, with no budget; the binary64 face through
  `NatJson.ofBinary64`, the native face directly. Not established: the round trip of an arbitrary
  value that fits a shape, which needs the write guard; textual JSON identity; that a refusal's
  reason is the only one the input has. Consumers: the tool's wire (`Tool.Wire`), the native shell
  (`Tool.Native.serveTree`), and the MCP server's argument refusals.
- **`read_toBinary64`** (a step of `json-read-located`, the theorem that replaces `kit_json.ml`'s
  caveat K1): within the profile, the two faces read a tree alike.
-/
set_option autoImplicit false
namespace Effect4.Tool.CodecProfile
open Effect4 (Json NatJson JsonSite)
open Effect4.Store

/-- **A successful guarded write reads back as the original carrier.** The pointer of
`codec-profile-retains-value`. -/
@[semantics "exact-codecs" (requirement := R12)]
theorem write_read {α : Type} [Canonical α] (value : α) (json : Effect4.Json)
    (h : write value = .ok json) : read json = .ok value := by
  unfold write at h
  split at h
  · cases hc : carries (Canonical.toVal value) with
    | false =>
      simp only [hc, Bool.not_false, ↓reduceIte] at h
      cases h
    | true =>
      simp only [hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      cases hr : read (α := α) (Canonical.printArrays value) with
      | error r =>
        rw [hr] at h
        cases h
      | ok decoded =>
        rw [hr] at h
        dsimp only at h
        split at h
        · rename_i he
          have hd : decoded = value := Canonical.toVal_injective he
          subst decoded
          have hj := Except.ok.inj h
          subst json
          exact hr
        · cases h
  · cases h

/-- **The located reader erases to the codec's reader**: on the binary64 tree, forgetting where
and why it refuses gives `read`'s answer. `read` is the located reader's projection, so this holds
by definition and is the bridge `write_readLocated` transports by. A step of
`json-read-located`. -/
@[semantics "exact-codecs" (requirement := R12)]
theorem profileLocated_erases {α : Type} [Canonical α] (j : Json) :
    (readLocated (α := α) (NatJson.ofBinary64 j)).toOption = (read (α := α) j).toOption := by
  unfold read
  cases readLocated (α := α) (NatJson.ofBinary64 j) <;> rfl

/-- **Whatever the profile reads is the carrier whose canonical print is the input's binary64
image, normalised.** The pointer of `json-read-located`. -/
@[semantics "exact-codecs" (requirement := R12)]
theorem profileLocated_exact {α : Type} [Canonical α] {t : NatJson} {a : α}
    (h : readLocated t = .ok a) : Canonical.print a = (Canonical.shape α).order t.toBinary64 := by
  unfold readLocated at h
  split at h
  · exact Canonical.readLocated_exact h
  · cases h

/-- **A guarded write reads back through the located reader**, transported from `write_read`
through `read`, the located reader's projection. A step of `json-read-located`. -/
@[semantics "exact-codecs" (requirement := R12)]
theorem write_readLocated {α : Type} [Canonical α] {a : α} {j : Json} (h : write a = .ok j) :
    readLocated (NatJson.ofBinary64 j) = .ok a := by
  have hr := write_read a j h
  unfold read at hr
  cases hl : readLocated (α := α) (NatJson.ofBinary64 j) with
  | error r =>
    rw [hl] at hr
    cases hr
  | ok a' =>
    rw [hl] at hr
    cases hr
    rfl

/-- **Every refusal of the profile names a site of its input**: a value it holds, a field missing
from an object it holds, the root where the carrier refuses, or the shape's root where the profile
refuses the shape. The diagnostic property of `json-read-located`. -/
@[semantics "exact-codecs" (requirement := R12)]
theorem profileLocated_site {α : Type} [Canonical α] {t : NatJson} {r : JsonRefusal}
    (h : readLocated (α := α) t = .error r) : JsonSite.Valid t r.site := by
  unfold readLocated at h
  split at h
  · exact Canonical.readLocated_site h
  · cases h
    rfl

/-- **Within the profile, the two faces read a tree alike**: the binary64 face reads the tree's
binary64 image as the native face reads the tree. A step of `json-read-located`; it replaces the
comment-only caveat K1 of the deleted `kit_json.ml`. -/
@[semantics "exact-codecs" (requirement := R12)]
theorem read_toBinary64 {α : Type} [Canonical α] {t : NatJson} (h : t.within = true) :
    read (α := α) t.toBinary64 = (readLocated t).mapError .unreadable := by
  unfold read
  rw [ofBinary64_toBinary64 h]

end Effect4.Tool.CodecProfile
