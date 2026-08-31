import Cas.Schema.Codec.Core

/-!
# The byte-level rendering law

`encode` under a well-formed code emits canonically spelled values —
every object node's keys already in strict order — so the canonical
rendering (`Json.renderCompact`) performs no reordering on the encode
image: the bytes a value node's identity is computed over are the
structural fold of the encoding, with no hidden sort
(`renderCompact_encode`). Together with `encode_inj` this pins one
byte string per described value under a fixed well-formed code.
-/

namespace Cas.Schema

open Cas.Json

/-- Emitted keys are the code's field names with optional-absent
fields skipped — a sublist, so key order (and strict sortedness)
transports from the code. -/
theorem encodeFields_keys_sublist :
    ∀ (fs : List (String × Bool × Ast)) (x : ElFields fs),
      List.Sublist ((encodeFields fs x).map (·.1)) (fs.map (fun f => f.1))
  | [], _ => by simp [encodeFields]
  | (n, true, a) :: fs, (xv, rest) => by
    cases xv with
    | some v =>
      simpa [encodeFields] using
        List.Sublist.cons_cons n (encodeFields_keys_sublist fs rest)
    | none =>
      simpa [encodeFields] using
        List.Sublist.cons n (encodeFields_keys_sublist fs rest)
  | (n, false, a) :: fs, (v, rest) => by
    simpa [encodeFields] using
      List.Sublist.cons_cons n (encodeFields_keys_sublist fs rest)

/-- The scalar images are canonical. -/
theorem encInt_canonical (i : SafeInt) : (encInt i).Canonical := by
  unfold encInt
  split <;> trivial

theorem encLit_canonical (l : LitVal) : (encLit l).Canonical := by
  cases l with
  | int i => exact encInt_canonical i
  | _ => trivial

/-- The reference sentinel is canonical (`"id" < "tag"`, one outer
key). -/
theorem encRef_canonical (tag : UInt8) (addr : Addr32) :
    (encRef tag addr).Canonical := by
  refine ⟨List.pairwise_singleton _ _, ⟨?_, trivial, trivial, trivial⟩, trivial⟩
  refine List.Pairwise.cons (fun b hb => ?_) (List.pairwise_singleton _ _)
  simp only [List.mem_singleton] at hb
  subst hb
  show ("id" : String) < "tag"
  decide

mutual

/-- The encode image is canonically spelled: under a well-formed code,
every object the encoder emits has strictly sorted keys. -/
theorem encode_canonical :
    ∀ (a : Ast), a.WF → ∀ (x : El a), (encode a x).Canonical
  | .null, _, _ => trivial
  | .bool, _, _ => trivial
  | .int, _, i => encInt_canonical i
  | .str, _, _ => trivial
  | .lit l, _, _ => encLit_canonical l
  | .arr a, ha, xs => by
    simp only [encode]
    exact encodeList_canonical a ha xs
  | .struct fs, ⟨hsorted, hwf⟩, x => by
    simp only [encode]
    refine ⟨?_, encodeFields_canonical fs hwf x⟩
    have hkeys : List.Pairwise (· < ·) (fs.map (fun f => f.1)) :=
      (List.pairwise_map).mpr hsorted
    have hsub := encodeFields_keys_sublist fs x
    exact (List.pairwise_map).mp (hkeys.sublist hsub)
  | .ref t, _, r => encRef_canonical t r.addr
  | .union ms _, ⟨_, hwf⟩, x =>
    encodeMembers_canonical (discriminatedB ms) ms hwf x

/-- The union image is canonical because the MEMBER's image is: a
tagged union's wire shape is the wire shape of the member that matched,
with no envelope of our own to spell. -/
theorem encodeMembers_canonical :
    ∀ (b : Bool) (ms : List Ast), WFMembers ms →
      ∀ (x : cond b (ElMembers ms) Empty), (encodeMembers b ms x).Canonical
  | true, [], _, x => Empty.elim x
  | true, [a], hwf, x => encode_canonical a hwf.1 x
  | true, a :: b :: rest, hwf, x =>
    match x with
    | Sum.inl y => encode_canonical a hwf.1 y
    | Sum.inr y => encodeMembers_canonical true (b :: rest) hwf.2 y
  | false, _, _, x => Empty.elim x

theorem encodeList_canonical :
    ∀ (a : Ast), a.WF → ∀ (xs : List (El a)),
      CanonicalItems (xs.map (encode a))
  | _, _, [] => trivial
  | a, ha, x :: xs => by
    exact ⟨encode_canonical a ha x, encodeList_canonical a ha xs⟩

theorem encodeFields_canonical :
    ∀ (fs : List (String × Bool × Ast)), WFFields fs → ∀ (x : ElFields fs),
      CanonicalFields (encodeFields fs x)
  | [], _, _ => trivial
  | (n, true, a) :: fs, ⟨ha, hwf⟩, (xv, rest) => by
    cases xv with
    | some v =>
      exact ⟨encode_canonical a ha v, encodeFields_canonical fs hwf rest⟩
    | none =>
      simpa [encodeFields] using encodeFields_canonical fs hwf rest
  | (n, false, a) :: fs, ⟨ha, hwf⟩, (v, rest) =>
    ⟨encode_canonical a ha v, encodeFields_canonical fs hwf rest⟩

end

/-- THE binding: on the encode image the canonical rendering is the
structural fold — no reordering stands between a described value and
its bytes. -/
theorem renderCompact_encode {a : Ast} (ha : a.WF) (x : El a) :
    Json.renderCompact (encode a x) = Json.renderPlain (encode a x) :=
  Json.renderCompact_eq_renderPlain _ (encode_canonical a ha x)

end Cas.Schema
