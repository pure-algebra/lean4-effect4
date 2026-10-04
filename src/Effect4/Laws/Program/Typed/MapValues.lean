import Effect4.Program.Typed
import Effect4.Laws.Machine.Map
import Effect4.Laws.Auto.RuleSets

/-! Shared map-value proof steps for `denote-typed`.
The Boolean and world-indexed native-atom proofs consume the same carrier reconstruction and
canonical-order facts. They concern the existing string-map image, with every payload premise
retained. They do not establish scheduler progress, JSON admission or target execution.
The contract is `docs/research/2026-10-03-data-language/maps-tuples-brief.md`, decisions row 197. -/

set_option autoImplicit false

namespace Effect4.Program.Typed.MapValues
open Effect4.Machine

/-- Element witnesses reconstruct the entire encoded list, keeping each payload predicate.
Both map membership inversions and ordinary entry conversion use this fact. -/
theorem encoded_of_all {α β : Type} (encode : β → α) (P : β → Prop)
    (values : List α) (h : ∀ value ∈ values, ∃ entry, value = encode entry ∧ P entry) :
    ∃ entries : List β, values = entries.map encode ∧ ∀ entry ∈ entries, P entry := by
  induction values with
  | nil => exact ⟨[], rfl, fun _ hmem => nomatch hmem⟩
  | cons value values ih =>
    obtain ⟨entry, rfl, hp⟩ := h value List.mem_cons_self
    obtain ⟨entries, rfl, hentries⟩ := ih (fun v hv => h v (List.mem_cons_of_mem _ hv))
    refine ⟨entry :: entries, rfl, ?_⟩
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact hp
    · exact hentries e he

/-- Canonical field order implies the existing map-value order check. -/
theorem sorted_pairs {entries : List (String × Val)}
    (h : Field.Ascending Field.bytesKey entries) :
    sortedEntries (entries.map fun e => .pair (.str e.1) e.2) = true := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    cases entries with
    | nil => rfl
    | cons next rest =>
      have hp := List.pairwise_cons.mp h
      exact Bool.and_eq_true_iff.mpr ⟨hp.1 next List.mem_cons_self, ih hp.2⟩

/-- Canonicalization retains a payload predicate. This is shared by map update and construction. -/
theorem canon_all {P : Val → Prop} {entries : List (String × Val)}
    (h : ∀ e ∈ entries, P e.2) :
    ∀ e ∈ Field.canonBy Field.bytesKey entries, P e.2 :=
  fun e he => h e (Field.mem_canonBy he)

end Effect4.Program.Typed.MapValues
