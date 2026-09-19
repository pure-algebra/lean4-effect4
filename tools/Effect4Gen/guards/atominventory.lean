/-! ## Acceptance guards for the generated atom inventory

Appended verbatim by `--append tools/Effect4Gen/guards/atominventory.lean` into
`src/Effect4/Program/AtomInventory.lean`. The generator reads the constructor list off the
environment, so the list cannot omit a constructor; `all_complete` is the guard that says so
inside the language, and `covers_iff` turns the Boolean coverage check a consumer runs into the
universal statement about the alphabet. Both were hand-written beside a hand-written `all`
until the inventory became generated; their statements and their proofs are unchanged. -/

namespace Effect4.Program.NativeAtom

/-- Every constructor is in the inventory. -/
theorem all_complete (atom : NativeAtom) : atom ∈ all := by
  cases atom <;> simp [all]

/-- Covering the names is covering the alphabet. -/
theorem covers_iff (consumerNames : List String) :
    covers consumerNames = true ↔ ∀ atom : NativeAtom, atom.name ∈ consumerNames := by
  simp only [covers, names, List.all_eq_true, List.mem_map, List.contains_iff_mem]
  constructor
  · intro h atom
    exact h atom.name ⟨atom, all_complete atom, rfl⟩
  · intro h value hv
    obtain ⟨atom, _, rfl⟩ := hv
    exact h atom

end Effect4.Program.NativeAtom

/-! ## Receipts -/

#print axioms Effect4.Program.NativeAtom.all_complete
#print axioms Effect4.Program.NativeAtom.covers_iff
