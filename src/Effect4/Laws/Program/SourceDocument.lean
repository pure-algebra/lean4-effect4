import Effect4.Program.Typing.SourceDocument
import Effect4.Laws.Program.SourceTable

/-!
# Laws.Program.SourceDocument — soundness of atomic checked edits (`Doc.commit_sound`)

* `edit_exists`: the edit a `Change` makes exists (`Sketch.edit`) whenever the target address holds
  the expected sub-program.
* `Doc.commit_sound`: an accepted edit (`d.commit t c policy = .ok d'`) matches the document
  identity (`t.doc = d.id`) and revision (`t.revision = d.revision`), keeps the document identity
  (`d'.id = d.id`), advances the revision (`d'.revision = d.revision + 1`), keeps the session
  coherent (`d'.session.Coherent`), preserves the application (`d'.session.app = d.session.app`),
  holds the edited sketch, and types the new sketch under `Sketch.sourceCheck`. Under
  `Policy.keepExactType`, the old root type and the focus's environment and type at `t.path` are
  preserved.

## Placement

- **Concept**: `initial-algebras-folds` (`docs/core/semantics.md`); property:
  `source-session-coherent`.
- **Question**: serves the proposed compatibility claim `checked-edit-atomic` (consumers:
  `Tools.Session`'s `replace` and checked `omit`).
- **Reach**: every coherent document `d`, target `t`, change `c`, and policy `policy`.
- **What it does not establish**: it does not establish program admission (`admitProgram`), runtime
  behaviour, or that an exact fill is always accepted.
- **What it unlocks**: R14 (`docs/core/system-map.md`).
-/

set_option autoImplicit false

namespace Effect4.Program

/-- **The edit a change makes exists where the address holds a program.**

- **Concept**: `initial-algebras-folds` (`docs/core/semantics.md`); property:
  `source-session-coherent`.
- **Question**: step of `Doc.commit_sound` (consumer: `Doc.commit_sound`).
- **Reach**: every `d : Doc`, `t : EditTarget`, `c : Change`, and `e : Edit` with
  `(Node.eff d.session.sketch.program).at_ t.path = some (.eff t.expected)` and
  `d.editOf t c = some e`.
- **Exclusions**: does not establish typing or session coherence by itself.
- **Unlocks**: R14 (`docs/core/system-map.md`). -/
theorem edit_exists {d : Doc} {t : EditTarget} {c : Change} {e : Edit}
    (hat : (Node.eff d.session.sketch.program).at_ t.path = some (.eff t.expected))
    (he : d.editOf t c = some e) : ∃ s', d.session.sketch.edit d.session.app e = some s' := by
  cases c with
  | fill q =>
    cases he
    obtain ⟨p', hrep⟩ := Node.replaceAt_eff q hat
    exact ⟨_, Sketch.fillAt_of_replaceAt hrep⟩
  | omitHole name =>
    unfold Doc.editOf at he
    obtain ⟨f, -, rfl⟩ := Option.map_eq_some_iff.mp he
    obtain ⟨p', hrep⟩ := Node.replaceAt_eff (Sketch.hole d.session.app d.session.sketch.holes.length) hat
    exact ⟨_, Sketch.fillAt_of_replaceAt (s := { d.session.sketch with
      holes := d.session.sketch.holes ++ [Row.hole name f.ty.answer f.ty.error f.ty.requires.elems] })
      hrep⟩

/-- **An accepted edit is the checked edit.**

- **Concept**: `initial-algebras-folds` (`docs/core/semantics.md`); property:
  `source-session-coherent`.
- **Question**: serves `checked-edit-atomic` (consumers: `Tools.Session`'s `replace` and checked
  `omit`).
- **Reach**: every `d d' : Doc`, `t : EditTarget`, `c : Change`, and `policy : Policy` with
  `d.session.Coherent` and `d.commit t c policy = .ok d'`.
- **Exclusions**: does not establish `admitProgram`, runtime behaviour, or completeness of
  acceptance.
- **Unlocks**: R14 (`docs/core/system-map.md`). -/
theorem Doc.commit_sound {d d' : Doc} {t : EditTarget} {c : Change} {policy : Policy}
    (hc : d.session.Coherent) (h : d.commit t c policy = .ok d') :
    t.doc = d.id ∧ t.revision = d.revision ∧ d'.id = d.id ∧ d'.revision = d.revision + 1 ∧
      d'.session.Coherent ∧ d'.session.app = d.session.app ∧
      (∃ e, d.editOf t c = some e ∧ d.session.sketch.edit d.session.app e = some d'.session.sketch) ∧
      ∃ T', d'.session.sketch.sourceCheck d.session.app = .ok T' ∧
        (policy = .keepExactType →
          d.session.sketch.sourceCheck d.session.app = .ok T' ∧
          Table.typedAt d'.session.table t.path = Table.typedAt d.session.table t.path) := by
  unfold Doc.commit at h
  split at h
  · cases h
  · rename_i hdoc'
    have hdoc : t.doc = d.id := Decidable.of_not_not hdoc'
    split at h
    · cases h
    · rename_i hrev'
      have hrev : t.revision = d.revision := Decidable.of_not_not hrev'
      split at h
      · cases h
      · rename_i hat'
        have hat : (Node.eff d.session.sketch.program).at_ t.path = some (.eff t.expected) :=
          Decidable.of_not_not hat'
        split at h
        · cases h
        · rename_i e he
          dsimp only at h
          obtain ⟨s', hedit⟩ := edit_exists hat he
          have hcoh : (d.after e).Coherent := SourceSession.feed_coherent hc _
          have hkeep := SourceSession.feed_keeps d.session e
          have hsk : (d.after e).sketch = s' := hkeep.2 _ hedit
          have happ : (d.after e).app = d.session.app := hkeep.1
          have hview := SourceSession.view_type hcoh
          rw [happ] at hview
          have hed : d.session.sketch.edit d.session.app e = some (d.after e).sketch := by
            rw [hsk]
            exact hedit
          split at h
          · cases h
          · rename_i T' hT
            have hsrc : (d.after e).sketch.sourceCheck d.session.app = .ok T' :=
              Effect4.Laws.Auto.toOption_eq_some.mp (hview ▸ hT)
            split at h
            · cases h
              exact ⟨hdoc, hrev, rfl, rfl, hcoh, happ, ⟨e, he, hed⟩, T', hsrc, fun hp => nomatch hp⟩
            · split at h
              · cases h
              · rename_i hold'
                have hold : d.session.view.type = some T' := Decidable.of_not_not hold'
                split at h
                · cases h
                · rename_i hloc'
                  have hloc : Table.typedAt (d.after e).table t.path =
                      Table.typedAt d.session.table t.path := Decidable.of_not_not hloc'
                  cases h
                  have hold2 := SourceSession.view_type hc
                  rw [hold] at hold2
                  exact ⟨hdoc, hrev, rfl, rfl, hcoh, happ, ⟨e, he, hed⟩, T', hsrc,
                    fun _ => ⟨Effect4.Laws.Auto.toOption_eq_some.mp hold2.symm, hloc⟩⟩

end Effect4.Program
