import Effect4.Laws.Machine.Keeps
import ProofGraph.AxiomAudit

/-!
# Probe: the fiber table as a finite map, related up to a world of fiber ids

A finite probe for `../README.md` §2.3 ("two schedules relate tables as finite maps"). Two
schedules append fibers in different orders and mint different ids. So DET-3's relation reads the
fiber table by lookup: a world relates the ids of two machines, and related ids name related
fibers. The relation on fibers is a parameter `R`, indexed by the world, and Kripke-monotone.

It shows, on the real `RunMachine.fiber?` and `RunMachine.update`:

1. `TableRel` mentions no list order: lookups only.
2. **Lookup** respects the relation.
3. **Update** of related fibers at related ids keeps it. The proof needs the world to be a
   partial bijection: equality of ids must give the same answer on both sides.
4. **Appending** a fresh fiber on each side keeps it, at the world extended by the new pair.
5. A **pointwise map** over every fiber, such as `dropToken`'s observer filter, keeps it when the
   map respects `R`.

These are the per-edit facts of the fibers field for DET-3's `names-equivariant`, generic in the
relation on fibers. It is not a library module. It compiles with `lake env lean` against the built
`Effect4.Laws.Machine.Keeps`, and its last command audits its own declarations.
-/

set_option autoImplicit false

namespace Effect4.Machine.TablesProbe

open Effect4 Effect4.Machine

universe u v w

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
  {κ φ η : Type (max u v)}

/-! ## Worlds of fiber ids -/

/-- A world relates the fiber ids of a left machine to those of a right machine. -/
abbrev IdWorld := FiberId → FiberId → Prop

/-- A partial bijection of ids. -/
structure PBij (w : IdWorld) : Prop where
  right : ∀ a b b', w a b → w a b' → b = b'
  left : ∀ a a' b, w a b → w a' b → a = a'

def IdWorld.le (w w' : IdWorld) : Prop := ∀ a b, w a b → w' a b

def IdWorld.extend (w : IdWorld) (a b : FiberId) : IdWorld := fun x y => w x y ∨ (x = a ∧ y = b)

theorem IdWorld.le_extend (w : IdWorld) (a b : FiberId) : w.le (w.extend a b) :=
  fun _ _ h => Or.inl h

/-- Two optional fibers agree: both absent, or both present and related. -/
def OptRel {A B : Type w} (r : A → B → Prop) : Option A → Option B → Prop
  | none, none => True
  | some a, some b => r a b
  | _, _ => False

/-! ## The table relation -/

section
variable (R : IdWorld → RunFiber ν σ β ε δ ι α χ κ φ → RunFiber ν σ β ε δ ι α χ κ φ → Prop)

/-- **Two fiber tables agree up to a world.** Related ids name related fibers or nothing, and every
present fiber's id has a partner. Only lookups occur: the lists' orders are free. -/
structure TableRel (w : IdWorld) (m₁ m₂ : RunMachine ν σ β ε δ ι α χ St κ φ η) : Prop where
  lookup : ∀ a b, w a b → OptRel (R w) (m₁.fiber? a) (m₂.fiber? b)
  left : ∀ a f, m₁.fiber? a = some f → ∃ b, w a b
  right : ∀ b g, m₂.fiber? b = some g → ∃ a, w a b

/-- **Lookup** respects the relation. -/
theorem TableRel.fiber? {w : IdWorld} {m₁ m₂ : RunMachine ν σ β ε δ ι α χ St κ φ η}
    (h : TableRel R w m₁ m₂) {a b : FiberId} (related : w a b) :
    OptRel (R w) (m₁.fiber? a) (m₂.fiber? b) :=
  h.lookup a b related

/-- A fiber found by its id carries that id. -/
theorem id_of_fiber? {m : RunMachine ν σ β ε δ ι α χ St κ φ η} {a : FiberId}
    {f : RunFiber ν σ β ε δ ι α χ κ φ} (found : m.fiber? a = some f) : f.id = a := by
  unfold RunMachine.fiber? at found
  have holds : decide (f.id = a) = true := List.find?_some (p := fun g : RunFiber ν σ β ε δ ι α χ κ φ => decide (g.id = a)) found
  exact of_decide_eq_true holds

/-- A fiber found by its id is a member. -/
theorem mem_of_fiber? {m : RunMachine ν σ β ε δ ι α χ St κ φ η} {a : FiberId}
    {f : RunFiber ν σ β ε δ ι α χ κ φ} (found : m.fiber? a = some f) : f ∈ m.fibers := by
  unfold RunMachine.fiber? at found
  exact List.mem_of_find?_eq_some found

/-- **Update** of related fibers at related ids keeps the relation, when both ids are present. -/
theorem TableRel.update {w : IdWorld} (hw : PBij w) {m₁ m₂ : RunMachine ν σ β ε δ ι α χ St κ φ η}
    (h : TableRel R w m₁ m₂) {f₁ f₂ : RunFiber ν σ β ε δ ι α χ κ φ} (ids : w f₁.id f₂.id)
    (fibers : R w f₁ f₂) {g₁ g₂ : RunFiber ν σ β ε δ ι α χ κ φ}
    (present₁ : m₁.fiber? f₁.id = some g₁) (present₂ : m₂.fiber? f₂.id = some g₂) :
    TableRel R w (m₁.update f₁) (m₂.update f₂) := by
  have self₁ := RunMachine.fiber?_update_self f₁ m₁
    ⟨g₁, mem_of_fiber? present₁, id_of_fiber? present₁⟩
  have self₂ := RunMachine.fiber?_update_self f₂ m₂
    ⟨g₂, mem_of_fiber? present₂, id_of_fiber? present₂⟩
  refine ⟨fun a b related => ?_, fun a f found => ?_, fun b g found => ?_⟩
  · rcases decEq a f₁.id with differ | same
    · have differ₂ : b ≠ f₂.id := fun same₂ =>
        differ (hw.left a f₁.id b related (same₂ ▸ ids))
      rw [RunMachine.fiber?_update_other f₁ m₁ a differ,
        RunMachine.fiber?_update_other f₂ m₂ b differ₂]
      exact h.lookup a b related
    · subst same
      have same₂ : b = f₂.id := hw.right _ _ _ related ids
      subst same₂
      rw [self₁, self₂]
      exact fibers
  · rcases decEq a f₁.id with differ | same
    · rw [RunMachine.fiber?_update_other f₁ m₁ a differ] at found
      exact h.left a f found
    · exact ⟨f₂.id, same ▸ ids⟩
  · rcases decEq b f₂.id with differ | same
    · rw [RunMachine.fiber?_update_other f₂ m₂ b differ] at found
      exact h.right b g found
    · exact ⟨f₁.id, same ▸ ids⟩

/-! ## Appending a fresh fiber -/

/-- Lookup in a table with one fiber appended. -/
theorem fiber?_append (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (f : RunFiber ν σ β ε δ ι α χ κ φ)
    (a : FiberId) :
    ({ m with fibers := m.fibers ++ [f] } : RunMachine ν σ β ε δ ι α χ St κ φ η).fiber? a =
      (m.fiber? a).or (if f.id = a then some f else none) := by
  unfold RunMachine.fiber?
  rw [List.find?_append]
  rcases decEq f.id a with differ | same
  · rw [if_neg differ]
    simp only [List.find?_cons, List.find?_nil, differ, decide_false]
  · rw [if_pos same]
    simp only [List.find?_cons, same, decide_true]

/-- **Appending** a fresh fiber on each side keeps the relation at the extended world, when the
relation on fibers is monotone in the world. -/
theorem TableRel.append {w : IdWorld} {m₁ m₂ : RunMachine ν σ β ε δ ι α χ St κ φ η}
    (mono : ∀ w w', w.le w' → ∀ f g, R w f g → R w' f g)
    (h : TableRel R w m₁ m₂) {f₁ f₂ : RunFiber ν σ β ε δ ι α χ κ φ}
    (fresh₁ : m₁.fiber? f₁.id = none) (fresh₂ : m₂.fiber? f₂.id = none)
    (unrelated₁ : ∀ b, ¬ w f₁.id b) (unrelated₂ : ∀ a, ¬ w a f₂.id)
    (fibers : R (w.extend f₁.id f₂.id) f₁ f₂) :
    TableRel R (w.extend f₁.id f₂.id) { m₁ with fibers := m₁.fibers ++ [f₁] }
      { m₂ with fibers := m₂.fibers ++ [f₂] } := by
  have grows := IdWorld.le_extend w f₁.id f₂.id
  refine ⟨fun a b related => ?_, fun a f found => ?_, fun b g found => ?_⟩
  · rw [fiber?_append, fiber?_append]
    rcases related with old | ⟨rfl, rfl⟩
    · have differ₁ : f₁.id ≠ a := fun same => unrelated₁ b (same ▸ old)
      have differ₂ : f₂.id ≠ b := fun same => unrelated₂ a (same ▸ old)
      have before := h.lookup a b old
      rw [if_neg differ₁, if_neg differ₂]
      revert before
      cases m₁.fiber? a <;> cases m₂.fiber? b
      · exact fun _ => trivial
      · exact fun no => absurd no id
      · exact fun no => absurd no id
      · exact fun before => mono _ _ grows _ _ before
    · rw [fresh₁, fresh₂, if_pos rfl, if_pos rfl]
      exact fibers
  · rw [fiber?_append] at found
    cases old : m₁.fiber? a with
    | some f' =>
      obtain ⟨b, related⟩ := h.left a f' old
      exact ⟨b, Or.inl related⟩
    | none =>
      rw [old] at found
      rcases decEq f₁.id a with differ | same
      · rw [if_neg differ] at found
        cases found
      · exact ⟨f₂.id, Or.inr ⟨same.symm, rfl⟩⟩
  · rw [fiber?_append] at found
    cases old : m₂.fiber? b with
    | some g' =>
      obtain ⟨a, related⟩ := h.right b g' old
      exact ⟨a, Or.inl related⟩
    | none =>
      rw [old] at found
      rcases decEq f₂.id b with differ | same
      · rw [if_neg differ] at found
        cases found
      · exact ⟨f₁.id, Or.inr ⟨rfl, same.symm⟩⟩

/-! ## A pointwise map over every fiber -/

/-- Lookup after a map that keeps every fiber's id. -/
theorem fiber?_map (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (g : RunFiber ν σ β ε δ ι α χ κ φ → RunFiber ν σ β ε δ ι α χ κ φ) (keeps : ∀ f, (g f).id = f.id)
    (a : FiberId) :
    ({ m with fibers := m.fibers.map g } : RunMachine ν σ β ε δ ι α χ St κ φ η).fiber? a =
      (m.fiber? a).map g := by
  unfold RunMachine.fiber?
  rw [List.find?_map]
  congr 2
  funext f
  simp only [Function.comp_apply, keeps]

/-- **A pointwise map** that keeps ids and respects the relation keeps the table relation:
`dropToken`'s observer filter is one. -/
theorem TableRel.map {w : IdWorld} {m₁ m₂ : RunMachine ν σ β ε δ ι α χ St κ φ η}
    (h : TableRel R w m₁ m₂) (g₁ g₂ : RunFiber ν σ β ε δ ι α χ κ φ → RunFiber ν σ β ε δ ι α χ κ φ)
    (keeps₁ : ∀ f, (g₁ f).id = f.id) (keeps₂ : ∀ f, (g₂ f).id = f.id)
    (respects : ∀ f f', R w f f' → R w (g₁ f) (g₂ f')) :
    TableRel R w { m₁ with fibers := m₁.fibers.map g₁ } { m₂ with fibers := m₂.fibers.map g₂ } := by
  refine ⟨fun a b related => ?_, fun a f found => ?_, fun b f found => ?_⟩
  · rw [fiber?_map m₁ g₁ keeps₁, fiber?_map m₂ g₂ keeps₂]
    have before := h.lookup a b related
    revert before
    cases m₁.fiber? a <;> cases m₂.fiber? b
    · exact fun _ => trivial
    · exact fun no => absurd no id
    · exact fun no => absurd no id
    · exact fun before => respects _ _ before
  · rw [fiber?_map m₁ g₁ keeps₁] at found
    cases old : m₁.fiber? a with
    | none => rw [old] at found; cases found
    | some f' => exact h.left a f' old
  · rw [fiber?_map m₂ g₂ keeps₂] at found
    cases old : m₂.fiber? b with
    | none => rw [old] at found; cases found
    | some f' => exact h.right b f' old

end

end Effect4.Machine.TablesProbe

/-! ## The audit: every declaration of this probe, by the gate's walk -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.map₂.toList.filterMap fun (n, _) =>
    if (`Effect4.Machine.TablesProbe).isPrefixOf n && !n.isInternal then some n else none
  let (results, _) := ProofGraph.reachedAxiomsMany env names.toArray {} (ProofGraph.isGoal env)
  let mut outside : Array Name := #[]
  for (n, r) in names.toArray.zip results do
    match r with
    | none => outside := outside.push n
    | some reached =>
      if reached.any (fun a => !ProofGraph.trustedAxioms.contains a) then outside := outside.push n
  unless outside.isEmpty do
    throwError m!"probe audit: outside [propext, Quot.sound]: {outside}"
  logInfo m!"probe audit: {names.length} declarations within [propext, Quot.sound]"
