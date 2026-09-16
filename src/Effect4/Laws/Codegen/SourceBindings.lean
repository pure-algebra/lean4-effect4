import Effect4.Codegen.SourceBindings
import Effect4.Laws.Codegen.Bindings

/-!
# Original-source binding checks

The scope traversal collects uses from the retained syntax. Executable resolution
is connected to `Bindings.Resolves`, whose constructors select the nearest name
and require its capability. Reflection and certificate laws compose that relation
over every collected use. Scope-entry blockers prevent resolution through a later
local declaration; activation exposes exactly that local binding afterward.

These laws concern the stated conservative lexical profile, not a formalization
of all TypeScript scoping, annotation typing, rendered text or host behavior.
-/

namespace Effect4.Codegen.SourceBindings

open TypeScript Bindings

/-- A collected occurrence resolves in its recorded lexical scope. -/
def Use.Resolved (use : Use) : Prop :=
  ∃ binding, Resolves use.env use.name use.space binding

theorem useResolved_iff (use : Use) : useResolved use = true ↔ use.Resolved := by
  simp only [useResolved, Option.isSome_iff_exists, Use.Resolved, resolve_iff]

theorem Analysis.resolved_iff (analysis : Analysis) :
    analysis.resolved = true ↔ analysis.valid = true ∧
      ∀ use ∈ analysis.uses, use.Resolved := by
  simp only [Analysis.resolved, Bool.and_eq_true, List.all_eq_true, useResolved_iff]

/-- Every syntax child contributes its requirements; a failed child cannot be lost. -/
theorem Analysis.append_resolved (left right : Analysis) :
    (left.append right).resolved = true ↔ left.resolved = true ∧ right.resolved = true := by
  simp only [Analysis.resolved, Analysis.append, List.all_append, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨lv, rv⟩, lu, ru⟩
    exact ⟨⟨lv, lu⟩, rv, ru⟩
  · rintro ⟨⟨lv, lu⟩, rv, ru⟩
    exact ⟨⟨lv, rv⟩, lu, ru⟩

theorem Analysis.require_resolved (analysis : Analysis) (valid : Bool) :
    (analysis.require valid).resolved = true ↔ valid = true ∧ analysis.resolved = true := by
  simp [Analysis.resolved, Analysis.require, Bool.and_assoc]

/-- The original imports are lawful and every retained lexical use resolves.
The validity field is the traversal's explicit shape/spelling restriction. -/
structure WellBound (allowed : List Origin) (module : TypeScript.Module) : Prop where
  imports : LawfulImports allowed module.imports
  shape : (moduleUses module).valid = true
  uses : ∀ use ∈ (moduleUses module).uses, use.Resolved

theorem check_iff (allowed : List Origin) (module : TypeScript.Module) :
    check allowed module = true ↔ WellBound allowed module := by
  simp only [check, Bool.and_eq_true, lawfulImports_iff, Analysis.resolved_iff]
  constructor
  · rintro ⟨imports, shape, uses⟩
    exact ⟨imports, shape, uses⟩
  · intro bound
    exact ⟨bound.imports, bound.shape, bound.uses⟩

theorem Checked.wellBound {allowed : List Origin} {module : TypeScript.Module}
    (checked : Checked allowed module) : WellBound allowed module :=
  (check_iff allowed module).mp checked.checked

theorem Checked.recheck {allowed : List Origin} {module : TypeScript.Module}
    (checked : Checked allowed module) : validate allowed module = some checked := by
  simp [validate, checked.checked]

/-- The computed API admits exactly the stated binding judgment. -/
theorem validate_iff (allowed : List Origin) (module : TypeScript.Module) :
    (∃ checked, validate allowed module = some checked) ↔ WellBound allowed module := by
  constructor
  · rintro ⟨checked, _⟩
    exact checked.wellBound
  · intro bound
    let checked : Checked allowed module := ⟨(check_iff allowed module).mpr bound⟩
    exact ⟨checked, checked.recheck⟩

theorem validate_refusal_iff (allowed : List Origin) (module : TypeScript.Module) :
    validate allowed module = none ↔ ¬ WellBound allowed module := by
  rw [← check_iff]
  unfold validate
  split <;> simp_all

/-- The selected binding is unique, has the requested name and capability, and
belongs to the actual occurrence environment. -/
theorem Checked.use_binding {allowed : List Origin} {module : TypeScript.Module}
    (checked : Checked allowed module) {use : Use}
    (occurs : use ∈ (moduleUses module).uses) :
    ∃ binding, Resolves use.env use.name use.space binding ∧
      binding ∈ use.env ∧ binding.name = use.name ∧ binding.available use.space = true ∧
      ∀ other, Resolves use.env use.name use.space other → other = binding := by
  obtain ⟨binding, found⟩ := checked.wellBound.uses use occurs
  refine ⟨binding, found, found.mem, found.name, found.available, ?_⟩
  intro other otherFound
  exact Option.some.inj ((resolve_iff.mpr otherFound).symm.trans (resolve_iff.mpr found))

/-- Predeclared local names prevent an earlier occurrence from resolving to an
outer import, type or local of the same name, in either namespace. -/
theorem resolve_pending (env : List Binding) (names : List String) (name : String)
    (space : Space) (declared : name ∈ names) :
    resolve (pendingEnv env names) name space = none := by
  induction names with
  | nil => simp at declared
  | cons first rest ih =>
    by_cases same : first = name
    · subst first
      cases space <;> simp [pendingEnv, pendingBinding, resolve, Binding.available]
    · have mem : name ∈ rest := (List.mem_cons.mp declared).resolve_left (Ne.symm same)
      simpa [pendingEnv, pendingBinding, resolve, same] using ih mem

/-- Once reached, a local value declaration resolves to that local, independently
of same-named pending entries and enclosing imports. -/
theorem resolve_active_value (env : List Binding) (name : String) :
    resolve (valueBinding name :: env) name .value = some (valueBinding name) := by
  simp [resolve, valueBinding, Binding.available]

/-- A local value cannot accidentally expose an enclosing type of the same name. -/
theorem resolve_active_type_denied (env : List Binding) (name : String) :
    resolve (valueBinding name :: env) name .type = none := by
  simp [resolve, valueBinding, Binding.available]

/-- Sequential declarations analyze the initializer under the preceding scope,
then expose the declared value in the remainder of this same block. -/
theorem stmtsUses_letInit (env : List Binding) (locals : List String) (name : String)
    (value : Expr) (type : Option TypeRef) (rest : List Stmt) :
    stmtsUses env locals (.letInit name value type :: rest) =
      (stmtUses env locals (.letInit name value type)).append
        (stmtsUses (valueBinding name :: env) (name :: locals) rest) := rfl

/-- A child block is analyzed, but its bindings do not extend the following
statements of the parent. Each child's own locals are masked at its entry. -/
theorem stmtsUses_ifElse (env : List Binding) (locals : List String) (test : Expr)
    (yes no rest : List Stmt) :
    stmtsUses env locals (.ifElse test yes no :: rest) =
      ((exprUses env test).append ((stmtsUses (blockEnv env yes) [] yes).append
        (stmtsUses (blockEnv env no) [] no))).append (stmtsUses env locals rest) := rfl

end Effect4.Codegen.SourceBindings
