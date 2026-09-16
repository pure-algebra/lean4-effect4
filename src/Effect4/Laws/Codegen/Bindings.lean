import Effect4.Codegen.Bindings

/-!
# Import resolution laws

The declarative resolution relation follows lexical order and cannot skip a
shadowing name. Import admission establishes uniqueness, legal local spellings,
and declared origin membership. Neither conclusion is a host typing judgment.
-/

namespace Effect4.Codegen.Bindings

/-- A name denotes the first binding with that name, in an available space. -/
inductive Resolves : List Binding → String → Space → Binding → Prop where
  | here {binding : Binding} {rest : List Binding} {name : String} {space : Space}
      (same : binding.name = name) (available : binding.available space = true) :
      Resolves (binding :: rest) name space binding
  | there {head binding : Binding} {rest : List Binding} {name : String} {space : Space}
      (different : head.name ≠ name) (resolved : Resolves rest name space binding) :
      Resolves (head :: rest) name space binding

/-- The executable lookup decides the independent nearest-name relation. -/
theorem resolve_iff {env : List Binding} {name : String} {space : Space}
    {binding : Binding} : resolve env name space = some binding ↔
      Resolves env name space binding := by
  induction env with
  | nil =>
      simp [resolve]
      intro resolution
      cases resolution
  | cons head rest ih =>
      by_cases same : head.name = name
      · by_cases available : head.available space = true
        · simp only [resolve, same, ↓reduceIte, available]
          constructor
          · intro equal
            cases equal
            exact .here same available
          · intro resolution
            cases resolution with
            | here => rfl
            | there different => exact (different same).elim
        · have disabled : head.available space = false := Bool.eq_false_iff.mpr available
          constructor
          · intro resolved
            simp [resolve, same, disabled] at resolved
          · intro resolution
            cases resolution with
            | here _ enabled => simp [disabled] at enabled
            | there different => exact (different same).elim
      · simp only [resolve, same, if_false]
        constructor
        · intro result
          exact .there same (ih.mp result)
        · intro resolution
          cases resolution with
          | here equal => exact (same equal).elim
          | there _ found => exact ih.mpr found

theorem Resolves.mem {env : List Binding} {name : String} {space : Space}
    {binding : Binding} (resolution : Resolves env name space binding) :
    binding ∈ env := by
  induction resolution with
  | here => exact List.mem_cons_self
  | there _ _ ih => exact List.mem_cons_of_mem _ ih

theorem Resolves.name {env : List Binding} {name : String} {space : Space}
    {binding : Binding} (resolution : Resolves env name space binding) :
    binding.name = name := by
  induction resolution with
  | here same => exact same
  | there _ _ ih => exact ih

theorem Resolves.available {env : List Binding} {name : String} {space : Space}
    {binding : Binding} (resolution : Resolves env name space binding) :
    binding.available space = true := by
  induction resolution with
  | here _ available => exact available
  | there _ _ ih => exact ih

/-- Successful lookup returns an existing binding with the requested name and
capability, without asserting anything about its host implementation. -/
theorem resolve_properties {env : List Binding} {name : String} {space : Space}
    {binding : Binding} (resolved : resolve env name space = some binding) :
    binding ∈ env ∧ binding.name = name ∧ binding.available space = true :=
  let relation := resolve_iff.mp resolved
  ⟨relation.mem, relation.name, relation.available⟩

/-- A shadowing binding with the wrong capability prevents outer resolution. -/
theorem resolve_shadowed (binding : Binding) (rest : List Binding) (space : Space)
    (disabled : binding.available space = false) :
    resolve (binding :: rest) binding.name space = none := by
  simp [resolve, disabled]

/-- A type-only namespace import cannot expose an outer value with its alias. -/
theorem namespace_typeOnly_denied (name path : String) (outer : List Binding) :
    resolve (ofImport (.all name path true) ++ outer) name .value = none := by
  simp [ofImport, resolve, Binding.available]

/-- The two type-only markers combine by disjunction, rather than one replacing
the other. This equation also records the imported/local-name distinction. -/
theorem named_import_binding (binding : TypeScript.ImportBinding) (path : String)
    (typeOnly : Bool) :
    ofImport (.named [binding] path typeOnly) =
      [⟨binding.localName, .imported path (some binding.imported),
        !(typeOnly || binding.typeOnly), true⟩] := rfl

theorem named_typeOnly_denied (binding : TypeScript.ImportBinding) (path : String)
    (typeOnly : Bool) (outer : List Binding)
    (marked : typeOnly = true ∨ binding.typeOnly = true) :
    resolve (ofImport (.named [binding] path typeOnly) ++ outer)
      binding.localName .value = none := by
  rcases marked with marked | marked <;>
    simp [ofImport, resolve, Binding.available, marked]

/-- Declarative import conditions, stated without calling the checker. -/
structure LawfulImports (allowed : List Origin) (imports : List TypeScript.Import) : Prop where
  unique : ((ofImports imports).map (·.name)).Nodup
  legal : ∀ binding ∈ ofImports imports, TypeScript.targetIdentifier binding.name = true
  permitted : ∀ binding ∈ ofImports imports, binding.origin ∈ allowed

theorem lawfulImports_iff (allowed : List Origin) (imports : List TypeScript.Import) :
    lawfulImports allowed imports = true ↔ LawfulImports allowed imports := by
  simp only [lawfulImports, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  constructor
  · rintro ⟨unique, entries⟩
    exact ⟨unique, fun binding mem => (entries binding mem).1,
      fun binding mem => (entries binding mem).2⟩
  · intro admitted
    exact ⟨admitted.unique, fun binding mem =>
      ⟨admitted.legal binding mem, admitted.permitted binding mem⟩⟩

/-- Resolving through an admitted import list yields a permitted origin. Its
local spelling and requested capability are established by the same lookup. -/
theorem lawfulImports_resolve {allowed : List Origin} {imports : List TypeScript.Import}
    {name : String} {space : Space} {binding : Binding}
    (lawful : lawfulImports allowed imports = true)
    (resolved : resolve (ofImports imports) name space = some binding) :
    binding.name = name ∧ binding.available space = true ∧
      TypeScript.targetIdentifier binding.name = true ∧ binding.origin ∈ allowed := by
  have admitted := (lawfulImports_iff allowed imports).mp lawful
  obtain ⟨mem, same, available⟩ := resolve_properties resolved
  exact ⟨same, available, admitted.legal binding mem, admitted.permitted binding mem⟩

theorem ofImports_append (left right : List TypeScript.Import) :
    ofImports (left ++ right) = ofImports left ++ ofImports right := by
  simp [ofImports]

end Effect4.Codegen.Bindings
