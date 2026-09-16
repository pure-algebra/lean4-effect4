import TypeScript.Syntax
import TypeScript.Identifier

/-!
# Source import bindings

An import retains its module, imported name, local alias and value/type distinction.
The two capabilities describe syntactic availability only: this module does not
assert that a package exports a symbol or that a value export denotes a type.
The source profile must check the resolved origin and its permitted uses.

Resolution first selects the nearest binding with the requested name, then checks
its space. A local binding with no type capability therefore blocks an outer type
binding instead of accidentally falling through to it. These data describe the
original target envelope; they are not another program representation.
-/

namespace Effect4.Codegen.Bindings

inductive Space where
  | value
  | type
  deriving BEq, DecidableEq, Repr

/-- The identity behind a local spelling. `none` denotes a namespace import. -/
inductive Origin where
  | imported (path : String) (exported : Option String)
  | local
  | builtin
  deriving DecidableEq, Repr

instance : BEq Origin := ⟨fun left right => decide (left = right)⟩

instance : LawfulBEq Origin where
  eq_of_beq := by
    intro left right equal
    exact of_decide_eq_true equal
  rfl := by
    intro origin
    exact decide_eq_true rfl

/-- Availability in the two source namespaces; package meaning is separate. -/
structure Binding where
  name : String
  origin : Origin
  value : Bool
  type : Bool
  deriving BEq, DecidableEq, Repr

def Binding.available (binding : Binding) : Space → Bool
  | .value => binding.value
  | .type => binding.type

/-- Preserve import aliases and origins. Either type-only marker removes value
availability. Even an ordinary named import still needs profile validation before
it may be used as a particular target type. -/
def ofImport : TypeScript.Import → List Binding
  | .all name path typeOnly =>
      [⟨name, .imported path none, !typeOnly, true⟩]
  | .named names path typeOnly =>
      names.map fun name =>
        ⟨name.localName, .imported path (some name.imported),
          !(typeOnly || name.typeOnly), true⟩

def ofImports (imports : List TypeScript.Import) : List Binding :=
  imports.flatMap ofImport

/-- Resolve the nearest *name*, then test its capability. Never search past a
shadowing binding merely because its capability does not fit the requested use. -/
def resolve : List Binding → String → Space → Option Binding
  | [], _, _ => none
  | binding :: rest, name, space =>
      if binding.name = name then
        if binding.available space then some binding else none
      else resolve rest name space

/-- Import admission checks spelling, unique local names, and the explicit list
of permitted origins. It makes no claim about host exports or target typing. -/
def lawfulImports (allowed : List Origin) (imports : List TypeScript.Import) : Bool :=
  let bindings := ofImports imports
  decide (bindings.map (·.name)).Nodup && bindings.all fun binding =>
    TypeScript.targetIdentifier binding.name && decide (binding.origin ∈ allowed)

end Effect4.Codegen.Bindings
