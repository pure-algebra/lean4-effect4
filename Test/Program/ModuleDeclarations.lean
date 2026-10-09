import Effect4.Author
import Effect4.Run

/-! Named declarations remain the existing definition sources.
These finite controls read their columns and ordered installation.
They exercise zero and multiple runtime arguments, group parameters and recursive calls.
Placement: helpers of the existing module construction claims, serving R4.
The source adapter consumes these named declarations.
No control establishes coherence of manually forged call fields or whole-run agreement. -/

set_option autoImplicit false
namespace Test.Program.ModuleDeclarations
open Effect4 Effect4.Program Effect4.Program.Authoring

/-- Every operation supplies its declaration and invocation from one Def.of result. -/
eff_module Entries (A : Ty) where
  zero : .nat := succeed (nat 7);
  identity (value : A) : A := succeed value;
  third (first : .nat) (second : .bool) (last : .string) : .string :=
    andThen (succeed first) (andThen (succeed second) (succeed last))

def numbers : Entries := Entries.make "named" .nat

#guard numbers.definitions.zero.name = "e4$named$zero"
#guard numbers.definitions.zero.decl.request = .unit
#guard numbers.definitions.identity.params = [("value", .nat)]
#guard numbers.definitions.identity.decl.request = .nat
#guard numbers.definitions.identity.answer = .nat
#guard numbers.definitions.third.decl.request = .prod .nat (.prod .bool .string)
#guard numbers.definitions.third.answer = .string
#guard numbers.defs.map (·.name) =
  [numbers.definitions.zero.name, numbers.definitions.identity.name, numbers.definitions.third.name]
#guard numbers.defs.map (·.decl) =
  [numbers.definitions.zero.decl, numbers.definitions.identity.decl, numbers.definitions.third.decl]

/-- Observe installed calls through the existing public machine interface. -/
def runModule (m : Module NativeOp) :=
  (Api.Author.build m).toOption.bind fun built => (Api.run built.program 200).exit

#guard runModule (numbers.module numbers.zero) = some (.success (.nat 7))
#guard runModule (numbers.module (numbers.identity (nat 19))) = some (.success (.nat 19))
#guard runModule (numbers.module (numbers.third (nat 1) (bool true) (str "last"))) =
  some (.success (.str "last"))
#guard (Api.Author.build (numbers.module (numbers.identity (str "wrong")))).toOption.isNone
#guard runModule (numbers.module (Def.invoke numbers.definitions.identity.name [nat 23])) =
  some (.success (.nat 23))

/-- Different compile-time parameters change the named declarations as well as their bodies. -/
eff_module Parameters (A : Ty) (label : String) where
  echo (value : A) : A := succeed value;
  label : .string := succeed (str label)

def strings : Parameters := Parameters.make "strings" .string "parameter"
#guard strings.definitions.echo.decl.request = .string
#guard strings.definitions.echo.answer = .string
#guard runModule (strings.module strings.label) = some (.success (.str "parameter"))
#guard ((numbers.install (strings.module strings.label)).defs.map (·.name)) =
  ["e4$named$zero", "e4$named$identity", "e4$named$third", "e4$strings$echo", "e4$strings$label"]

/-- The call record still precedes all bodies, including forward and recursive calls. -/
eff_module Recursive using self where
  start : .nat := self.count (nat 4);
  count (n : .nat) : .nat :=
    ifElse (app "eq" [n, nat 0]) (succeed n) (self.count (app "sub" [n, nat 1]))

def recursive : Recursive := Recursive.make "recursive"
#guard recursive.definitions.start.decl.request = .unit
#guard recursive.definitions.count.decl.request = .nat
#guard recursive.defs.map (·.name) = ["e4$recursive$start", "e4$recursive$count"]
#guard runModule (recursive.module recursive.start) = some (.success (.nat 0))

/-- Declared failures and service requirements stay on their one named source. -/
def numberKey : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩
eff_module Columns where
  raise (message : .string) : .never error .string := fail message;
  get : .nat requires [numberKey] := service numberKey

def columns : Columns := Columns.make "columns"
#guard columns.definitions.raise.error = .string
#guard columns.definitions.get.requires = [numberKey]
#guard columns.defs.map (·.error) = [.string, .never]
#guard columns.defs.map (·.requires) = [[], [numberKey]]

-- A module called Definitions keeps its own type inside generated helper namespaces.
namespace SelfShadowing

eff_module Definitions where
  value : .nat := succeed (nat 17)

def declared : Definitions := Definitions.make "definitions"
#guard declared.definitions.value.name = "e4$definitions$value"
#guard declared.defs.map (·.decl) = [declared.definitions.value.decl]
#guard runModule (declared.module declared.value) = some (.success (.nat 17))

end SelfShadowing

/-- An uppercase operation keeps its existing spelling without shadowing the metadata record. -/
eff_module Uppercase where
  Definitions : .nat := succeed (nat 1)

def uppercase : Uppercase := Uppercase.make "uppercase"
#guard uppercase.definitions.Definitions.answer = .nat
#guard uppercase.defs.map (·.name) = ["e4$uppercase$Definitions"]
#guard runModule (uppercase.module uppercase.Definitions) = some (.success (.nat 1))

-- Exact generated type references survive operation, parameter and namespace spellings.
namespace TypeNameHygiene

eff_module Collision where
  CollisionDeclarations : .nat := succeed (nat 1)

def collision : Collision := Collision.make "collision"
#guard collision.definitions.CollisionDeclarations.answer = .nat
#guard runModule (collision.module collision.CollisionDeclarations) = some (.success (.nat 1))

eff_module ParameterCollision (ParameterCollisionDeclarations : Ty) where
  identity (value : ParameterCollisionDeclarations) : ParameterCollisionDeclarations := succeed value

def parameter : ParameterCollision := ParameterCollision.make "parameter" .nat
#guard parameter.definitions.identity.answer = .nat
#guard runModule (parameter.module (parameter.identity (nat 29))) = some (.success (.nat 29))

eff_module Nested.Collision where
  CollisionDeclarations : .nat := succeed (nat 31)

def nested : Nested.Collision := Nested.Collision.make "nested"
#guard nested.definitions.CollisionDeclarations.answer = .nat
#guard runModule (nested.module nested.CollisionDeclarations) = some (.success (.nat 31))

eff_module _root_.Test.Program.ModuleDeclarations.Rooted where
  RootedDeclarations : .nat := succeed (nat 37)

def rooted : _root_.Test.Program.ModuleDeclarations.Rooted :=
  _root_.Test.Program.ModuleDeclarations.Rooted.make "rooted"
#guard rooted.definitions.RootedDeclarations.answer = .nat
#guard runModule (rooted.module rooted.RootedDeclarations) = some (.success (.nat 37))

end TypeNameHygiene

/-- error: operation name is reserved by the generated record -/
#guard_msgs in
eff_module ReservedField where
  definitions : .nat := succeed (nat 1)

end Test.Program.ModuleDeclarations
