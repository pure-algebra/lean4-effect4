import Effect4.Api
import Effect4.Api.Author
import Effect4.Program.Authoring.Module

/-!
# AuthoringModule — finite controls for grouped authoring declarations

The controls build and run modules through the public authoring interface.
They exercise parameter order, declarations, instance names, and source hygiene.
No control states a semantic theorem.
-/

set_option autoImplicit false

namespace Test.Program.AuthoringModule

open Effect4 Effect4.Program Effect4.Program.Authoring

/-- An instance of identity operations at a declared type. -/
eff_module Echo (A : Ty) where
  /-- Return the supplied value through one named invocation. -/
  echo (value : A) : A := succeed value;
  ping : .nat := succeed (nat 7);
  third (first : A) (second : A) (last : A) : A :=
    andThen (succeed first) (andThen (succeed second) (succeed last))

def numbers : Echo := Echo.make "numbers" .nat

#guard numbers.defs.map (·.name) = ["e4$numbers$echo", "e4$numbers$ping", "e4$numbers$third"]
#guard numbers.defs.map (·.params) =
  [[("value", .nat)], [], [("first", .nat), ("second", .nat), ("last", .nat)]]
#guard numbers.defs.map (·.answer) = [.nat, .nat, .nat]
#guard numbers.defs.all fun d => d.error == .never && d.requires.isEmpty
#guard (Echo.definition.echo "legacyEcho" .string).src.name = "legacyEcho"
#guard (Echo.definition.echo "legacyEcho" .string).src.params = [("value", .string)]

/-- Build and observe one finite run through the public application interface. -/
def runModule (m : Module NativeOp) :=
  (Api.Author.build m).toOption.bind fun built => (Api.run built.program 100).exit

#guard runModule (numbers.module (numbers.echo (nat 9))) = some (.success (.nat 9))
#guard runModule (numbers.module numbers.ping) = some (.success (.nat 7))
#guard runModule (numbers.module (numbers.third (nat 1) (nat 2) (nat 3))) =
  some (.success (.nat 3))
#guard (Api.Author.build (numbers.module (numbers.echo (str "wrong")))).toOption.isNone
#guard runModule ((Echo.make "strings" .string).module
  ((Echo.make "strings" .string).echo (str "ok"))) = some (.success (.str "ok"))

/-- Multiple compile-time parameters remain ordinary Lean arguments.
eff_module Labelled (A : Ty) (label : String) where
  identity (value : A) : A := succeed value;
  text : .string := succeed (str label)

#guard runModule ((Labelled.make "labelled" .nat "hello").module
  (Labelled.make "labelled" .nat "hello").text) = some (.success (.str "hello"))

-- Printable identifiers also work for an instance name containing punctuation and Unicode.
def unusual : Echo := Echo.make "numbers.with space_λ" .nat

#guard ((Api.Author.build (unusual.module (unusual.echo (nat 3)))).toOption.bind
  fun built => Api.printModule "main" built.program).isSome
#guard runModule (unusual.module (unusual.echo (nat 3))) = some (.success (.nat 3))

-- A caller's written variable keeps its reading through the invocation. -/
def caller : Src NativeOp := eff do
  let value ← succeed (nat 19)
  let operation ← succeed (nat 23)
  numbers.echo (app "add" [value, operation])

#guard runModule (numbers.module caller) = some (.success (.nat 42))
#guard ((numbers.install { main := numbers.ping, defs :=
  [(Echo.definition.ping "otherPing" .nat).src] }).defs.map (·.name)) =
  ["e4$numbers$echo", "e4$numbers$ping", "e4$numbers$third", "otherPing"]

/-- The native number service used by the requirements controls. -/
def numberKey : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩

eff_module Services where
  get : .nat requires [numberKey] := service numberKey

#guard (Services.make "services").defs.map (·.requires) = [[numberKey]]
#guard runModule ((Services.make "services").module
  (provideService numberKey (nat 17) (Services.make "services").get)) =
  some (.success (.nat 17))

eff_module MissingService where
  get : .nat := service numberKey

#guard (Api.Author.build ((MissingService.make "missing").module
  (provideService numberKey (nat 17) (MissingService.make "missing").get))).toOption.isNone

eff_module MissingError where
  raise (text : .string) : .never := fail text

#guard (Api.Author.build ((MissingError.make "missing").module
  ((MissingError.make "missing").raise (str "bad")))).toOption.isNone

-- A declaration with the wrong result remains a checker refusal.
eff_module WrongAnswer where
  value : .bool := succeed (nat 1)

#guard (Api.Author.build ((WrongAnswer.make "wrong").module
  (WrongAnswer.make "wrong").value)).toOption.isNone

-- Two installed instances retain separate definitions.
def twoInstances : Module NativeOp :=
  let strings := Echo.make "strings" .string
  numbers.install (strings.module (strings.echo (str "separate")))

#guard runModule twoInstances = some (.success (.str "separate"))
#guard twoInstances.defs.length = 6
#guard (Api.Author.build (numbers.install (numbers.module numbers.ping))).toOption.isNone

-- Static explicit calls can refer to a later entry.
eff_module Forward where
  first : .nat := Def.invoke (Def.qualifiedName "forward" "last") [];
  last : .nat := succeed (nat 31)

#guard runModule ((Forward.make "forward").module (Forward.make "forward").first) =
  some (.success (.nat 31))

-- The call record builds before the bodies, including runtime recursion.
eff_module Counting using self where
  forward : .nat := self.count (nat 4);
  count (n : .nat) : .nat :=
    ifElse (app "eq" [n, nat 0]) (succeed n)
      (self.count (app "sub" [n, nat 1]))

#guard runModule ((Counting.make "counting").module (Counting.make "counting").forward) =
  some (.success (.nat 0))
#guard runModule ((Counting.make "different").module
    ((Counting.make "different").count (nat 3))) = some (.success (.nat 0))

-- The error column appears once and reaches the declaration.
eff_module Failure where
  raise (text : .string) : .never error .string requires [] := fail text

#guard (Failure.make "failure").defs.map (·.error) = [.string]
#guard runModule ((Failure.make "failure").module ((Failure.make "failure").raise (str "bad"))) =
  some (.failure (.fail (.text "bad")))

/-- error: duplicate operation name -/
#guard_msgs in
eff_module Duplicate where
  same : .nat := succeed (nat 1);
  same : .nat := succeed (nat 2)

/-- error: duplicate parameter name -/
#guard_msgs in
eff_module DuplicateParameter where
  op (value : .nat) (value : .nat) : .nat := succeed value

/-- error: duplicate parameter name -/
#guard_msgs in
eff_module DuplicateGroup (A : Ty) (A : Ty) where
  op : A := succeed unit

/-- error: runtime parameter collides with a group parameter -/
#guard_msgs in
eff_module Collision (A : Ty) where
  op (A : .nat) : .nat := succeed A

/-- error: operation name is reserved by the generated record -/
#guard_msgs in
eff_module Reserved where
  defs : .nat := succeed (nat 1)

/-- error: operation name is reserved by the generated record -/
#guard_msgs in
eff_module ReservedDefinition where
  definition : .nat := succeed (nat 1)

/-- error: parameter name is reserved by the generated constructor -/
#guard_msgs in
eff_module ReservedGroup (instanceName : Ty) where
  op : .nat := succeed (nat 1)

/-- error: call record name collides with a parameter -/
#guard_msgs in
eff_module SelfCollision (self : Ty) using self where
  op : .nat := succeed (nat 1)

/-- error: call record name collides with a parameter -/
#guard_msgs in
eff_module SelfArgument using self where
  op (self : .nat) : .nat := succeed self

/-- error: a parameter needs one simple name -/
#guard_msgs in
eff_module QualifiedParameter where
  op (nested.value : .nat) : .nat := succeed unit

/--
error: Application type mismatch: The argument
  y
has type
  Env
but is expected to have type
  TermSrc
in the application
  succeed y
-/
#guard_msgs in
eff_module HigherOrder where
  op (x : .nat) : .nat := fun y => succeed y

-- Qualified declaration names follow ordinary Lean namespace rules.
eff_module Nested.Identity where
  value : .nat := succeed (nat 8)

#guard runModule ((Nested.Identity.make "nested").module (Nested.Identity.make "nested").value) =
  some (.success (.nat 8))

end Test.Program.AuthoringModule
