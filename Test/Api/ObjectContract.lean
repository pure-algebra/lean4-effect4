import Effect4.Laws.Api.Object
import Effect4.Api.RefusalsDerived
import Effect4.Program.Authoring.ApplicationService
import Test.Dogfood.Scenario.Todo.Data
import Compiler.Check

/-! Finite program-object evaluations and refusal controls, decisions row 439.
The library laws own admission and byte exactness. These controls exercise their actual carriers.
No comparison here establishes host execution, migration or hash injectivity. -/

set_option autoImplicit false
namespace Test.Api.ObjectContract
open Effect4 Effect4.Program Effect4.Store Effect4.Api

/-- The to-do's service, built as `Compiler.check` builds it. -/
def todoBuilt : Option Built :=
  match Test.Dogfood.Scenario.Todo.application.serviceModule "TodoApp" with
  | .ok m => (Author.build m).toOption
  | .error _ => none

/-- The to-do's object. -/
def todoObject : Option Object := todoBuilt.map Object.ofBuilt

-- finite evaluation: the to-do's object exists, its tree is well formed, and its names are its
-- signature's, so `load_bytes` applies to it
#guard todoObject.isSome
#guard (todoObject.map fun o => decide (toVal o).WF) = some true
#guard (todoBuilt.map fun b => b.rowNames == b.app.rowNames) = some true

-- finite evaluation: the bytes read back to the same object, and a second write is the same bytes
#guard (todoObject.map fun o => match Object.read o.bytes with
  | .ok o' => o' == o && o'.bytes == o.bytes
  | .error _ => false) = some true

-- finite evaluation: the bytes load to a built program with the same data and the same printed
-- certificate as the original and as the compiler's hand JSON
#guard (todoBuilt.map fun b => match Object.load (Object.ofBuilt b).bytes with
  | .ok c => Object.ofBuilt c == Object.ofBuilt b && c.rowNames == b.rowNames &&
      Compiler.jsonText (Compiler.tree c.certificate) == Compiler.jsonText (Compiler.certificate b)
  | .error _ => false) = some true

-- finite evaluation: the generated print of the certificate is the compiler's hand JSON, byte
-- for byte
#guard (todoBuilt.map fun b =>
  Compiler.jsonText (Compiler.tree b.certificate) == Compiler.jsonText (.obj [
    ("answer", Compiler.tree b.ty.answer), ("error", Compiler.tree b.ty.error),
    ("requires", Compiler.tree b.requires), ("rows", Compiler.tree b.table),
    ("services", Compiler.tree (nativeSignature b.table).keyNames),
    ("declarations", Compiler.tree b.program.defsOf)])) =
  some true

-- finite evaluation: the root of the to-do's table holds its certified type
#guard (todoBuilt.map fun b => match (Object.ofBuilt b).table with
  | ⟨[], _, some (.ok t)⟩ :: _ => t == b.ty
  | _ => false) = some true

-- control: a bare program's node (kind `program`, the shape of `Eff`) is no object: the reader
-- refuses its spec, the layout's name, before it reads the payload
#guard (todoObject.map fun o => Object.read (nodeOf o.program).encode ==
  .error (.content .spec)) = some true

-- control: an extra field with a wrong specification refuses at the specification check;
-- the same extra field under the current specification refuses at the payload reader
#guard (todoObject.map fun o =>
  let v2 : Store.Val := match toVal o with
    | .ctor 0 args => .ctor 0 (args ++ [.nat 2])
    | v => v
  Object.read (Node.encode ⟨0, .program, sha256 [], v2⟩) == .error (.content .spec) &&
    Object.read (Node.encode ⟨0, .program, specOf Object, v2⟩) == .error (.content .payload)) =
  some true

-- finite evaluation: the specification's shape includes the program and type families.
-- A different specification digest refuses; hash injectivity is not assumed.
#guard ["Eff", "Stmt", "LayerTerm", "Ty", "Term"].all fun n =>
  ((Canonical.shape Object).defs.map (·.1)).contains n

-- control: one changed byte of the header is the node reader's refusal, located
#guard (todoObject.map fun o => Object.read (1 :: o.bytes.drop 1) ==
  .error (.node (.badVersion 1))) = some true

-- control: the to-do's program at the empty signature is refused by admission, with the located
-- typing refusal that `Api.explain` gives at the same signature
#guard (todoObject.map fun o =>
  match (Object.mk {} o.program).open, Api.explain o.program {} with
  | .error (.illTyped r), some r' => r == r'
  | _, _ => false) = some true


-- control: truncation and trailing data cannot become an accepted object.
#guard (todoObject.map fun o => (Object.read o.bytes.dropLast).toOption.isNone &&
  (Object.read (o.bytes ++ [0])).toOption.isNone) = some true
#guard (Object.read []).toOption.isNone

-- control: the node has another kind, although its payload is an object.
#guard (todoObject.map fun o => Object.read
  (Node.encode ⟨0, .schema, specOf Object, toVal o⟩) ==
    .error (.content (.kind .program .schema))) = some true

-- finite evaluation: service reading retains the to-do's four methods and their arities.
#guard (todoObject.map fun o => match o.services with
  | .ok ss => ss.map (fun sv => (sv.name, sv.init, sv.methods)) ==
      [("TodoApp", 0, [("add", 1, 1), ("list", 2, 0),
        ("complete", 3, 1), ("remove", 4, 1)])]
  | .error _ => false) = some true

-- control: loading an encoded object still performs program admission.
#guard (todoObject.map fun o =>
  match Object.load (Object.bytes ⟨{}, o.program⟩), Api.explain o.program {} with
  | .error (.admission (.illTyped r)), some r' => r == r'
  | _, _ => false) = some true

-- finite evaluation: all three load refusal branches have the generated exact codec.
#guard ([Object.LoadRefusal.node (.badVersion 1), .content .spec,
  .admission (.illTyped ⟨[1], .unboundVariable [] 3 1⟩)]).all fun r =>
    Canonical.ofVal (Canonical.toVal r) == some r

/-- A source reference to an earlier layer; raw syntax checking refuses the reference. -/
def sharedLayer : Object :=
  let key : ServiceKey := ⟨⟨40⟩, ⟨4⟩⟩
  ⟨{}, .bind
    (.provideLayer (.succeed key (.nat 7)) false (.service key))
    (.provideLayer (.ref [0, 0]) false (.service key))⟩

-- control: object inspection must follow source references, as program admission does.
#guard sharedLayer.open.toOption.isSome
#guard (Checker.check sharedLayer.app.signature [] [] sharedLayer.program).toOption.isNone
#guard sharedLayer.table.head?.bind (·.result) = some (.ok (.pure .nat))

/-- The signature's service declaration is needed by the program; its named type is used by a row. -/
def fullObject : Object :=
  let key : ServiceKey := ⟨⟨Effect4.Machine.Env.firstFreeName⟩, ⟨900⟩⟩
  ⟨{ rows := [Row.hole "next" (.app "Count" [])],
     services := [(key, .nat)], types := [("Count", .nat)] },
    .provideService key (.lit (.nat 42)) (.service key)⟩

-- finite evaluation: all three signature fields survive storage and program admission.
#guard fullObject.open.toOption.isSome
#guard Object.read fullObject.bytes == .ok fullObject
#guard (Object.load fullObject.bytes).toOption.map Object.ofBuilt == some fullObject
#guard ({ fullObject with app := { fullObject.app with services := [] } }).open.toOption.isNone
#guard ({ fullObject with app := { fullObject.app with types := [] } }).open.toOption.isNone

/-- Typing alone succeeds, but the signature declares a reserved service name. -/
def badSignature : Object :=
  ⟨{ services := [(⟨⟨0⟩, ⟨900⟩⟩, .nat)] }, .succeed (.lit .unit)⟩

-- control: loading runs signature admission before accepting a typed program.
#guard (Api.typeOf badSignature.program badSignature.app).isSome
#guard match Object.load badSignature.bytes with
  | .error (.admission (.signature (.service 0 .reservedName))) => true
  | _ => false

end Test.Api.ObjectContract
