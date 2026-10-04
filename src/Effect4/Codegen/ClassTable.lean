import Effect4.Codegen.PrintLeaf
import Effect4.Codegen.SourceBindings
import Effect4.Program.AtomInventory

/-!
# Codegen.ClassTable — the classes a module declares (decisions row 120, ruling (b))

A printed module declares one `Data.TaggedError` class per tagged payload type it names
(`Codegen/Classes.lean`). Its program names a class in two ways: a construction in the class form
(`Classes.classTag?`), and a printed type that mentions a payload record type, which prints as the
class name (`Types.ofTy`): the declaration type's two columns, a record construction's declared
fields and a loop's cursor annotation (`Formation.programAnnotations`).

`moduleClasses` collects them, in first-occurrence order, constructions first, and refuses the
module by name (`PrintRefusal.payloadClass`, with the tag) when the face cannot declare one:

* a construction of a payload type outside the class form (`construction`);
* a tag that is not a TypeScript identifier (`notIdentifier`);
* a tag that collides with a name the module binds (`collides`): the `effect` namespaces it
  imports, `Data` among them; the prelude's atoms; the builtins and the type names the printer
  spells; the rows the program performs; its own export name; and what `exportNameSafe` excludes
  (printed binders, reserved heads, layer reference names, term helpers);
* two payload types under one tag with different fields (`fieldsDiffer`): constructions must
  agree exactly, since the reader restores a construction's declared fields from its class; a
  type must be the same type (`Ty.normalize`);
* a class whose declaration does not read back (`unreadable`, `checkedDecl`).

The class's fields are its constructions' declared fields (`_tag` first, the rest in written
order), or, when no construction names the tag, a mentioned type's normalized fields with `_tag`
moved first. Nothing here is target typing or execution.
-/

set_option autoImplicit false

namespace Effect4.Codegen

/-- The `effect` namespaces a printed module may import: the printer's heads and the native rows
use these, `Exit`, `Option` and `Result` spell printed values, and `Data` holds the payload
classes' `Data.TaggedError` (decisions row 120). The reading boundary admits them as import
origins (`effectOrigins`, `Codegen/Admit.lean`); a payload class may not take one as its name. -/
def effectNamespaces : List String :=
  ["Effect", "Layer", "Ref", "Fiber", "Cause", "Deferred", "Scope", "Context",
    "Exit", "Option", "Result", "Data"]

namespace ClassTable

open Effect4.Program Effect4.Codegen.Classes

/-- A payload type's fields in the class's shape: `_tag` first, then the other fields in order. -/
def classShape (tag : String) (fields : Fields) : Fields :=
  ("_tag", false, .lit tag) :: fields.filter (fun f => f.1 != "_tag")

/-- The tag of a tagged payload record type (`payloadRecordTy`), whatever its spelling. -/
def payloadTag? (fields : Fields) : Option String :=
  if payloadRecordTy fields then Program.Record.tagOf (.record fields) else none

/-- The payload record types a type mentions once normalized, each with its tag and its fields in
the class's shape: every node `Formation.nodes` collects that `payloadRecordTy` admits. `ofTy`
prints each as its class name, so a module that prints the type declares each. -/
def typeClasses (t : Ty) : List (String × Fields) :=
  (Formation.nodes t.normalize).filterMap fun node => match node with
    | .record fields => (payloadTag? fields).map fun tag => (tag, classShape tag fields)
    | _ => none

/-- One construction's class: none for a record that is no payload type; the tag and declared
fields of a construction in the class form; a refusal, named by the tag, otherwise. -/
def siteClass (site : RecordSite) : Except PrintRefusal (Option (String × Fields)) :=
  match payloadTag? site.1 with
  | none => .ok none
  | some tag =>
    if !TypeScript.targetIdentifier tag then .error (.payloadClass tag .notIdentifier)
    else match classTag? site.1 site.2.1 site.2.2 with
      | some _ => .ok (some (tag, site.1))
      | none => .error (.payloadClass tag .construction)

/-- Merge one class entry into a table: a new tag appends, an old one must agree. A
construction's fields must equal the class's (`exact`): the reader restores them from it. A
mentioned type's must be the same type. -/
def mergeClass (exact : Bool) (table : Classes) (entry : String × Fields) :
    Except PrintRefusal Classes :=
  match table.lookup entry.1 with
  | none => .ok (table ++ [entry])
  | some fields =>
    let same := if exact then decide (fields = entry.2)
      else decide (Ty.normalize (.record fields) = Ty.normalize (.record entry.2))
    if same then .ok table else .error (.payloadClass entry.1 .fieldsDiffer)

/-- The rows a program performs, by the generated program fold. -/
def programRows {Op : Type} (sig : Signature Op) (program : Eff Op) : List Program.Row :=
  foldMap_eff [] (· ++ ·) program (f_eff := fun node => match node with
    | .perform op _ => [sig.rowOf op]
    | _ => [])

/-- The names a payload class may not take (`ClassRefusal.collides`): the `effect` namespaces,
the prelude's atoms, the builtins and the type names the printer spells (`Readonly`, `Record`),
the export name, and the qualified root and trailing names of every row the program performs. -/
def takenNames (exportName : String) (rows : List Program.Row) : List String :=
  effectNamespaces ++ NativeAtom.names ++ SourceBindings.builtins.map (·.name) ++
    ["Readonly", "Record", exportName] ++
    rows.flatMap fun row => (SourceBindings.qualifiedRoot row.spelling).getD row.spelling :: row.trailing

/-- Why a class's name cannot be declared, if it cannot: the tag is no identifier, or it
collides with a taken name or with what `exportNameSafe` excludes. -/
def nameFault (taken : List String) (tag : String) : Option ClassRefusal :=
  if !TypeScript.targetIdentifier tag then some .notIdentifier
  else if !exportNameSafe tag || taken.contains tag then some .collides
  else none

/-- One class's declaration, accepted only when it reads back to the class
(`Classes.readClassDecl`): the module's reader restores the class's fields from it. -/
def checkedDecl (entry : String × Fields) : Except PrintRefusal TypeScript.ClassDecl :=
  match classDecl entry.1 entry.2 with
  | some c =>
    if readClassDecl c = some entry then .ok c else .error (.payloadClass entry.1 .unreadable)
  | none => .error (.payloadClass entry.1 .unreadable)

/-- **The module's classes and their declarations** (decisions row 120, ruling (b)): one class per
tagged payload type its program constructs or its printed types mention, in first-occurrence
order, constructions first; or the refusal, named by the tag. -/
def moduleClasses {Op : Type} (sig : Signature Op) (name : String) (ty : EffTy) (program : Eff Op) :
    Except PrintRefusal (Classes × List TypeScript.ClassDecl) := do
  let built ← (programRecords program).mapM siteClass
  let typed := ([ty.answer, ty.error] ++ (Formation.programAnnotations program).map Prod.snd).flatMap
    typeClasses
  let table ← built.reduceOption.foldlM (mergeClass true) []
  let table ← typed.foldlM (mergeClass false) table
  let taken := takenNames name (programRows sig program)
  match table.findSome? fun entry => (nameFault taken entry.1).map fun why => (entry.1, why) with
  | some (tag, why) => .error (.payloadClass tag why)
  | none => do
    let decls ← table.mapM checkedDecl
    .ok (table, decls)

end ClassTable

end Effect4.Codegen
