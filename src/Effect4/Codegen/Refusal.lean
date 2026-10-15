module

/-!
# Codegen.Refusal — the codegen's refusal alphabets: the printer's, the class table's, the reader's

Three alphabets of plain data, below the printer and the reader. `PrintRefusal` says why the
printer declined a program, `ClassRefusal` why a module cannot declare an error payload's class,
and `ReadRefusal` why the reader declined a tree. They carry spellings, paths and integers only,
so this module imports nothing.

They stand apart from the printer (`Codegen/PrintLeaf.lean`) and the reader (`Codegen/Read.lean`)
because the program interface carries them. The refusals an agent can be shown are content
(decisions row 17), and the generated `Api/RefusalsDerived.lean` reads these three through
`Effect4.Api`. So the interface imports this module and not the codegen: an edit of the printer
or the reader rebuilds the codegen's importers alone, and an edit here rebuilds the interface's.
-/

@[expose] public section

namespace Effect4.Program

/-- Why a module cannot declare an error payload's class (decisions row 120, ruling (b): one
`Data.TaggedError` class per tagged payload type, named by its tag). Each is a refusal of the
module, named with the tag (`PrintRefusal.payloadClass`). -/
inductive ClassRefusal
  /-- The tag is not a TypeScript identifier, so no class can be named by it. -/
  | notIdentifier
  /-- The tag collides with a name the module already binds: an import (`Data`, `Effect`, …),
  an atom or row of its prelude, a reserved head, a builtin, or one of its own declarations. -/
  | collides
  /-- Two payload types under one tag with different fields: one class cannot declare both. -/
  | fieldsDiffer
  /-- A construction of the payload type outside the class form (`Classes.classTag?`): `_tag`
  is not its first field, its first name and the tag's literal, or a name repeats `_tag`. -/
  | construction
  /-- The class's printed declaration does not read back to its fields
  (`ClassTable.checkedDecl`): a field type TypeScript spells like another (`number`), or a field
  naming another class. -/
  | unreadable
deriving DecidableEq, Repr

/-- Why the printer declined a program. `internalAction` names what the template table refuses
(`RowOut.refuse`): the `ActionTerm` constructor whose rc.112 counterpart has no public export
with the same frame shape, a child fork into a scope, and a definition block in an expression's
place. It also names a defect of the table (`table:`) and a site the typed print cannot annotate
(`typed:`). `layerRef` is the declaration block's (the host rows slice): a layer reference whose
target path names no layer, so no `const` can be hoisted for it. `payloadClass` is the module's:
an error payload class it cannot declare. The cases after `callbackRequirement` name the
definition, the service or the method that a block's print refuses (the codegen refactor's CR-8). -/
inductive PrintRefusal
  | internalAction (name : String)
  | layerRef (target : List Nat)
  /-- A row table carries an unsafe spelling (colliding with binders or reserved heads). -/
  | unsafeName (spelling : String)
  /-- A legacy target type has no structural reading in the supported profile. Named by a row's
  spelling, it is also the refusal of an operation's type arguments (`printCall`): one of them
  has no printed form, or the row's call cannot carry them on its head (`withHeadTypes`). -/
  | typeSpelling (text : String)
  /-- An error payload class the module cannot declare, named by its tag (decisions row 120). -/
  | payloadClass (tag : String) (why : ClassRefusal)
  /-- An operation that carries a binder term on a row whose printed form is no call, named by the
  row's spelling: a value row has no argument list to carry the term's function
  (`withFunction`). No native row is such a row: the eight term rows are call rows, and each
  prints its term (the state plan's T5). -/
  | binderTerm (spelling : String)
  /-- An invocation whose programs need a service that the printed parameter's type cannot carry,
  at the invocation's path (decisions row 340; Codex's HO3-REQ-01): the header closes a
  parameter's requirement row as `never`, so tsgo refuses the call. Kept until the target can
  bind a requirement variable on the header. -/
  | callbackRequirement (path : List Nat)
  /-- An invocation with programs of a definition that the signature lacks, or that takes no
  program, by the definition's position in its block (`printInvoke`): the row call invokes a
  definition that takes no program. -/
  | invocation (definition : Nat)
  /-- A definition block that holds no definition: it would print as its main program alone, and
  read back as it (`printModuleWith`). -/
  | emptyBlock
  /-- A definition block whose declarations and bodies differ in number, from the definition at
  this position on (`printDefsWith`). The checker refuses such a block too. -/
  | bodies (position : Nat)
  /-- A name that two definitions of a block with a service share, or that two of the names its
  services declare share, a key and a layer among them (`serviceFault`). -/
  | serviceName (name : String)
  /-- A definition that is a method of a service the block does not declare, by the definition and
  the service it names (`serviceFault`). -/
  | strayMethod (definition service : String)
  /-- A service that does not print, by its name: its initial program is missing, takes a request
  or a program; it has no method, two with one name, or one whose name is no plain key; or its
  name or its layer's is a definition's or carries a layer path (`serviceFaultOf`). -/
  | service (name : String)
  /-- A method of a service that does not print, by the service and the method: its definition is
  missing, or its request is not the service's state and the method's arguments
  (`serviceFaultOf`). -/
  | serviceMethod (service method : String)
deriving DecidableEq, Repr

/-- Why the reader declined a tree. The TypeScript reader's alphabet is generated from this one
(`ReadRefusal` in `ts/eff/templates.gen.ts`, `tools/Drivers/TsGen.lean`; DI-88's first step). -/
inductive ReadRefusal
  /-- A call whose head is a reserved name with no `Eff` reading in that position
  (`Cause.fail` outside a cause, `Effect.whileLoop` outside its suspend). -/
  | unknownHead (name : String)
  /-- An identifier that is no binder, no reserved name, and no value row. -/
  | unknownIdent (name : String)
  /-- A row called with an argument list its row table does not print. -/
  | arity (head : String)
  /-- A lambda, `const` or `step` parameter that is not the binder due at that position. -/
  | binder (expected : String)
  /-- Any other form the printer never emits; `what` names the position. -/
  | shape (what : String)
  /-- A negative integer literal. -/
  | negative (value : Int)
  /-- A statement form the printer never emits. -/
  | unsupportedStmt
  /-- A binder, return or local annotation the raw printer never emits; `site` names the
  position. This is not `arity` (an argument list the row table does not print) and not
  `unsupportedStmt` (a statement form with no reading): a consumer routing on the alphabet
  must be able to tell "annotated, not admitted here" from "wrong shape". -/
  | annotation (site : String)
deriving DecidableEq, Repr

end Effect4.Program
