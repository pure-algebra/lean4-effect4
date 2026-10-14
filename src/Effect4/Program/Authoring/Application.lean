module

public import Effect4.Program.Authoring
public import Effect4.Program.Authoring.Defs
public import Effect4.Program.Authoring.Lifts
public import Effect4.Program.RowProtocol

/-!
# Program.Authoring.Application — an application: named programs over one row table

Slice APP of the claims packet (`docs/research/2026-10-07-packet-application-claims.md`, §3.2;
decisions rows 307 (9) and 336 (9)). An application is the declarations of a `Module` and a list of
entries. It adds no representation of a program: each entry builds through `Module` and
`Api.Author.build`, so `Module`, `Api.Built` and `Run` do not change.

* **An entry has typed parameters.** Its body reads a parameter through `var`, as a program reads
  any answer. Its open program (`openProgram`) is the body elaborated under the parameters' names:
  first-order data that the checker types at the parameters' types.
* **An entry at its arguments is a closed program.** `Entry.applied` binds each argument with
  `bind` over `succeed`, in order, so the body reads the argument as it reads any answer.
* **One table.** Every module of the application supplies the application's row table
  (`moduleOf_table`). The declarations are one `Module` (`declarations`), so the table is
  `Module.table`'s.
* **Declared protocols.** Beside its rows' types, an application may declare a protocol of a row
  (`RowProtocol`), checked at the row's columns (`protocolsFormed`).
* **Definitions that the entries invoke** (decisions row 378 (8)). An entry invokes the
  application's definitions by name, with programs where a definition takes them
  (`Def.invokeWith`). A banked block joins the definitions by reference (`DefSrc.ofBlock`), its
  bytes kept, so the built application can pin the bank's digest (row 378 (4)). An open program is
  checked at the application's table and its definitions (`signature`).

What stays out: the application as one stored value with canonical bytes, and one module with
several exports (the packet's slice 13). An open program reads the application's rows and
definitions and nothing else: an entry that names a shared layer has its open program refused at
that site, a located refusal. Its applied form builds through the module, as any program does.
-/

@[expose] public section

namespace Effect4.Program.Authoring

open Effect4.Program

/-- One named program of an application: its parameters, each a name and a type, and its body.
The body reads a parameter through `var`. -/
structure Application.Entry (Op : Type) where
  name : String
  params : List (String × Ty) := []
  body : Src Op

/-- The entry's body with each parameter bound to an argument, in order: a closed program. The
binder of a parameter is `bind`'s, so the body reads the argument as it reads any answer. A
parameter with no argument stays unbound, and the elaboration refuses its first read. -/
def Application.Entry.applied {Op : Type} (e : Application.Entry Op) (args : List TermSrc) :
    Src Op :=
  (e.params.zip args).foldr (fun pa rest => bind pa.1.1 (succeed pa.2) rest) e.body

/-- An application: the declarations of a `Module`, and several named programs over them. -/
structure Application (Op : Type) where
  name : String
  rows : List RowDef := []
  services : List ServiceDef := []
  layers : List (String × LayerSrc Op) := []
  /-- The application's definitions, which its entries invoke by name. A banked block joins them
  by reference (`DefSrc.ofBlock`), its bytes kept. -/
  defs : List (DefSrc Op) := []
  /-- The declared protocols of the application's rows, by the row's spelling
  (`src/Effect4/Program/RowProtocol.lean`). A row with none has the protocol of its types. -/
  protocols : RowProtocols := []
  entries : List (Application.Entry Op)

namespace Application

variable {Op : Type}

/-- The entry of a name: the first entry declared under it. -/
def entry? (app : Application Op) (name : String) : Option (Application.Entry Op) :=
  app.entries.find? (·.name == name)

/-- The names of the application's programs, in declaration order. -/
def entryNames (app : Application Op) : List String := app.entries.map (·.name)

/-- The application's declarations as a module. An application holds no program of its own, so
the module's main program answers the unit value; `moduleOf` replaces it by an entry. The
module's readers (`Module.rowDefs`, `Module.table`) read the declarations. -/
def declarations (app : Application Op) : Module Op :=
  { rows := app.rows, services := app.services, layers := app.layers, defs := app.defs,
    main := succeed unit }

/-- The module of one entry at its arguments: the application's declarations, and the applied
body as its main program. `Api.Author.build` builds it as it builds any module. -/
def moduleOf (app : Application Op) (e : Application.Entry Op) (args : List TermSrc) : Module Op :=
  { app.declarations with main := e.applied args }

/-- The application's row table: the table of its declarations. -/
def table (app : Application Op) : RowTable := app.declarations.table

/-- **Every entry is checked against one table**: the module of any entry at any arguments
supplies the application's table. Consumer: the claims of an application, which read one table
for all its programs (`Test/Dogfood/Scenario/Todo.lean`). -/
theorem moduleOf_table (app : Application Op) (e : Application.Entry Op) (args : List TermSrc) :
    (app.moduleOf e args).table = app.table := rfl

/-- **The application's protocols are formed**: each names a row of its table, and its terms are
typed at that row's columns (`RowProtocols.formed`). -/
def protocolsFormed (app : Application NativeOp) : Bool := app.protocols.formed app.table

/-- The entry's own program, open in its parameters: the body elaborated under the parameters'
names, over the application's rows and definitions. It is first-order data, at the root path. An
invocation in it names a definition by its position in the application's block, so it is checked
at the block's signature (`signature`). -/
def openProgram (app : Application Op) (e : Application.Entry Op) : Except Refusal (Eff Op) := do
  let rows ← rowNamesOf app.declarations.rowDefs
  let defs ← defNamesOf app.defs
  e.body { names := e.params.map (·.1), rows := rows, defs := defs } []

/-- The signature an entry's open program is checked at: the native signature of the
application's table, extended by its definitions' declarations (`Signature.withDefs`). A program
that invokes no definition is checked the same as at the table's own signature
(`defs_conservative`, `src/Effect4/Laws/Program/Definitions.lean`). -/
def signature (app : Application NativeOp) : Signature NativeOp :=
  (nativeSignature app.table).withDefs (app.defs.map (·.decl))

end Application

end Effect4.Program.Authoring
