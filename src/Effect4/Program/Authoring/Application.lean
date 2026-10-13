module

public import Effect4.Program.Authoring
public import Effect4.Program.Authoring.Lifts

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
  (`moduleOf_table`).

What stays out: the application as one stored value with canonical bytes, and one module with
several exports (the packet's slice 13). An open program reads the application's rows and nothing
else: an entry that names a shared layer or invokes a definition has its open program refused at
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
  defs : List (DefSrc Op) := []
  entries : List (Application.Entry Op)

namespace Application

variable {Op : Type}

/-- The entry of a name: the first entry declared under it. -/
def entry? (app : Application Op) (name : String) : Option (Application.Entry Op) :=
  app.entries.find? (·.name == name)

/-- The names of the application's programs, in declaration order. -/
def entryNames (app : Application Op) : List String := app.entries.map (·.name)

/-- The rows the application supplies, in table order: its own declarations, then each service's
operations, as `Module.rowDefs` orders them. -/
def rowDefs (app : Application Op) : List RowDef := app.rows ++ app.services.flatMap (·.ops)

/-- The module of one entry at its arguments: the application's declarations, and the applied
body as its main program. `Api.Author.build` builds it as it builds any module. -/
def moduleOf (app : Application Op) (e : Application.Entry Op) (args : List TermSrc) : Module Op :=
  { rows := app.rows, services := app.services, layers := app.layers, defs := app.defs,
    main := e.applied args }

/-- The application's row table. -/
def table (app : Application Op) : RowTable := RowDef.table app.rowDefs

/-- **Every entry is checked against one table**: the module of any entry at any arguments
supplies the application's table. Consumer: the claims of an application, which read one table
for all its programs (`Test/Dogfood/Scenario/Todo.lean`). -/
theorem moduleOf_table (app : Application Op) (e : Application.Entry Op) (args : List TermSrc) :
    (app.moduleOf e args).table = app.table := rfl

/-- The entry's own program, open in its parameters: the body elaborated under the parameters'
names, over the application's rows. It is first-order data, at the root path. -/
def openProgram (app : Application Op) (e : Application.Entry Op) : Except Refusal (Eff Op) := do
  let rows ← rowNamesOf app.rowDefs
  e.body { names := e.params.map (·.1), rows := rows } []

end Application

end Effect4.Program.Authoring
