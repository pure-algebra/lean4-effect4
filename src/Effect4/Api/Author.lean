import Effect4.Api.Built
import Effect4.Program.Authoring.Services

/-!
# Api.Author — one call from what an author wrote to what a run needs

A program is written as a `Module` (`Program/Authoring.lean`): the host rows it declares, the
services it declares, the shared layers declared once by name, and the main program. `build`
takes that one value to the one value a run needs (`Api.Built`): the table assembled from the
declarations in order, the first-order tree, the admission certificate, and the spelling each
row was declared under.

Everything the build can refuse already has a located refusal, and `BuildRefusal` is their
sum: the scope reader's (a name with no binder, a row or a layer nobody declared, a name only
the surface may write), the checker's (DI-86, the deepest node whose own rule refuses), and
admission's (the table's names, the runner's registrations, the reserved integer type). The
type refusal is the located one: `admitProgram` answers `illTyped` without a site, so a build
that fails to type asks `Api.explain` where.

The table is the module's own. That is the point of declaring rows: an external position is
a position in whichever table is supplied beside the program (DI-22), and a module that
declares its rows is checked against the table it was written against.
-/

namespace Effect4.Api

open Effect4.Program Effect4.Program.Authoring

/-- Why a module could not be built: the three located refusals that already exist. -/
inductive BuildRefusal
  /-- The scope reader refused, at the path where it did. -/
  | scope (refusal : Effect4.Program.Authoring.Refusal)
  /-- The checker refused, at the deepest node whose own rule refuses (DI-86). -/
  | typing (refusal : Effect4.Program.TypeRefusal)
  /-- Admission refused: a table name, a registration, or the reserved integer type. -/
  | admission (refusal : Effect4.Program.AdmitRefusal)
  /-- A service's declared carrier is not the one the signature types its key at, so the
  declaration and the checker disagree about what `Effect.service(key)` answers. -/
  | serviceCarrier (key : Effect4.ServiceKey) (declared : Ty) (signature : Option Ty)
deriving DecidableEq

namespace Author

/-- The first service whose declared carrier is not the one the native signature types its
key at. Decidable, and the same comparison `ServiceDef.Agrees` makes at a declaration site. -/
def disagreeingService (m : Module NativeOp) (table : RowTable) : Option BuildRefusal :=
  m.services.findSome? fun s =>
    let signature := (nativeSignature table).serviceTy s.key
    if signature == some s.carrier then none
    else some (.serviceCarrier s.key s.carrier signature)

/-- Elaborate, assemble the table in declaration order, type and admit: one call, one value.
The rows are the module's own declarations followed by each service's operations, in order,
and their positions are what `Row.call` resolved against. -/
def build (m : Module NativeOp) : Except BuildRefusal Built :=
  match Authoring.elaborateModule m with
  | .error refusal => .error (.scope refusal)
  | .ok program =>
    let table := m.table
    match disagreeingService m table with
    | some refusal => .error refusal
    | none =>
      match admitProgram program table with
      | .ok admitted =>
        .ok { table := table, program := program, admitted := admitted, rowNames := m.rowNames }
      | .error .illTyped =>
        match Api.explain program table with
        | some refusal => .error (.typing refusal)
        | none => .error (.admission .illTyped)
      | .error why => .error (.admission why)

/-- A program with no declarations of its own: the module whose only field is its main. -/
def program (src : Src NativeOp) : Except BuildRefusal Built := build { main := src }

end Author

namespace Built

/-- The built program as a typed one: the admission certificate extends the typing
certificate, so every reading `Typed` has is this one's, through this projection and not by
a second definition. -/
def typed (b : Built) : Typed b.table := ⟨b.program, b.admitted.toTypedProgram⟩

/-- The certified type of the built program. -/
def ty (b : Built) : EffTy := b.typed.ty

/-- The full keys the built program performs against, in the canonical key order. -/
def requires (b : Built) : List Effect4.ServiceKey := b.typed.requires

/-- Whether the built program needs nothing from its surroundings. -/
def closed (b : Built) : Bool := b.typed.closed

/-- The position a declared spelling was given in the table. -/
def positionOf (b : Built) (spelling : String) : Option Nat :=
  (b.rowNames.find? (fun entry => entry.1 == spelling)).map Prod.snd

/-- The ordinary run of a built program: the certificate is the evidence, so nothing is
re-derived (`Api.runAdmitted`). The run a caller holds is `Run.runPure` (`src/Effect4/Run.lean`);
this is its reading. -/
def run (b : Built) (budget : Budget := {}) : Inspection :=
  Api.runAdmitted b.admitted budget.fuel [] budget.compileFuel

/-- `Effect.runSyncExit` on a built program. -/
def runSync (b : Built) (budget : Budget := {}) : ExitV := b.typed.runSync budget

/-- The printed syntax of the built program, against its own table. -/
def print (b : Built) : Except PrintRefusal TypeScript.Expr := b.typed.print

/-- The canonical bytes of the built program. -/
def bytes (b : Built) : Store.Bytes := b.typed.bytes

end Built

end Effect4.Api
