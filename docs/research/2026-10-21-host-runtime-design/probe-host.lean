import Test.Dogfood.Scenario.Todo.CachedProgram
import Compiler.Check
import Compiler.Emit
import Test.Dogfood.Scenario.Todo.Typed
import Effect4.Laws.Api.HostDrive
import Effect4.Run.Tree
import Effect4.Codegen.RowServices
import Effect4.Run.Kit

/-! Probe: the host interface is the object's row table, and a host is a comodel of the row
signature that the table determines. The tree's three spellings of a host are one function of a
reactor; a typed host is a section into reactors; the TypeScript interface is a function of the
rows. Each `#guard` is a finite evaluation on the to-do; the theorem is proved. -/

set_option autoImplicit false
namespace Probe.Host
open Effect4 Effect4.Program Effect4.Machine
open Test.Dogfood.Scenario.Todo (repository Repo)

/-- The to-do's object: its service module built, as `Compiler.check` builds it, with the service
name written. A declaration that calls `Compiler.check` reaches `Classical.choice` through the
name's `String.capitalize`, a toolchain constant, so the probes' declarations avoid it. -/
def todoObject : Option Object :=
  (Test.Dogfood.Scenario.Todo.Cached.built? Test.Dogfood.Scenario.Todo.application).map Object.ofBuilt

-- finite evaluation: it is the object that `check` builds
#guard (Compiler.check Test.Dogfood.Scenario.Todo.application).toOption.map Object.ofBuilt = todoObject

/-! ## 1. The interface is the row table -/

-- by definition: the row signature's operations are a row's position with a request, and its
-- answers are exits; nothing else of the object enters it
example (o : Object) : (Denote.RowSig o.app.rows).Op = ((_ : Fin o.app.rows.length) × Val) := rfl
example (o : Object) (op : (Denote.RowSig o.app.rows).Op) :
    (Denote.RowSig o.app.rows).Answer op = ExitV := rfl

-- finite evaluation: the to-do's interface is its four rows, each a data row the host answers
#guard todoObject.map (fun o => (List.range o.app.rows.length).map (Denote.dataRow o.app.rows)) =
  some [true, true, true, true]
-- finite evaluation: Σ_app holds no service declaration and no named type beside the rows; the
-- rows' one key has the built-in unit carrier, so no service value crosses to the host
#guard todoObject.map (fun o => (o.app.services.length, o.app.types.length)) = some (0, 0)
#guard todoObject.map (fun o => (o.app.rows.flatMap (·.requires)).eraseDups.map o.app.serviceTy) =
  some [some .unit]

/-! ## 2. One host, read three ways -/

/-- **The call tree's host is the laws' host** at every row that the table keeps in its normal
form: `Tree.Host.ofReactor` (the kit's runner) and `reactorHost` (the comodel H9 quantifies over)
answer alike. Placement: concept `host-session-protocol`; the proposed claim `host-one-reading`
(role compatibility); consumer: the planned goal `ofProgram_eq_denoteRowsB`
(`src/Effect4/Laws/Run/Tree.lean`), whose runs need one host on both sides. Reach: any reactor,
any row whose external reading is its raw reading. -/
theorem treeHost_eq_reactorHost (table : RowTable) {σ : Type} (r : Run.Reactor σ) (i : Nat)
    (hi : i < table.length) (v : Val) (st : σ) (hrow : externalRow table i = table[i]?) :
    Run.Tree.Host.ofReactor table r i v st = (Run.reactorHost table r).answer ⟨⟨i, hi⟩, v⟩ st := by
  unfold Run.Tree.Host.ofReactor Run.reactorHost
  dsimp only
  rw [hrow]
  cases table[i]? <;> rfl

-- finite evaluation: the to-do's rows are kept in their normal form, so the theorem's premise
-- holds at each of them
#guard todoObject.map (fun o => (List.range o.app.rows.length).all fun i =>
  decide (externalRow o.app.rows i = o.app.rows[i]?)) = some true

/-! ## 3. A typed host is a section into reactors -/

/-- Small members of each row's request, under the application's named types (`Kit.samples`),
and the requests that hit a stored to-do. -/
def probes (o : Object) : List (Row × Val) :=
  o.app.rows.flatMap fun row =>
    ((Run.Kit.samples o.app.types 3 row.request) ++
      (if row.spelling == "TodoRepo.setDone" then
        [Val.list [.nat 1, .bool true], Val.list [.nat 2, .bool false]]
       else if row.spelling == "TodoRepo.insert" then [Val.str "milk"] else [])).map (row, ·)

def states : List Repo := [(1, []), (2, [(1, "milk", false)]), (3, [(1, "milk", true), (2, "tea", false)])]

/-- A reactor's answer as comparable data: its exit, or the cell of a delayed read, and the next
state. -/
def answerKey : Option (Api.HostSession.Answer × Repo) → Option (Sum Val Nat × Repo)
  | some (.ofExit ex, st) => some (.inl (exitImage.toVal ex), st)
  | some (.ofRefGet cell, st) => some (.inr cell.index, st)
  | none => none

-- finite evaluation: ten requests over the four rows, at three states
#guard todoObject.map (fun o => (probes o).length) = some 10

open Test.Dogfood.Scenario.Todo.Typed in
-- finite evaluation: the typed model, read as a reactor (`Host.reactor`, `Reactor.fallible`), gives
-- the untyped repository's answer and next state at every probe request and state
#guard todoObject.map (fun o => (probes o).all fun (row, v) => states.all fun st =>
  decide (answerKey (model.reactor row v st) = answerKey (repository row v st))) = some true

-- finite evaluation: every answer the repository gives there is one the row's columns admit at
-- every machine (`answerAdmits`), so the guard of `guardRows_envelops` changes nothing there
#guard todoObject.map (fun o => (probes o).all fun (row, v) => states.all fun st =>
  match repository row v st with
  | some (c, _) => Run.answerAdmits o.app.types row c
  | none => true) = some true
#guard todoObject.map (fun o => (probes o).all fun (row, v) => states.all fun st =>
  decide (answerKey ((repository.guardRows o.app.types) row v st) = answerKey (repository row v st))) =
  some true
-- control: an answer outside the row's answer column is one the guard removes
#guard todoObject.map (fun o => match o.app.rows.head? with
  | some row => !Run.answerAdmits o.app.types row (.ofExit (.success (.nat 7)))
  | none => false) = some true

/-! ## 4. The TypeScript interface is a function of the rows -/

-- finite evaluation: the rows print as one service key and its namespace (`rowServiceDecls`),
-- and no row is left for a free host namespace (`hostBindings`)
#guard todoObject.map (fun o => match rowServiceDecls (nativeSignature o.app.rows) o.app.rows with
  | .ok ds => ds.map (·.name)
  | .error _ => []) = some ["TodoRepoKey", "TodoRepo"]
#guard todoObject.map (fun o => match hostBindings (nativeSignature o.app.rows) o.app.rows with
  | .ok (spaces, _) => spaces
  | .error _ => ["refused"]) = some []

-- finite evaluation (the plan's hole C): emission's import table binds a package row's namespace to
-- a prelude file that implements it (`Compiler.adapters`, `Compiler.adapterOf`), so a module with a
-- SQL row imports its host from `./prelude/sql.ts`; the to-do's namespace has no adapter
#guard (Compiler.hostSpaces Packages.sqliteBun, Compiler.adapterOf "Sql", Compiler.adapterOf "TodoRepo") =
  (["Sql"], some "./prelude/sql.ts", none)

end Probe.Host
