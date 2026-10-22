import Effect4.Program.Authoring.Claims
import Test.Dogfood.Scenario.Todo
import Effect4.Laws.Library.Ref.Cache
import Effect4.Store.Domain.ProgramWire

/-!
# Test.Dogfood.Bank — the bank of verified implementations

Decisions row 378 (1), (4) and (5). A bank entry is a verified implementation: its `Eff`
definition block, the digest of the block's canonical bytes (`Canonical.digest`), its interface,
the Lean model it implements, and its claim. The claim is a claim record about an
implementation (row 378 (7); `ClaimRecord`, `src/Effect4/Program/Authoring/Claims.lean`), whose statement is
the agreement theorem about the block. Its status is the plan's (`#plan_status`). Proofs stay in
Lean, and an entry holds the names that the plan checks.

* **Staleness** (row 378 (5)). The agreement theorem reads the block itself (`bodyOf`,
  `src/Effect4/Laws/Library/Ref/Cache.lean`), so an edit of the block breaks its proof. A
  `#guard` checks the recorded digest against the block, so an edit without a new digest fails
  the build.
* **Reference** (row 378 (4)). An application names a module by its model and its interface. The
  built application pins the digest of the block that it imposes. The first entry, the Ref cache
  (row 378 (18)), stands at the types of the to-do's `list` (`Test/Dogfood/Scenario/Todo.lean`):
  the element `Todo`, and the repository's error `SqlError`.
* **The interface** is the block's declarations (`Entry.operations`), the host rows that its
  bodies call, and its type parameters with the types that the entry gives them.

Each line below is a finite evaluation or a control (decisions row 301). A run is a finite
probe on the Lean machine: a client of the banked block, driven by the to-do's reference model
`repository`, from one stored to-do.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Test.Dogfood.Bank

open Effect4 Effect4.Program Effect4.Machine
open Effect4.Machine.Env (Requirement)
open Effect4.Program.Denote (blockOf? paramsAsRows)
open Effect4.Program.Authoring (About Evidence ClaimRecord)
open Test.Dogfood.Scenario.Todo (repository Repo todo)
open Examples.Todo (application noTodo)

export Effect4.Bank (Entry)

/-- **The banked Ref cache** (decisions row 378 (18)), at the types of the to-do's `list`: the
element type `Todo` and the loader's error `SqlError`. Its bodies call no host row: the loader
is a program parameter of `get`. Its agreement theorem is `cache_agrees`. -/
def refCache : Entry where
  name := "Ref.Cache"
  block := Ref.Cache.block Examples.Todo.Todo.ty
    Examples.Todo.SqlError.ty
  digest := "c2bbfd58a550c7efe4e44b2800597bc708c41c7ebfe60dff1dada2a9eabd410c"
  rows := []
  types := [("A", Examples.Todo.Todo.ty),
    ("E", Examples.Todo.SqlError.ty)]
  model := (``Effect4.Ref.Cache.Model.read).getPrefix
  claim := { statement := ``Effect4.Ref.Cache.cache_agrees, about := .implementation,
             evidence := .«theorem» }

/-! ## Staleness and admission -/

/-- A block with the definitions of `b`, a main program, and the bodies changed by `edit`. -/
def withMain (b main : NativeEff) (edit : List NativeEff → List NativeEff := id) : NativeEff :=
  match blockOf? b with
  | some (decls, bodies, _) => .defs decls (Authoring.effsOfList (edit bodies)) main .nil
  | none => main

/-- The path and the reason of the checker's refusal, if it refuses. -/
def refusedAt (r : Except TypeRefusal EffTy) : Option (List Nat × String) :=
  (Checker.refusal r).map fun why => (why.path, why.reason.head)

/-- The checker's signature at the entry's own rows. -/
def interfaceSig : Signature NativeOp := ({ rows := refCache.rows } : SigApp).signature

-- staleness (row 378 (5)): the recorded digest is the digest of the block's canonical bytes
#guard (Store.Canonical.digest refCache.block).hex = refCache.digest
-- control: an edit of the block moves its digest, so the guard above refuses the edit until the
-- digest is recorded again. Here `invalidate` forgets its write
#guard (Store.Canonical.digest (withMain refCache.block (.succeed (.lit .unit))
  (·.set 2 (.succeed (.lit .unit))))).hex ≠ refCache.digest
-- finite evaluation: the checker admits the block at the entry's own rows, none, so its bodies
-- call no host row; the main answers `unit`
#guard Checker.checkModule interfaceSig refCache.block == .ok ⟨.unit, .never, Requirement.empty⟩
-- control: a `make` at `none` without the ascription types the cell at `none`'s own type, and the
-- check refuses the block at that body: a cell is invariant
#guard refusedAt (Checker.checkModule interfaceSig (withMain refCache.block (.succeed (.lit .unit))
  (·.set 0 (.perform .refMake (.app "none" .nil))))) = some ([0, 0], "bodyNotDeclared")

/-! ## Runs under the to-do's reference model -/

/-- A program of the to-do's, elaborated at its rows. Each one used here reads no variable. -/
def todoProgram (p : Authoring.Src NativeOp) : NativeEff :=
  match p { rows := application.declarations.rowNames } [] with
  | .ok e => e
  | .error _ => .succeed (.lit .unit)

/-- The loader that the to-do's `list` passes: the to-do's own `list`, one call of `all`. -/
def loadList : Effs NativeOp := .cons (todoProgram Examples.Todo.list) .nil

/-- A read of the cache at the cell, level 0, with the to-do's loader. -/
def read : NativeEff := .invoke 1 (.var 0) loadList

/-- The to-do's write of a new to-do, "tea". -/
def addTea : NativeEff :=
  todoProgram (Examples.Todo.TodoRepo.insert (Authoring.str "tea"))

/-- A pair of two values, as the atom `pair` builds it. -/
def pairT (a b : Term) : Term := .app "pair" (.cons a (.cons b .nil))

/-- A client of a block: it makes the cell (level 0), then runs `rest`. -/
def client (b rest : NativeEff) (edit : List NativeEff → List NativeEff := id) : NativeEff :=
  withMain b (.bind (.perform (.call 0) (.lit .unit)) rest) edit

/-- The repository's state where a run starts: one to-do stored, "milk". -/
def start : Repo := (2, [(1, "milk", false)])

/-- A program built over the to-do's table, run by the reference model from `start`: the run,
and the model's state after it. -/
def runOf (p : NativeEff) : Option (Run × Repo) :=
  (Api.Author.Internal.finishBuild p application.table).toOption.map fun b =>
      Run.runWith b repository start application.name

/-- A run's exit, and the number of host answers that it applied. -/
def observe (p : NativeEff) : Option (Option ExitV × Nat) :=
  (runOf p).map fun r => (r.1.exit, (Effect4.Run.appliedExits r.1).length)

/-- The stored to-do as a value, and the list that holds it. -/
def milk : Val := Val.list [todo 1 "milk" false]

/-- `get` alone on a fresh cell: the client of `get_session`, its loader the to-do's `all` read as
a row. -/
def freshGet : NativeEff :=
  .bind (Ref.Cache.makeBody Examples.Todo.Todo.ty) (paramsAsRows 1 Ref.Cache.getBody)

-- finite evaluation: the to-do's `all`, the loader's row, is a data row of the to-do's table, the
-- fragment premise of `get_session`
#guard Effect4.Program.Denote.dataRow application.table 1
-- finite evaluation: a run of `get_session`'s client meets its premises (funded, at rest, driven
-- by a host) and observes the model's read of an empty cache: the stored list, held in the cell,
-- after one answer
#guard (runOf freshGet).map (fun r =>
    Effect4.Run.funded r.1 && Effect4.Run.atRest r.1 && Effect4.Run.hostDriven r.1 &&
      r.1.exit == some (Exit.success milk) && r.1.machine.state.refs == [Store.Val.some milk] &&
      (Effect4.Run.appliedExits r.1).length == 1) == some true
-- finite evaluation: two reads ask the repository once; the second answers the held list
#guard observe (client refCache.block
    (.bind read (.bind read (.succeed (pairT (.var 1) (.var 2)))))) ==
  some (some (Exit.success (Val.list [milk, milk])), 1)
-- control: a `get` that holds nothing asks the repository at each read, so the count of answers
-- tells it from the cache
#guard observe (client refCache.block
    (.bind read (.bind read (.succeed (pairT (.var 1) (.var 2)))))
    (·.set 1 (.perform (.param 0) (.lit .unit)))) ==
  some (some (Exit.success (Val.list [milk, milk])), 2)
-- control: a write between two reads leaves the second read stale. It answers the held list
-- without the new to-do, which the repository holds. An application invalidates on a write
#guard (runOf (client refCache.block
    (.bind read (.bind addTea (.bind read (.succeed (pairT (.var 1) (.var 3)))))))).map
    (fun r => (r.1.exit, r.2)) ==
  some (some (Exit.success (Val.list [milk, milk])), (3, [(1, "milk", false), (2, "tea", false)]))
-- finite evaluation: with the invalidation after the write, the second read asks again, and it
-- holds the new to-do
#guard observe (client refCache.block
    (.bind read (.bind addTea (.bind (.perform (.call 2) (.var 0))
      (.bind read (.succeed (pairT (.var 1) (.var 4)))))))) ==
  some (some (Exit.success
    (Val.list [milk, Val.list [todo 1 "milk" false, todo 2 "tea" false]])), 3)
-- control (the reach of `cache_agrees`): a loader that writes the cache's cell, then fails. The
-- next read answers a list that the repository never gave, and asks it nothing. The law reads the
-- loader as a row, and a row writes no cell
#guard observe (client refCache.block
    (.bind (.catchCause (.invoke 1 (.var 0) (.cons (.bind
        (.perform .refSet (pairT (.var 0)
          (.app "some" (.cons (.app "cons" (.cons noTodo (.cons (.app "nil" .nil) .nil))) .nil))))
        (.fail (pairT (.lit (.str "SqlError")) (.lit (.str "planted"))))) .nil))
      (.succeed (.lit .unit)))
      (.bind read (.succeed (.var 2))))) ==
  some (some (Exit.success (Val.list [todo 0 "" false])), 0)

end Test.Dogfood.Bank
