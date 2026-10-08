import Effect4.Laws.Modules.Pool.Steps
import Effect4.Laws.Modules.Pool.Typing

/-! Finite controls of Pool's Step data and its public source terms.
Concept: Translation Simulation and Store Typing. Consumers: `pool-steps-agree` and
Pool's six operation typing statements, requirements R10 and R4.
These controls cover the listed cells, request keys, and source scopes only.
They establish no wrapper, allocation, progress, or host execution claim. -/

set_option autoImplicit false
namespace Test.Program.PoolData
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring Effect4.Modules
open Effect4.Pool.Model
open Effect4.Schema Effect4.Schema.Model

def table : Table := {handle := fun i => ⟨i⟩, hint := fun i => ⟨i + 20⟩}
def resources (i : Nat) : Val := .nat (100 + i)
def cells : List State :=
  [⟨[], [], [], false, 1⟩,
   ⟨[⟨5, 7, false, 0⟩], [5], [1, 2, 1], false, 9⟩,
   ⟨[⟨5, 7, true, 9⟩], [], [1, 2, 1], false, 10⟩,
   ⟨[⟨5, 7, true, 9⟩], [], [1, 2, 1], true, 10⟩]

def observe (src : TermSrc) (values : List Val) : Option Val :=
  match src {names := ["id", "hint", "cell", "stamp", "lease", "count"]} [] with
  | .error _ => none
  | .ok term => evalTerm values term

def values (s : State) : List Val :=
  [.promise (table.handle 1), .promise ⟨77⟩, cellVal table resources s, .nat 5, .nat 9, .nat 1]

#guard (Pool.Data.lease .nat).normal
#guard (Pool.Data.giveBack .nat).normal
#guard (Pool.Data.withdraw .nat).normal
#guard (Pool.Data.drain .nat).normal
#guard (Pool.Data.select .nat).normal
#guard (Pool.Data.close .nat).normal

-- Every reply and updated field is compared with the independent model.
#guard cells.all fun s => decide
  (observe (Pool.leaseStep (var "id") (var "hint") (var "cell")) (values s) =
    some (.list [leaseReplyVal resources (lease s 1).2,
      cellVal (table.renew 1 ⟨77⟩) resources (lease s 1).1]))
#guard cells.all fun s => decide
  (observe (Pool.returnStep (var "stamp") (var "lease") (var "cell")) (values s) =
    some (.list [returnReplyVal (giveBack s 5 9).2, cellVal table resources (giveBack s 5 9).1]))
#guard cells.all fun s => decide
  (observe (Pool.withdrawStep (var "id") (var "cell")) (values s) =
    some (.list [.unit, cellVal table resources (withdraw s 1)]))
#guard cells.all fun s => decide
  (observe (Pool.drainStep (var "id") (var "hint") (var "cell")) (values s) =
    some (.list [.bool (drain s 1).2, cellVal (table.renew 1 ⟨77⟩) resources (drain s 1).1]))
#guard cells.all fun s => decide
  (observe (Pool.selectStep (var "count") (var "cell")) (values s) =
    some (.list [selectReplyVal table (select s 1).2, cellVal table resources (select s 1).1]))
#guard cells.all fun s => decide
  (observe (Pool.closeStep (var "cell")) (values s) =
    some (.list [closeReplyVal (close s).2, cellVal table resources (close s).1]))

-- Identity removal does not compare hints, resources, or arbitrary value trees.
#guard Model.deferredEqual Leaves.deferredKeys ⟨1⟩ ⟨1⟩
#guard !Model.deferredEqual Leaves.deferredKeys ⟨1⟩ ⟨2⟩
#guard !Model.deferredEqual Leaves.opaque (.nat 1) (.nat 1)
#guard (observe (Pool.leaseStep (var "missing") (var "hint") (var "cell"))
  (values ⟨[], [], [], false, 1⟩)).isNone

end Test.Program.PoolData
