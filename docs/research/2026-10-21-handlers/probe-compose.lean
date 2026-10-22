import Test.Api.SessionFixtures
import Compiler.Graphs
import Tools.View.LayerGraph
import Test.Program.SignatureSum

/-! # Probe 3: the four compositions, each on the to-do

Vertical (`provide`), horizontal (`tensor`), the transformer (`wrap`) and forwarding (the open
right summand), each shown on the plain and the cached to-do, with its law and its boundary.
Run: `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-21-handlers/probe-compose.lean`. -/

open Effect4 Effect4.Program Effect4.Api Effect4.Program.Authoring Test.Api.SessionFixtures
open Test.Dogfood.Scenario.Todo (todoRepoKey repository Repo)

namespace Probe

/-! ## 3a. Vertical: `provide`, on the typing -/

def kA : ServiceKey := ⟨⟨31⟩, ⟨6⟩⟩
def kB : ServiceKey := ⟨⟨32⟩, ⟨6⟩⟩
def kC : ServiceKey := todoRepoKey

/-- `a` provides `kA` and reads `kC`; `b` provides `kB`; `c` provides `kC`. -/
def a : LayerTerm NativeOp := .effect kA (.service kC)
def b : LayerTerm NativeOp := .effect kB (.succeed (.lit .unit))
def c : LayerTerm NativeOp := .effect kC (.succeed (.lit .unit))

def layerTy (t : LayerTerm NativeOp) : Option (List String × List String) :=
  (Checker.checkLayer (nativeSignature []) [] t).toOption.map fun l =>
    (l.out.elems.map keyText, l.requires.elems.map keyText)

/-! ## 3b. Horizontal: `tensor`, on the reactors -/

def rows : List Row := Test.Dogfood.Scenario.Todo.TodoRepo.rows.map (·.row)

/-- An answer's value, where it is a success: the one observation these checks compare. -/
def value : Api.HostSession.Answer → Option Val
  | .ofExit (.success v) => some v
  | _ => none

/-- The observation of a tensor's step, with the state swapped: the value and the two states. -/
def swapped {α β : Type} : Option (Api.HostSession.Answer × α × β) → Option (Option Val × β × α)
  | some (x, (p, q)) => some (value x, (q, p))
  | none => none

def plain {α β : Type} : Option (Api.HostSession.Answer × α × β) → Option (Option Val × α × β)
  | some (x, (p, q)) => some (value x, (p, q))
  | none => none

/-- On the repository's rows, which the queue declines, the two orders agree up to the swap of
the state. -/
def commutes (row : Row) (sent : Val) : Bool :=
  reprStr (swapped (Run.Reactor.tensor Run.Reactor.queue repository row sent ([.unit], (1, [])))) ==
    reprStr (plain (Run.Reactor.tensor repository Run.Reactor.queue row sent ((1, []), [.unit])))

/-- A reactor that answers every row with unit: it overlaps the repository on every row. -/
def always : Run.Reactor Unit := fun _ _ s => some (.ofExit (.success .unit), s)

def leftWins (row : Row) (sent : Val) : Bool :=
  reprStr (swapped (Run.Reactor.tensor always repository row sent ((), (1, [])))) ==
    reprStr (plain (Run.Reactor.tensor repository always row sent ((1, []), ())))

/-- The session's `next` row, which the repository declines and the queue answers. -/
def nextRow : Row := (Row.host ServiceSession.nextName .unit .unit).row

/-! ## 3c. The transformer: `wrap`, on the clauses -/

/-- The nodes of one definition's body: address, constructor, what it names. -/
def body (b : Built) (k : Nat) : List (String × String × String) :=
  let r := Compiler.Graphs.read b
  (r.nodes.filter (·.scope == .def_ k)).map fun n =>
    (Compiler.Graphs.address n.address, n.ctor, r.namesText n.names)

/-- `wrap` with no entry under the name is the identity on the clause. -/
def wrapIdentity : Bool :=
  let m : Application.Imposed NativeOp := { Test.Dogfood.Scenario.Todo.listCache with around := [] }
  elaborate (m.wrap "list" unit (succeed unit)) == elaborate (succeed (Op := NativeOp) unit)

/-! ## 3d. Forwarding: the open right summand -/

def sessionRequires (b : Built) : List String := b.requires.map keyText

end Probe

open Probe

-- 3a. `(a ∘ b) ∘ c` and `a ∘ (b ∘ c)`: the typing is not associative; the inner `provide`
-- hides `kC` from `a` (Effect: `Layer<ROut2, E, RIn | Exclude<RIn2, ROut>>`, `Layer.ts:2258`)
#eval layerTy (.provide (.provide a b) c)
#eval layerTy (.provide a (.provide b c))
-- with `provideMerge` inside, `kC` stays exposed and the two agree (`Layer.ts:2704`)
#eval layerTy (.provide a (.provideMerge b c))
-- on the incidence, `provide` is overlay and overlay is associative: G1 and the algebraic graph
#check @Tools.View.LayerGraph.hypergraph_provide
#check @Tools.View.AGraph.overlay_assoc
-- 3b. the queue and the repository on disjoint rows: commutative up to the swap of the state
#eval rows.map fun row => (row.spelling, commutes row (.str "milk"))
#eval (nextRow.spelling, commutes nextRow .unit)
-- the boundary: two reactors that both answer a row; the left wins, so no commutation
#eval rows.map fun row => (row.spelling, leftWins row (.str "milk"))
#check @Test.Program.SignatureSum.sum_not_tensor
-- the states of a tensor are a product: the cached to-do's state is `(context, cell)`
#eval cachedBuilt.map fun b => (b.program.defsOf.filter (·.role == .serviceInit "TodoApp")).map (·.answer.render)
-- 3c. `list`'s clause, plain: the state provided to the entry's program
#eval todoBuilt.map (body · 2)
-- `list`'s clause, cached: the state split, the cache's `get` invoked with the plain clause as its
-- loader (`Def.invokeWith`, the scoped operation), the context provided inside
#eval cachedBuilt.map (body · 5)
#eval wrapIdentity
-- 3d. the requirement row the session leaves to the host: the init's `k30_6`, and nothing foreign
#eval todoSession.map sessionRequires
#eval todoSession.map fun b => (ServiceSession.foreign b).map keyText
#eval cachedSession.map sessionRequires
#check @Effect4.Laws.Effects.interpret_inl_restrict
