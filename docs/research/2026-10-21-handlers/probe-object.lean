import Test.Api.SessionFixtures
import Compiler.Graphs

/-! # Probe 1: the handler as its own object, read by one fold

A service block is a handler. This probe reads it as one value: the service's name, the state
it carries (its init's answer), its init, its clauses (the methods) and what it forwards.
The read is `cata_eff` over `EffAlgebra.ofLayer`, as `Compiler.Graphs.read` reads its relations:
the `defs` node contributes the services of its declarations (`servicesOf`,
`src/Effect4/Program/Services.lean`); every other node joins its children.
Run: `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-21-handlers/probe-object.lean`. -/

open Effect4 Effect4.Program Effect4.Api Test.Api.SessionFixtures

namespace Probe

/-- The handler object. `requires` is what the init reads from the context: Effect's `RIn` of
`Layer<I, E, RIn>`. `forwards` is what the clauses still require after the state's keys are
discharged: the open right summand. -/
structure Handler where
  service : String
  state : Ty
  init : Nat
  clauses : List (String × Nat × Nat)
  requires : List ServiceKey
  forwards : List ServiceKey

/-- One service of a block as a handler, from its declarations (`Service`, `servicesOf`). -/
def Handler.ofService (decls : List DefDecl) (s : Service) : Option Handler := do
  let init ← decls[s.init]?
  let methods := s.methods.filterMap fun (_, k, _) => decls[k]?
  pure { service := s.name, state := init.answer, init := s.init, clauses := s.methods,
         requires := init.requires, forwards := (methods.flatMap (·.requires)).eraseDups }

/-- The algebra: the `defs` node reads its declarations as handlers; every node joins its
children's. The carrier is the same at every sort. -/
def algebra : EffAlgebra NativeOp (fun _ => List Handler) :=
  EffAlgebra.ofLayer fun _ _ args =>
    (args.flatMap fun | .decls ds => (servicesOf ds).filterMap (Handler.ofService ds) | _ => []) ++
    (args.flatMap fun | .child _ hs => hs | _ => [])

/-- **The handlers of a built program**: one fold. -/
def handlers (b : Built) : List Handler := cata_eff algebra b.program

/-- The rows a handler's clauses perform, read off the calls relation (`Compiler.Graphs.read`):
what the handler hands to the next layer. -/
def Handler.rows (b : Built) (h : Handler) : List String :=
  let r := Compiler.Graphs.read b
  (r.calls.filterMap fun c =>
    match c.scope, c.target with
    | .def_ k, .row i => if h.clauses.any (·.2.1 == k) then (r.row? i).map (·.spelling) else none
    | _, _ => none).eraseDups

def keyName (k : ServiceKey) : String := keyText k

def Handler.show (b : Built) (h : Handler) : List (String × String) :=
  [("service", h.service), ("state", h.state.render), ("init", toString h.init),
   ("clauses", toString (h.clauses.map fun (m, k, n) => s!"{m}@{k}/{n}")),
   ("requires", toString (h.requires.map keyName)), ("forwards", toString (h.forwards.map keyName)),
   ("rows", toString (h.rows b))]

end Probe

open Probe

-- the plain to-do: one handler, its state the context of the repository's key
#eval todoBuilt.map fun b => (handlers b).map (·.show b)
-- the cached to-do: two handlers; the cache's state is a cell; the to-do's state is the context
-- beside that cell, and its clauses hand the cache's rows (`refGet`, `refSet`) to the next layer
#eval cachedBuilt.map fun b => (handlers b).map (·.show b)
-- agreement of folds: the fold reads what the root's declarations declare
#eval todoBuilt.map fun b => (handlers b).map (·.service) == (servicesOf b.program.defsOf).map (·.name)
#eval cachedBuilt.map fun b => (handlers b).map (·.service) == (servicesOf b.program.defsOf).map (·.name)
