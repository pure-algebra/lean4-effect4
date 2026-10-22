import Test.Api.SessionFixtures

/-! # Probe 2: the fit law as the forgetting map

A handler's interface is its clauses with the state removed from each request. Two handlers of
one service fit when their interfaces agree. The tree already owns the forgetting map:
`methodArgs state d arity` (`src/Effect4/Program/Services.lean`), which the printer's method
types and the session's protocol rows read through. This probe states the interface as one fold
over that map, checks it on the plain and the cached to-do, and shows the consumer: the session
protocol of a service is a function of the interface alone.
Run: `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-21-handlers/probe-fit.lean`. -/

open Effect4 Effect4.Program Effect4.Api Test.Api.SessionFixtures

namespace Probe

/-- One clause of the interface: the method, its arguments after the state, its answer, its
error. -/
abbrev Clause := String × List Ty × Ty × Ty

/-- The forgetting map on one clause: `none` where the request does not begin with the state. -/
def forget (decls : List DefDecl) (state : Ty) (m : String × Nat × Nat) : Option Clause := do
  let d ← decls[m.2.1]?
  let args ← methodArgs state d m.2.2
  pure (m.1, args, d.answer, d.error)

/-- The interface of a service: every clause forgotten at the init's answer. -/
def interface (decls : List DefDecl) (s : Service) : Option (List Clause) := do
  let init ← decls[s.init]?
  s.methods.mapM (forget decls init.answer)

def serviceOf (b : Built) (name : String) : Option Service :=
  (servicesOf b.program.defsOf).find? (·.name == name)

def interfaceOf (b : Built) (name : String) : Option (List Clause) :=
  (serviceOf b name).bind (interface b.program.defsOf)

def stateOf (b : Built) (name : String) : Option String :=
  (serviceOf b name).bind fun s => (b.program.defsOf[s.init]?).map (·.answer.render)

/-- **Fit**: two built programs' handlers of one service have the same interface, and have one. -/
def fits (b b' : Built) (name : String) : Bool :=
  match interfaceOf b name, interfaceOf b' name with
  | some i, some i' => i == i'
  | _, _ => false

def showClause (c : Clause) : String × List String × String × String :=
  (c.1, c.2.1.map Ty.render, c.2.2.1.render, c.2.2.2.render)

/-- The session's protocol rows of a service, as the spelling and the columns of each row. -/
def protocol (b : Built) (name : String) : Option (List (String × String × String)) := do
  let s ← serviceOf b name
  let init ← b.program.defsOf[s.init]?
  let rows ← (ServiceSession.rows b.program.defsOf s init.answer).toOption
  pure (rows.map fun r => (r.spelling, r.request.render, r.answer.render))

end Probe

open Probe

-- the states differ
#eval todoBuilt.bind (stateOf · "TodoApp")
#eval cachedBuilt.bind (stateOf · "TodoApp")
-- the interfaces agree: the one value, printed once
#eval todoBuilt.bind (interfaceOf · "TodoApp") |>.map (·.map showClause)
#eval todoBuilt.bind fun a => cachedBuilt.map fun b => fits a b "TodoApp"
-- control: two services of one program with different clauses do not fit
#eval cachedBuilt.map fun b => (interfaceOf b "ListCache" == interfaceOf b "TodoApp", (interfaceOf b "ListCache").map (·.map showClause))
-- control: the forgetting map is undefined at a state the request does not begin with
#eval todoBuilt.map fun b => (servicesOf b.program.defsOf).map fun s =>
  s.methods.map fun m => (forget b.program.defsOf .unit m).isSome
-- the consumer: the protocol rows of the two handlers are one table
#eval todoBuilt.bind (protocol · "TodoApp")
#eval todoBuilt.bind fun a => cachedBuilt.map fun b => protocol a "TodoApp" == protocol b "TodoApp"
