import Test.Api.SessionFixtures
import Compiler.Graphs
import Effects.Coalgebra.Comodel

/-! # Probe 4: the two compositions the runner form does not have

A clause that captures its continuation, and a parameterised handler whose clause returns a new
state. This probe shows, by the types of the tree, where each would have to enter, and how much
of each the to-do already does another way.
Run: `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-21-handlers/probe-missing.lean`. -/

open Effect4 Effect4.Program Effect4.Api Test.Api.SessionFixtures

namespace Probe

/-- The constructors of the cached to-do's program, counted by name. -/
def counts (b : Built) (names : List String) : List (String × Nat) :=
  let r := Compiler.Graphs.read b
  names.map fun n => (n, (r.nodes.filter (·.ctor == n)).length)

/-- The store operations a program performs, counted: a fold that reads each `perform`'s
operation. -/
def storeOps : EffAlgebra NativeOp (fun _ => Nat × Nat × Nat) :=
  EffAlgebra.ofLayer fun _ _ args =>
    args.foldl (fun (m, g, s) a => match a with
      | .op .refMake => (m + 1, g, s)
      | .op .refGet => (m, g + 1, s)
      | .op .refSet => (m, g, s + 1)
      | .child _ (m', g', s') => (m + m', g + g', s + s')
      | _ => (m, g, s)) (0, 0, 0)

/-- A method's answer is never a pair with its state: no clause returns a new state. -/
def answersState (b : Built) : List (String × Bool) :=
  b.program.defsOf.filterMap fun d => match d.role with
    | .serviceMethod s m _ =>
      let state := (b.program.defsOf.find? (·.role == .serviceInit s)).map (·.answer)
      some (m, match d.answer with | .prod _ snd => some snd == state | _ => false)
    | _ => none

end Probe

open Probe

-- 4a. a clause sees its operation and answers it; the continuation stays in the free monad
#check @Effects.Handler.handle
#check @Effects.Program.vis
#check @Effects.Comodel.answer
-- a method is a definition: request to answer, no binder for a continuation
#check @Effect4.Program.DefDecl.mk
-- the failure handlers of `Eff` take a program for the cause, with no continuation argument
#check @Effect4.Program.Eff.catchCause
#check @Effect4.Program.Eff.matchCause
-- the to-do uses none of them; its clauses return directly
#eval cachedBuilt.map (counts · ["catchCause", "matchCause", "catchIf", "provideContext", "invoke"])
-- 4b. the state is handed in by `provideContext`, a constructor, and never handed back
#check @Effect4.Program.Eff.provideContext
#eval cachedBuilt.map answersState
-- the session's dispatch binds the state once for the lifetime (`ServiceSession.main`)
#check @Effect4.Api.ServiceSession.dispatch
-- what a parameter does today: the cache's cell is a `Ref` in the state, written through the
-- store's rows (make, get, set), so the "parameter" changes without a clause returning it
#eval cachedBuilt.map fun b => cata_eff storeOps b.program
#eval todoBuilt.map fun b => cata_eff storeOps b.program
