import Effect4.Api

/-!
# `E4-CTX-CE-001`: a checked program at a closed row dies with `missingService` (seeded)

The object language's `setContext` action writes the fiber's context raw
(`WithFiberAction.setContext`, `src/Effect4/Machine/Fibers.lean`). The checker types it by the
written value's type alone (`Checker.checkAction`, `src/Effect4/Program/Checker.lean`), and
`Ty.context` carries no row. So a region that provides a service can reset the context to one
captured outside it, and the checker still counts the service as provided below.

rc.112 has no such program: its context reader is typed by its row, and its `setContext` is a
region over a body whose requirement the context covers (`context`, `setContext`,
`provideContext`, `vendor/effect-4.0.0-rc.112/src/internal/effect.ts`). The printer refuses the
action (`Codegen/Templates.lean`), so no emitted module shows the defect; the checker and the
machine do.

The witnesses are finite runs on the frame machine at budget 400, an empty row table and the
decisions `evaluate`, `flush`. The control is the same region without the reset. It refutes, on
the current language, decisions row 117's part two (no `missingService` at a closed row, R9).
The forced repair is the research note's option A
(`docs/research/2026-10-11-machine-from-the-base/context-transformers.md`, §4).
-/

set_option autoImplicit false

namespace Test.Counterexamples.Program.ContextReset

open Effect4 Effect4.Machine Effect4.Program

abbrev E := Eff NativeOp

def key : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩
def n (i : Nat) : Term := .lit (.nat i)
def u : Term := .lit .unit
def tape : List Api.Decision := [Api.evaluate, Api.flush]

/-- A region provides `key`, resets the context to the one captured outside it, and reads `key`. -/
def reset : E :=
  .bind (.withFiber .getContext)
    (.provideService key (n 1)
      (.bind (.withFiber (.setContext (.var 0))) (.service key)))

/-- A definition whose request is a context sets it, then runs its parameter, which reads `key`
under the caller's region. -/
def gDecl : DefDecl :=
  { name := "g", request := .context, answer := .nat,
    params := [{ name := "p", request := .unit, answer := .nat }] }

def resetInBody : E :=
  .defs [gDecl] (.cons (.bind (.withFiber (.setContext (.var 0))) (.perform (.param 0) u)) .nil)
    (.bind (.withFiber .getContext)
      (.provideService key (n 2) (.invoke 0 (.var 0) (.cons (.service key) .nil)))) .nil

/-- Control: the same region without the reset. -/
def control : E :=
  .bind (.withFiber .getContext)
    (.provideService key (n 1) (.service key))

/-- The run's exit dies with exactly `missingService`. -/
def diesMissing (ex : Option ExitV) : Bool :=
  match ex with
  | some (.failure c) =>
    c.reasons.length == 1 && c.reasons.all fun r => match r with
      | Reason.die .missingService _ => true
      | _ => false
  | _ => false

-- The checker's row is closed, and the program is admitted.
#guard (Api.typeOf reset []).map (·.requires.elems) = some []
#guard (admitProgram reset).toOption.isSome
#guard (Api.typeOf resetInBody []).map (·.requires.elems) = some []
#guard (admitProgram resetInBody).toOption.isSome

-- The attack: both die with `missingService`.
#guard diesMissing (Api.replay reset 400 tape).exit
#guard diesMissing (Api.replay resetInBody 400 tape).exit

-- The control: without the reset, the region's value is read.
#guard (Api.typeOf control []).map (·.requires.elems) = some []
#guard (Api.replay control 400 tape).exit == some (.success (.nat 1))

end Test.Counterexamples.Program.ContextReset
