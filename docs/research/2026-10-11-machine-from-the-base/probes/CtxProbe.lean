import Effect4.Api

/-!
Probe (scratch): the dynamic context of a passed program, and the context typing against raw
`setContext`.

1. A definition's body provides a service around its parameter site; the passed program reads
   the service. Which value does it read: the body's or the caller's?
2. A region provides a service, then resets the context to one captured outside the region, then
   reads the service. The checker's lexical row says the read is provided.
-/

open Effect4 Effect4.Machine Effect4.Program

namespace CtxProbe

abbrev E := Eff NativeOp

def key : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩
def n (i : Nat) : Term := .lit (.nat i)
def u : Term := .lit .unit
def tape : List Api.Decision := [Api.evaluate, Api.flush]

def fDecl : DefDecl :=
  { name := "f", request := .unit, answer := .nat,
    params := [{ name := "p", request := .unit, answer := .nat }] }

/-- The body provides 1 around its parameter site; the caller provides 2 around the call. -/
def dyn : E :=
  .defs [fDecl] (.cons (.provideService key (n 1) (.perform (.param 0) u)) .nil)
    (.provideService key (n 2) (.invoke 0 u (.cons (.service key) .nil))) .nil

/-- Control: the body provides nothing. -/
def lexical : E :=
  .defs [fDecl] (.cons (.perform (.param 0) u) .nil)
    (.provideService key (n 2) (.invoke 0 u (.cons (.service key) .nil))) .nil

/-- The body provides 1; the caller provides nothing. -/
def bodyOnly : E :=
  .defs [fDecl] (.cons (.provideService key (n 1) (.perform (.param 0) u)) .nil)
    (.invoke 0 u (.cons (.service key) .nil)) .nil

/-- The body runs its parameter twice: inside its region, then after it. -/
def tDecl : DefDecl :=
  { name := "f", request := .unit, answer := .prod .nat .nat,
    params := [{ name := "p", request := .unit, answer := .nat }] }

def twice : E :=
  .defs [tDecl]
    (.cons (.bind (.provideService key (n 1) (.perform (.param 0) u))
      (.bind (.perform (.param 0) u) (.succeed (.app "pair" (.cons (.var 1) (.cons (.var 2) .nil))))))
      .nil)
    (.provideService key (n 2) (.invoke 0 u (.cons (.service key) .nil))) .nil

/-- A forked child reads the service after the parent's region has ended. -/
def forked : E :=
  .bind (.provideService key (n 1) (.withFiber (.fork (.service key) ⟨true, false, .inherit⟩)))
    (.awaitFiber (.var 0) .joinEffect)

/-- A region provides 1, resets the context to the one captured outside, then reads. -/
def reset : E :=
  .bind (.withFiber .getContext)
    (.provideService key (n 1)
      (.bind (.withFiber (.setContext (.var 0))) (.service key)))

/-- A definition whose request is a context: the body sets it, then runs the parameter. -/
def gDecl : DefDecl :=
  { name := "g", request := .context, answer := .nat,
    params := [{ name := "p", request := .unit, answer := .nat }] }

def resetInBody : E :=
  .defs [gDecl] (.cons (.bind (.withFiber (.setContext (.var 0))) (.perform (.param 0) u)) .nil)
    (.bind (.withFiber .getContext)
      (.provideService key (n 2) (.invoke 0 (.var 0) (.cons (.service key) .nil)))) .nil

def reasonText (r : Reason Err Defect FiberId Ann) : String :=
  match r with
  | Reason.fail e _ => s!"fail {repr e}"
  | Reason.die d _ => s!"die {repr d}"
  | Reason.interrupt _ _ => "interrupt"

def report (name : String) (p : E) : IO Unit := do
  let ty := match Api.typeOf p [] with
    | some t => s!"answer {repr t.answer}, requires {repr t.requires.elems}"
    | none => "refused"
  let r := Api.replay p 400 tape
  let ex := match r.exit with
    | some (.success v) => s!"success {repr v}"
    | some (.failure c) => s!"failure {c.reasons.map reasonText}"
    | none => "no exit"
  IO.println s!"== {name}\n  type: {ty}\n  admitted: {(admitProgram p).toOption.isSome}\n  exit: {ex}"

end CtxProbe

open CtxProbe in
def main : IO Unit := do
  report "dyn" dyn
  report "lexical" lexical
  report "bodyOnly" bodyOnly
  report "twice" twice
  report "forked" forked
  report "reset" reset
  report "resetInBody" resetInBody
