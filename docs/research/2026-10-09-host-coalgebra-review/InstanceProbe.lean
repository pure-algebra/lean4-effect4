import Effect4.Laws.Api.HostSession

set_option autoImplicit false
set_option maxRecDepth 8192

namespace HostCoalgebraReview
open Effect4 Effect4.Machine Effect4.Program

def first : Row :=
  { name := "first", spelling := "L.first", kind := .async, registration := .external,
    request := .list (.var 0), answer := .option (.var 0), cite := "review" }

def call : NativeEff := .perform (.external 0) (.var 0)

def instanceFor (element : Ty) : Option (CallInstance NativeOp) :=
  callAt (nativeSignature [first]) [.list element] call []

-- These are local checked calls in the declared environments, not closed session runs.
#guard (instanceFor .nat).map (fun c => (c.request, c.answer)) =
  some (.list .nat, .option .nat)
#guard (instanceFor .string).map (fun c => (c.request, c.answer)) =
  some (.list .string, .option .string)
#guard Val.hasTy (.list []) (.list .nat) []
#guard Val.hasTy (.list []) (.list .string) []

-- The machine contributes only its empty allocation table to these data-only checks.
def machine : NativeMachine := (Api.run (.succeed (.lit .unit)) 10).machine

def admits (element : Ty) (value : Val) : Option Bool :=
  (instanceFor element).map fun c =>
    (admitInstance c machine Api.root 0 (.ofExit (.success value))).isNone

#guard admits .nat (.some (.nat 1)) = some true
#guard admits .string (.some (.nat 1)) = some false
#guard admits .nat (.some (.str "one")) = some false
#guard admits .string (.some (.str "one")) = some true
#guard admits .nat .none = some true
#guard admits .string .none = some true
#guard externalAdmits [first] 0 (.ofExit (.success (.some (.nat 1)))) = false

#eval (admits .nat (.some (.nat 1)), admits .string (.some (.nat 1)))
#eval (admits .nat (.some (.str "one")), admits .string (.some (.str "one")))

end HostCoalgebraReview
