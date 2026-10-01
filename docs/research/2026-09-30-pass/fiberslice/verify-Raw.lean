import Effect4.Api

/-! Verifier probe (fiberslice): the slice wires the declaration clause into the two checked
answer routes (`HostSession.preflight`, `replayCheckedFrom`). The certified entry points
`replayAdmitted` (Api.lean:425-433) and the certificate-first `Api.Typed.replay` (Api.lean:471)
replay the caller's tape without decision admission, by design ("Raw"). They take the forged
fiber answer today and would after the slice. Finite checks, not proofs. Base `be15b062`. -/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Research.Pass.FiberSliceVerify.Raw
open Effect4 Effect4.Machine Effect4.Program

def fiberRow : Row where
  name := "returnFiber"
  spelling := "Host.returnFiber"
  kind := .async
  registration := .external
  request := .unit
  answer := .fiberOf .nat .never
  error := .never
  cite := "verifier probe"

def table : RowTable := [fiberRow]
def opts : Supervision.ForkOptions := ⟨true, true, .interruptible⟩

/-- The seat's forged program: the child returns a string, the program is checked at `nat`. -/
def wrongProgram : Api.Program :=
  .bind (.withFiber (.fork (.succeed (.lit (.str "wrong"))) opts))
    (.bind (.perform (.external 0) (.lit .unit)) (.awaitFiber (.var 1) .joinEffect))

def tape : List Api.Decision :=
  [Api.evaluate, .answerAsync Api.root 0 (.ofExit (.success (Value.fiber 1))), Api.flush]

-- the certificate exists
#guard (admitProgram wrongProgram table).toOption.isSome
#guard (Api.check wrongProgram table).toOption.isSome
-- and the certified replays finish the `nat` program with the string
#guard (match admitProgram wrongProgram table with
  | .ok admitted => (Api.replayAdmitted admitted 1000 tape).exit == some (.success (.str "wrong"))
  | .error _ => false)
#guard (match Api.check wrongProgram table with
  | .ok t => (t.replay tape).exit == some (.success (.str "wrong"))
  | .error _ => false)

end Research.Pass.FiberSliceVerify.Raw
