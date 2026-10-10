import Effect4.Api
import TestSupport.AcquireHandle

/-!
Retained argument cleanup control at f00008ee.
Concept: residual-program-typing; claim: denote-typed; R4/M6.
Consumers: acquireIn_typed, CaptureTyped, finalizerAdmitted_mono, capture_release, denoteFin_typed.
Reach: one admitted program with a captured allocated handle and a fixed reply tape.
Limits: finite reference-machine evaluation, not world-extension proof or outside-host evidence.
-/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Test.CX1aCleanupReview
open Effect4 Effect4.Program Effect4.Machine
open Test.Api.AcquireHandleContract (resource table)

def unitProgram : NativeEff := .succeed (.lit .unit)
def slot : ParamDecl := { name := "cleanup", request := .unit, answer := .unit }
def decl : DefDecl :=
  { name := "registerCleanup", request := .unit, answer := .unit,
    params := [slot], requires := [nativeScopeKey] }
def body : NativeEff := .acquireRelease unitProgram (.perform (.param 0) (.lit .unit))
def program (cleanup : NativeEff) : NativeEff := .defs [decl] (.cons body .nil)
  (.scoped (.bind (.perform (.external 0) (.lit .unit))
    (.bind (.invoke 0 (.lit .unit) (.cons cleanup .nil))
      (.perform (.external 2) (.var 0)))))
def cleanup : NativeEff := .perform (.external 1) (.var 0)
def answer (v : Val) : Completion Val Err Defect FiberId Ann := .ofExit (.success v)

-- The argument captures the caller's handle; its own unit argument occupies variable 1.
#guard Api.typeOf (program cleanup) table == some (EffTy.pure .nat)
#guard Api.typeOf (program (.perform (.external 1) (.var 1))) table == none
-- Fixed replies correspond to acquire, read, then delayed close.
#guard (Api.run (program cleanup) 1000
  [answer (.nat 0), answer (.nat 7), answer .unit] table).outcome == .finished
#guard (Api.run (program cleanup) 1000
  [answer (.nat 0), answer (.nat 7), answer .unit] table).exit == some (.success (.nat 7))
#guard (Api.run (program cleanup) 1000
  [answer (.nat 0), answer (.nat 7), answer .unit] table).stores.externals.allocated == [resource]
-- The unanswered cleanup remains live, retaining the allocated handle.
#guard (Api.run (program cleanup) 1000
  [answer (.nat 0), answer (.nat 7)] table).outcome == .frontier
#guard (Api.run (program cleanup) 1000
  [answer (.nat 0), answer (.nat 7)] table).exit == none
#guard (Api.run (program cleanup) 1000
  [answer (.nat 0), answer (.nat 7)] table).stores.externals.allocated == [resource]

end Test.CX1aCleanupReview
