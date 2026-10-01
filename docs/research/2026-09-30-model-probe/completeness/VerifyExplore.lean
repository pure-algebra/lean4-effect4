import Effect4.Api
import Effect4.Api.HostProtocol
import Effect4.Api.Author

/-! Verifier's exploration for the completeness seat (printed values only; the guarded
fixture is `VerifyRun.lean`). Read against HEAD `7cae243a`. -/

set_option autoImplicit false

namespace Probe.CompletenessVerify.Explore

open Effect4 Effect4.Machine Effect4.Program

def interruptRoot : Api.Decision :=
  RunDecision.interruptFrom none ReasonAnnotations.empty Api.root

def pairT (a b : Term) : Term := .app "pair" (.cons a (.cons b .nil))

def opts : Supervision.ForkOptions := ⟨false, false, .inherit⟩

/-- A cell at 0; a scope whose release increments the cell; the body parks forever. -/
def counting : NativeEff :=
  .bind (.perform .refMake (.lit (.nat 0)))
    (.bind
      (.scoped
        (.bind
          (.acquireRelease (.succeed (.lit .unit)) (.perform (.refUpdate .incr) (.var 0)))
          (.bind (.perform .deferredMake (.lit .unit)) (.perform .deferredAwait (.var 2)))))
      (.perform .refGet (.var 0)))

/-- Two releases registered in one scope: the seat's setter release, twice. -/
def setterTwice : NativeEff :=
  .bind (.perform .refMake (.lit (.nat 0)))
    (.bind
      (.scoped
        (.bind
          (.acquireRelease (.succeed (.lit .unit))
            (.perform .refSet (pairT (.var 0) (.lit (.nat 1)))))
          (.acquireRelease (.succeed (.lit .unit))
            (.perform .refSet (pairT (.var 0) (.lit (.nat 1)))))))
      (.perform .refGet (.var 0)))

/-- Two releases registered in one scope: the counting release, twice. -/
def counterTwice : NativeEff :=
  .bind (.perform .refMake (.lit (.nat 0)))
    (.bind
      (.scoped
        (.bind
          (.acquireRelease (.succeed (.lit .unit)) (.perform (.refUpdate .incr) (.var 0)))
          (.acquireRelease (.succeed (.lit .unit)) (.perform (.refUpdate .incr) (.var 0)))))
      (.perform .refGet (.var 0)))

/-- The counting release with a body that finishes normally. -/
def countingDone : NativeEff :=
  .bind (.perform .refMake (.lit (.nat 0)))
    (.bind
      (.scoped
        (.acquireRelease (.succeed (.lit .unit)) (.perform (.refUpdate .incr) (.var 0))))
      (.perform .refGet (.var 0)))

#eval (Api.typeOf counting).isSome
#eval (Api.typeOf setterTwice).isSome
#eval (Api.typeOf counterTwice).isSome
#eval (Api.typeOf countingDone).isSome
#eval (Api.run counting 200).machine.state.refs
#eval (Api.replay counting 200 [Api.evaluate, Api.flush, interruptRoot]).machine.state.refs
#eval (Api.replay counting 200 [Api.evaluate, Api.flush, interruptRoot]).outcome
#eval (Api.replay counting 200 [Api.evaluate, Api.flush, interruptRoot, interruptRoot]).machine.state.refs
#eval (Api.replay counting 200 [Api.evaluate, Api.flush, interruptRoot, interruptRoot]).outcome
#eval (Api.run setterTwice 200).machine.state.refs
#eval (Api.run counterTwice 200).machine.state.refs
#eval (Api.run countingDone 200).machine.state.refs
#eval (Api.run countingDone 200).outcome

/-! Silent re-pointing: an inserted row of the same type. -/

def row (name spelling : String) (request answer : Ty) : Row :=
  { name, spelling, kind := .async, registration := .external, request, answer,
    error := .never, cite := "docs/research/2026-09-30-model-probe/completeness/VerifyExplore.lean" }

def table : RowTable := [ row "ping" "Host.ping" .unit .string, row "pong" "Host.pong" .unit .string ]
def zap : Row := row "zap" "Host.zap" .unit .string
def callPong : NativeEff := .perform (.external 1) (.lit .unit)

#eval decide (Api.typeOf callPong (zap :: table) = Api.typeOf callPong table)
#eval (Api.typeOf callPong table).isSome
#eval (Api.print callPong table).map (TypeScript.Render.expr TypeScript.house0 0)
#eval (Api.print callPong (zap :: table)).map (TypeScript.Render.expr TypeScript.house0 0)
#eval decide (Api.bytesOf callPong = Api.bytesOf callPong)
#eval (table[1]?).map (·.spelling)
#eval ((zap :: table)[1]?).map (·.spelling)
#eval LawfulTable (zap :: table)
#eval (Api.run callPong 100 [] table).reasons
#eval (Api.run callPong 100 [] (zap :: table)).reasons

/-! Forked work queued behind a parked root: what do the reasons say? -/

/-- The root forks a child that completes the deferred the root then awaits. -/
def forkCompletes : NativeEff :=
  .bind (.perform .deferredMake (.lit .unit))
    (.bind (.withFiber (.fork (.perform .deferredSucceed (pairT (.var 0) (.lit (.nat 5)))) opts))
      (.perform .deferredAwait (.var 0)))

/-- The root forks a child that does nothing, then awaits a deferred nobody completes. -/
def forkThenWait : NativeEff :=
  .bind (.withFiber (.fork (.succeed (.lit (.nat 1))) opts))
    (.bind (.perform .deferredMake (.lit .unit)) (.perform .deferredAwait (.var 1)))

#eval (Api.typeOf forkCompletes).isSome
#eval (Api.typeOf forkThenWait).isSome
#eval (Api.replay forkCompletes 200 [Api.evaluate]).outcome
#eval (Api.replay forkCompletes 200 [Api.evaluate]).reasons
#eval (Api.replay forkCompletes 200 [Api.evaluate]).machine.armed
#eval (Api.replay forkCompletes 200 [Api.evaluate]).machine.fibers.map (fun f => (f.id, f.exit.isSome, f.parked == .notParked))
#eval Api.HostProtocol.observe (Api.replay forkCompletes 200 [Api.evaluate]).machine
#eval (Api.replay forkCompletes 200 [Api.evaluate, Api.flush]).outcome
#eval (Api.replay forkThenWait 200 [Api.evaluate]).reasons
#eval (Api.replay forkThenWait 200 [Api.evaluate]).machine.armed
#eval (Api.replay forkThenWait 200 [Api.evaluate, Api.flush]).reasons

/-! An observer's resume while every fiber is parked. -/

/-- The root forks a child that answers 1 and joins it. -/
def forkJoin : NativeEff :=
  .bind (.withFiber (.fork (.succeed (.lit (.nat 1))) opts))
    (.awaitFiber (.var 0) Supervision.ObserverMode.joinEffect)

/-- The root yields, then answers. -/
def yielding : NativeEff := .bind (.yieldNow 0) (.succeed (.lit (.nat 3)))

#eval (Api.typeOf forkJoin).isSome
#eval (Api.typeOf yielding).isSome
#eval (Api.replay forkJoin 200 [Api.evaluate]).reasons
#eval (Api.replay forkJoin 200 [Api.evaluate]).machine.armed
#eval (Api.replay forkJoin 200 [Api.evaluate, RunDecision.fire Api.root]).outcome
#eval (Api.replay forkJoin 200 [Api.evaluate, RunDecision.fire Api.root]).reasons
#eval (Api.replay forkJoin 200 [Api.evaluate, RunDecision.fire Api.root]).machine.armed
#eval (Api.replay forkJoin 200 [Api.evaluate, RunDecision.fire Api.root]).machine.fibers.map (fun f => (f.id, f.exit.isSome, f.parked == .notParked))
#eval (Api.replay forkJoin 200 [Api.evaluate, RunDecision.fire Api.root, RunDecision.fire Api.root]).outcome
#eval (Api.replay forkJoin 200 [Api.evaluate, Api.flush]).outcome
#eval (Api.replay yielding 200 [Api.evaluate]).reasons
#eval (Api.replay yielding 200 [Api.evaluate]).machine.armed
#eval (Api.replay yielding 200 [Api.evaluate]).machine.fibers.map (fun f => (f.id, f.exit.isSome, f.parked == .notParked))

/-! Dogfood conclusions §2 at HEAD: the singleton-mergeAll identity program (Lean side). -/

def dogKey : ServiceKey := ⟨⟨7⟩, ⟨4⟩⟩

def identityProgram : NativeEff :=
  .provideLayer (.mergeAll (.cons (.effect dogKey (.withFiber .getId)) .nil)) false
    (.bind (.service dogKey)
      (.bind (.withFiber .getId)
        (.succeed (.app "eq" (.cons (.var 0) (.cons (.var 1) .nil))))))

#eval (Api.typeOf identityProgram).isSome
#eval decide (Api.typeOf identityProgram = some ⟨.bool, .never, .empty⟩)
#eval decide ((Api.run identityProgram 1000).exit = some (.success (.bool false)))
#eval decide ((Api.run identityProgram 1000).exit = some (.success (.bool true)))
#eval (Api.run identityProgram 1000).outcome

/-! A release registered in a manual scope the program never closes. -/

def unclosed : NativeEff :=
  .bind (.perform .refMake (.lit (.nat 0)))
    (.bind (.perform (.scopeMake .sequential) (.lit .unit))
      (.bind
        (.provideService nativeScopeKey (.var 1)
          (.acquireRelease (.succeed (.lit .unit)) (.perform (.refUpdate .incr) (.var 0))))
        (.perform .refGet (.var 0))))

#eval (Api.typeOf unclosed).isSome
#eval decide (Api.typeOf unclosed = some ⟨.nat, .never, .empty⟩)
#eval (Api.run unclosed 200).outcome
#eval (Api.run unclosed 200).machine.state.refs
#eval decide ((Api.run unclosed 200).exit = some (.success (.nat 0)))
#eval (Api.run unclosed 200).machine.fibers.map (fun f => (f.id, f.exit.isSome))
#eval (Api.run unclosed 200).machine.state.scopes.entries.length

/-! R1's seventh carrier: a service key whose type code the six do not spell. -/

def key10 : ServiceKey := ⟨⟨10⟩, ⟨10⟩⟩
def readKey10 : NativeEff := .service key10

#eval (Api.typeOf readKey10).isSome
#eval (typeOfProgram (nativeSignatureWith [] [(key10, .string)]) readKey10).isSome
#eval (admitProgram readKey10 []).toOption.isSome

end Probe.CompletenessVerify.Explore
