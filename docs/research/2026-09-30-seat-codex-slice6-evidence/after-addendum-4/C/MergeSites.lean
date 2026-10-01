import Test.Program.TypedCorpus
open Effect4 Effect4.Machine Effect4.Program
open Test.Program.TypedCorpus (Entry es key key2)
namespace MergeSites
def u : Term := .lit .unit
def unitProgram : NativeEff := .succeed u
def opts : Supervision.ForkOptions := ⟨true, false, .inherit⟩
def daemon : Supervision.ForkOptions := ⟨true, true, .inherit⟩
def ordinary : NativeEff :=
  .bind (.withFiber (.fork unitProgram opts)) (.awaitFiber (.var 0) .joinEffect)
def explicitScope : NativeEff :=
  .bind (.perform (.scopeMake .sequential) u)
    (.withFiber (.forkIn unitProgram opts (.var 0)))
/-- The parallel-close fixture from RuntimeRContract.parTwo: two original children and
both finalizer forks must actually exist before its site check counts as coverage. -/
def finalizers : NativeEff :=
  .bind (.perform (.scopeMake .parallel) u)
    (.bind (.perform .deferredMake u)
      (.bind (.withFiber (.forkIn (.perform .deferredAwait (.var 1)) daemon (.var 0)))
        (.bind (.withFiber (.forkIn (.perform .deferredAwait (.var 1)) daemon (.var 0)))
          (.bind (.exit unitProgram) (.withFiber (.closeScope (.var 0) (.var 4)))))))
def race : NativeEff :=
  .withFiber (.raceAll (es [.perform .sleep (.lit (.nat 1)), unitProgram]))
def multiple : NativeEff :=
  .bind (.withFiber (.fork unitProgram opts))
    (.bind (.withFiber (.fork unitProgram daemon)) unitProgram)
def merge : NativeEff :=
  .provideLayer (.merge (.succeed key (.nat 1)) (.succeed key2 (.nat 2))) false (.service key)
def mergeAll : NativeEff :=
  .provideLayer (.mergeAll (.cons (.succeed key (.nat 1))
    (.cons (.succeed key2 (.nat 2)) .nil))) false (.service key)


#eval (Api.replay merge 4000 [Api.evaluate, Api.flush]).machine.forks
#eval (Api.replay mergeAll 4000 [Api.evaluate, Api.flush]).machine.forks
end MergeSites
