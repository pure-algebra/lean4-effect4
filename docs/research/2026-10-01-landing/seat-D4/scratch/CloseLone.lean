import Effect4.Laws.Program.RuntimeR
import Effect4.Laws.Program.Typed.Assembly
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched

def closeLone : NativeEff :=
  .scoped
    (.bind (.acquireRelease (.succeed (.lit (.nat 1))) (.succeed (.lit (.nat 5))))
      (.bind (.service nativeScopeKey)
        (.bind (.exit (.succeed (.lit .unit)))
          (.withFiber (.closeScope (.var 1) (.var 2))))))

def machineOf : RReplay → RState
  | .finished m | .frontier _ m | .stuck _ m => m
def termExit (p : NativeEff) (tape : List Api.Decision) : Option ExitV :=
  ((machineOf (replayR p 200 tape)).fiber? Api.root).bind RunFiber.exit
def frameExit (p : NativeEff) (tape : List Api.Decision) : Option ExitV :=
  (Api.replay p 200 tape).exit

#guard Program.typeOfProgram (closeLone : Effect4.Program.Typed.ProgramSource).signature closeLone == some ⟨.unit, .never, .empty⟩
#guard frameExit closeLone [Api.evaluate, Api.flush] == some (.success .unit)
#guard frameExit closeLone [Api.evaluate, Api.flush] != some (.success (.nat 5))
#guard termExit closeLone [Api.evaluate, Api.flush] == some (.success .unit)
#eval Api.wellTyped closeLone
