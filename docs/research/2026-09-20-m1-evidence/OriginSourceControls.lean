import Effect4.Program.Compile

/-! Finite Phase A source provenance controls. Compile separately after the source tree
is built. These controls exercise actual source paths and the two entrant race cursor. -/
namespace Effect4.Program.PhaseA.OriginSourceControls
open Effect4 Effect4.Machine

def options : Supervision.ForkOptions := ⟨true, false, .interruptible⟩
def child : NativeEff := .succeed (.lit (.nat 1))
def forkProgram : NativeEff := .withFiber (.fork child options)
def forkInProgram : NativeEff := .withFiber (.forkIn child options (.var 0))
def scopedProgram : NativeEff := .withFiber (.forkScoped child options)
def raceProgram : NativeEff := .withFiber (.raceAll
  (.cons (.fail (.lit (.nat 7))) (.cons child .nil)))

def actionSite : Option NAction → Option (List Nat)
  | some (.fork _ _ site) => some site
  | some (.forkIn _ _ _ site) => some site
  | some (.forkScoped _ _ site) => some site
  | _ => none

def raceSite : Option NAction → Option (List Nat)
  | some (.raceAll _ site) => site
  | _ => none

#guard actionSite (actionAt forkProgram (rootPoint 100)) = some [0]
#guard actionSite (actionAt forkInProgram
  { rootPoint 100 with env := [Val.scopeHandle 7] }) = some [0]
#guard actionSite (forkScopedAt scopedProgram (rootPoint 100) 7) = some [0]
#guard raceSite (actionAt raceProgram (rootPoint 100)) = some [0, 0]

abbrev Machine := RunMachine EffName EffThunk Val Err Defect FiberId Ann Ctx Stores

def run (program : NativeEff) : Machine :=
  (runFork (interpOf program) 2000 (RunMachine.empty Stores.empty : Machine)
    (compile program 2000) emptyCtx).1

#guard (run forkProgram).fibers.map (·.origin) = [.root, .forked ⟨0⟩ false [0]]
#guard (run raceProgram).fibers.map (·.origin) =
  [.root, .forked ⟨0⟩ true [0, 0], .forked ⟨0⟩ true [0, 0, 1]]

end Effect4.Program.PhaseA.OriginSourceControls
