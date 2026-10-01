import Test.Program.ExitTypeLane

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace SideAudit.Layer
open Effect4 Effect4.Machine Effect4.Program
open Test.Program.ExitTypeLane (lanePrograms)

def layerSites (p : NativeEff) : List (LayerTerm NativeOp × List Nat) :=
  foldMapAt_eff [] (· ++ ·) [] p (f_layer := fun l q => [(l, q)])

def missingServiceLeaves : List (String × List Nat) :=
  lanePrograms.flatMap fun e =>
    if Api.wellTyped e.program e.table then
      (layerSites e.program.expandRefs).filterMap fun (l, q) =>
        match l with
        | .effect key _ | .succeed key _ =>
          if ((nativeSignature e.table).serviceTy key).isNone then some (e.name, q) else none
        | _ => none
    else []

#eval missingServiceLeaves.length
#eval missingServiceLeaves

-- The lane's existing detector explicitly misses these proposed new refusals.
def unknownKey : ServiceKey := ⟨⟨40⟩, ⟨40⟩⟩
def untypedSucceed : NativeEff :=
  .provideLayer (.succeed unknownKey (.nat 5)) false (.succeed (.lit .unit))
def untypedEffect : NativeEff :=
  .provideLayer (.effect unknownKey (.succeed (.lit (.nat 5)))) false (.succeed (.lit .unit))
#guard Api.wellTyped untypedSucceed
#guard Api.wellTyped untypedEffect
#guard (nativeSignature []).serviceTy unknownKey = none

-- Slice-1 green controls: the lexical environment alone is reset, at layer entry.
def k : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩
def dependency : ServiceKey := ⟨⟨5⟩, ⟨4⟩⟩
def bodyRetainsOuter (localBuild : Bool) : NativeEff :=
  .bind (.succeed (.lit (.bool false)))
    (.provideLayer (.effect k (.succeed (.lit (.nat 1)))) localBuild
      (.bind (.service k) (.succeed (.var 0))))
def serviceContextRetained (localBuild : Bool) : NativeEff :=
  .provideService dependency (.lit (.nat 5))
    (.provideLayer (.effect k (.service dependency)) localBuild (.service k))
#guard Api.wellTyped (bodyRetainsOuter false)
#guard Api.wellTyped (bodyRetainsOuter true)
#guard Api.wellTyped (serviceContextRetained false)
#guard Api.wellTyped (serviceContextRetained true)
#guard (Api.replay (bodyRetainsOuter false) 200 [Api.evaluate, Api.flush]).exit = some (.success (.bool false))
#guard (Api.replay (bodyRetainsOuter true) 200 [Api.evaluate, Api.flush]).exit = some (.success (.bool false))
#guard (Api.replay (serviceContextRetained false) 200 [Api.evaluate, Api.flush]).exit = some (.success (.nat 5))
#guard (Api.replay (serviceContextRetained true) 200 [Api.evaluate, Api.flush]).exit = some (.success (.nat 5))
end SideAudit.Layer
