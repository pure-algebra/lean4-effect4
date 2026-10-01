import Effect4.Laws.Program.RuntimeR

/-!
E4-PROV-CE-005: a layer's effect body starts in the empty lexical environment
used by its checker. The former runtime entry inherited the enclosing binders,
so a locally bound variable could read an unrelated outer value instead.

These are finite runs at budget 200 with an empty table and no host answers.
Concrete executions are finite `#guard` checks. The theorem below transports
every fiber exit through the existing native/reference agreement at that boundary. The layer body is closed, while the program under the layer
retains its enclosing binders and the layer retains its service context.
Sources: the retained registry LayerGap/verify-Gaps probes and LayerControls.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Test.Counterexamples.Runtime.LayerEnvironment
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched

abbrev E := Eff NativeOp

def n (i : Nat) : Term := .lit (.nat i)
def s (x : String) : Term := .lit (.str x)
def key : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩
def dependency : ServiceKey := ⟨⟨5⟩, ⟨4⟩⟩
def tape : List Api.Decision := [Api.evaluate, Api.flush]

/-- The layer's own level zero is the string, despite the enclosing number. -/
def errLeak : E :=
  .bind (.succeed (n 9))
    (.scoped (.provideLayer (.effect key (.bind (.succeed (s "x")) (.fail (.var 0)))) false
      (.service key)))

/-- The same layer without an enclosing binder. -/
def errLeakControl : E :=
  .scoped (.provideLayer (.effect key (.bind (.succeed (s "x")) (.fail (.var 0)))) false
    (.service key))

/-- The fork inside the layer is checked with its string at level zero. -/
def forkLeak : E :=
  .bind (.succeed (n 9))
    (.scoped (.provideLayer
      (.effect key (.bind (.succeed (s "x"))
        (.bind (.withFiber (.fork (.succeed (.var 0)) ⟨true, false, .inherit⟩))
          (.bind (.awaitFiber (.var 1) .joinEffect) (.succeed (n 1))))))
      false (.service key)))

/-- Discarding the layer result does not change its lexical environment. -/
def discardLeak : E :=
  .bind (.succeed (n 9))
    (.scoped (.provideLayer (.effectDiscard (.bind (.succeed (s "x")) (.fail (.var 0)))) false
      (.succeed (.lit .unit))))

/-- Reading the layer's own number makes successor return two. -/
def crash1 : E :=
  .bind (.succeed (s "s"))
    (.scoped (.provideLayer
      (.effect key (.bind (.succeed (n 1))
        (.succeed (.app "succ" (.cons (.var 0) .nil)))))
      false (.service key)))

/-- A closed successful layer remains a control. -/
def valueControl : E :=
  .scoped (.provideLayer (.effect key (.succeed (n 5))) false (.service key))

/-- Resetting the layer entry must leave the program body's enclosing binder intact. -/
def bodyRetainsOuter (localBuild : Bool) : E :=
  .bind (.succeed (.lit (.bool false)))
    (.provideLayer (.effect key (.succeed (n 1))) localBuild
      (.bind (.service key) (.succeed (.var 0))))

/-- The lexical reset must retain the service context needed to build the layer. -/
def serviceContextRetained (localBuild : Bool) : E :=
  .provideService dependency (n 5)
    (.provideLayer (.effect key (.service dependency)) localBuild (.service key))

def firstFail (ex : Option ExitV) : Option Val :=
  ex.bind fun e => match e with
    | .failure c => firstErrorValue? c
    | .success _ => none

/-- Fixture check: the successful payload, or every typed failure with no other reasons,
fits the checked columns. This is not a general exit-admission judgment. -/
def rootFits (p : E) : Option Bool :=
  (Api.typeOf p []).bind fun ty =>
    let r := Api.replay p 200 tape
    r.exit.map fun ex => match ex with
      | .success v => Val.hasTy v ty.answer r.machine.state.externals.allocated
      | .failure c =>
          causeAdmits (fun v t => Val.hasTy v t r.machine.state.externals.allocated) ty.error c &&
            c.reasons.all (fun reason => reason.tag == .fail)

theorem key_service_nat : (nativeSignature []).serviceTy key = some .nat := by
  decide +kernel

theorem errLeak_checked :
    Api.typeOf errLeak [] = some ⟨.nat, .string, Env.Requirement.empty⟩ := by
  decide +kernel

theorem forkLeak_checked :
    Api.typeOf forkLeak [] = some (EffTy.pure .nat) := by
  decide +kernel

theorem forkLeak_handle :
    (Checker.checkAction (nativeSignature []) [.string] [] (.fork (.succeed (.var 0) : E)
      ⟨true, false, .inherit⟩)).toOption.map (·.answer) = some (.fiberOf .string .never) := by
  decide +kernel

theorem discardLeak_checked :
    Api.typeOf discardLeak [] = some ⟨.unit, .string, Env.Requirement.empty⟩ := by
  decide +kernel

theorem crash1_checked : Api.typeOf crash1 [] = some (EffTy.pure .nat) := by
  decide +kernel

#guard [errLeak, forkLeak, discardLeak, crash1, errLeakControl, valueControl].all fun p =>
  (admitProgram p []).toOption.isSome

/-- Native and reference fiber exits agree at the empty table and without host answers.
Concrete outcomes below are executable checks, not kernel reductions of whole runs. -/
theorem fiber_exit_agreement (program : NativeEff) (fuel : Nat)
    (decisions : List Api.Decision) (id : FiberId) :
    ((Api.replay program fuel decisions).machine.fiber? id).bind RunFiber.exit =
      ((replayR program fuel decisions).machine.fiber? id).bind RunFiber.exit := by
  rw [replay_machine]
  exact BMeans.exitOf (ReplayRel.machine (replay_rel program fuel fuel decisions)) id

-- The former outer number is replaced by the layer's declared string failure.
#guard firstFail (Api.replay errLeak 200 tape).exit = some (.str "x")
#guard firstFail (((replayR errLeak 200 tape).machine.fiber? Api.root).bind RunFiber.exit) =
  some (.str "x")

-- The child returns a string, as declared by forkLeak_handle.
#guard ((Api.replay forkLeak 200 tape).machine.fiber? ⟨1⟩).bind RunFiber.exit =
  some (.success (.str "x"))
#guard ((replayR forkLeak 200 tape).machine.fiber? ⟨1⟩).bind RunFiber.exit =
  some (.success (.str "x"))

#guard firstFail (Api.replay discardLeak 200 tape).exit = some (.str "x")
#guard firstFail (((replayR discardLeak 200 tape).machine.fiber? Api.root).bind RunFiber.exit) =
  some (.str "x")

#guard (Api.replay crash1 200 tape).exit = some (.success (.nat 2))
#guard ((replayR crash1 200 tape).machine.fiber? Api.root).bind RunFiber.exit =
  some (.success (.nat 2))

#guard [errLeak, forkLeak, discardLeak, crash1].all (fun p => rootFits p == some true)

-- Closed layer controls retain their original outcomes and checked payload types.
#guard firstFail (Api.replay errLeakControl 200 tape).exit = some (.str "x")
#guard firstFail (((replayR errLeakControl 200 tape).machine.fiber? Api.root).bind RunFiber.exit) =
  some (.str "x")
#guard (Api.replay valueControl 200 tape).exit = some (.success (.nat 5))
#guard ((replayR valueControl 200 tape).machine.fiber? Api.root).bind RunFiber.exit =
  some (.success (.nat 5))
#guard rootFits errLeakControl = some true
#guard rootFits valueControl = some true

#guard Api.wellTyped (bodyRetainsOuter false)
#guard Api.wellTyped (bodyRetainsOuter true)
#guard Api.wellTyped (serviceContextRetained false)
#guard Api.wellTyped (serviceContextRetained true)

#guard (Api.replay (bodyRetainsOuter false) 200 tape).exit = some (.success (.bool false))
#guard (Api.replay (bodyRetainsOuter true) 200 tape).exit = some (.success (.bool false))
#guard ((replayR (bodyRetainsOuter false) 200 tape).machine.fiber? Api.root).bind RunFiber.exit =
  some (.success (.bool false))
#guard ((replayR (bodyRetainsOuter true) 200 tape).machine.fiber? Api.root).bind RunFiber.exit =
  some (.success (.bool false))
#guard (Api.replay (serviceContextRetained false) 200 tape).exit = some (.success (.nat 5))
#guard (Api.replay (serviceContextRetained true) 200 tape).exit = some (.success (.nat 5))
#guard ((replayR (serviceContextRetained false) 200 tape).machine.fiber? Api.root).bind RunFiber.exit =
  some (.success (.nat 5))
#guard ((replayR (serviceContextRetained true) 200 tape).machine.fiber? Api.root).bind RunFiber.exit =
  some (.success (.nat 5))

#print axioms key_service_nat
#print axioms errLeak_checked
#print axioms forkLeak_checked
#print axioms forkLeak_handle
#print axioms discardLeak_checked
#print axioms crash1_checked
#print axioms fiber_exit_agreement

end Test.Counterexamples.Runtime.LayerEnvironment
