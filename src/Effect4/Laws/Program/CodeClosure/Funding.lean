import Effect4.Laws.Program.CodeClosure.Predicate
import Effect4.Laws.Machine.PrimWeights
import Effect4.Laws.Machine.FrameWeights

/-!
Concept: scope-lifetime-finalization R11.
Question: one callback-reservation producer over the generated code annotation.
Consumers: full finalizer source debit and the older source-opportunity restriction.
Unary success callbacks may receive a reservation at their recorded push.
Other callback slots retain their original name reservation.
The local arm bounds establish no command or history bound.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Effect4.Program.CodeClosure.Funding
open Effect4 Effect4.Machine Effect4.Program

abbrev current (weights : PrimWeights.Model EffName EffThunk) (code : NCode) : Nat :=
  cata_prim (PrimWeights.currentAlgebra weights) code

abbrev saved (weights : PrimWeights.Model EffName EffThunk) (successWeight : EffName → Nat) (code : NCode) : Nat :=
  (cata_prim (PrimWeights.pairedAlgebra weights successWeight) code).2

/-- Iterator bodies and continuations spend a single reservation. -/
def iterWeight (weights : PrimWeights.Model EffName EffThunk) :
    IterStep EffName EffThunk Val Err Defect FiberId Ann NCode → Nat
  | .resume body next => current weights body + weights.name next
  | _ => 0

/-- Repeated loop bodies receive no renewable selected-source reservation. -/
def loopWeight (weights : PrimWeights.Model EffName EffThunk) : LoopNext Val NCode → Nat
  | .continue _ body | .finish body => current weights body

/-- The actual interpreter hooks spend their callback slot's reserved weight. -/
structure Hooks (weights : PrimWeights.Model EffName EffThunk) (successWeight : EffName → Nat)
    (names successNames : EffName → Prop) (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann) : Prop where
  value : ∀ callback value, successNames callback → current weights (interp.contA callback value) ≤ successWeight callback
  bothValue : ∀ callback value, names callback → current weights (interp.contA callback value) ≤ weights.name callback
  cause : ∀ callback cause, names callback → current weights (interp.contE callback cause) ≤ weights.name callback
  iterator : ∀ callback value, names callback → iterWeight weights (interp.iterNext callback value).2 ≤ weights.name callback
  loop : ∀ callback cursor value, names callback → loopWeight weights (interp.loopResume callback cursor value) = 0
  cancel : ∀ callback cause, names callback → current weights (interp.cancelThenFail callback cause) ≤ weights.name callback

/-- Exit representations carry no active source reservation. -/
theorem exit_zero (weights : PrimWeights.Model EffName EffThunk) (exit : ExitV) :
    current weights (Prim.ofExit exit) = 0 := by
  cases exit <;> rfl

/-- The generated active projection of a constant continuation agrees with the scalar fold. -/
theorem constant_saved (weights : PrimWeights.Model EffName EffThunk) (successWeight : EffName → Nat)
    (body next : NCode) : saved weights successWeight (.onSuccessConst body next) = current weights next :=
  PrimWeights.paired_current weights successWeight next

/-- A value arm spends the saved reservation of its actual callback role. -/
theorem armA (weights : PrimWeights.Model EffName EffThunk) (successWeight : EffName → Nat)
    (names successNames : EffName → Prop) (thunks : EffThunk → Prop)
    (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann)
    (hooks : Hooks weights successWeight names successNames interp)
    (code : NCode) (value : Val) (provided : Option ExitV) (next : NCode) (pushed : List NCode)
    (held : RoleCode names successNames thunks code)
    (found : code.armA interp value provided = some (next, pushed)) :
    current weights next + (pushed.map (saved weights successWeight)).sum ≤ saved weights successWeight code := by
  revert found held
  fun_cases Prim.armA interp code value provided
  all_goals intro held found
  case case3 body onValue onCause =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
    change current weights (interp.contA onValue value) + 0 ≤ weights.name onValue + weights.name onCause
    have bound := hooks.bothValue onValue value held.2.1
    omega
  case case10 generator cursor body next selected =>
    have bound := hooks.iterator generator value held
    rw [selected] at bound
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
    exact bound
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [saved, current, cata_prim, PrimWeights.paired_current, iterWeight, loopWeight, exit_zero]) (add safe apply [hooks.value]) (add safe forward [hooks.loop]) (add safe tactic (by omega))

/-- A cause arm spends its actual saved handler reservation. -/
theorem armE (weights : PrimWeights.Model EffName EffThunk) (successWeight : EffName → Nat)
    (names successNames : EffName → Prop) (thunks : EffThunk → Prop)
    (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann)
    (hooks : Hooks weights successWeight names successNames interp)
    (code : NCode) (cause : CauseV) (provided : Option ExitV) (next : NCode) (pushed : List NCode)
    (held : RoleCode names successNames thunks code)
    (found : code.armE interp cause provided = some (next, pushed)) :
    current weights next + (pushed.map (saved weights successWeight)).sum ≤ saved weights successWeight code := by
  revert found held
  fun_cases Prim.armE interp code cause provided
  all_goals intro held found
  case case2 body onValue onCause =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
    change current weights (interp.contE onCause cause) + 0 ≤ weights.name onValue + weights.name onCause
    have bound := hooks.cause onCause cause held.2.2
    omega
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [saved, current, cata_prim, PrimWeights.paired_current, exit_zero]) (add safe apply [hooks.cause, hooks.cancel]) (add safe tactic (by omega))

end Effect4.Program.CodeClosure.Funding
