import Test.Dogfood.Scenario.Atomic.StageObservation
import Effect4.Laws.Auto.KernelRfl

/-!
Concept: store-typing R4.
Consumer: the actual root controller of `Atomic.Store.shop_stages`.
The source controller forks seven fibers, awaits six requests, sleeps, stops its daemon and reads the window.
These source facts do not supply their own history invariant.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Test.Dogfood.Scenario.Atomic.RootSource
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto

/-- The actual root source head has the operation and operand fixed by its binder position. -/
def head (root : NativeEff) (binder : Nat) : Bool :=
  match Node.at_ (.eff root) (List.replicate binder 1) with
  | some (.eff (.bind (.withFiber (.fork _ _)) _)) => decide (binder < 9 ∨ binder = 15)
  | some (.eff (.bind (.awaitFiber (.var slot) .awaitValue) _)) =>
    decide ((9 ≤ binder ∧ binder < 14 ∧ slot = binder - 5) ∨ (binder = 16 ∧ slot = 15))
  | some (.eff (.bind (.perform .sleep (.lit (.nat 1500))) _)) => decide (binder = 14)
  | some (.eff (.bind (.withFiber (.interrupt (.var 3))) _)) => decide (binder = 17)
  | some (.eff (.perform .refGet (.var 0))) => decide (binder = 18)
  | _ => false

/-- The entire post-initialization root sequence uses precisely these source heads. -/
theorem census :
    (Store.shopProgram.map fun root => (List.range 16).all fun offset => head root (offset + 3)) = some true := by
  kernel_rfl

/-- Every actual post-prefix root source point has its checked operation shape. -/
theorem head_at (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (binder : Nat) (lower : 3 ≤ binder) (upper : binder ≤ 18) : head built.program binder = true := by
  have source : Store.shopProgram = some built.program := by
    unfold Store.shopProgram
    rw [(Api.Author.build_retains accepted).1]
    rfl
  have checked := census
  rw [source] at checked
  have small : binder - 3 < 16 := by omega
  have selected := List.all_eq_true.mp (Option.some.inj checked) (binder - 3) (List.mem_range.mpr small)
  have same : binder - 3 + 3 = binder := by omega
  simpa only [same] using selected
/-- The actual root source address exposes one of its five native operation forms. -/
theorem forms (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (binder : Nat) (lower : 3 ≤ binder) (upper : binder ≤ 18) :
    (∃ body options rest, (binder < 9 ∨ binder = 15) ∧
      Node.at_ (.eff built.program) (List.replicate binder 1) = some (.eff (.bind (.withFiber (.fork body options)) rest))) ∨
    (∃ slot rest, ((9 ≤ binder ∧ binder < 14 ∧ slot = binder - 5) ∨ (binder = 16 ∧ slot = 15)) ∧
      Node.at_ (.eff built.program) (List.replicate binder 1) = some (.eff (.bind (.awaitFiber (.var slot) .awaitValue) rest))) ∨
    (∃ rest, binder = 14 ∧ Node.at_ (.eff built.program) (List.replicate binder 1) =
      some (.eff (.bind (.perform .sleep (.lit (.nat 1500))) rest))) ∨
    (∃ rest, binder = 17 ∧ Node.at_ (.eff built.program) (List.replicate binder 1) =
      some (.eff (.bind (.withFiber (.interrupt (.var 3))) rest))) ∨
    (binder = 18 ∧ Node.at_ (.eff built.program) (List.replicate binder 1) = some (.eff (.perform .refGet (.var 0)))) := by
  have checked := head_at built accepted binder lower upper
  unfold head at checked
  split at checked
  · rename_i body options rest found
    exact .inl ⟨body, options, rest, of_decide_eq_true checked, found⟩
  · rename_i slot rest found
    exact .inr (.inl ⟨slot, rest, of_decide_eq_true checked, found⟩)
  · rename_i rest found
    exact .inr (.inr (.inl ⟨rest, of_decide_eq_true checked, found⟩))
  · rename_i rest found
    exact .inr (.inr (.inr (.inl ⟨rest, of_decide_eq_true checked, found⟩)))
  · rename_i found
    exact .inr (.inr (.inr (.inr ⟨of_decide_eq_true checked, found⟩)))
  · cases checked
end Test.Dogfood.Scenario.Atomic.RootSource
