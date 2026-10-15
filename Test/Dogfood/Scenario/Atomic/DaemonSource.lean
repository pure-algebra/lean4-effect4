import Test.Dogfood.Scenario.Atomic.RootFork

/-!
Concept: store-typing R4.
Consumer: the actual Atomic daemon loop and its refill primitive producer.
The finite source reader identifies the one sleep and the one window reset.
This source equality does not establish a history invariant.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Test.Dogfood.Scenario.Atomic.DaemonSource
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto

def body : NativeEff := .bind (.perform .sleep (.lit (.nat 1000)))
  (.perform (.refUpdateWith (Store.refillAt 5)) (.var 0))

def program : NativeEff := .iterate none (.lit (.bool true)) (.lit (.bool true)) (.var 3) (.var 3) body

theorem source_census : (Store.shopProgram.bind fun root => Node.at_ (.eff root) (StageSource.bodyPath 0)) =
    some (.eff program) := by
  kernel_rfl

/-- The detached daemon starts with exactly its authored infinite refill loop. -/
theorem source_at (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built) :
    Node.at_ (.eff built.program) (StageSource.bodyPath 0) = some (.eff program) := by
  have source : Store.shopProgram = some built.program := by
    unfold Store.shopProgram
    rw [(Api.Author.build_retains accepted).1]
    rfl
  have checked := source_census
  rw [source] at checked
  exact checked
end Test.Dogfood.Scenario.Atomic.DaemonSource
