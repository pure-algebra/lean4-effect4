import Effect4.Laws.Auto.KernelRfl

/-! Readers and a control for the kernel reflexivity tactic. -/

open Effect4.Laws.Auto

namespace Test.Program.KernelRfl

-- Reader: a symbolic value remains free during kernel reduction.
theorem symbolic_add_zero (n : Nat) : n + 0 = n := by kernel_rfl

/--
error: (kernel) declaration type mismatch, 'Test.Program.KernelRfl._example' has type
  ∀ (n : Nat), n + 1 = n + 1
but it is expected to have type
  ∀ (n : Nat), n + 1 = n
-/
#guard_msgs in
example (n : Nat) : n + 1 = n := by kernel_rfl

end Test.Program.KernelRfl
