import Effect4.Laws.Program.Typed.Assembly

/-! Seat TYPES (formal pass, 2026-10-01), a tooling fact the other probes use.

`Ty.sub` is well-founded recursion, so plain `decide` and `rfl` do not evaluate it (the comment
at `Laws/Program/Template.lean:332-333` says so, and adds that the kernel does not reduce it). `decide +kernel` does: the kernel unfolds the
recursion. So a concrete fact about `sub`, `normalize`, `join` or the checker can be certified
directly, which makes counterexamples and fixtures cheap (`M5CounterProbe.lean` uses it for the
checker's answer). Also printed: the generated whole-state predicate's shape. -/

set_option autoImplicit false
open Effect4 Effect4.Program Effect4.Program.Typed

theorem k1 : Ty.sub .nat .string = false := by decide +kernel
theorem k2 : Ty.join .nat .string = .union .nat .string := by decide +kernel
theorem k3 : Sched.GuardKind.hasExitArm .onSuccess (.success (Effect4.Machine.Val.fiber ⟨1⟩)) = true := rfl

#print Effect4.Program.Typed.RStateOk
#print Effect4.Program.Typed.RSavedOk
#print axioms k1
#print axioms k2
#print axioms k3
