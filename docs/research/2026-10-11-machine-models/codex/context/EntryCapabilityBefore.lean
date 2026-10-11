import Effect4.Laws.Program.Typed.Context

/-!
Concept: residual-program-typing, R4; dependency of typed-state-reachable.
Control: completion typing alone does not establish interruption coverage at entry.
This checked pre-refinement reader uses the shared ProgramArrow at commit 2b974a2fc.
It records no execution history or source admission claim.
-/
set_option autoImplicit false
namespace Test.TypedContextEntryBefore
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed Effect4.Program.Sched

example (root : ProgramSource) (world : Typed.World) (available missing : Env.Requirement)
    (absent : ¬ Row.Subset missing available) :
    AmbientProg root world available (EffTy.pure .unit, available, missing)
      (.pure (.success Val.unit)) ∧
      ¬ Row.Subset ((EffTy.pure .unit, available, missing) : AmbientPosition).2.2 available :=
  ⟨.pure ⟨strongExit_success _ _ _ trivial, Row.subset_refl available⟩, absent⟩

end Test.TypedContextEntryBefore
