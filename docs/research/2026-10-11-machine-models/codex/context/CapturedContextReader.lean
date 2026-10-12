import Effect4.Laws.Program.Typed.Context

/-!
Concept: residual-program-typing, R4 and R9; dependency of typed-state-reachable.
The reader uses the captured completion of the existing program arrow.
The negative control retains the ordinary position's missing value correlation.
It is conditional proof evidence, not an admitted closed-program counterexample.
-/
set_option autoImplicit false
namespace Test.TypedContextCapturedReader
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed Effect4.Program.Sched

-- The installed getter's saved callback has actual service coverage and membership.
example (world : Typed.World) (guaranteed : Env.Requirement) (ctx : Ctx)
    (payload : AmbientExit world
      (ambientInput (.capturedContext guaranteed) (.success (Val.context ctx)))
      (.capturedContext guaranteed) (.success (Val.context ctx)))
    (key : ServiceKey) (member : key ∈ guaranteed) :
    ServicesFit world ctx.services ∧ (ctx.services.getV key).isSome = true := by
  have captured := ambient_captured_context payload
  exact ⟨captured.1, captured.2 key member⟩

-- A context missing the guarantee cannot satisfy the captured completion.
example (world : Typed.World) (guaranteed : Env.Requirement) (ctx : Ctx)
    (missing : ¬ ctx.services.Satisfies guaranteed) :
    ¬ AmbientExit world
      (ambientInput (.capturedContext guaranteed) (.success (Val.context ctx)))
      (.capturedContext guaranteed) (.success (Val.context ctx)) := by
  intro payload
  exact missing (ambient_captured_context payload).2

-- The same missing context remains admitted by an ordinary coarse result position.
example (world : Typed.World) (available : Env.Requirement) (ctx : Ctx)
    (services : ServicesFit world ctx.services) (missing : ¬ ctx.services.Satisfies available) :
    AmbientExit world available (EffTy.pure .context, available, available)
      (.success (Val.context ctx)) ∧ ¬ ctx.services.Satisfies available := by
  refine ⟨⟨strongExit_success _ _ _ ?_, Row.subset_refl _⟩, missing⟩
  exact ⟨rfl, ctx, Val.context?_context ctx, services, live_context_of_servicesFit services⟩

end Test.TypedContextCapturedReader
