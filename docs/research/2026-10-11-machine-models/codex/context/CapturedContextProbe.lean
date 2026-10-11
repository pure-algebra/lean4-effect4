import Effect4.Laws.Program.Typed.Context

/-!
Concept: residual-program-typing, R4 and R9, dependency of typed-state-reachable.
This probe uses the existing ProgramArrow with a captured-getter completion index.
It checks a value-correlated input for the provider's saved onSuccess callback.
It adds no stored program, world, evaluator or configuration relation.
The core ambient position remains unchanged pending coordinator review.
-/
set_option autoImplicit false
namespace Test.TypedContextCapturedProbe
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed Effect4.Program.Sched

private def inputOf (guaranteed : Env.Requirement) : ExitV → Env.Requirement
  | .success value => match Val.context? value with
    | some ctx => ctx.services.keysRow
    | none => guaranteed
  | .failure _ => guaranteed

private def exitAt (world : Typed.World) (available guaranteed : Env.Requirement) (exit : ExitV) : Prop :=
  ExitOk world (EffTy.pure .context) exit ∧ Row.Subset guaranteed available ∧
    Row.Subset (inputOf guaranteed exit) available

private abbrev CaptureProg (root : ProgramSource) :=
  ProgramArrow (fun world (_ : Env.Requirement) => storePre root world)
    (fun world (_ : Env.Requirement) => storePost world)
    (ambientFiberPre root) ambientFiberPost ambientFiberInput exitAt
    (fun world available kind row exit => kind.hasExitArm exit = true ∧ exitAt world available row exit)
    inputOf (fun ctx => ctx.services.keysRow) (fun available row => Row.Subset row available)

-- The actual getter's postcondition constructs this completion using the same program arrow.
example (root : ProgramSource) (world : Typed.World) (available : Env.Requirement) :
    CaptureProg root world available available (fiberValR .getContext rfl) := by
  refine .fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) .context (.inl rfl) ?_ (Row.subset_refl available)
  intro later ordered answer post
  obtain ⟨members, ctx, decoded, coverage⟩ := post
  have bound := (Provision.satisfies_iff_subset_keysRow ctx.services available).mp coverage
  change CaptureProg root later (match Val.context? answer with
    | some ctx => ctx.services.keysRow
    | none => available) available (.pure (.success answer))
  rw [decoded]
  refine .pure ⟨strongExit_success _ _ _ members, bound, ?_⟩ bound
  change Row.Subset (match Val.context? answer with
    | some ctx => ctx.services.keysRow
    | none => available) ctx.services.keysRow
  rw [decoded]
  exact Row.subset_refl _

-- At its saved callback cut, the returned context covers the original guarantee.
example (world : Typed.World) (guaranteed : Env.Requirement) (ctx : Ctx)
    (payload : exitAt world (inputOf guaranteed (.success (Val.context ctx))) guaranteed
      (.success (Val.context ctx))) : ctx.services.Satisfies guaranteed := by
  have covered := payload.2.1
  change Row.Subset (guaranteed) (match Val.context? (Val.context ctx) with
    | some ctx => ctx.services.keysRow
    | none => guaranteed) at covered
  rw [Val.context?_context] at covered
  exact (Provision.satisfies_iff_subset_keysRow _ guaranteed).mpr covered

-- The ordinary static position records current services, not ownership of a returned context.
example (world : Typed.World) (available : Env.Requirement) (ctx : Ctx)
    (services : ServicesFit world ctx.services) (missing : ¬ ctx.services.Satisfies available) :
    AmbientExit world available (EffTy.pure .context, available, available)
      (.success (Val.context ctx)) ∧ ¬ ctx.services.Satisfies available := by
  refine ⟨⟨strongExit_success _ _ _ ?_, Row.subset_refl _⟩, missing⟩
  exact ⟨rfl, ctx, Val.context?_context ctx, services, live_context_of_servicesFit services⟩

end Test.TypedContextCapturedProbe
