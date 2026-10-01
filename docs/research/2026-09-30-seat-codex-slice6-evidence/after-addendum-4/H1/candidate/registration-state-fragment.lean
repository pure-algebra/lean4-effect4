/-- A concrete reply must meet the actual saved stack, independently of whatever type
certified the current administrative operation. This names a local delivery boundary. -/
def StackReply (root : ProgramSource) (w : World) (fiber : RFiber) (replyTy : EffTy) : Prop :=
  ∃ final, w.Γ fiber.id = some final ∧
    Contracts.StackAccepts (TypedProg root) FitsExit (frameProtocols root) w replyTy final
      fiber.frame.stack ∧ Contracts.InterruptProvenance fiber.frame

/-- The direct registration marker owns a real race on this fiber, and the race token's
result meets this host's saved continuation. This finite current-code clause covers both
immediate buffered settlement and parking; it is not the open recursive code-site scan. -/
def RegistrationState (root : ProgramSource) (w : World) (m : RState) : Prop :=
  ∀ fiber ∈ m.fibers, ∀ raceId, raceRegistrationR fiber.frame.current = some raceId →
    ∃ race resultTy, m.race? raceId = some race ∧ race.host = fiber.id ∧
      w.Θ race.host race.token = some resultTy ∧ StackReply root w fiber resultTy

/-- A loaded code with no direct registration marker needs no race/token correlation yet. -/
theorem registrationState_load (root : ProgramSource) (w : World) (fuel compileFuel : Nat)
    (noMarker : raceRegistrationR (denoteR root.program root.program (rootPoint compileFuel)) = none) :
    RegistrationState root w (loadR root.program fuel compileFuel) := by
  intro fiber hf raceId marker
  change fiber ∈ [_] at hf
  rw [List.mem_singleton] at hf
  subst fiber
  change raceRegistrationR (denoteR root.program root.program (rootPoint compileFuel)) = some raceId at marker
  rw [noMarker] at marker
  cases marker

