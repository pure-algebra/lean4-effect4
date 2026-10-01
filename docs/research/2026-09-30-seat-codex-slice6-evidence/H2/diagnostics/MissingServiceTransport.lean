import Effect4.Laws.Program.Typed.Membership

/-! An isolated statement diagnostic for H2 part two. This supplies no saved frame,
reachable run, or counterexample to `popR_typed`. It tests only whether equality of error
columns transports a requirement-dependent exit exclusion. -/

set_option autoImplicit false
namespace SideAudit.H2.MissingServiceTransport
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed
abbrev W := Effect4.Program.Typed.World

def forbidden (ty : EffTy) : Reason Err Defect FiberId Ann → Bool
  | .die defect _ => defect == .badName || defect == .notImplemented ||
      (defect == .missingService && ty.requires == Env.Requirement.empty)
  | _ => false

def NoShapeDefect (ty : EffTy) : ExitV → Prop
  | .success _ => True
  | .failure cause => cause.reasons.any (forbidden ty) = false

def ExitOk (w : W) (ty : EffTy) (ex : ExitV) : Prop :=
  FitsExit w ty ex ∧ NoShapeDefect ty ex

def requiredTy : EffTy := ⟨.unit, .never, Env.Requirement.single nativeScopeKey⟩
def closedTy : EffTy := EffTy.pure .unit
def missing : CauseV := Cause.die .missingService

theorem same_error : requiredTy.error = closedTy.error := rfl

theorem requirements_differ : requiredTy.requires ≠ closedTy.requires := by decide

/-- The proposed part-two condition allows this defect with a nonempty requirement row. -/
theorem allowed_inside (w : W) : ExitOk w requiredTy (.failure missing) := by
  refine ⟨fitsExit_of_clean w requiredTy missing rfl, ?_⟩
  rfl

/-- The same exit is excluded at an empty requirement row. -/
theorem excluded_outside (w : W) : ¬ ExitOk w closedTy (.failure missing) := by
  intro h
  have impossible := h.2
  change true = false at impossible
  exact Bool.noConfusion impossible

/-- The error-column-only helper cannot be retained for the full part-two condition.
This does not refute the stack walk: there is no admitted frame or service evidence here. -/
theorem failure_of_error_refuted (w : W) :
    ¬ (∀ (tin tout : EffTy) (cause : CauseV), tin.error = tout.error →
      ExitOk w tin (.failure cause) → ExitOk w tout (.failure cause)) := by
  intro transport
  exact excluded_outside w
    (transport requiredTy closedTy missing same_error (allowed_inside w))

#print axioms same_error
#print axioms requirements_differ
#print axioms allowed_inside
#print axioms excluded_outside
#print axioms failure_of_error_refuted
end SideAudit.H2.MissingServiceTransport
