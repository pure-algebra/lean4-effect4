import Effect4.Laws.Program.Typed.Stack

/-! H2 part two: the original isolated error-column diagnostic, followed by the audit's
saved-frame witness in namespace AuditH2. The first subsection alone has no frame; the
second checks one accepted saved loop and its returned failure. Neither supplies a
reachable run from checked source or refutes the existing FitsExit theorem. -/

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

namespace AuditH2
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed.Contracts SideAudit.H2.MissingServiceTransport
abbrev W := Effect4.Program.Typed.World
def inner : EffTy := ⟨.never, .never, Env.Requirement.single nativeScopeKey⟩
def outer : EffTy := EffTy.pure .unit
def name : EffName := .abort
def saved : RSaved := ⟨.pure (.success .unit), [], false, none, false⟩
theorem loop_admitted (src : ProgramSource) (w : W) :
    StackAccepts (TypedProg src) ExitOk (frameProtocols src) w inner outer [.loop name .unit] := by
  apply StackAccepts.cons (middle := outer)
  · apply FrameAccepts.loop
    exact LoopProtocol.step (tin := inner) (tout := outer) rfl (fun _ h => False.elim h)
  · exact StackAccepts.nil outer

theorem input_ok (w : W) : ExitOk w inner (.failure missing) :=
  ⟨fitsExit_of_clean w inner missing rfl, rfl⟩

theorem provenance : InterruptProvenance saved := by
  constructor
  · intro c h
    cases h
  · intro h
    cases h

theorem output_eq (interp : RInterp) :
    (popR interp (.failure missing) [.loop name .unit] saved).2 = some (.failure missing) := rfl

theorem output_bad (w : W) : ¬ ExitOk w outer (.failure missing) := excluded_outside w

#print axioms loop_admitted
#print axioms input_ok
#print axioms provenance
#print axioms output_eq
#print axioms output_bad
end AuditH2
