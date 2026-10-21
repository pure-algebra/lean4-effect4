import Effect4.Api.Session
import Effect4.Laws.Api.Object
import Effect4.Laws.Auto.Inversion
import Effect4.Laws.Auto.Semantics

/-!
# Checked service-session construction

Placement: host-session-protocol, compatibility, R6 and R13.
`service-session-checked` states exact construction, admission and closed requirements.
`service-session-retains` states the retained block and signature fields.
Consumers are the public constructor, positional callers and the permanent session battery.
The replaced main program need not keep its behaviour. No progress, physical I/O or arbitrary
service acceptance follows. The placement precedes proof work in the session landing plan.
-/

set_option autoImplicit false
namespace Effect4.Api
open Effect4.Program

/-- Helper of service-session-checked. The permanent negative battery reads this exact
admission refusal, without erasing its location or reason. -/
theorem ServiceSession.finish_admission_error_iff (object : Object) (why : AdmitRefusal) :
    ServiceSession.finish object = .error (SessionRefusal.admission why) ↔ object.open = .error why := by
  unfold ServiceSession.finish
  cases opened : object.open with
  | error refusal =>
    change (Except.error (SessionRefusal.admission refusal) : Except SessionRefusal Built) =
      .error (SessionRefusal.admission why) ↔
        Except.error refusal = (Except.error why : Except AdmitRefusal Built)
    aesop
  | ok built =>
    change (if built.requires.isEmpty then Except.ok built
      else .error (SessionRefusal.requirements [1] built.requires)) =
        .error (SessionRefusal.admission why) ↔
        Except.ok built = (Except.error why : Except AdmitRefusal Built)
    split <;> aesop

/-- service-session-checked: construction succeeds exactly when its candidate opens as the
result and that result has no remaining service requirements. -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem Built.session_ok_iff (before : Built) (name : String) (after : Built) :
    before.session name = .ok after ↔
      ∃ object, ServiceSession.candidate before name = .ok object ∧
        object.open = .ok after ∧ after.requires = [] := by
  change (ServiceSession.candidate before name >>= ServiceSession.finish) = .ok after ↔ _
  rw [Effect4.Laws.Auto.bind_eq_ok]
  constructor
  · rintro ⟨object, hc, hf⟩
    unfold ServiceSession.finish at hf
    obtain ⟨built, ho, hr⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hf
    have opened := Effect4.Laws.Auto.mapError_eq_ok.mp ho
    split at hr
    · have same := Effect4.Laws.Auto.pure_eq_ok.mp hr
      subst built
      exact ⟨object, hc, opened, List.isEmpty_iff.mp ‹after.requires.isEmpty = true›⟩
    · cases hr
  · rintro ⟨object, hc, ho, hr⟩
    refine ⟨object, hc, ?_⟩
    unfold ServiceSession.finish
    rw [ho]
    change (if after.requires.isEmpty then Except.ok after
      else .error (SessionRefusal.requirements [1] after.requires)) = .ok after
    aesop

/-- service-session-retains: successful construction replaces the main program, retains the
rest of its block and signature, and appends rows after all existing external positions. -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem Built.session_retains {before after : Built} {name : String}
    (h : before.session name = .ok after) :
    ∃ decls bodies oldMain newMain layers appended,
      before.program = .defs decls bodies oldMain layers ∧
      after.program = .defs decls bodies newMain layers ∧
      after.app = { before.app with rows := before.table ++ appended } := by
  obtain ⟨object, hc, ho, _⟩ := (Built.session_ok_iff before name after).mp h
  have retained := Object.ofBuilt_of_open ho
  unfold ServiceSession.candidate at hc
  obtain ⟨services, _, hc⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hc
  split at hc
  next service selected =>
    split at hc
    next decls bodies oldMain layers block =>
      split at hc
      next init initial =>
        obtain ⟨appended, _, hc⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hc
        obtain ⟨newMain, _, hc⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hc
        have made := Effect4.Laws.Auto.pure_eq_ok.mp hc
        have source : before.program = .defs decls bodies oldMain layers := by
          unfold Eff.block? at block
          split at block
          · aesop
          · cases block
        have exactObject := retained.trans made.symm
        exact ⟨decls, bodies, oldMain, newMain, layers, appended, source,
          congrArg Object.program exactObject, congrArg Object.app exactObject⟩
      next => cases hc
    next => cases hc
  next => cases hc

end Effect4.Api
