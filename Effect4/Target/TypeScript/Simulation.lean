import Effect4.Runtime.Runtime
import Effect4.Concurrency.Scheduler
import Effect4.Semantics.Observation

/-!
# Target.TypeScript.Simulation

Owner: the projections from the frame machine's alphabet (`Effect4.FrameEvent`,
`Effect4/Runtime/Runtime.lean`) and the scheduler's alphabet (`Effect4.Event`,
`Effect4/Concurrency/Scheduler.lean`) into the shared service-level trace
alphabet (`Effect4.Trace.Event`, `Effect4/Semantics/Observation.lean`). This
is the one module allowed to see both sides (`docs/FRAMES-DAG.md` separation
7; `docs/TRACE-DAG.md` edge `bridges`).

Only finalizers and outcomes project: a `ranFinalizer` becomes `finalizer`
with the exit it observed, a `yielded` exit becomes `done`, a scheduler
`completed` becomes `done`; everything else is a frame or scheduler fact with
no service-level shadow and projects to `none`. No simulation is claimed: the
projections state what a frame-level or scheduler-level observation *would*
say in the service-level alphabet, so that a future bridge theorem has a
statement to make. The host side (`harness/trace/patched/`) records the
corresponding rc.112 rows in receipts; they are evidence of nothing yet.
-/

namespace Effect4

open Effects.Trace (Val Outcome)

/-- The outcome of an exit: the value, the first failure's error, or an
interruption; a defect with no failure before it projects through `defect`. -/
def Exit.toOutcome {β : Type v} {ε δ ι α : Type u}
    (value : β → Val) (error : ε → Val) (defect : δ → Val) : Exit β ε δ ι α → Outcome Val
  | .success v => .success (value v)
  | .failure cause =>
      match cause.reasons.find? (fun reason => reason.tag = ReasonTag.fail) with
      | some (.fail e _) => .failure (error e)
      | _ =>
          if cause.reasons.any (fun reason => reason.tag = ReasonTag.interrupt) then .interrupted
          else
            match cause.reasons.find? (fun reason => reason.tag = ReasonTag.die) with
            | some (.die d _) => .failure (defect d)
            | _ => .interrupted

/-- The service-level shadow of a frame event: finalizers and the yielded
exit; nothing else. `region` names the region a finalizer belongs to. -/
def FrameEvent.toTrace {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}
    (region : ν → Nat) (value : β → Val) (error : ε → Val) (defect : δ → Val) :
    FrameEvent ν σ β ε δ ι α → Option Effect4.Trace.Event
  | .ranFinalizer finalizer exit =>
      some (.finalizer (region finalizer) (Exit.toOutcome value error defect exit))
  | .yielded exit => some (.done (Exit.toOutcome value error defect exit))
  | _ => none

/-- The service-level shadow of a scheduler event: a completed fiber's
result, as the outcome; scheduling, joins, interrupts and masks have none. -/
def Event.toTrace {τ : Type u} (result : τ → Outcome Val) : Event τ → Option Effect4.Trace.Event
  | .completed _ r => some (.done (result r))
  | _ => none

/-- Project a frame trace to its service-level shadow, dropping the rest. -/
def FrameEvent.traceOf {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}
    (region : ν → Nat) (value : β → Val) (error : ε → Val) (defect : δ → Val)
    (events : List (FrameEvent ν σ β ε δ ι α)) : Effect4.Trace.Log :=
  events.filterMap (FrameEvent.toTrace region value error defect)

theorem FrameEvent.traceOf_nil {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}
    (region : ν → Nat) (value : β → Val) (error : ε → Val) (defect : δ → Val) :
    FrameEvent.traceOf region value error defect ([] : List (FrameEvent ν σ β ε δ ι α)) = [] := rfl

/-- A pushed or popped frame leaves no service-level row. -/
theorem FrameEvent.toTrace_popped {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}
    (region : ν → Nat) (value : β → Val) (error : ε → Val) (defect : δ → Val)
    (frame : Prim ν σ β ε δ ι α) :
    FrameEvent.toTrace region value error defect (.popped frame) = none := rfl

/-- A run's finalizer rows are exactly its `ranFinalizer` events, in order. -/
theorem FrameEvent.traceOf_finalizers {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}
    (region : ν → Nat) (value : β → Val) (error : ε → Val) (defect : δ → Val)
    (finalizer : ν) (exit : Exit β ε δ ι α) (rest : List (FrameEvent ν σ β ε δ ι α)) :
    FrameEvent.traceOf region value error defect (.ranFinalizer finalizer exit :: rest) =
      .finalizer (region finalizer) (Exit.toOutcome value error defect exit) ::
        FrameEvent.traceOf region value error defect rest := rfl

end Effect4
