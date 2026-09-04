import Effect4.Runtime.Runtime
import Effect4.Semantics.Observation

/-!
# Target.TypeScript.Simulation

Owner: the projection from the frame machine's alphabet (`Effect4.FrameEvent`,
`Effect4/Runtime/Runtime.lean`) into the shared service-level trace alphabet
(`Effect4.Trace.Event`, `Effect4/Semantics/Observation.lean`)
(`docs/TRACE-DAG.md` edge `bridges`). The scheduler-side projection this
module also owned was retired on 2026-09-04 with the old scheduler
(`docs/research/2026-09-04-retire-old-machines.md`).

Only finalizers and outcomes project: a `ranFinalizer` becomes `finalizer`
with the exit it observed and a `yielded` exit becomes `done`; everything else
is a frame fact with no service-level shadow and projects to `none`. No
simulation is claimed: the projection states what a frame-level observation
*would* say in the service-level alphabet, so that a future bridge theorem has
a statement to make. The host side (`harness/trace/patched/`) records the
corresponding rc.112 rows in receipts; they are evidence of nothing yet.
-/

namespace Effect4

open Effects.Trace (Val Outcome)

/-- The outcome of an exit: the value, the first failure's error, an
interruption, or (a die with no failure before it) a defect. -/
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
            | some (.die d _) => .defect (defect d)
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
