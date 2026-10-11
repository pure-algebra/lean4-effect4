import Effect4.Laws.Machine.PopTrace
import Effect4.Laws.Contracts.FramePath

/-!
Concept: scope-lifetime-finalization R11 and store-typing R4.
Question: one native pop transport serves semantic and exact source saved-frame families.
Reach: an external edge predicate over existing frames and its ordered path.
Each instance supplies actual scratch, selection, skip, and hook obligations.
Consumers: AnswerFlowPop, AnswerFlowCausePop and HostTimeoutFrames.pop_from.
This contract supplies no pending cause, provided exit, future world or finalizer premise.
Those remain obligations of the chosen edge family and its callback consumers.
-/
set_option autoImplicit false
namespace Effect4.Machine.PopTrace
open Effect4 Effect4.Contracts
universe u v w
variable {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} {Kind : Type w}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

/-- One-step closure of an external saved-frame family under the actual pop operations.
The edge is a predicate on existing frames, not another program representation. -/
structure Family (demand : Arm) (skip : Bool)
    (Edge : Kind → Kind → Prim ν σ β ε δ ι α → Prop)
    (Scratch : FrameFiber ν σ β ε δ ι α → Prop)
    (Claim : Kind → Kind → Option (Cause ε δ ι α) → FramePop ν σ β ε δ ι α → Prop) : Prop where
  nil : ∀ kind fiber cause, Scratch fiber → Claim kind kind cause ⟨.empty, [], [], fiber, cause⟩
  selected : ∀ input middle output frame rest fiber cause answer,
    Edge input middle frame → Path Edge middle output rest → Scratch fiber →
    frame.answerOf demand (frame.ensure fiber).2 = some answer →
    (skip && (frame.ensure fiber).1.interrupted) = false →
    Claim input output cause ⟨answer, [frame], frame.passEvents (frame.ensure fiber).2,
      {(frame.ensure fiber).1 with stack := (frame.ensure fiber).1.stack ++ rest}, cause⟩
  drain : ∀ input middle frame fiber after, Edge input middle frame → Scratch fiber →
    Scratch (FrameFiber.passPushed demand skip (frame.ensure fiber).1 after).fiber
  continued : ∀ input middle output frame rest fiber before after tail,
    Edge input middle frame → Path Edge middle output rest → Scratch fiber →
    Passes demand skip frame fiber before after →
    (FrameFiber.passPushed demand skip (frame.ensure fiber).1 after).answer = .empty →
    Claim middle output (FrameFiber.passPushed demand skip (frame.ensure fiber).1 after).carriedCause tail →
    Claim input output before (FrameFiber.passOn frame (frame.ensure fiber).2
      (FrameFiber.joinPushed demand skip (frame.ensure fiber).1 rest tail after))
  hooked : ∀ input middle output frame rest fiber before after tail,
    Edge input middle frame → Path Edge middle output rest → Scratch fiber →
    Passes demand skip frame fiber before after →
    (FrameFiber.passPushed demand skip (frame.ensure fiber).1 after).answer ≠ .empty →
    Claim input output before (FrameFiber.passOn frame (frame.ensure fiber).2
      (FrameFiber.joinPushed demand skip (frame.ensure fiber).1 rest tail after))

/-- The actual pop trace transports every family with the supplied one-step closure laws. -/
theorem Family.trace {demand : Arm} {skip : Bool}
    {Edge : Kind → Kind → Prim ν σ β ε δ ι α → Prop}
    {Scratch : FrameFiber ν σ β ε δ ι α → Prop}
    {Claim : Kind → Kind → Option (Cause ε δ ι α) → FramePop ν σ β ε δ ι α → Prop}
    (family : Family demand skip Edge Scratch Claim)
    {frames fiber cause parts suffix pop}
    (trace : Trace demand skip frames fiber cause parts suffix pop)
    {input output : Kind} (path : Path Edge input output frames) (scratch : Scratch fiber) :
    Claim input output cause pop := by
  induction trace generalizing input output with
  | nil fiber cause => cases path; exact family.nil input fiber cause scratch
  | selected frame rest fiber cause answer chosen kept =>
    cases path with
    | cons head tail => exact family.selected _ _ _ _ _ _ _ _ head tail scratch chosen kept
  | continued frame rest fiber before after parts suffix tail passed drained next ih =>
    cases path with
    | cons head path =>
      exact family.continued _ _ _ _ _ _ _ _ _ head path scratch passed drained
        (ih path (family.drain _ _ _ _ _ head scratch))
  | hooked frame rest fiber before after tail passed answered =>
    cases path with
    | cons head path => exact family.hooked _ _ _ _ _ _ _ _ _ head path scratch passed answered

/-- The same family transports the real fused pop, without a private frame traversal. -/
theorem Family.popFrom {demand : Arm} {skip : Bool}
    {Edge : Kind → Kind → Prim ν σ β ε δ ι α → Prop}
    {Scratch : FrameFiber ν σ β ε δ ι α → Prop}
    {Claim : Kind → Kind → Option (Cause ε δ ι α) → FramePop ν σ β ε δ ι α → Prop}
    (family : Family demand skip Edge Scratch Claim) (input output : Kind)
    (frames : List (Prim ν σ β ε δ ι α)) (fiber : FrameFiber ν σ β ε δ ι α)
    (cause : Option (Cause ε δ ι α)) (path : Path Edge input output frames)
    (scratch : Scratch fiber) : Claim input output cause (FrameFiber.popFrom demand skip frames fiber cause) := by
  obtain ⟨parts, suffix, trace⟩ := popFrom_spec demand skip frames fiber cause
  exact family.trace trace path scratch

end Effect4.Machine.PopTrace
