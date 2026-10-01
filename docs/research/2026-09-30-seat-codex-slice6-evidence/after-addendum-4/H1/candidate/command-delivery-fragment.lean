/-- The existing await protocol certifies a finite list of declared target columns.
This is a command-admission requirement; the runtime's missing-target behavior is unchanged. -/
def FiberListColumns (w : World) (targets : List FiberId) (answer error : Ty) : Prop :=
  ∀ id ∈ targets, FiberColumnsBelow w id answer error

/-- asVoid(awaitCode kind) has a unit answer. joinEffect can retain the target's typed
failures; awaitValue and awaitAll return encoded exits as successful values. -/
def AfterInterruptReply (w : World) : ParkKind → EffTy → Prop
  | .join target .joinEffect, replyTy => ∃ sourceTy, w.Γ target = some sourceTy ∧
      replyTy = ⟨.unit, sourceTy.error, Env.Requirement.empty⟩
  | .join target .awaitValue, replyTy => ∃ sourceTy, w.Γ target = some sourceTy ∧
      replyTy = EffTy.pure .unit
  | .awaitAll targets, replyTy => ∃ answer error, FiberListColumns w targets answer error ∧
      replyTy = EffTy.pure .unit
  | .race _, _ => False

/-- Commands with no carried code can still install a concrete reply or an iterator frame.
Their finite targets and result columns must meet the actual host stack. This does not ask
that an evaluated transition be typed, and does not quantify over unknown code continuations. -/
def CommandDeliveryOk (root : ProgramSource) (w : World) (m : RState) : RCmd → Prop
  | .afterInterrupt host _ kind => ∀ fiber, m.fiber? host = some fiber →
      ∃ replyTy, AfterInterruptReply w kind replyTy ∧ StackReply root w fiber replyTy
  | .raceCancel _ host _ remaining visited => ∀ fiber, m.fiber? host = some fiber →
      ∃ answer error, FiberListColumns w (visited ++ remaining) answer error ∧
        StackReply root w fiber (EffTy.pure .unit)
  | .closeParAwait host _ targets => ∀ fiber, m.fiber? host = some fiber →
      ∃ answer error, FiberListColumns w targets answer error ∧
        (frameProtocols root).iterator w
          ⟨.list (.exitOf answer error), error, Env.Requirement.empty⟩
          ⟨.unit, error, Env.Requirement.empty⟩ (interpR root.program).closeDoneName ∧
        StackReply root w fiber ⟨.unit, error, Env.Requirement.empty⟩
  | _ => True

