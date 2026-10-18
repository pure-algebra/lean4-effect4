import Effect4.Program.Typing.SourceDocument
import Effect4.Laws.Program.SourceTable
import Effect4.Laws.Auto.Obligations
/-!
Placement: initial-algebras-folds; source-session-coherent and typed-replacement, R14.
Question: checked-edit-atomic and validating document replay.
Reach: sealed documents, exact snapshots, accepted action histories, and the stated policy premises.
Exclusions: admission, progress, native execution, and positive-root conclusions for draft.
Consumers: the tool's atomic wrapper, ordered fill publication, and document replay.
A keepExact edit retains an initially refused root; positivity therefore requires the old positive-root premise.
-/
set_option autoImplicit false
namespace Effect4.Program
open _root_.Effect4.Program.Check

@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Doc.step_replay (origin : DocOrigin) (history : List DocAction) (action : DocAction) :
    replayDoc origin (history ++ [action]) =
      ((DocInternal.replayStep Oracle.uncached
        (DocInternal.replayState origin history) action).value).map (·.session) := by
  unfold replayDoc
  rw [DocInternal.replayState_snoc]

@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Doc.step_refuses {o : Oracle} {d : Doc} {snap : Snap} {action : DocAction}
    {why : DocRefusal} (h : (d.step o snap action).value = .error why) :
    (((d.step o snap action).value.map Prod.fst).toOption.getD d) = d := by
  rw [h]
  rfl

@[semantics "initial-algebras-folds" (requirement := R14)]
proof_goal Doc.step_coherent {o : Oracle} {d next : Doc} {snap : Snap} {action : DocAction}
    {receipt : Receipt} (hc : d.session.Coherent)
    (h : (d.step o snap action).value = .ok (next,receipt)) :
    snap = d.snap ∧ next.origin = d.origin ∧ next.history = d.history ++ [action] ∧
      next.session.Coherent ∧ next.session.app = d.session.app

/-- Corrected old commit observation: keepExact needs an initially positive root. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
proof_goal Doc.commit_sound {o : Oracle} {d next : Doc} {snap : Snap}
    {items : List (Place × Change)} {policy : FeedPolicy} {receipt : Receipt}
    (hc : d.session.Coherent)
    (hpolicy : policy = .keepExact ∨ policy = .recheck)
    (hpositive : policy = .keepExact → ∃ T, d.session.sketch.sourceCheck d.session.app = .ok T)
    (h : (d.step o snap (.commit items policy)).value = .ok (next,receipt)) :
    snap = d.snap ∧ next.origin = d.origin ∧ next.snap.revision = d.snap.revision + 1 ∧
      next.session.Coherent ∧ next.session.app = d.session.app ∧
      ∃ T', next.session.sketch.sourceCheck next.session.app = .ok T' ∧
        (policy = .keepExact → d.session.sketch.sourceCheck d.session.app = .ok T')


/-- A single kept edit retains both exact observations, including an initially refused root. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
proof_goal Doc.commit_one_keepExact {o : Oracle} {d next : Doc} {snap : Snap}
    {place : Place} {change : Change} {receipt : Receipt} {path : List Nat} {expected : NativeEff}
    (hc : d.session.Coherent) (hp : path ≠ [])
    (hplace : place.resolve d.session.app d.session.sketch = .ok (path,expected))
    (h : (d.step o snap (.commit [(place,change)] .keepExact)).value = .ok (next,receipt)) :
    next.session.view.type = d.session.view.type ∧
      Table.typedAt next.session.table path = Table.typedAt d.session.table path


/-- The old single-edit observations, with the required initial positive-root premise. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
proof_goal Doc.commit_single_sound {o : Oracle} {d next : Doc} {snap : Snap}
    {path : List Nat} {expected : NativeEff} {change : Change} {policy : FeedPolicy}
    {receipt : Receipt} (hc : d.session.Coherent)
    (hpolicy : policy = .keepExact ∨ policy = .recheck)
    (hpositive : policy = .keepExact → ∃ T, d.session.sketch.sourceCheck d.session.app = .ok T)
    (h : (d.step o snap (.commit [(.at_ path expected,change)] policy)).value = .ok (next,receipt)) :
    snap = d.snap ∧ next.id = d.id ∧ next.revision = d.revision + 1 ∧
      next.session.Coherent ∧ next.session.app = d.session.app ∧
      (∃ e, DocInternal.editOf d.session path change = .ok e ∧
        d.session.sketch.edit d.session.app e = some next.session.sketch) ∧
      ∃ T', next.session.sketch.sourceCheck d.session.app = .ok T' ∧
        (policy = .keepExact → d.session.sketch.sourceCheck d.session.app = .ok T' ∧
          Table.typedAt next.session.table path = Table.typedAt d.session.table path)

/-- An entry's immediate revert restores its prior program and retains appended hole rows. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
proof_goal Doc.revert_program {o : Oracle} {before after back : Doc} {snap : Snap}
    {action : DocAction} {receipt inverse : Receipt}
    (hc : before.session.Coherent)
    (ha : (before.step o snap action).value = .ok (after,receipt))
    (hr : (after.step o after.snap (.revert before.history.length)).value = .ok (back,inverse)) :
    back.session.sketch.program = before.session.sketch.program ∧
      back.session.sketch.holes = after.session.sketch.holes
end Effect4.Program
