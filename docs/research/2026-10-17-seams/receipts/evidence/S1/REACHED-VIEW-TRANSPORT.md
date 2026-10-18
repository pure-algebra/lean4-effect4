# Reach transport for S1

The old reachable-state claim changes status in this proposal.
Its old source proof establishes every draft edit list.
The new Doc implementation proves replay construction independently of table coherence.
`Doc.coherent` remains a planned goal.
Therefore, the new `SourceSession.reached_view` depends on that goal.
Do not report it as an independently proved claim.

## Old statement and proof

The owner is `Effect4.Laws.Program.SourceTable`.
The source below is retained verbatim from the production worktree before S1.

```lean
theorem reached_view (app : SigApp) (s : Sketch) (edits : List Edit) :
    ((SourceSession.open app s).run edits).view.table =
        ((SourceSession.open app s).run edits).sketch.sourceTable app ∧
      ((SourceSession.open app s).run edits).view.refusals =
        ((SourceSession.open app s).run edits).sketch.sourceRefusals app ∧
      ((SourceSession.open app s).run edits).view.type =
        (((SourceSession.open app s).run edits).sketch.sourceCheck app).toOption := by
  have happ : ((SourceSession.open app s).run edits).app = app := run_keeps _ edits
  have h := reached_coherent app s edits
  have h₀ := table_eq h
  have h₁ := view_refusals h
  have h₂ := view_type h
  rw [happ] at h₀ h₁ h₂
  exact ⟨h₀, h₁, h₂⟩
```

## Transport

Map the initial application and sketch to `DocOrigin`.
Choose any document identity.
Map each old edit to `DocAction.draft` in the same order.
The canonical `replayDoc` interprets that history through `DocInternal.apply` and the policy feed.
No second edit interpreter is introduced.

`SourceSession.replay_drafts_view` states the old fragment through that replay.
It quantifies over every old application, initial sketch, and edit list.
It retains the table, refusal, and root observations without a coherence premise.
It also states the exact resulting sketch through the existing `Sketch.edit` fold.
That connector remains a planned goal.

`SourceSession.view_eq` is the conditional helper on a coherent source session.
`SourceSession.reached_view` observes every sealed document.
The new reach includes commit and revert histories as well as draft histories.
Its proof uses the explicit `Doc.coherent` goal.

The slice receipt must record this status regression and the open transport.
The generated semantics and plan tools must measure its final status after central placement.
The previously checked temporary core audit establishes neither open goal.
