import Effect4.Library.Channel.Ops
import Effect4.Laws.Library.Pull.Scope

/-!
# Channel builders keep source scope

Placement: helpers of channel-batch-transform and channel-completion-transform, translation-simulation, R10.
The plan is docs/research/2026-10-09-channel-transforms-plan.md.
The consumers are the Channel protocol laws and public Channel operations.
The state and every callback result must be scoped under the supplied payload reader.
Scope alone establishes no typing, reading, capture lifetime or stored-call execution.
-/

set_option autoImplicit false
namespace Effect4.Channel
open Effect4.Program Effect4.Program.Authoring

private theorem invoke_one_scoped (upstream : DefSrc NativeOp) {state : TermSrc}
    (hstate : state.Scoped) : (Def.invoke upstream.name [state]).Scoped := by
  refine ⟨fun env path tree h => ?_⟩
  unfold Def.invoke at h
  cases found : env.defs.find? (fun entry => entry.1 == upstream.name) with
  | none =>
    rw [found] at h
    cases h
  | some entry =>
    rcases entry with ⟨name, index⟩
    rw [found] at h
    change (perform (.call index) state) env path = .ok tree at h
    exact (perform_scoped (.call index) (fun _ => rfl) hstate).holds env path tree h

/-- The batch dispatcher keeps scope where its input and batch callback do. -/
theorem Internal.mapEffectOf_scoped {self : Src NativeOp} {transform : TermSrc → Src NativeOp}
    (hself : self.Scoped)
    (ht : ∀ batch : TermSrc, batch.Scoped → (transform batch).Scoped) :
    (Internal.mapEffectOf self transform).Scoped :=
  bindWith_scoped hself fun _ ha => Pull.matchAnswer_scoped ha
    (fun _ hc => bindWith_scoped (ht _ hc) fun _ hm =>
      succeed_scoped (Pull.chunkValue_scoped hm))
    (fun _ hd => succeed_scoped (Pull.endValue_scoped hd))

/-- A stored upstream's state and the selected batch callback keep scope. -/
theorem mapEffect_scoped (upstream : DefSrc NativeOp) {state : TermSrc}
    {transform : TermSrc → Src NativeOp} (hstate : state.Scoped)
    (ht : ∀ batch : TermSrc, batch.Scoped → (transform batch).Scoped) :
    (mapEffect upstream state transform).Scoped :=
  Internal.mapEffectOf_scoped (invoke_one_scoped upstream hstate) ht

/-- Pure batch mapping keeps scope under the callback's payload reader. -/
theorem map_scoped (upstream : DefSrc NativeOp) {state : TermSrc}
    {transform : TermSrc → TermSrc} (hstate : state.Scoped)
    (ht : ∀ batch : TermSrc, batch.Scoped → (transform batch).Scoped) :
    (map upstream state transform).Scoped :=
  mapEffect_scoped upstream hstate fun _ hc => succeed_scoped (ht _ hc)

/-- The completion dispatcher keeps scope where its input and leftover callback do. -/
theorem Internal.mapDoneEffectOf_scoped {self : Src NativeOp} {transform : TermSrc → Src NativeOp}
    (hself : self.Scoped)
    (ht : ∀ leftover : TermSrc, leftover.Scoped → (transform leftover).Scoped) :
    (Internal.mapDoneEffectOf self transform).Scoped :=
  bindWith_scoped hself fun _ ha => Pull.matchAnswer_scoped ha
    (fun _ hc => succeed_scoped (Pull.chunkValue_scoped hc))
    (fun _ hd => bindWith_scoped (ht _ hd) fun _ hm =>
      succeed_scoped (Pull.endValue_scoped hm))

/-- A stored upstream's state and the selected completion callback keep scope. -/
theorem mapDoneEffect_scoped (upstream : DefSrc NativeOp) {state : TermSrc}
    {transform : TermSrc → Src NativeOp} (hstate : state.Scoped)
    (ht : ∀ leftover : TermSrc, leftover.Scoped → (transform leftover).Scoped) :
    (mapDoneEffect upstream state transform).Scoped :=
  Internal.mapDoneEffectOf_scoped (invoke_one_scoped upstream hstate) ht

/-- Pure completion mapping keeps scope under the callback's leftover reader. -/
theorem mapDone_scoped (upstream : DefSrc NativeOp) {state : TermSrc}
    {transform : TermSrc → TermSrc} (hstate : state.Scoped)
    (ht : ∀ leftover : TermSrc, leftover.Scoped → (transform leftover).Scoped) :
    (mapDone upstream state transform).Scoped :=
  mapDoneEffect_scoped upstream hstate fun _ hd => succeed_scoped (ht _ hd)

end Effect4.Channel
