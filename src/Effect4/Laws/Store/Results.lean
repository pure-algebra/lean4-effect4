import Effect4.Store.Domain.Cas
import Effect4.Laws.Auto.Semantics

/-!
# One result per query (seams ST3)

Placement: `exact-codecs`, stored carriers, R13.

- **Question** (`cas-result-once`, preservation): a reached store holds at most one result node for
  each designated query. The pointer is `Cas.result_once`.
- **Reach.** Every store the canonical event interpreter reaches from empty: accepted commits,
  interrupted prefixes and checked restoration. Each passes every node through `Store.putNode`,
  whose result rule (`resultFault`) scans every binding. Word replay and verification apply the
  same rule (`apply_resultOnce`, `verify_sound`).
- **Not established.** The result's truth, the host action's determinism, progress, and hash
  injectivity. Two distinct outputs for one query refuse (`poisoned`). The rule does not say which
  output is right; a wrong first result can satisfy it.
- **Consumers.** ST4's session chains read results through `Cas.read`, and S6 serves them. The
  gate cache keys a result by its command (seams plan §4.5, D1).

The proof carries `Store.Sound` through every event: `stageNodes_sound`, `commit_sound`,
`interrupted_sound`, `restore_sound`, then `Cas.sound`. The invariant's result field covers every
binding, shadowed ones included, because the conflict scan reads them all.
-/

set_option autoImplicit false

namespace Effect4.Store

/-- Helper of `cas-result-once`: soundness reads the resident nodes only, never the roots. -/
theorem sound_of_nodes_eq {store next : Store} (same : next.nodes = store.nodes)
    (sound : store.Sound) : next.Sound := by
  obtain ⟨nodes, roots⟩ := next
  obtain ⟨nodes', roots'⟩ := store
  simp only at same
  subst same
  exact ⟨sound.version, sound.wf, sound.refs, sound.handles, sound.addressed, sound.closed,
    sound.results⟩

/-- Helper of `cas-result-once`: accepted staging keeps the final store and every fresh prefix
sound. -/
theorem stageNodes_sound {store final : Store} {index : Nat} {nodes : List Node}
    {outcomes : List (Digest × NodeOutcome)} {prefixes : List Store}
    (sound : store.Sound)
    (accepted : store.stageNodes index nodes = .ok (outcomes, final, prefixes)) :
    final.Sound ∧ ∀ kept ∈ prefixes, kept.Sound := by
  induction nodes generalizing store index outcomes final prefixes with
  | nil =>
    simp only [Store.stageNodes, Except.ok.injEq, Prod.mk.injEq] at accepted
    obtain ⟨rfl, rfl, rfl⟩ := accepted
    exact ⟨sound, fun _ member => nomatch member⟩
  | cons node nodes ih =>
    simp only [Store.stageNodes] at accepted
    split at accepted
    · exact nomatch accepted
    · exact nomatch accepted
    · next digest next admitted =>
      split at accepted
      · exact nomatch accepted
      · next tail final' prefixes' staged =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at accepted
        obtain ⟨rfl, rfl, rfl⟩ := accepted
        have nextSound := putNode_sound sound admitted
        obtain ⟨finalSound, prefixSound⟩ := ih nextSound staged
        refine ⟨finalSound, ?_⟩
        intro kept member
        cases member with
        | head => exact nextSound
        | tail _ member => exact prefixSound kept member
    · next digest next admitted =>
      split at accepted
      · exact nomatch accepted
      · next tail final' prefixes' staged =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at accepted
        obtain ⟨rfl, rfl, rfl⟩ := accepted
        exact ih (putNode_sound sound admitted) staged

/-- Helper of `cas-result-once`: an accepted commit keeps the store sound. -/
theorem commit_sound {store next : Store} {transaction : Txn} {receipt : Receipt}
    (sound : store.Sound) (accepted : store.commit transaction = .ok (receipt, next)) :
    next.Sound := by
  simp only [Store.commit] at accepted
  split at accepted
  · exact nomatch accepted
  · next receipt' final prefixes prepared =>
    obtain ⟨staged, admitted, moved⟩ := prepare_ok prepared
    simp only [Except.ok.injEq, Prod.mk.injEq] at accepted
    obtain ⟨rfl, rfl⟩ := accepted
    exact sound_of_nodes_eq (stageMoves_nodes moved) (stageNodes_sound sound admitted).1

/-- Helper of `cas-result-once`: every accepted cut keeps the store sound. -/
theorem interrupted_sound {store next : Store} {transaction : Txn} {cut : Cut}
    (sound : store.Sound) (accepted : store.interrupted transaction cut = .ok next) :
    next.Sound := by
  cases cut with
  | published =>
    obtain ⟨receipt, committed⟩ := interrupted_published accepted
    exact commit_sound sound committed
  | nodes count =>
    simp only [Store.interrupted] at accepted
    split at accepted
    · exact nomatch accepted
    · next receipt final prefixes prepared =>
      obtain ⟨staged, admitted, _⟩ := prepare_ok prepared
      injection accepted with accepted
      subst accepted
      have prefixesSound := (stageNodes_sound sound admitted).2
      cases last : (prefixes.take count).getLast? with
      | none =>
        simp only [Option.getD_none]
        exact sound_of_nodes_eq rfl sound
      | some kept =>
        simp only [Option.getD_some]
        exact sound_of_nodes_eq (store := kept) rfl
          (prefixesSound kept (List.mem_of_mem_take (List.mem_of_getLast? last)))

/-- Helper of `cas-result-once`: checked restoration admits every node from empty, so the
restored store is sound. -/
theorem restore_sound {store next : Store} {image : RecoveryImage}
    (accepted : store.restore image = .ok next) : next.Sound := by
  unfold Store.restore at accepted
  split at accepted
  · split at accepted
    · exact nomatch accepted
    · next outcomes staged prefixes prepared =>
      split at accepted
      · exact nomatch accepted
      · injection accepted with same
        subst same
        exact sound_of_nodes_eq (store := staged) rfl (stageNodes_sound empty_sound prepared).1
  · exact nomatch accepted

/-- Helper of `cas-result-once`: the one event interpreter keeps the store sound. -/
theorem eventStep_sound {store next : Store} {event : Event} (sound : store.Sound)
    (accepted : eventStep store event = .ok next) : next.Sound := by
  cases event with
  | commit transaction =>
    simp only [eventStep] at accepted
    cases committed : store.commit transaction with
    | error why =>
      rw [committed] at accepted
      exact nomatch accepted
    | ok pair =>
      rw [committed] at accepted
      injection accepted with same
      subst same
      exact commit_sound sound committed
  | interrupt transaction cut => exact interrupted_sound sound accepted
  | restore image => exact restore_sound accepted

/-- Helper of `cas-result-once`: replay from a sound store reaches a sound store. -/
theorem replayEventsFrom_sound {store next : Store} {events : List Event} (sound : store.Sound)
    (accepted : replayEventsFrom store events = .ok next) : next.Sound := by
  induction events generalizing store with
  | nil =>
    injection accepted with same
    subst same
    exact sound
  | cons event events ih =>
    simp only [replayEventsFrom] at accepted
    split at accepted
    · exact nomatch accepted
    · next step stepped => exact ih (eventStep_sound sound stepped) accepted

/-- Helper of `cas-result-once`: every reached store is sound. -/
theorem Cas.sound (cas : Cas) : cas.store.Sound := by
  obtain ⟨events, reached⟩ := cas.reached
  exact replayEventsFrom_sound empty_sound reached

/-- **At most one result per query** (`cas-result-once`). Two bindings of a reached store that
answer one designated query hold the same node. -/
@[semantics "exact-codecs" (requirement := R13)]
theorem Cas.result_once (cas : Cas) {query : Digest} {a b : Digest × Node}
    (ha : a ∈ cas.store.nodes) (hb : b ∈ cas.store.nodes)
    (qa : a.2.resultQuery? = some query) (qb : b.2.resultQuery? = some query) : a.2 = b.2 :=
  cas.sound.results.unique ha hb qa qb

end Effect4.Store
