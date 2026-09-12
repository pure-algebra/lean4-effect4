import Effect4.Laws.Program.Agreement
import Effect4.Laws.Machine.StoresLaws

/-!
DI-71 layer memo reuse and the owner-approved fresh-map isolation law.
Proof graph: store-hit and continuation equations establish memo reuse;
parent-closed lookup and single-operation framing lift through LocalSteps to
fresh_never_shares. The memo-hit laws quantify over arbitrary MemoEntry values.
Isolation covers operations routed through the fresh map and its isolated
region; independently selected ambient program-level provideLayer is outside
that scope. Compiler and store behavior remain unchanged.
-/

set_option autoImplicit false

namespace Effect4.Program.LayerSharing
open Effect4 Effect4.Machine Effect4.Program

/-- A parentless map's lookup can return only its own entry. -/
theorem lookup_parentless (w : MemoWorld) (id : MemoMapId) (m : MemoMap)
    (hm : w.mapAt id = some m) (hp : m.parent = none) (layer : LayerId) (n : Nat) :
    w.lookup layer (n + 1) id = (w.entryAt id layer).map (fun e => (id, e)) := by
  simp only [MemoWorld.lookup]
  cases w.entryAt id layer <;> simp [hm, hp]

theorem get_parentless (w : MemoWorld) (id : MemoMapId) (m : MemoMap)
    (hm : w.mapAt id = some m) (hp : m.parent = none) (layer : LayerId) :
    w.get layer id = (w.entryAt id layer).map (fun e => (id, e)) :=
  lookup_parentless w id m hm hp layer w.length

theorem mapAt_setMap_other (w : MemoWorld) (m : MemoMap) (id : MemoMapId)
    (hne : id ≠ m.id) : (w.setMap m).mapAt id = w.mapAt id := by
  induction w with
  | nil => rfl
  | cons a rest ih =>
    unfold MemoWorld.setMap MemoWorld.mapAt at *
    simp only [List.map_cons, List.find?_cons]
    by_cases ha : a.id = m.id
    · simp only [ha, ↓reduceIte]
      have hmi : m.id ≠ id := Ne.symm hne
      simp only [hmi, decide_false, ih]
    · simp only [ha, ↓reduceIte]
      split <;> simp_all

/-- A hit registers release and awaits the stored deferred; it contains no build. -/
theorem memoize_hit (root : NativeEff) (q : Point) (map : MemoMapId) (scope : Nat)
    (entry : MemoEntry) (owner : MemoMapId) :
    contAOf root (.memoize q map scope) (Val.pair (Val.promise entry.deferred) (Val.memoMap owner)) =
      Prim.onSuccess (scopeAddAt scope (FinName.memoEntry q.path owner))
        (EffName.awaitPromise entry.deferred) :=
  Effect4.Program.Agreement.contAOf_memoize_hit (root := root) q map scope entry.deferred owner


/-- The store hit and the continuation agree on the stored deferred and owner. -/
theorem memoGet_memoize_hit (root : NativeEff) (s : Stores) (q : Point)
    (map : MemoMapId) (scope : Nat) (entry : MemoEntry) (owner : MemoMapId)
    (h : s.memo.get q.path map = some (owner, entry)) :
    (syncOpStep (.memoGet q.path map) s).map (fun (s', v) => (s'.refs, contAOf root (.memoize q map scope) v)) =
      some (s.refs, Prim.onSuccess (scopeAddAt scope (FinName.memoEntry q.path owner))
        (EffName.awaitPromise entry.deferred)) := by
  rw [syncOpStep_memoGet_some s q.path map h]
  simp only [Option.map_some, memoize_hit]

theorem fresh_forks_without_parent (l : LayerTerm NativeOp) (q : Point) (map : MemoMapId) (scope : Nat) :
    compileLayer (.fresh l) q map scope =
      Prim.onSuccess (Prim.sync (EffThunk.op (.memoFork none))) (EffName.freshThen (q.child 0) scope) := rfl

def Isolated (inside : List MemoMapId) (w : MemoWorld) : Prop :=
  ∀ m ∈ w, m.id ∈ inside → ∀ parent, m.parent = some parent → parent ∈ inside

theorem lookup_owner_inside {inside : List MemoMapId} {w : MemoWorld}
    (hw : Isolated inside w) (layer : LayerId) (fuel : Nat) (id : MemoMapId)
    (hi : id ∈ inside) {owner : MemoMapId} {entry : MemoEntry}
    (h : w.lookup layer fuel id = some (owner, entry)) : owner ∈ inside := by
  induction fuel generalizing id with
  | zero => simp [MemoWorld.lookup] at h
  | succ fuel ih =>
    simp only [MemoWorld.lookup] at h
    cases he : w.entryAt id layer with
    | some e =>
      simp only [he, Option.some.injEq, Prod.mk.injEq] at h
      exact h.1 ▸ hi
    | none =>
      simp only [he] at h
      cases hm : w.mapAt id with
      | none => simp [hm] at h
      | some m =>
        simp only [hm] at h
        cases hp : m.parent with
        | none => simp [hp] at h
        | some parent =>
          simp only [hp] at h
          have facts := MemoWorld.mapAt_mem hm
          have hparent := hw m facts.1 (facts.2 ▸ hi) parent hp
          exact ih parent hparent h

theorem mapAt_updateEntry_other (w : MemoWorld) (id other : MemoMapId) (layer : LayerId)
    (f : MemoEntry → MemoEntry) (hne : other ≠ id) :
    (w.updateEntry id layer f).mapAt other = w.mapAt other := by
  unfold MemoWorld.updateEntry
  cases hm : w.mapAt id with
  | none => rfl
  | some m =>
    apply mapAt_setMap_other
    simpa only [(MemoWorld.mapAt_mem hm).2] using hne

theorem mapAt_insertEntry_other (w : MemoWorld) (id other : MemoMapId) (layer : LayerId)
    (e : MemoEntry) (hne : other ≠ id) :
    (w.insertEntry id layer e).mapAt other = w.mapAt other := by
  unfold MemoWorld.insertEntry
  cases hm : w.mapAt id with
  | none => rfl
  | some m =>
    apply mapAt_setMap_other
    simpa only [(MemoWorld.mapAt_mem hm).2] using hne

theorem mapAt_deleteEntry_other (w : MemoWorld) (id other : MemoMapId) (layer : LayerId)
    (hne : other ≠ id) : (w.deleteEntry id layer).mapAt other = w.mapAt other := by
  unfold MemoWorld.deleteEntry
  cases hm : w.mapAt id with
  | none => rfl
  | some m =>
    apply mapAt_setMap_other
    simpa only [(MemoWorld.mapAt_mem hm).2] using hne

theorem isolated_setMap {inside : List MemoMapId} {w : MemoWorld} (hw : Isolated inside w)
    (m : MemoMap) (hm : m.id ∈ inside → ∀ parent, m.parent = some parent → parent ∈ inside) :
    Isolated inside (w.setMap m) := by
  intro a ha hi parent hp
  obtain ⟨b, hb, hba⟩ := List.mem_map.mp ha
  split at hba <;> subst a
  · exact hm hi parent hp
  · exact hw b hb hi parent hp

theorem isolated_updateEntry {inside : List MemoMapId} {w : MemoWorld} (hw : Isolated inside w)
    (id : MemoMapId) (layer : LayerId) (f : MemoEntry → MemoEntry) :
    Isolated inside (w.updateEntry id layer f) := by
  unfold MemoWorld.updateEntry
  cases hm : w.mapAt id with
  | none => exact hw
  | some m =>
    apply isolated_setMap hw
    exact hw m (MemoWorld.mapAt_mem hm).1

theorem isolated_insertEntry {inside : List MemoMapId} {w : MemoWorld} (hw : Isolated inside w)
    (id : MemoMapId) (layer : LayerId) (e : MemoEntry) :
    Isolated inside (w.insertEntry id layer e) := by
  unfold MemoWorld.insertEntry
  cases hm : w.mapAt id with
  | none => exact hw
  | some m =>
    apply isolated_setMap hw
    exact hw m (MemoWorld.mapAt_mem hm).1

theorem isolated_deleteEntry {inside : List MemoMapId} {w : MemoWorld} (hw : Isolated inside w)
    (id : MemoMapId) (layer : LayerId) : Isolated inside (w.deleteEntry id layer) := by
  unfold MemoWorld.deleteEntry
  cases hm : w.mapAt id with
  | none => exact hw
  | some m =>
    apply isolated_setMap hw
    exact hw m (MemoWorld.mapAt_mem hm).1

theorem isolated_append {inside : List MemoMapId} {w : MemoWorld} (hw : Isolated inside w)
    (m : MemoMap) (hm : m.id ∈ inside → ∀ parent, m.parent = some parent → parent ∈ inside) :
    Isolated inside (w ++ [m]) := by
  intro a ha hi parent hp
  rcases List.mem_append.mp ha with ha | ha
  · exact hw a ha hi parent hp
  · have he : a = m := List.mem_singleton.mp ha
    subst a
    exact hm hi parent hp

theorem mapAt_append_other (w : MemoWorld) (m : MemoMap) (id : MemoMapId)
    (hne : id ≠ m.id) : (w ++ [m]).mapAt id = w.mapAt id := by
  unfold MemoWorld.mapAt
  rw [List.find?_append]
  simp [List.find?, Ne.symm hne]

/-- The operation selects a map in the isolated region; new maps have local parents. -/
def Local (inside : List MemoMapId) (s : Stores) : SyncOp → Prop
  | .memoFork parent => ⟨s.nextName⟩ ∈ inside ∧ ∀ p, parent = some p → p ∈ inside
  | .memoGet _ id | .memoBuild _ id | .memoComplete _ id _ | .memoRelease _ id => id ∈ inside
  | _ => False

theorem local_step {inside : List MemoMapId} {s s' : Stores} {op : SyncOp} {v : Val}
    (hw : Isolated inside s.memo) (hl : Local inside s op)
    (hs : syncOpStep op s = some (s', v)) :
    Isolated inside s'.memo ∧ ∀ outside, outside ∉ inside →
      s'.memo.mapAt outside = s.memo.mapAt outside := by
  cases op <;> simp only [Local] at hl
  case memoFork parent =>
    rw [syncOpStep_memoFork] at hs
    cases hs
    constructor
    · apply isolated_append hw
      exact fun _ => hl.2
    · intro outside ho
      apply mapAt_append_other
      intro h
      exact ho (h ▸ hl.1)
  case memoGet layer id =>
    cases hg : s.memo.get layer id with
    | none =>
      rw [syncOpStep_memoGet_none s layer id hg] at hs
      cases hs
      exact ⟨hw, fun _ _ => rfl⟩
    | some found =>
      rcases found with ⟨owner, entry⟩
      have hown := lookup_owner_inside hw layer (s.memo.length + 1) id hl hg
      rw [syncOpStep_memoGet_some s layer id hg] at hs
      cases hs
      refine ⟨isolated_updateEntry hw owner layer (fun e => { e with observers := e.observers + 1 }), ?_⟩
      intro outside ho
      exact mapAt_updateEntry_other s.memo owner outside layer
        (fun e => { e with observers := e.observers + 1 }) (fun h => ho (h ▸ hown))
  case memoBuild layer id =>
    rw [syncOpStep_memoBuild] at hs
    cases hs
    refine ⟨isolated_insertEntry hw _ _ _, ?_⟩
    intro outside ho
    exact mapAt_insertEntry_other _ _ _ _ _ (fun h => ho (h ▸ hl))
  case memoComplete layer id exit =>
    cases he : s.memo.entryAt id layer with
    | none =>
      rw [syncOpStep_memoComplete_none s layer id exit he] at hs
      cases hs
      exact ⟨hw, fun _ _ => rfl⟩
    | some entry =>
      rw [syncOpStep_memoComplete_some s layer id exit he] at hs
      cases hs
      refine ⟨isolated_updateEntry hw id layer (fun e => { e with effect := Prim.ofExit exit }), ?_⟩
      intro outside ho
      exact mapAt_updateEntry_other s.memo id outside layer
        (fun e => { e with effect := Prim.ofExit exit }) (fun h => ho (h ▸ hl))
  case memoRelease layer id =>
    cases he : s.memo.entryAt id layer with
    | none =>
      rw [syncOpStep_memoRelease_none s layer id he] at hs
      cases hs
      exact ⟨hw, fun _ _ => rfl⟩
    | some entry =>
      by_cases hobs : entry.observers ≤ 1
      · rw [syncOpStep_memoRelease_last s layer id he hobs] at hs
        cases hs
        refine ⟨isolated_deleteEntry hw _ _, ?_⟩
        intro outside ho
        exact mapAt_deleteEntry_other _ _ _ _ (fun h => ho (h ▸ hl))
      · rw [syncOpStep_memoRelease_dec s layer id he hobs] at hs
        cases hs
        refine ⟨isolated_updateEntry hw id layer (fun e => { e with observers := e.observers - 1 }), ?_⟩
        intro outside ho
        exact mapAt_updateEntry_other s.memo id outside layer
          (fun e => { e with observers := e.observers - 1 }) (fun h => ho (h ▸ hl))

inductive LocalSteps (inside : List MemoMapId) : Stores → Stores → Prop
  | refl (s : Stores) : LocalSteps inside s s
  | step {s middle after : Stores} {op : SyncOp} {v : Val}
      (hl : Local inside s op) (exec : syncOpStep op s = some (middle, v))
      (rest : LocalSteps inside middle after) : LocalSteps inside s after

theorem localSteps_frame {inside : List MemoMapId} {s after : Stores}
    (h : LocalSteps inside s after) (hw : Isolated inside s.memo) :
    Isolated inside after.memo ∧ ∀ outside, outside ∉ inside →
      after.memo.mapAt outside = s.memo.mapAt outside := by
  induction h with
  | refl => exact ⟨hw, fun _ _ => rfl⟩
  | step hl hs _ ih =>
    have first := local_step hw hl hs
    have rest := ih first.1
    exact ⟨rest.1, fun id ho => (rest.2 id ho).trans (first.2 id ho)⟩

/-- The owner-approved isolation claim is about map-routed operations, not all
program execution that happens lexically inside a Layer.effect construction. -/
theorem fresh_never_shares (inside : List MemoMapId) (s fresh after : Stores)
    (hnew : (⟨s.nextName⟩ : MemoMapId) ∈ inside)
    (hdisjoint : ∀ m ∈ s.memo, m.id ∉ inside)
    (hf : syncOpStep (.memoFork none) s = some (fresh, Val.memoMap ⟨s.nextName⟩))
    (hsteps : LocalSteps inside fresh after) :
    Isolated inside after.memo ∧
    (∀ layer id, id ∈ inside → ∀ owner entry,
      after.memo.get layer id = some (owner, entry) → owner ∈ inside) ∧
    (∀ id m, s.memo.mapAt id = some m → after.memo.mapAt id = some m) := by
  have hi : Isolated inside s.memo := by
    intro m hm hin
    exact (hdisjoint m hm hin).elim
  have hl : Local inside s (.memoFork none) := ⟨hnew, by simp⟩
  have result := localSteps_frame (LocalSteps.step hl hf hsteps) hi
  refine ⟨result.1, ?_, ?_⟩
  · intro layer id hid owner entry he
    exact lookup_owner_inside result.1 layer (after.memo.length + 1) id hid he
  · intro id m hm
    have facts := MemoWorld.mapAt_mem hm
    have hout : id ∉ inside := by
      rw [← facts.2]
      exact hdisjoint m facts.1
    exact (result.2 id hout).trans hm

#print axioms lookup_parentless
#print axioms get_parentless
#print axioms mapAt_setMap_other
#print axioms memoize_hit
#print axioms memoGet_memoize_hit
#print axioms fresh_forks_without_parent
#print axioms lookup_owner_inside
#print axioms mapAt_updateEntry_other
#print axioms mapAt_insertEntry_other
#print axioms mapAt_deleteEntry_other
#print axioms isolated_setMap
#print axioms isolated_updateEntry
#print axioms isolated_insertEntry
#print axioms isolated_deleteEntry
#print axioms isolated_append
#print axioms mapAt_append_other
#print axioms local_step
#print axioms localSteps_frame
#print axioms fresh_never_shares
end Effect4.Program.LayerSharing
