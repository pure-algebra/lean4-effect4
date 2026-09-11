import Effect4.Store.Store

/-!
# Effect4.Store.Cascade — Multi-Tier Cascading CAS Store

This module provides the basic, intuitive ergonomics for multi-tier / cascading CAS stores:
1. **`CascadingStore`**: A two-tier store pairing a sovereign local workspace (`localStore`)
   with an upstream fallback (`upstreamStore`).
2. **Local-First Lookup**: `cs.find d` checks `cs.localStore` first, falling back to `cs.upstreamStore`.
3. **Sovereign Local Writes**: `cs.putLocal` writes exclusively into the local store, preserving upstream invariants.
4. **Promotion**: `cs.promote d` promotes a local node into the upstream store.
5. **Monotonicity**: Looking up a node that exists in either tier succeeds without collision.

All definitions in this module are strictly constructive and remain within `[propext, Quot.sound]`.
-/

set_option autoImplicit false

namespace Effect4.Store

/-- A two-tier cascading CAS store: a sovereign local workspace with an upstream fallback. -/
structure CascadingStore where
  localStore : Store
  upstreamStore : Store

instance : Inhabited CascadingStore := ⟨⟨Store.empty, Store.empty⟩⟩

namespace CascadingStore

/-- The empty cascading store. -/
def empty : CascadingStore := ⟨Store.empty, Store.empty⟩

/-- Project the local store. -/
abbrev «local» (cs : CascadingStore) : Store := cs.localStore

/-- Project the upstream store. -/
abbrev upstream (cs : CascadingStore) : Store := cs.upstreamStore

/-- Look up a node by its digest: checks the local store first; falls back to upstream. -/
def find (cs : CascadingStore) (d : Digest) : Option Node :=
  cs.localStore.find d <|> cs.upstreamStore.find d

/-- Checks whether a digest exists in either tier. -/
def contains (cs : CascadingStore) (d : Digest) : Bool :=
  (cs.find d).isSome

theorem find_of_local {cs : CascadingStore} {d : Digest} {n : Node}
    (h : cs.localStore.find d = some n) : cs.find d = some n := by
  dsimp [find]
  rw [h]
  rfl

theorem find_of_upstream {cs : CascadingStore} {d : Digest} {n : Node}
    (hnone : cs.localStore.find d = none)
    (hup : cs.upstreamStore.find d = some n) : cs.find d = some n := by
  dsimp [find]
  rw [hnone, hup]
  rfl

/-- Identifies which tier contains a digest. -/
inductive SourceTier where
  | «local»
  | upstream
deriving DecidableEq, Repr

/-- Look up a node alongside the source tier it was found in. -/
def findWithSource (cs : CascadingStore) (d : Digest) : Option (Node × SourceTier) :=
  match cs.localStore.find d with
  | some n => some (n, .«local»)
  | none =>
    match cs.upstreamStore.find d with
    | some n => some (n, .upstream)
    | none => none

/-- Local-first put: writes a node into the local store, leaving upstream unchanged. -/
def putLocal (cs : CascadingStore) (n : Node) : Except Admission (Outcome × Digest × CascadingStore) :=
  match cs.localStore.putNode n with
  | .ok (outcome, digest, newLocal) => .ok (outcome, digest, { cs with localStore := newLocal })
  | .error a => .error a

/-- Promote a node from the local store into upstream. -/
def promote (cs : CascadingStore) (d : Digest) : Except Admission (Outcome × Digest × CascadingStore) :=
  match cs.localStore.find d with
  | none => .error (.dangling d)
  | some node =>
    match cs.upstreamStore.putNode node with
    | .ok (outcome, digest, newUpstream) => .ok (outcome, digest, { cs with upstreamStore := newUpstream })
    | .error a => .error a

/-- Sub-store relation: Every node present in `a` is present in `b`. -/
def sub (a b : CascadingStore) : Prop :=
  ∀ d n, a.find d = some n → b.find d = some n

theorem sub_refl (cs : CascadingStore) : cs.sub cs := fun _ _ h => h

theorem sub_trans {a b c : CascadingStore} (h₁ : a.sub b) (h₂ : b.sub c) : a.sub c :=
  fun d n h => h₂ d n (h₁ d n h)

/-- Local put preserves all contained digests (monotonicity). -/
theorem contains_putLocal {cs : CascadingStore} {n : Node} {o : Outcome} {d : Digest} {cs' : CascadingStore}
    (h : cs.putLocal n = .ok (o, d, cs')) {target : Digest}
    (hc : cs.contains target = true) : cs'.contains target = true := by
  dsimp [contains, find] at hc ⊢
  unfold putLocal at h
  split at h
  · next outcome digest newLocal hput =>
    injection h with h
    rcases h with ⟨ho, hd, rfl⟩
    dsimp
    have hsub : cs.localStore.sub newLocal := putNode_sub hput
    cases hloc : cs.localStore.find target with
    | some nodeLoc =>
      have hnew := hsub target nodeLoc hloc
      rw [hnew]
      rfl
    | none =>
      rw [hloc] at hc
      dsimp at hc
      cases hnew : newLocal.find target with
      | some nodeNew => rfl
      | none =>
        dsimp
        exact hc
  · contradiction

/-- Promotion preserves all contained digests (monotonicity). -/
theorem contains_promote {cs : CascadingStore} {d : Digest} {o : Outcome} {d' : Digest} {cs' : CascadingStore}
    (h : cs.promote d = .ok (o, d', cs')) {target : Digest}
    (hc : cs.contains target = true) : cs'.contains target = true := by
  dsimp [contains, find] at hc ⊢
  unfold promote at h
  split at h
  · contradiction
  · next node hloc =>
    split at h
    · next outcome digest newUpstream hput =>
      injection h with h
      rcases h with ⟨ho, hd, rfl⟩
      dsimp
      have hsub : cs.upstreamStore.sub newUpstream := putNode_sub hput
      cases hlocTarget : cs.localStore.find target with
      | some nodeLoc => rfl
      | none =>
        rw [hlocTarget] at hc
        dsimp at hc
        obtain ⟨nodeUp, hup⟩ := Option.isSome_iff_exists.mp hc
        have hnewUp := hsub target nodeUp hup
        rw [hnewUp]
        rfl
    · contradiction

end CascadingStore

end Effect4.Store
