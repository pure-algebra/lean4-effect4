import Tools.View.Connector
import Tools.View.KeyMap

/-!
# Cached connector outlines

The key contains every input to the connector constructor.
The graph normalizes route coordinates before lookup and moves the answer after lookup.
The laws compare exact integer outlines, without a rasterization claim.

Placement: `docs/research/2026-10-13-continuous-connectors-plan.md`.
These tool laws serve `initial-algebras-folds` and R14 under decisions row 334(3).
-/

namespace Tools.View.Connector

/-- The inputs of a connector outline, after the graph normalizes its route coordinates. -/
structure Request where
  seed : Nat
  noise : Nat
  wave : Nat
  width : Int
  tip : Bool
  segments : List Cubic
  source : Option Dock
  target : Option Dock
deriving DecidableEq, Hashable

/-- The exact integer outline requested by the cache key. -/
def Request.outline (r : Request) : List Cubic :=
  stroke r.seed { noise := r.noise, wave := r.wave } r.width r.segments r.tip r.source r.target

/-- Outlines indexed by all their construction inputs. -/
abbrev Cache := KeyMap Request (List Cubic)

/-- Every cached answer is the exact outline of its request. -/
def Cache.Valid (cache : Cache) : Prop :=
  ∀ r s, cache.get? r = some s → s = r.outline

/-- Read an outline, computing and retaining it on the first request. -/
def cached (cache : Cache) (r : Request) : List Cubic × Cache :=
  match cache.get? r with
  | some s => (s, cache)
  | none => let s := r.outline; (s, cache.insert r s)

/-- Fresh drawing starts with a valid cache. A premise of `cached_eq`. -/
theorem Cache.valid_empty : Cache.Valid {} := by
  intro r s h
  rw [KeyMap.get?_empty] at h
  cases h

/-- A valid cache answers the requested outline. The graph drawing consumes this observation. -/
theorem cached_eq {cache : Cache} (hv : cache.Valid) (r : Request) :
    (cached cache r).1 = r.outline := by
  unfold cached
  cases h : cache.get? r with
  | none => rfl
  | some s => exact hv r s h

/-- Drawing retains validity for the next frame. -/
theorem cached_valid {cache : Cache} (hv : cache.Valid) (r : Request) :
    (cached cache r).2.Valid := by
  unfold cached
  cases h : cache.get? r with
  | some s => exact hv
  | none =>
    intro k s hs
    rw [KeyMap.get?_insert] at hs
    by_cases hk : r = k
    · rw [if_pos hk] at hs
      subst k
      cases hs
      rfl
    · rw [if_neg hk] at hs
      exact hv k s hs

end Tools.View.Connector
