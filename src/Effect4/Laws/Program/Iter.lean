import Effects.Algebra.Laws

/-!
# Program.Iter: budgeted iteration in the free monad

The single home of budgets for every loop-shaped meaning (the `select` and `iterate` packet
§2.2, the core constructs brief §4). `iter f k x` runs the step `f` from the cursor `x` at most
`k` times: a step answers `inl y` to stop with `y` and `inr x'` to continue at `x'`. `none`
means the budget ended first. It is Elgot iteration cut at a budget, generic over the
signature, so the loop arm of a meaning is one application of it.

`iter_zero` and `iter_succ` are the unfolding. `iter_uniform` is uniformity: a pure change of
the cursor's representation relates two iterations, which is the law an index cursor against an
`uncons` cursor needs, and at `h := id` the law that replaces one step function by an equal one.
-/

set_option autoImplicit false

namespace Effect4.Program.Denote

variable {S : Effects.Signature.{0, 0}} {X X' Y : Type}

/-- What a step's answer does: stop with the answer, or go on at the next cursor. -/
def iterNext (next : X → Effects.Program S (Option Y)) : Y ⊕ X → Effects.Program S (Option Y)
  | .inl y => pure (some y)
  | .inr x' => next x'

/-- Budgeted iteration: `f` answers `inl` to stop with a result and `inr` to continue with the
next cursor. `none` means the budget ended first. -/
def iter (f : X → Effects.Program S (Y ⊕ X)) : Nat → X → Effects.Program S (Option Y)
  | 0, _ => pure none
  | k + 1, x => f x >>= iterNext (iter f k)

theorem iter_zero (f : X → Effects.Program S (Y ⊕ X)) (x : X) : iter f 0 x = pure none := rfl

theorem iter_succ (f : X → Effects.Program S (Y ⊕ X)) (k : Nat) (x : X) :
    iter f (k + 1) x = f x >>= iterNext (iter f k) := rfl

/-- Uniformity: a pure change of cursor representation relates two iterations. -/
theorem iter_uniform (f : X → Effects.Program S (Y ⊕ X)) (g : X' → Effects.Program S (Y ⊕ X'))
    (h : X → X') (hfg : ∀ x, Sum.map id h <$> f x = g (h x)) :
    ∀ (k : Nat) (x : X), iter f k x = iter g k (h x)
  | 0, _ => rfl
  | k + 1, x => by
    rw [iter_succ, iter_succ, ← hfg x, bind_map_left]
    refine bind_congr fun r => ?_
    cases r with
    | inl y => rfl
    | inr x' => exact iter_uniform f g h hfg k x'

/-- Two step functions that agree give the same iteration. -/
theorem iter_congr (f g : X → Effects.Program S (Y ⊕ X)) (hfg : ∀ x, f x = g x) (k : Nat)
    (x : X) : iter f k x = iter g k x := by
  exact iter_uniform f g id (fun x => by rw [Sum.map_id_id, id_map, hfg x]; rfl) k x

end Effect4.Program.Denote
