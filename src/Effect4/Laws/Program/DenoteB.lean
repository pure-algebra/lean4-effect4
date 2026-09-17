import Effect4.Laws.Program.Denote
import Effect4.Laws.Program.Iter

/-!
# Program.DenoteB: the loop-bearing fragment at a budget

The budgeted meaning of the `select` and `iterate` packet §2.3. `denoteB k e env` answers
`Option ExitV`: `none` is an unfinished program (the budget ended inside), and because the
answer is read through the store handler, the stores written so far are kept. The fragment is
sequences (`bind`) of loops (`iterate`) and straight programs; every other form is outside, as
it is for `denote`.

`iterateStep` is one round of a loop, in the shape `iter` takes: the test over the cursor, the
body, the step over the cursor and the body's answer, and at a failed test the result over the
cursor. Its raw-program rule is the machine's (`loopNextAt`, `loopResumeAt`, `loopFinishAt`): a
test that is not a Boolean, a step or a result that does not evaluate, is the wrong shape. An
unfinished body stops the loop unfinished (`inl none`), which is how nesting is carried: by the
answer type, not by a loop law.

Three lemmas carry what the plan's nesting clause asks for, and none mentions two loops:
`denoteB_bind_none` (an unfinished first program leaves the sequence unfinished at the first
program's stores), `denoteB_straight` (on the straight fragment the budgeted meaning is
`denote`, so every straight theorem is a corollary), and `denoteB_mono` (a finished answer at
`k` is the same answer at `k + 1`, stores included). The relation to the machine stays
existential; no step formula is claimed.
-/

set_option autoImplicit false

namespace Effect4.Program.Denote

open Effect4 Effect4.Machine Effect4.Program

/-! ## Running a program of the store signature -/

/-- A program of the store signature run from some stores: its answer and the stores left. -/
def runP {A : Type} (p : Effects.Program StoreSig A) (s : Stores) : A × Stores :=
  (Effects.interpret storeHandler p).run s

theorem runP_pure {A : Type} (a : A) (s : Stores) :
    runP (pure a : Effects.Program StoreSig A) s = (a, s) := rfl

theorem runP_bind {A B : Type} (p : Effects.Program StoreSig A)
    (c : A → Effects.Program StoreSig B) (s : Stores) :
    runP (p >>= c) s = runP (c (runP p s).1) (runP p s).2 := by
  unfold runP
  rw [show p >>= c = p.bind c from rfl, Effects.interpret_bind, StateT.run_bind]
  rfl

theorem runP_map {A B : Type} (φ : A → B) (p : Effects.Program StoreSig A) (s : Stores) :
    runP (φ <$> p) s = (φ (runP p s).1, (runP p s).2) := by
  rw [← bind_pure_comp, runP_bind]
  rfl

/-! ## The budgeted meaning -/

/-- One round of a loop at the cursor `c`, in `iter`'s shape. `body` is the body's budgeted
meaning as a function of its environment. -/
def iterateStep (body : List Val → Effects.Program StoreSig (Option ExitV)) (env : List Val)
    (test step result : Term) (c : Val) : Effects.Program StoreSig (Option ExitV ⊕ Val) :=
  match evalTerm (env ++ [c]) test with
  | some (Val.bool true) => body (env ++ [c]) >>= fun
    | none => pure (.inl none)
    | some (Exit.failure cause) => pure (.inl (some (Exit.failure cause)))
    | some (Exit.success a) =>
      match evalTerm (env ++ [c, a]) step with
      | some c' => pure (.inr c')
      | none => pure (.inl (some badShapeExit))
  | some (Val.bool false) =>
    pure (.inl (some (match evalTerm (env ++ [c]) result with
      | some v => Exit.success v
      | none => badShapeExit)))
  | _ => pure (.inl (some badShapeExit))

/-- What a sequence does with its first program's budgeted answer. -/
def seqB (rest : Val → Effects.Program StoreSig (Option ExitV)) :
    Option ExitV → Effects.Program StoreSig (Option ExitV)
  | none => pure none
  | some (Exit.failure c) => pure (some (Exit.failure c))
  | some (Exit.success v) => rest v

/-- The loop-bearing fragment at a budget: `none` is an unfinished program, its stores kept. -/
def denoteB (k : Nat) : NativeEff → List Val → Effects.Program StoreSig (Option ExitV)
  | .bind a b, env => denoteB k a env >>= seqB fun v => denoteB k b (env ++ [v])
  | .iterate _ initial test step result body, env =>
    match evalTerm env initial with
    | some c₀ =>
      Option.join <$> iter (iterateStep (fun env' => denoteB k body env') env test step result) k c₀
    | none => pure (some badShapeExit)
  | e, env => if Straight e then some <$> denote e env else pure (some outsideExit)

/-- Outside `bind` and `iterate` the budgeted meaning does not read the budget: it is the
straight meaning, or the outside exit. -/
theorem denoteB_other (k : Nat) (e : NativeEff) (env : List Val)
    (hbind : ∀ a b, e = .bind a b → False)
    (hiterate : ∀ c i t st r b, e = .iterate c i t st r b → False) :
    denoteB k e env = if Straight e then some <$> denote e env else pure (some outsideExit) := by
  rw [denoteB]
  · exact hbind
  · exact hiterate

/-- The budgeted meaning run from some stores. -/
def meaningB (k : Nat) (e : NativeEff) (env : List Val) (s : Stores) : Option ExitV × Stores :=
  runP (denoteB k e env) s

/-! ## The three lemmas -/

/-- An unfinished first program leaves the sequence unfinished, at the first program's stores. -/
theorem denoteB_bind_none (k : Nat) (a b : NativeEff) (env : List Val) (s s₁ : Stores)
    (h : meaningB k a env s = (none, s₁)) : meaningB k (.bind a b) env s = (none, s₁) := by
  unfold meaningB at h ⊢
  rw [denoteB, runP_bind, h]
  rfl

/-- On the straight fragment the budgeted meaning is `denote`: every straight-fragment theorem
is a corollary. -/
theorem denoteB_straight (k : Nat) :
    ∀ (e : NativeEff) (env : List Val), Straight e = true →
      denoteB k e env = some <$> denote e env
  | .bind a b, env, h => by
    obtain ⟨ha, hb⟩ := Straight.bind h
    rw [denoteB, denoteB_straight k a env ha, bind_map_left, denote,
      show (denote a env).bind (seqExit fun v => denote b (env ++ [v])) =
        denote a env >>= seqExit fun v => denote b (env ++ [v]) from rfl, map_bind]
    refine bind_congr fun ex => ?_
    cases ex with
    | success v => exact denoteB_straight k b (env ++ [v]) hb
    | failure c => exact (map_pure _ _).symm
  | .iterate _ _ _ _ _ _, _, h => absurd h Bool.false_ne_true
  | .succeed _, env, h | .fail _, env, h | .failCause _, env, h | .yieldError _, env, h
  | .sync _, env, h | .suspend _, env, h | .perform _ _, env, h | .gen _, env, h
  | .catchCause _ _, env, h | .matchCause _ _ _, env, h | .onExit _ _, env, h | .exit _, env, h
  | .uninterruptible _, env, h | .interruptible _, env, h
  | .whileLoop _ _ _ _, env, h | .yieldNow _, env, h | .callback _ _, env, h
  | .awaitFiber _ _, env, h | .withFiber _, env, h | .scoped _, env, h
  | .acquireRelease _ _, env, h | .provideLayer _ _ _, env, h | .service _, env, h
  | .provideService _ _ _, env, h | .catchIf _ _ _, env, h | .select _ _ _ _, env, h => by
    rw [denoteB_other k _ env (by intro _ _ h; cases h)
      (by intro _ _ _ _ _ _ h; cases h), if_pos h]

/-- Monotonicity of a loop in the budget, given that a larger budget changes no finished round:
a finished answer of `iter f k` is the same answer of `iter g (k + 1)`, stores included. -/
theorem iter_mono (f g : Val → Effects.Program StoreSig (Option ExitV ⊕ Val))
    (hfg : ∀ c s, (runP (f c) s).1 ≠ .inl none → runP (g c) s = runP (f c) s) :
    ∀ (k : Nat) (c : Val) (s : Stores) (x : ExitV) (s' : Stores),
      runP (Option.join <$> iter f k c) s = (some x, s') →
        runP (Option.join <$> iter g (k + 1) c) s = (some x, s')
  | 0, c, s, x, s', h => by
    rw [iter_zero, runP_map, runP_pure] at h
    cases h
  | k + 1, c, s, x, s', h => by
    rw [iter_succ, runP_map, runP_bind] at h
    rw [iter_succ, runP_map, runP_bind]
    rcases hr : runP (f c) s with ⟨r, s₁⟩
    rw [hr] at h
    cases r with
    | inl y =>
      cases y with
      | none =>
        rw [show iterNext (iter f k) (Sum.inl none) = pure (some none) from rfl, runP_pure] at h
        cases h
      | some ex =>
        have hg := hfg c s (by rw [hr]; intro hne; cases hne)
        rw [hg, hr]
        exact h
    | inr c' =>
      have hg := hfg c s (by rw [hr]; intro hne; cases hne)
      rw [hg, hr]
      have ih := iter_mono f g hfg k c' s₁ x s'
      rw [runP_map, runP_map] at ih
      exact ih h

/-- A finished answer at budget `k` is the same answer at `k + 1`, stores included. -/
theorem denoteB_mono :
    ∀ (e : NativeEff) (k : Nat) (env : List Val) (s : Stores) (x : ExitV) (s' : Stores),
      meaningB k e env s = (some x, s') → meaningB (k + 1) e env s = (some x, s')
  | .bind a b, k, env, s, x, s', h => by
    unfold meaningB at h ⊢
    rw [denoteB, runP_bind] at h
    rw [denoteB, runP_bind]
    rcases ha : runP (denoteB k a env) s with ⟨ra, s₁⟩
    rw [ha] at h
    cases ra with
    | none => rw [show seqB _ none = pure none from rfl, runP_pure] at h; cases h
    | some ex =>
      have ha' := denoteB_mono a k env s ex s₁ ha
      unfold meaningB at ha'
      rw [ha']
      cases ex with
      | failure c => exact h
      | success v => exact denoteB_mono b k (env ++ [v]) s₁ x s' h
  | .iterate _ initial test step result body, k, env, s, x, s', h => by
    unfold meaningB at h ⊢
    rw [denoteB] at h ⊢
    cases hi : evalTerm env initial with
    | none => rw [hi] at h; exact h
    | some c₀ =>
      rw [hi] at h
      refine iter_mono _ _ (fun c s₀ hne => ?_) k c₀ s x s' h
      unfold iterateStep at hne ⊢
      cases ht : evalTerm (env ++ [c]) test with
      | none => rfl
      | some tv =>
        cases tv with
        | bool flag =>
          cases flag with
          | false => rfl
          | true =>
            rw [ht] at hne
            dsimp only at hne ⊢
            rw [runP_bind] at hne ⊢
            rcases hb : runP (denoteB k body (env ++ [c])) s₀ with ⟨rb, s₁⟩
            rw [hb] at hne
            cases rb with
            | none => exact absurd rfl hne
            | some ex =>
              have hb' := denoteB_mono body k (env ++ [c]) s₀ ex s₁ hb
              unfold meaningB at hb'
              rw [hb', runP_bind, hb]
        | _ => rfl
  | .succeed _, k, env, s, x, s', h | .fail _, k, env, s, x, s', h
  | .failCause _, k, env, s, x, s', h | .yieldError _, k, env, s, x, s', h
  | .sync _, k, env, s, x, s', h | .suspend _, k, env, s, x, s', h
  | .perform _ _, k, env, s, x, s', h | .gen _, k, env, s, x, s', h
  | .catchCause _ _, k, env, s, x, s', h | .matchCause _ _ _, k, env, s, x, s', h
  | .onExit _ _, k, env, s, x, s', h | .exit _, k, env, s, x, s', h
  | .uninterruptible _, k, env, s, x, s', h | .interruptible _, k, env, s, x, s', h
  | .whileLoop _ _ _ _, k, env, s, x, s', h
  | .yieldNow _, k, env, s, x, s', h | .callback _ _, k, env, s, x, s', h
  | .awaitFiber _ _, k, env, s, x, s', h | .withFiber _, k, env, s, x, s', h
  | .scoped _, k, env, s, x, s', h | .acquireRelease _ _, k, env, s, x, s', h
  | .provideLayer _ _ _, k, env, s, x, s', h | .service _, k, env, s, x, s', h
  | .provideService _ _ _, k, env, s, x, s', h | .catchIf _ _ _, k, env, s, x, s', h
  | .select _ _ _ _, k, env, s, x, s', h => by
    unfold meaningB at h ⊢
    rw [denoteB_other k _ env (by intro _ _ h; cases h)
      (by intro _ _ _ _ _ _ h; cases h)] at h
    rw [denoteB_other (k + 1) _ env (by intro _ _ h; cases h)
      (by intro _ _ _ _ _ _ h; cases h)]
    exact h

end Effect4.Program.Denote
