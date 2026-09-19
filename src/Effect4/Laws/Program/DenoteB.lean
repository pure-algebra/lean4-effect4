import Effect4.Laws.Program.Denote
import Effect4.Laws.Program.Iter

/-!
# Program.DenoteB: the loop-bearing fragment at a budget

The budgeted meaning of the `select` and `iterate` packet §2.3. `denoteB k e env` answers
`Option ExitV`: `none` is an unfinished program (the budget ended inside), and because the
answer is read through the store handler, the stores written so far are kept. The fragment is
`Looped`: the straight fragment's own clauses with `iterate` added, so a loop may stand under a
sequence, a suspension, a decision, a handler, a finalizer or a reified exit, and inside
another loop's body. Every other form is outside, as it is for `denote`.

Every composite arm is `thenB`: run the first program, stop unfinished if it is, otherwise
continue from its exit. The arms differ only in the continuation, which is `denote`'s.

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

/-- Sequencing at a budget: an unfinished first program ends the whole unfinished. -/
def thenB (p : Effects.Program StoreSig (Option ExitV))
    (rest : ExitV → Effects.Program StoreSig (Option ExitV)) :
    Effects.Program StoreSig (Option ExitV) :=
  p >>= fun
    | none => pure none
    | some ex => rest ex

theorem runP_thenB_none {p : Effects.Program StoreSig (Option ExitV)}
    {rest : ExitV → Effects.Program StoreSig (Option ExitV)} {s s₁ : Stores}
    (h : runP p s = (none, s₁)) : runP (thenB p rest) s = (none, s₁) := by
  unfold thenB
  rw [runP_bind, h]
  rfl

theorem runP_thenB_some {p : Effects.Program StoreSig (Option ExitV)}
    {rest : ExitV → Effects.Program StoreSig (Option ExitV)} {s s₁ : Stores} {ex : ExitV}
    (h : runP p s = (some ex, s₁)) : runP (thenB p rest) s = runP (rest ex) s₁ := by
  unfold thenB
  rw [runP_bind, h]

/-- A finished sequence finished its first program, and the rest finished from there. -/
theorem runP_thenB_inv {p : Effects.Program StoreSig (Option ExitV)}
    {rest : ExitV → Effects.Program StoreSig (Option ExitV)} {s s' : Stores} {x : ExitV}
    (h : runP (thenB p rest) s = (some x, s')) :
    ∃ ex s₁, runP p s = (some ex, s₁) ∧ runP (rest ex) s₁ = (some x, s') := by
  rcases hp : runP p s with ⟨r, s₁⟩
  cases r with
  | none =>
    rw [runP_thenB_none hp] at h
    cases h
  | some ex =>
    rw [runP_thenB_some hp] at h
    exact ⟨ex, s₁, rfl, h⟩

/-- Over a program that always finishes, `thenB` is the plain sequence. -/
theorem thenB_map_some (p : Effects.Program StoreSig ExitV)
    (rest : ExitV → Effects.Program StoreSig (Option ExitV)) :
    thenB (some <$> p) rest = p >>= rest := by
  unfold thenB
  rw [bind_map_left]

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

/-- The loop-bearing fragment: `Straight`'s clauses, with `iterate` over a body of the
fragment. Every constructor is named (no fallback arm), so a constructor added to `Eff` is a
missing case here until it is classified (row 35, the fragment by exclusion); the leaves and
the exclusions are `Straight`'s, arm for arm (`Looped.of_straight`). -/
def Looped : NativeEff → Bool
  | .succeed _ => true
  | .fail _ => true
  | .failCause _ => true
  | .sync _ => true
  | .perform op _ =>
    match op.kind with
    | .sync => true
    | _ => false
  | .iterate _ _ _ _ _ body => Looped body
  | .suspend b => Looped b
  | .bind a b => Looped a && Looped b
  | .select _ _ a b => Looped a && Looped b
  | .exit b => Looped b
  | .catchCause b h => Looped b && Looped h
  | .matchCause b v c => Looped b && Looped v && Looped c
  | .onExit b f => Looped b && Looped f
  | .gen _ => false
  | .uninterruptible _ => false
  | .interruptible _ => false
  | .yieldNow _ => false
  | .awaitFiber _ _ => false
  | .withFiber _ => false
  | .scoped _ => false
  | .acquireRelease _ _ => false
  | .provideLayer _ _ _ => false
  | .service _ => false
  | .provideService _ _ _ => false
  | .catchIf _ _ _ => false

/-! ## The fragment's subprograms -/

theorem Looped.bind {a b : NativeEff} (h : Looped (.bind a b) = true) :
    Looped a = true ∧ Looped b = true := by
  simpa [Looped, Bool.and_eq_true] using h

theorem Looped.select {t : Term} {d : Decision} {a b : NativeEff}
    (h : Looped (.select t d a b) = true) : Looped a = true ∧ Looped b = true := by
  simpa [Looped, Bool.and_eq_true] using h

theorem Looped.catchCause {b h' : NativeEff} (h : Looped (.catchCause b h') = true) :
    Looped b = true ∧ Looped h' = true := by
  simpa [Looped, Bool.and_eq_true] using h

theorem Looped.matchCause {b v c : NativeEff} (h : Looped (.matchCause b v c) = true) :
    Looped b = true ∧ Looped v = true ∧ Looped c = true := by
  simpa [Looped, Bool.and_eq_true, and_assoc] using h

theorem Looped.onExit {b f : NativeEff} (h : Looped (.onExit b f) = true) :
    Looped b = true ∧ Looped f = true := by
  simpa [Looped, Bool.and_eq_true] using h

theorem Looped.suspend {b : NativeEff} (h : Looped (.suspend b) = true) : Looped b = true := by
  simpa [Looped] using h

theorem Looped.exit {b : NativeEff} (h : Looped (.exit b) = true) : Looped b = true := by
  simpa [Looped] using h

theorem Looped.iterate {c : Option Ty} {i t st r : Term} {b : NativeEff}
    (h : Looped (.iterate c i t st r b) = true) : Looped b = true := by
  simpa [Looped] using h

/-- Where the fragment meets the heads whose suspension body the compile decides itself: a
source suspension, a decision, and a loop. -/
theorem Looped.suspendDecided_iff {e : NativeEff} (hl : Looped e = true) :
    e.suspendDecided = true ↔
      (∃ b, e = .suspend b) ∨ (∃ s d a b, e = .select s d a b) ∨
        (∃ c i t st r b, e = .iterate c i t st r b) := by
  cases e <;> simp [Eff.suspendDecided, Looped] at hl ⊢

/-- The forms the budgeted meaning descends into. Every other form is a leaf. -/
def composite : NativeEff → Bool
  | .iterate _ _ _ _ _ _ | .suspend _ | .bind _ _ | .select _ _ _ _ | .exit _
  | .catchCause _ _ | .matchCause _ _ _ | .onExit _ _ => true
  | _ => false

/-- A leaf at a budget: the straight meaning, or the outside exit. It does not read the
budget. -/
def leafB (e : NativeEff) (env : List Val) : Effects.Program StoreSig (Option ExitV) :=
  if Straight e then some <$> denote e env else pure (some outsideExit)

/-- The loop-bearing fragment at a budget: `none` is an unfinished program, its stores kept.
Each composite arm is `denote`'s arm with `thenB` for the sequence. -/
def denoteB (k : Nat) : NativeEff → List Val → Effects.Program StoreSig (Option ExitV)
  | .iterate _ initial test step result body, env =>
    match evalTerm env initial with
    | some c₀ =>
      Option.join <$> iter (iterateStep (fun env' => denoteB k body env') env test step result) k c₀
    | none => pure (some badShapeExit)
  | .suspend b, env => denoteB k b env
  | .bind a b, env => thenB (denoteB k a env) fun
    | Exit.success v => denoteB k b (env ++ [v])
    | Exit.failure c => pure (some (Exit.failure c))
  | .select t d a b, env =>
    match (evalTerm env t).bind d.decide with
    | some (true, bound) => denoteB k a (env ++ bound.toList)
    | some (false, bound) => denoteB k b (env ++ bound.toList)
    | none => pure (some badShapeExit)
  | .exit b, env => thenB (denoteB k b env) fun ex => pure (some (Exit.success (reifyExitVal ex)))
  | .catchCause b h, env => thenB (denoteB k b env) fun
    | Exit.success v => pure (some (Exit.success v))
    | Exit.failure c => denoteB k h (env ++ [Val.exitErr c])
  | .matchCause b v c, env => thenB (denoteB k b env) fun
    | Exit.success x => denoteB k v (env ++ [x])
    | Exit.failure cause => denoteB k c (env ++ [Val.exitErr cause])
  | .onExit b f, env => thenB (denoteB k b env) fun ex =>
    thenB (denoteB k f (env ++ [reifyExitVal ex])) fun fex =>
      pure (some (Exit.restoreAfterFinalizer ex (finVoid fex)))
  | e, env => leafB e env

/-- A leaf's budgeted meaning does not read the budget. -/
theorem denoteB_leaf (k : Nat) (e : NativeEff) (env : List Val) (h : composite e = false) :
    denoteB k e env = leafB e env := by
  rw [denoteB] <;> intros <;> subst_vars <;> cases h

/-- The budgeted meaning run from some stores. -/
def meaningB (k : Nat) (e : NativeEff) (env : List Val) (s : Stores) : Option ExitV × Stores :=
  runP (denoteB k e env) s

/-! ## The lemmas -/

/-- An unfinished first program leaves the sequence unfinished, at the first program's stores. -/
theorem denoteB_bind_none (k : Nat) (a b : NativeEff) (env : List Val) (s s₁ : Stores)
    (h : meaningB k a env s = (none, s₁)) : meaningB k (.bind a b) env s = (none, s₁) := by
  unfold meaningB at h ⊢
  rw [denoteB]
  exact runP_thenB_none h

/-- The straight fragment is inside the loop-bearing one. -/
theorem Looped.of_straight : ∀ (e : NativeEff), Straight e = true → Looped e = true
  | .suspend b, h => by rw [Looped]; exact Looped.of_straight b (Straight.suspend h)
  | .bind a b, h => by
    rw [Looped, Looped.of_straight a (Straight.bind h).1, Looped.of_straight b (Straight.bind h).2]
    rfl
  | .select _ _ a b, h => by
    rw [Looped, Looped.of_straight a (Straight.select h).1,
      Looped.of_straight b (Straight.select h).2]
    rfl
  | .exit b, h => by rw [Looped]; exact Looped.of_straight b (Straight.exit h)
  | .catchCause b h', h => by
    rw [Looped, Looped.of_straight b (Straight.catchCause h).1,
      Looped.of_straight h' (Straight.catchCause h).2]
    rfl
  | .matchCause b v c, h => by
    rw [Looped, Looped.of_straight b (Straight.matchCause h).1,
      Looped.of_straight v (Straight.matchCause h).2.1,
      Looped.of_straight c (Straight.matchCause h).2.2]
    rfl
  | .onExit b f, h => by
    rw [Looped, Looped.of_straight b (Straight.onExit h).1,
      Looped.of_straight f (Straight.onExit h).2]
    rfl
  | .succeed _, h | .fail _, h | .failCause _, h | .sync _, h | .perform _ _, h => h
  | .iterate _ _ _ _ _ _, h | .gen _, h | .uninterruptible _, h | .interruptible _, h
  | .yieldNow _, h | .awaitFiber _ _, h
  | .withFiber _, h | .scoped _, h | .acquireRelease _ _, h | .provideLayer _ _ _, h
  | .service _, h | .provideService _ _ _, h | .catchIf _ _ _, h => absurd h Bool.false_ne_true

/-- On the straight fragment the budgeted meaning is `denote`: every straight-fragment theorem
is a corollary. -/
theorem denoteB_straight (k : Nat) :
    ∀ (e : NativeEff) (env : List Val), Straight e = true →
      denoteB k e env = some <$> denote e env
  | .suspend b, env, h => by
    rw [denoteB, denote]
    exact denoteB_straight k b env (Straight.suspend h)
  | .bind a b, env, h => by
    obtain ⟨ha, hb⟩ := Straight.bind h
    rw [denoteB, denoteB_straight k a env ha, thenB_map_some, denote,
      show (denote a env).bind (seqExit fun v => denote b (env ++ [v])) =
        denote a env >>= seqExit fun v => denote b (env ++ [v]) from rfl, map_bind]
    refine bind_congr fun ex => ?_
    cases ex with
    | success v => exact denoteB_straight k b (env ++ [v]) hb
    | failure c => exact (map_pure _ _).symm
  | .select t d a b, env, h => by
    obtain ⟨ha, hb⟩ := Straight.select h
    rw [denoteB, denote]
    cases hd : (evalTerm env t).bind d.decide with
    | none => exact (map_pure _ _).symm
    | some r =>
      obtain ⟨flag, bound⟩ := r
      cases flag with
      | true => exact denoteB_straight k a (env ++ bound.toList) ha
      | false => exact denoteB_straight k b (env ++ bound.toList) hb
  | .exit b, env, h => by
    rw [denoteB, denoteB_straight k b env (Straight.exit h), thenB_map_some, denote,
      show (denote b env).bind (fun ex => pure (Exit.success (reifyExitVal ex))) =
        denote b env >>= fun ex => pure (Exit.success (reifyExitVal ex)) from rfl, map_bind]
    exact bind_congr fun ex => (map_pure _ _).symm
  | .catchCause b h', env, h => by
    obtain ⟨hb, hh⟩ := Straight.catchCause h
    rw [denoteB, denoteB_straight k b env hb, thenB_map_some, denote]
    show _ = some <$> (denote b env >>= _)
    rw [map_bind]
    refine bind_congr fun ex => ?_
    cases ex with
    | success v => exact (map_pure _ _).symm
    | failure c => exact denoteB_straight k h' (env ++ [Val.exitErr c]) hh
  | .matchCause b v c, env, h => by
    obtain ⟨hb, hv, hc⟩ := Straight.matchCause h
    rw [denoteB, denoteB_straight k b env hb, thenB_map_some, denote]
    show _ = some <$> (denote b env >>= _)
    rw [map_bind]
    refine bind_congr fun ex => ?_
    cases ex with
    | success x => exact denoteB_straight k v (env ++ [x]) hv
    | failure cause => exact denoteB_straight k c (env ++ [Val.exitErr cause]) hc
  | .onExit b f, env, h => by
    obtain ⟨hb, hf⟩ := Straight.onExit h
    rw [denoteB, denoteB_straight k b env hb, thenB_map_some, denote]
    show _ = some <$> (denote b env >>= _)
    rw [map_bind]
    refine bind_congr fun ex => ?_
    rw [denoteB_straight k f (env ++ [reifyExitVal ex]) hf, thenB_map_some]
    show _ = some <$> (denote f (env ++ [reifyExitVal ex]) >>= _)
    rw [map_bind]
    exact bind_congr fun fex => (map_pure _ _).symm
  | .iterate _ _ _ _ _ _, _, h => absurd h Bool.false_ne_true
  | .succeed _, env, h | .fail _, env, h | .failCause _, env, h
  | .sync _, env, h | .perform _ _, env, h | .gen _, env, h
  | .uninterruptible _, env, h | .interruptible _, env, h
  | .yieldNow _, env, h
  | .awaitFiber _ _, env, h | .withFiber _, env, h | .scoped _, env, h
  | .acquireRelease _ _, env, h | .provideLayer _ _ _, env, h | .service _, env, h
  | .provideService _ _ _, env, h | .catchIf _ _ _, env, h => by
    rw [denoteB_leaf k _ env rfl, leafB, if_pos h]

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
  | .suspend b, k, env, s, x, s', h => by
    unfold meaningB at h ⊢
    rw [denoteB] at h ⊢
    exact denoteB_mono b k env s x s' h
  | .bind a b, k, env, s, x, s', h => by
    unfold meaningB at h ⊢
    rw [denoteB] at h ⊢
    obtain ⟨ex, s₁, ha, hrest⟩ := runP_thenB_inv h
    rw [runP_thenB_some (denoteB_mono a k env s ex s₁ ha)]
    cases ex with
    | success v => exact denoteB_mono b k (env ++ [v]) s₁ x s' hrest
    | failure c => exact hrest
  | .select t d a b, k, env, s, x, s', h => by
    unfold meaningB at h ⊢
    rw [denoteB] at h ⊢
    cases hd : (evalTerm env t).bind d.decide with
    | none => rw [hd] at h; exact h
    | some r =>
      rw [hd] at h
      obtain ⟨flag, bound⟩ := r
      cases flag with
      | true => exact denoteB_mono a k (env ++ bound.toList) s x s' h
      | false => exact denoteB_mono b k (env ++ bound.toList) s x s' h
  | .exit b, k, env, s, x, s', h => by
    unfold meaningB at h ⊢
    rw [denoteB] at h ⊢
    obtain ⟨ex, s₁, hb, hrest⟩ := runP_thenB_inv h
    rw [runP_thenB_some (denoteB_mono b k env s ex s₁ hb)]
    exact hrest
  | .catchCause b h', k, env, s, x, s', h => by
    unfold meaningB at h ⊢
    rw [denoteB] at h ⊢
    obtain ⟨ex, s₁, hb, hrest⟩ := runP_thenB_inv h
    rw [runP_thenB_some (denoteB_mono b k env s ex s₁ hb)]
    cases ex with
    | success v => exact hrest
    | failure c => exact denoteB_mono h' k (env ++ [Val.exitErr c]) s₁ x s' hrest
  | .matchCause b v c, k, env, s, x, s', h => by
    unfold meaningB at h ⊢
    rw [denoteB] at h ⊢
    obtain ⟨ex, s₁, hb, hrest⟩ := runP_thenB_inv h
    rw [runP_thenB_some (denoteB_mono b k env s ex s₁ hb)]
    cases ex with
    | success y => exact denoteB_mono v k (env ++ [y]) s₁ x s' hrest
    | failure cause => exact denoteB_mono c k (env ++ [Val.exitErr cause]) s₁ x s' hrest
  | .onExit b f, k, env, s, x, s', h => by
    unfold meaningB at h ⊢
    rw [denoteB] at h ⊢
    obtain ⟨ex, s₁, hb, hrest⟩ := runP_thenB_inv h
    rw [runP_thenB_some (denoteB_mono b k env s ex s₁ hb)]
    obtain ⟨fex, s₂, hf, hlast⟩ := runP_thenB_inv hrest
    rw [runP_thenB_some (denoteB_mono f k (env ++ [reifyExitVal ex]) s₁ fex s₂ hf)]
    exact hlast
  | .succeed _, k, env, s, x, s', h | .fail _, k, env, s, x, s', h
  | .failCause _, k, env, s, x, s', h
  | .sync _, k, env, s, x, s', h | .perform _ _, k, env, s, x, s', h
  | .gen _, k, env, s, x, s', h | .uninterruptible _, k, env, s, x, s', h
  | .interruptible _, k, env, s, x, s', h
  | .yieldNow _, k, env, s, x, s', h
  | .awaitFiber _ _, k, env, s, x, s', h | .withFiber _, k, env, s, x, s', h
  | .scoped _, k, env, s, x, s', h | .acquireRelease _ _, k, env, s, x, s', h
  | .provideLayer _ _ _, k, env, s, x, s', h | .service _, k, env, s, x, s', h
  | .provideService _ _ _, k, env, s, x, s', h | .catchIf _ _ _, k, env, s, x, s', h => by
    unfold meaningB at h ⊢
    rw [denoteB_leaf k _ env rfl] at h
    rw [denoteB_leaf (k + 1) _ env rfl]
    exact h

/-- A finished answer holds at every larger budget. -/
theorem denoteB_mono_le (e : NativeEff) (env : List Val) (s : Stores) (x : ExitV) (s' : Stores)
    {k k' : Nat} (hk : k ≤ k') (h : meaningB k e env s = (some x, s')) :
    meaningB k' e env s = (some x, s') := by
  induction hk with
  | refl => exact h
  | step _ ih => exact denoteB_mono e _ env s x s' ih

/-- The finished answer of a program is one: two budgets that both finish agree, stores
included. This is what makes "the meaning of a loop" a function of the program. -/
theorem meaningB_unique (e : NativeEff) (env : List Val) (s : Stores) {k k' : Nat}
    {x x' : ExitV} {s₁ s₂ : Stores} (h : meaningB k e env s = (some x, s₁))
    (h' : meaningB k' e env s = (some x', s₂)) : x = x' ∧ s₁ = s₂ := by
  have a := denoteB_mono_le e env s x s₁ (Nat.le_max_left k k') h
  have b := denoteB_mono_le e env s x' s₂ (Nat.le_max_right k k') h'
  rw [a] at b
  cases b
  exact ⟨rfl, rfl⟩

end Effect4.Program.Denote
