import Effect4.Laws.Program.Agreement
import Effect4.Laws.Program.DenoteB
import Effect4.Laws.Program.LoopAgreement
import Effect4.Laws.Program.Intro.Weight
import Effect4.Laws.Program.LoopSound

/-!
# The loop agreement, layer A: the local run and the budgeted meaning

`Laws/Program/Agreement.lean` proves that the local machine (one fiber, the frame machine's
step over the stores) reaches a straight program's meaning. This module proves the same for
loops, against the budgeted meaning `denoteB` (the packet
`docs/research/2026-09-17-loop-agreement-ready-packet.md`, steps 1 and 2).

* **The loop's steps as local steps.** Entering a loop (`step_whileLoop_enter`), a value
  meeting the loop's frame (`step_success_enter`, through `armA_whileLoop`), a cause passing
  it (`step_failure_pass_whileLoop`: the frame declares the value arm only).
* **Rounds of `iter` are rounds of the frame** (`loop_reaches`). Given the body's agreement
  under the loop's frame, a finished budgeted loop from a cursor is reached by the machine from
  the loop's next decision at that cursor. Induction on the budget; `iterateStep` was written
  arm for arm as `loopNextAt`/`loopResumeAt`/`loopFinishAt`, and this is where that pays.
* **The agreement** (`localRun_compileB`, `localRun_rootB`) on all of `Looped`: a loop under
  a sequence, a suspension, a decision, a handler, a finalizer, a reified exit, or another loop.
  The composite arms are the straight proof's with `runP_thenB_inv` splitting the hypothesis
  where that proof rewrites with `meaning_*`; the straight leaves go through
  `localRun_compile`; a folded `exit` is straight (`straight_of_asExit`). There is no step
  bound: a loop's count is its rounds, so the statement is existential, as `LoopAgreement` is.
  Compile fuel is by depth, never by round (`depthB`, which is `depth` on straight programs).

Not here yet: layer B, the real machine's command loop over the local run
(`Agreement/Machine.lean`, whose plain invariant must learn the loop frame). Until layer B,
this is a theorem about the local machine.
-/

set_option autoImplicit false

namespace Effect4.Program.Agreement

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote

variable (root : NativeEff)

/-- The point a loop's hooks read: the loop's own point, with the local run's empty view of
completed fibers. -/
abbrev loopPoint (p : Point) : Point := { p with completed := [] }

/-- Entering a loop whose test holds: the body runs under the loop's frame. -/
theorem step_whileLoop_continue (p : Point) (c next : Val) (body : NCode) (K : List NCode)
    (i : Bool) (s : Stores) (h : loopNextAt root (loopPoint p) c = .continue next body) :
    localStep root (fiberOf (Prim.whileLoop (EffName.loop p) c) K i) s =
      .running (fiberOf body (Prim.whileLoop (EffName.loop p) next :: K) i) s := by
  have hstep := FrameFiber.step_whileLoop_true (primOf root) (fiberOf (Prim.whileLoop (EffName.loop p) c) K i)
    (EffName.loop p) c next body h
  show ofFrameStep ((fiberOf (Prim.whileLoop (EffName.loop p) c) K i).step (primOf root)).1 s = _
  rw [show fiberOf (Prim.whileLoop (EffName.loop p) c) K i =
    FrameFiber.mk (Prim.whileLoop (EffName.loop p) c) K i none false from rfl] at hstep ⊢
  rw [hstep]
  rfl

/-- Entering a loop that finishes at once: the finishing code, no frame. -/
theorem step_whileLoop_finish (p : Point) (c : Val) (code : NCode) (K : List NCode)
    (i : Bool) (s : Stores) (h : loopNextAt root (loopPoint p) c = .finish code) :
    localStep root (fiberOf (Prim.whileLoop (EffName.loop p) c) K i) s =
      .running (fiberOf code K i) s := by
  have hstep := FrameFiber.step_whileLoop_false (primOf root) (fiberOf (Prim.whileLoop (EffName.loop p) c) K i)
    (EffName.loop p) c code h
  show ofFrameStep ((fiberOf (Prim.whileLoop (EffName.loop p) c) K i).step (primOf root)).1 s = _
  rw [show fiberOf (Prim.whileLoop (EffName.loop p) c) K i =
    FrameFiber.mk (Prim.whileLoop (EffName.loop p) c) K i none false from rfl] at hstep ⊢
  rw [hstep]
  rfl

/-- The loop frame's value arm, read at the local interp. -/
theorem armA_whileLoop (p : Point) (c v : Val) (provided : Option ExitV) :
    (Prim.whileLoop (EffName.loop p) c : NCode).armA (primOf root) v provided =
      (match loopResumeAt root (loopPoint p) c v with
       | .continue next body => some (body, [Prim.whileLoop (EffName.loop p) next])
       | .finish code => some (code, [])) := by
  simp only [Prim.armA]
  have hres : PrimInterp.loopResume (primOf root) (EffName.loop p) c v =
      loopResumeAt root (loopPoint p) c v := rfl
  rw [hres]
  cases loopResumeAt root (loopPoint p) c v <;> rfl

/-- A value meets the loop's frame: the step, then the test, then the body under the frame at
the stepped cursor or the finishing code. -/
theorem step_success_whileLoop (p : Point) (c v : Val) (K : List NCode) (i : Bool) (s : Stores) :
    localStep root (fiberOf (Prim.success v) (Prim.whileLoop (EffName.loop p) c :: K) i) s =
      (match loopResumeAt root (loopPoint p) c v with
       | .continue next body =>
         .running (fiberOf body (Prim.whileLoop (EffName.loop p) next :: K) i) s
       | .finish code => .running (fiberOf code K i) s) := by
  let pop : NPop :=
    ⟨ContAnswer.frame (Prim.whileLoop (EffName.loop p) c), [], [], fiberOf (Prim.success v) K i⟩
  have hanswer : (popOf (fiberOf (Prim.success v) (Prim.whileLoop (EffName.loop p) c :: K) i)
      (Exit.success v)).answer = pop.answer := by cases i <;> rfl
  have hfiber : (popOf (fiberOf (Prim.success v) (Prim.whileLoop (EffName.loop p) c :: K) i)
      (Exit.success v)).fiber = pop.fiber := by cases i <;> rfl
  have h0 : localStep root
        (fiberOf (Prim.success v) (Prim.whileLoop (EffName.loop p) c :: K) i) s =
      exitFrom root (Exit.success v)
        (popOf (fiberOf (Prim.success v) (Prim.whileLoop (EffName.loop p) c :: K) i)
          (Exit.success v)) s := rfl
  rw [h0, exitFrom_ext root (Exit.success v) s hanswer hfiber]
  have h1 : exitFrom root (Exit.success v) pop s =
      ofFrameStep (resumeOf root (Exit.success v) pop) s := rfl
  rw [h1]
  simp only [resumeOf, pop, armA_whileLoop]
  cases loopResumeAt root (loopPoint p) c v <;> rfl

/-- A cause passes the loop's frame, which declares the value arm only. -/
theorem step_failure_pass_whileLoop (p : Point) (c : Val) (cause : CauseV) (K : List NCode)
    (i : Bool) (s : Stores) :
    localStep root (fiberOf (Prim.failure cause) (Prim.whileLoop (EffName.loop p) c :: K) i) s =
      localStep root (fiberOf (Prim.failure cause) K i) s := by
  have hpop := popFrom_pass Effect4.Arm.contE true (Prim.whileLoop (EffName.loop p) c) K
    (Prim.failure cause) i rfl rfl
  exact exitFrom_ext root _ s hpop.1 hpop.2

/-! ## Rounds of `iter` are rounds of the loop frame -/

/-- Where a loop's next decision leaves the fiber: the body under the frame, or the finishing
code with the frame gone. -/
def enter (q : Point) (K : List NCode) (i : Bool) : LoopNext Val NCode → NFiber
  | .continue next body => fiberOf body (Prim.whileLoop (EffName.loop q) next :: K) i
  | .finish code => fiberOf code K i

theorem step_whileLoop_enter (q : Point) (hq : loopPoint q = q) (c : Val) (K : List NCode)
    (i : Bool) (s : Stores) :
    localStep root (fiberOf (Prim.whileLoop (EffName.loop q) c) K i) s =
      .running (enter q K i (loopNextAt root q c)) s := by
  cases h : loopNextAt root q c with
  | «continue» next body =>
    exact step_whileLoop_continue root q c next body K i s (by rw [hq]; exact h)
  | finish code => exact step_whileLoop_finish root q c code K i s (by rw [hq]; exact h)

theorem step_success_enter (q : Point) (hq : loopPoint q = q) (c v : Val) (K : List NCode)
    (i : Bool) (s : Stores) :
    localStep root (fiberOf (Prim.success v) (Prim.whileLoop (EffName.loop q) c :: K) i) s =
      .running (enter q K i (loopResumeAt root q c v)) s := by
  rw [step_success_whileLoop, hq]
  cases loopResumeAt root q c v <;> rfl

/-- A finished round finishes the loop with the round's answer. -/
theorem iter_run_inl {f : Val → Effects.Program StoreSig (Option ExitV ⊕ Val)} (j : Nat)
    {c : Val} {s s₁ : Stores} {y : Option ExitV} (h : runP (f c) s = (.inl y, s₁)) :
    runP (Option.join <$> iter f (j + 1) c) s = (y, s₁) := by
  rw [iter_succ, runP_map, runP_bind, h,
    show iterNext (iter f j) (Sum.inl y) = pure (some y) from rfl, runP_pure]
  rfl

/-- A continuing round hands the rest of the budget the stepped cursor. -/
theorem iter_run_inr {f : Val → Effects.Program StoreSig (Option ExitV ⊕ Val)} (j : Nat)
    {c c' : Val} {s s₁ : Stores} (h : runP (f c) s = (.inr c', s₁)) :
    runP (Option.join <$> iter f (j + 1) c) s = runP (Option.join <$> iter f j c') s₁ := by
  rw [iter_succ, runP_map, runP_bind, h,
    show iterNext (iter f j) (Sum.inr c') = iter f j c' from rfl, runP_map]

theorem loopAt_iterate {q : Point} {cty : Ty} {init test step result : Term} {body : NativeEff}
    (h : Node.at_ (Node.eff root) q.path =
      some (Node.eff (.iterate cty init test step result body))) :
    loopAt root q = some (test, step, body) := by
  unfold loopAt
  rw [h]

theorem loopResultAt_iterate {q : Point} {cty : Ty} {init test step result : Term}
    {body : NativeEff}
    (h : Node.at_ (Node.eff root) q.path =
      some (Node.eff (.iterate cty init test step result body))) :
    loopResultAt root q = some result := by
  unfold loopResultAt
  rw [h]

/-- **Rounds of `iter` are rounds of the loop frame.** Given the body's agreement under the
loop's frame, a finished budgeted loop from the cursor `c` is reached by the machine from the
loop's next decision at `c`. -/
theorem loop_reaches (k : Nat) (q : Point) (hq : loopPoint q = q) {cty : Ty}
    {init test step result : Term} {body : NativeEff}
    (h : Node.at_ (Node.eff root) q.path =
      some (Node.eff (.iterate cty init test step result body)))
    (K : List NCode) (i : Bool)
    (hbody : ∀ (c : Val) (s : Stores) (ex : ExitV) (s' : Stores),
      meaningB k body (q.env ++ [c]) s = (some ex, s') →
      ∃ n, Reaches root n
        (fiberOf (resolve root (q.childWith 0 c)) (Prim.whileLoop (EffName.loop q) c :: K) i) s
        (fiberOf (Prim.ofExit ex) (Prim.whileLoop (EffName.loop q) c :: K) i) s') :
    ∀ (j : Nat) (c : Val) (s : Stores) (ex : ExitV) (s' : Stores),
      runP (Option.join <$> iter
        (iterateStep (fun env' => denoteB k body env') q.env test step result) j c) s =
          (some ex, s') →
      ∃ n, Reaches root n (enter q K i (loopNextAt root q c)) s (fiberOf (Prim.ofExit ex) K i) s'
  | 0, c, s, ex, s', hrun => by
    rw [iter_zero, runP_map, runP_pure] at hrun
    cases hrun
  | j + 1, c, s, ex, s', hrun => by
    have hNext : ∀ {x : Option Val} {ln : LoopNext Val NCode}, evalTerm (q.env ++ [c]) test = x →
        (match x with
         | some (Val.bool true) => LoopNext.continue c (resolve root (q.childWith 0 c))
         | some (Val.bool false) => .finish (loopFinishAt root q c)
         | _ => .finish badShape) = ln → loopNextAt root q c = ln := by
      intro x ln hx hln
      unfold loopNextAt
      rw [loopAt_iterate root h]
      dsimp only
      rw [hx]
      exact hln
    have hFinish : ∀ {x : Option Val} {code : NCode}, evalTerm (q.env ++ [c]) result = x →
        (match x with
         | some answer => Prim.success answer
         | none => badShape) = code → loopFinishAt root q c = code := by
      intro x code hx hcode
      unfold loopFinishAt
      rw [loopResultAt_iterate root h]
      dsimp only
      rw [hx]
      exact hcode
    -- a round that finishes at once, with the exit `y` and the machine already holding it
    have hdone : ∀ (y : ExitV) (ln : LoopNext Val NCode),
        runP (iterateStep (fun env' => denoteB k body env') q.env test step result c) s =
          (.inl (some y), s) →
        loopNextAt root q c = ln → enter q K i ln = fiberOf (Prim.ofExit y) K i →
        ∃ n, Reaches root n (enter q K i (loopNextAt root q c)) s
          (fiberOf (Prim.ofExit ex) K i) s' := by
      intro y ln hf hln hent
      rw [iter_run_inl j hf] at hrun
      cases hrun
      rw [hln, hent]
      exact ⟨0, Reaches.refl root _ s⟩
    cases ht : evalTerm (q.env ++ [c]) test with
    | none =>
      exact hdone badShapeExit _ (by unfold iterateStep; rw [ht]; rfl) (hNext ht rfl) rfl
    | some tv =>
      cases tv with
      | bool flag =>
        cases flag with
        | false =>
          cases hr : evalTerm (q.env ++ [c]) result with
          | none =>
            exact hdone badShapeExit (.finish badShape) (by unfold iterateStep; rw [ht, hr]; rfl)
              (by rw [hNext ht rfl, hFinish hr rfl]) rfl
          | some v =>
            exact hdone (Exit.success v) (.finish (Prim.success v))
              (by unfold iterateStep; rw [ht, hr]; rfl)
              (by rw [hNext ht rfl, hFinish hr rfl]) rfl
        | true =>
          rw [hNext ht rfl]
          -- the body's budgeted run
          rcases hb : runP (denoteB k body (q.env ++ [c])) s with ⟨rb, s₁⟩
          -- one round's run, from what the body's run gave
          have hF : ∀ (r : Option ExitV ⊕ Val),
              (match rb with
               | none => (pure (.inl none) : Effects.Program StoreSig (Option ExitV ⊕ Val))
               | some (Exit.failure cause) => pure (.inl (some (Exit.failure cause)))
               | some (Exit.success a) =>
                 match evalTerm (q.env ++ [c, a]) step with
                 | some c' => pure (.inr c')
                 | none => pure (.inl (some badShapeExit))) = pure r →
              runP (iterateStep (fun env' => denoteB k body env') q.env test step result c) s =
                (r, s₁) := by
            intro r hr
            unfold iterateStep
            rw [ht]
            dsimp only
            rw [runP_bind, hb]
            dsimp only
            cases rb with
            | none => cases hr; rfl
            | some exb =>
              cases exb with
              | failure cause => cases hr; rfl
              | success a =>
                dsimp only at hr ⊢
                cases hst : evalTerm (q.env ++ [c, a]) step with
                | none => rw [hst] at hr; cases hr; rfl
                | some c' => rw [hst] at hr; cases hr; rfl
          cases rb with
          | none =>
            rw [iter_run_inl j (hF _ rfl)] at hrun
            cases hrun
          | some exb =>
            obtain ⟨nb, hnb⟩ := hbody c s exb s₁ hb
            cases exb with
            | failure cause =>
              rw [iter_run_inl j (hF _ rfl)] at hrun
              obtain ⟨hex, hss⟩ := Prod.mk.inj hrun
              cases hex
              subst hss
              have hpass := Reaches.same s₁ (fun s₀ =>
                step_failure_pass_whileLoop root q c cause K i s₀)
              exact ⟨nb + 0, hnb.trans hpass⟩
            | success a =>
              have hstepA := Reaches.step (step_success_enter root q hq c a K i s₁)
              have hResume : ∀ {x : Option Val} {ln : LoopNext Val NCode},
                  evalTerm (q.env ++ [c, a]) step = x →
                  (match x with
                   | some next => loopNextAt root q next
                   | none => LoopNext.finish badShape) = ln → loopResumeAt root q c a = ln := by
                intro x ln hx hln
                unfold loopResumeAt
                rw [loopAt_iterate root h]
                dsimp only
                rw [hx]
                exact hln
              cases hs : evalTerm (q.env ++ [c, a]) step with
              | none =>
                rw [iter_run_inl j (hF (.inl (some badShapeExit)) (by dsimp only; rw [hs]))] at hrun
                obtain ⟨hex, hss⟩ := Prod.mk.inj hrun
                cases hex
                subst hss
                rw [hResume hs rfl] at hstepA
                exact ⟨nb + 1, hnb.trans hstepA⟩
              | some c' =>
                rw [iter_run_inr j (hF (.inr c') (by dsimp only; rw [hs]))] at hrun
                obtain ⟨n', hn'⟩ := loop_reaches k q hq h K i hbody j c' s₁ ex s' hrun
                rw [hResume hs rfl] at hstepA
                exact ⟨nb + 1 + n', (hnb.trans hstepA).trans hn'⟩
      | _ =>
        exact hdone badShapeExit _ (by unfold iterateStep; rw [ht]; rfl) (hNext ht rfl) rfl

/-! ## The agreement of the local run with the budgeted meaning -/

/-- The compile fuel a program of `Looped` needs: by depth, never by round. It is `depth` with
the loop's arm. -/
def depthB : NativeEff → Nat
  | .iterate _ _ _ _ _ body => depthB body + 1
  | .suspend b => depthB b + 1
  | .bind a b => max (depthB a) (depthB b) + 1
  | .branch _ a b => max (depthB a) (depthB b) + 1
  | .select _ _ a b => max (depthB a) (depthB b) + 1
  | .exit b => depthB b + 1
  | .catchCause b h => max (depthB b) (depthB h) + 1
  | .matchCause b v c => max (depthB b) (max (depthB v) (depthB c)) + 1
  | .onExit b f => max (depthB b) (depthB f) + 1
  | _ => 1

theorem depthB_pos (e : NativeEff) : 1 ≤ depthB e := by
  cases e <;> simp only [depthB] <;> omega

/-- On the straight fragment the two depths agree. -/
theorem depthB_straight : ∀ (e : NativeEff), Straight e = true → depthB e = depth e
  | .suspend b, h => by rw [depthB, depth, depthB_straight b (Straight.suspend h)]
  | .exit b, h => by rw [depthB, depth, depthB_straight b (Straight.exit h)]
  | .bind a b, h => by
    rw [depthB, depth, depthB_straight a (Straight.bind h).1, depthB_straight b (Straight.bind h).2]
  | .branch _ a b, h => by
    rw [depthB, depth, depthB_straight a (Straight.branch h).1,
      depthB_straight b (Straight.branch h).2]
  | .select _ _ a b, h => by
    rw [depthB, depth, depthB_straight a (Straight.select h).1,
      depthB_straight b (Straight.select h).2]
  | .catchCause a b, h => by
    rw [depthB, depth, depthB_straight a (Straight.catchCause h).1,
      depthB_straight b (Straight.catchCause h).2]
  | .onExit a b, h => by
    rw [depthB, depth, depthB_straight a (Straight.onExit h).1,
      depthB_straight b (Straight.onExit h).2]
  | .matchCause a b c, h => by
    rw [depthB, depth, depthB_straight a (Straight.matchCause h).1,
      depthB_straight b (Straight.matchCause h).2.1, depthB_straight c (Straight.matchCause h).2.2]
  | .iterate _ _ _ _ _ _, h => absurd h Bool.false_ne_true
  | .succeed _, _ | .fail _, _ | .failCause _, _ | .yieldError _, _ | .sync _, _
  | .perform _ _, _ | .gen _, _ | .uninterruptible _, _ | .interruptible _, _
  | .whileLoop _ _ _ _, _ | .yieldNow _, _ | .callback _ _, _ | .awaitFiber _ _, _
  | .withFiber _, _ | .scoped _, _ | .acquireRelease _ _, _ | .provideLayer _ _ _, _
  | .service _, _ | .provideService _ _ _, _ | .catchIf _ _ _, _ => rfl

theorem fuel_succB {e : NativeEff} {p : Point} (hd : depthB e ≤ p.fuel) :
    p.fuel = (p.fuel - 1) + 1 := by
  have := depthB_pos e
  omega

/-- A straight leaf: the straight theorem, read at the budgeted meaning. -/
theorem localRun_compileB_straight (k : Nat) (e : NativeEff) (p : Point) (K : List NCode)
    (i : Bool) (s : Stores) (ex : ExitV) (s' : Stores) (hs : Straight e = true)
    (h : Node.at_ (Node.eff root) p.path = some (Node.eff e)) (hd : depthB e ≤ p.fuel)
    (hm : meaningB k e p.env s = (some ex, s')) :
    ∃ c, Reaches root c (fiberOf (compileEff e p) K i) s (fiberOf (Prim.ofExit ex) K i) s' := by
  rw [depthB_straight e hs] at hd
  rw [meaningB_straight k e p.env s hs] at hm
  obtain ⟨hex, hss⟩ := Prod.mk.inj hm
  cases hex
  subst hss
  obtain ⟨c, _, hr⟩ := localRun_compile root e p K i s hs h hd
  exact ⟨c, hr⟩

/-- A program of the fragment whose compile is already an exit is straight: a loop compiles to
a suspension, and every composite but a folded `exit` to a frame. -/
theorem straight_of_asExit : ∀ (b : NativeEff) (q : Point) {exit : ExitV},
    Looped b = true → (compileEff b q).asExit? = some exit → Straight b = true
  | .exit b', q, exit, hl, h => by
    rcases hf : q.fuel with _ | n
    · rw [compileEff_at_zero _ hf] at h; simp [frontier, Prim.asExit?] at h
    · rw [compileEff_exit b' hf] at h
      cases hx : (compileEff b' (q.child 0)).asExit? with
      | none => rw [hx] at h; simp [Prim.asExit?] at h
      | some e' => exact straight_of_asExit b' (q.child 0) (Looped.exit hl) hx
  | .iterate c i t st r b', q, exit, _, h => by
    rcases hf : q.fuel with _ | n
    · rw [compileEff_at_zero _ hf] at h; simp [frontier, Prim.asExit?] at h
    · rw [compileEff_iterate c i t st r b' hf] at h; simp [Prim.asExit?] at h
  | .suspend b', q, exit, _, h => by
    rcases hf : q.fuel with _ | n
    · rw [compileEff_at_zero _ hf] at h; simp [frontier, Prim.asExit?] at h
    · rw [compileEff_suspend b' hf] at h; simp [Prim.asExit?] at h
  | .bind a b', q, exit, _, h => by
    rcases hf : q.fuel with _ | n
    · rw [compileEff_at_zero _ hf] at h; simp [frontier, Prim.asExit?] at h
    · rw [compileEff_bind a b' hf] at h; simp [Prim.asExit?] at h
  | .branch t a b', q, exit, _, h => by
    rcases hf : q.fuel with _ | n
    · rw [compileEff_at_zero _ hf] at h; simp [frontier, Prim.asExit?] at h
    · rw [compileEff_branch t a b' hf] at h; simp [Prim.asExit?] at h
  | .select t d a b', q, exit, _, h => by
    rcases hf : q.fuel with _ | n
    · rw [compileEff_at_zero _ hf] at h; simp [frontier, Prim.asExit?] at h
    · rw [compileEff_select t d a b' hf] at h; simp [Prim.asExit?] at h
  | .catchCause a b', q, exit, _, h => by
    rcases hf : q.fuel with _ | n
    · rw [compileEff_at_zero _ hf] at h; simp [frontier, Prim.asExit?] at h
    · rw [compileEff_catchCause a b' hf] at h; simp [Prim.asExit?] at h
  | .matchCause a b' c, q, exit, _, h => by
    rcases hf : q.fuel with _ | n
    · rw [compileEff_at_zero _ hf] at h; simp [frontier, Prim.asExit?] at h
    · rw [compileEff_matchCause a b' c hf] at h; simp [Prim.asExit?] at h
  | .onExit a b', q, exit, _, h => by
    rcases hf : q.fuel with _ | n
    · rw [compileEff_at_zero _ hf] at h; simp [frontier, Prim.asExit?] at h
    · rw [compileEff_onExit a b' hf] at h; simp [Prim.asExit?] at h
  | .succeed _, _, _, hl, _ | .fail _, _, _, hl, _ | .failCause _, _, _, hl, _
  | .yieldError _, _, _, hl, _ | .sync _, _, _, hl, _ | .perform _ _, _, _, hl, _
  | .gen _, _, _, hl, _ | .uninterruptible _, _, _, hl, _ | .interruptible _, _, _, hl, _
  | .whileLoop _ _ _ _, _, _, hl, _ | .yieldNow _, _, _, hl, _ | .callback _ _, _, _, hl, _
  | .awaitFiber _ _, _, _, hl, _ | .withFiber _, _, _, hl, _ | .scoped _, _, _, hl, _
  | .acquireRelease _ _, _, _, hl, _ | .provideLayer _ _ _, _, _, hl, _
  | .service _, _, _, hl, _ | .provideService _ _ _, _, _, hl, _
  | .catchIf _ _ _, _, _, hl, _ => hl

/-- **The local run agrees with the budgeted meaning.** A program of `Looped` compiled at an
address of the root, run by the local machine from any outer stack, reaches the fiber holding
its finished budgeted exit over the budgeted stores. No step bound: a loop's count is its
rounds. -/
theorem localRun_compileB (k : Nat) :
    ∀ (e : NativeEff) (p : Point) (K : List NCode) (i : Bool) (s : Stores) (ex : ExitV)
      (s' : Stores), Looped e = true →
      Node.at_ (Node.eff root) p.path = some (Node.eff e) → depthB e ≤ p.fuel →
      meaningB k e p.env s = (some ex, s') →
      ∃ c, Reaches root c (fiberOf (compileEff e p) K i) s (fiberOf (Prim.ofExit ex) K i) s'
  | .iterate cty init test step result body, p, K, i, s, ex, s', hl, h, hd, hm => by
    have hlb : Looped body = true := Looped.iterate hl
    have hdb : depthB body ≤ p.fuel - 1 := by rw [depthB] at hd; omega
    have hq : Node.at_ (Node.eff root) (loopPoint p).path =
        some (Node.eff (.iterate cty init test step result body)) := h
    rw [compileEff_iterate cty init test step result body (fuel_succB hd)]
    have hs := step_suspend root (EffThunk.body p) K i s
    simp only [interpAt] at hs
    rw [Effect4.Program.Sched.suspendBodyAt_iterate (q := loopPoint p) (fuel_succB hd) hq] at hs
    unfold meaningB at hm
    rw [denoteB] at hm
    cases hi : evalTerm p.env init with
    | none =>
      rw [hi] at hm
      obtain ⟨hex, hss⟩ := Prod.mk.inj hm
      cases hex
      subst hss
      rw [show evalTerm (loopPoint p).env init = none from hi] at hs
      exact ⟨1, Reaches.step hs⟩
    | some c₀ =>
      rw [hi] at hm
      rw [show evalTerm (loopPoint p).env init = some c₀ from hi] at hs
      have henter := Reaches.step (step_whileLoop_enter root (loopPoint p) rfl c₀ K i s)
      have hbody : ∀ (c : Val) (s₀ : Stores) (exb : ExitV) (s₁ : Stores),
          meaningB k body ((loopPoint p).env ++ [c]) s₀ = (some exb, s₁) →
          ∃ n, Reaches root n
            (fiberOf (resolve root ((loopPoint p).childWith 0 c))
              (Prim.whileLoop (EffName.loop (loopPoint p)) c :: K) i) s₀
            (fiberOf (Prim.ofExit exb) (Prim.whileLoop (EffName.loop (loopPoint p)) c :: K) i)
              s₁ := by
        intro c s₀ exb s₁ hmb
        have hat : Node.at_ (Node.eff root) ((loopPoint p).childWith 0 c).path =
            some (Node.eff body) := at_childWith hq 0 c
        rw [resolve_of_at hat]
        exact localRun_compileB k body ((loopPoint p).childWith 0 c) _ i s₀ exb s₁ hlb hat hdb hmb
      obtain ⟨n, hn⟩ := loop_reaches root k (loopPoint p) rfl hq K i hbody k c₀ s ex s' hm
      exact ⟨1 + 1 + n, ((Reaches.step hs).trans henter).trans hn⟩
  | .suspend b, p, K, i, s, ex, s', hl, h, hd, hm => by
    have hlb : Looped b = true := Looped.suspend hl
    have hb : Node.at_ (Node.eff root) ({ p with completed := [] }.child 0).path =
        some (Node.eff b) := at_child h 0
    have hdb : depthB b ≤ ({ p with completed := [] }.child 0).fuel := by
      show depthB b ≤ p.fuel - 1
      rw [depthB] at hd
      omega
    unfold meaningB at hm
    rw [denoteB] at hm
    have hm' : meaningB k b ({ p with completed := [] }.child 0).env s = (some ex, s') := hm
    obtain ⟨c, hr⟩ := localRun_compileB k b ({ p with completed := [] }.child 0) K i s ex s'
      hlb hb hdb hm'
    rw [compileEff_suspend b (fuel_succB hd)]
    have hs := step_suspend root (EffThunk.body p) K i s
    simp only [interpAt] at hs
    rw [suspendBodyAt_suspend (q := { p with completed := [] }) (fuel_succB hd) h,
      resolve_of_at hb] at hs
    exact ⟨1 + c, (Reaches.step hs).trans hr⟩
  | .bind a b, p, K, i, s, ex, s', hl, h, hd, hm => by
    have hlab : Looped a = true ∧ Looped b = true := Looped.bind hl
    have ha : Node.at_ (Node.eff root) (p.child 0).path = some (Node.eff a) := at_child h 0
    have hfa : depthB a ≤ (p.child 0).fuel := by
      show depthB a ≤ p.fuel - 1
      rw [depthB] at hd
      have := Nat.le_max_left (depthB a) (depthB b)
      omega
    unfold meaningB at hm
    rw [denoteB] at hm
    obtain ⟨exa, s₁, hma, hrest⟩ := runP_thenB_inv hm
    have hma' : meaningB k a (p.child 0).env s = (some exa, s₁) := hma
    obtain ⟨ca, hra⟩ := localRun_compileB k a (p.child 0)
      (Prim.onSuccess (compileEff a (p.child 0)) (EffName.cont p) :: K) i s exa s₁ hlab.1 ha hfa
      hma'
    rw [compileEff_bind a b (fuel_succB hd)]
    have hpush := Reaches.step
      (step_push_onSuccess root (compileEff a (p.child 0)) (EffName.cont p) K i s)
    cases exa with
    | success v =>
      have hb : Node.at_ (Node.eff root) ({ p with completed := [] }.childWith 1 v).path =
          some (Node.eff b) := at_childWith h 1 v
      have hfb : depthB b ≤ ({ p with completed := [] }.childWith 1 v).fuel := by
        show depthB b ≤ p.fuel - 1
        rw [depthB] at hd
        have := Nat.le_max_right (depthB a) (depthB b)
        omega
      have hmb : meaningB k b ({ p with completed := [] }.childWith 1 v).env s₁ = (some ex, s') :=
        hrest
      obtain ⟨cb, hrb⟩ := localRun_compileB k b ({ p with completed := [] }.childWith 1 v) K i
        s₁ ex s' hlab.2 hb hfb hmb
      have hpop := Reaches.step
        (step_success_onSuccess root v (compileEff a (p.child 0)) (EffName.cont p) K i s₁)
      simp only [interpAt] at hpop
      rw [contAOf_cont, resolve_of_at hb] at hpop
      exact ⟨1 + ca + 1 + cb, ((hpush.trans hra).trans hpop).trans hrb⟩
    | failure c =>
      obtain ⟨hex, hss⟩ := Prod.mk.inj hrest
      cases hex
      subst hss
      have hpass := Reaches.same s₁ (fun s₀ =>
        step_failure_pass_onSuccess root c (compileEff a (p.child 0)) (EffName.cont p) K i s₀)
      exact ⟨1 + ca + 0, (hpush.trans hra).trans hpass⟩
  | .branch t a b, p, K, i, s, ex, s', hl, h, hd, hm => by
    obtain ⟨hla, hlb⟩ := Looped.branch hl
    have ha : Node.at_ (Node.eff root) ({ p with completed := [] }.child 0).path =
        some (Node.eff a) := at_child h 0
    have hb : Node.at_ (Node.eff root) ({ p with completed := [] }.child 1).path =
        some (Node.eff b) := at_child h 1
    have hfa : depthB a ≤ ({ p with completed := [] }.child 0).fuel := by
      show depthB a ≤ p.fuel - 1
      rw [depthB] at hd
      have := Nat.le_max_left (depthB a) (depthB b)
      omega
    have hfb : depthB b ≤ ({ p with completed := [] }.child 1).fuel := by
      show depthB b ≤ p.fuel - 1
      rw [depthB] at hd
      have := Nat.le_max_right (depthB a) (depthB b)
      omega
    rw [compileEff_branch t a b (fuel_succB hd)]
    have hs := step_suspend root (EffThunk.body p) K i s
    simp only [interpAt] at hs
    unfold meaningB at hm
    rw [denoteB] at hm
    have hbadCase : (∀ flag, evalTerm p.env t ≠ some (Val.bool flag)) →
        runP (pure (some badShapeExit)) s = (some ex, s') →
        ∃ c, Reaches root c (fiberOf (Prim.suspend (EffThunk.body p)) K i) s
          (fiberOf (Prim.ofExit ex) K i) s' := by
      intro hbad hm'
      obtain ⟨hex, hss⟩ := Prod.mk.inj hm'
      cases hex
      subst hss
      rw [suspendBodyAt_branch_bad (q := { p with completed := [] }) (fuel_succB hd) h hbad] at hs
      exact ⟨1, Reaches.step hs⟩
    cases ht : evalTerm p.env t with
    | none =>
      rw [ht] at hm
      exact hbadCase (fun flag hh => by rw [ht] at hh; cases hh) hm
    | some tv =>
      rw [ht] at hm
      cases tv with
      | bool flag =>
        cases flag with
        | true =>
          have hm' : meaningB k a ({ p with completed := [] }.child 0).env s = (some ex, s') := hm
          obtain ⟨c, hr⟩ := localRun_compileB k a ({ p with completed := [] }.child 0) K i s ex s'
            hla ha hfa hm'
          rw [suspendBodyAt_branch_true (q := { p with completed := [] }) (fuel_succB hd) h ht,
            resolve_of_at ha] at hs
          exact ⟨1 + c, (Reaches.step hs).trans hr⟩
        | false =>
          have hm' : meaningB k b ({ p with completed := [] }.child 1).env s = (some ex, s') := hm
          obtain ⟨c, hr⟩ := localRun_compileB k b ({ p with completed := [] }.child 1) K i s ex s'
            hlb hb hfb hm'
          rw [suspendBodyAt_branch_false (q := { p with completed := [] }) (fuel_succB hd) h ht,
            resolve_of_at hb] at hs
          exact ⟨1 + c, (Reaches.step hs).trans hr⟩
      | _ => exact hbadCase (fun flag hh => by rw [ht] at hh; cases hh) hm
  | .select t d a b, p, K, i, s, ex, s', hl, h, hd, hm => by
    obtain ⟨hla, hlb⟩ := Looped.select hl
    have hda : depthB a ≤ p.fuel - 1 := by
      rw [depthB] at hd
      have := Nat.le_max_left (depthB a) (depthB b)
      omega
    have hdb : depthB b ≤ p.fuel - 1 := by
      rw [depthB] at hd
      have := Nat.le_max_right (depthB a) (depthB b)
      omega
    rw [compileEff_select t d a b (fuel_succB hd)]
    have hs := step_suspend root (EffThunk.body p) K i s
    simp only [interpAt] at hs
    unfold meaningB at hm
    rw [denoteB] at hm
    rcases hdec : (evalTerm p.env t).bind d.decide with _ | ⟨first, bound⟩
    · rw [hdec] at hm
      obtain ⟨hex, hss⟩ := Prod.mk.inj hm
      cases hex
      subst hss
      rw [suspendBodyAt_select_bad (q := { p with completed := [] }) (fuel_succB hd) h hdec] at hs
      exact ⟨1, Reaches.step hs⟩
    · rw [hdec] at hm
      rw [suspendBodyAt_select_of_decide (q := { p with completed := [] }) (fuel_succB hd) h
        hdec] at hs
      cases first with
      | true =>
        cases bound with
        | none =>
          have ha : Node.at_ (Node.eff root) ({ p with completed := [] }.child 0).path =
              some (Node.eff a) := at_child h 0
          have hm' : meaningB k a ({ p with completed := [] }.child 0).env s = (some ex, s') := by
            simp only [Option.toList, List.append_nil] at hm
            exact hm
          obtain ⟨c, hr⟩ := localRun_compileB k a ({ p with completed := [] }.child 0) K i s ex s'
            hla ha hda hm'
          simp only [Bool.cond_true, Point.childBind] at hs
          rw [resolve_of_at ha] at hs
          exact ⟨1 + c, (Reaches.step hs).trans hr⟩
        | some v =>
          have ha : Node.at_ (Node.eff root) ({ p with completed := [] }.childWith 0 v).path =
              some (Node.eff a) := at_childWith h 0 v
          have hm' : meaningB k a ({ p with completed := [] }.childWith 0 v).env s =
              (some ex, s') := hm
          obtain ⟨c, hr⟩ := localRun_compileB k a ({ p with completed := [] }.childWith 0 v) K i s
            ex s' hla ha hda hm'
          simp only [Bool.cond_true, Point.childBind] at hs
          rw [resolve_of_at ha] at hs
          exact ⟨1 + c, (Reaches.step hs).trans hr⟩
      | false =>
        cases bound with
        | none =>
          have hb : Node.at_ (Node.eff root) ({ p with completed := [] }.child 1).path =
              some (Node.eff b) := at_child h 1
          have hm' : meaningB k b ({ p with completed := [] }.child 1).env s = (some ex, s') := by
            simp only [Option.toList, List.append_nil] at hm
            exact hm
          obtain ⟨c, hr⟩ := localRun_compileB k b ({ p with completed := [] }.child 1) K i s ex s'
            hlb hb hdb hm'
          simp only [Bool.cond_false, Point.childBind] at hs
          rw [resolve_of_at hb] at hs
          exact ⟨1 + c, (Reaches.step hs).trans hr⟩
        | some v =>
          have hb : Node.at_ (Node.eff root) ({ p with completed := [] }.childWith 1 v).path =
              some (Node.eff b) := at_childWith h 1 v
          have hm' : meaningB k b ({ p with completed := [] }.childWith 1 v).env s =
              (some ex, s') := hm
          obtain ⟨c, hr⟩ := localRun_compileB k b ({ p with completed := [] }.childWith 1 v) K i s
            ex s' hlb hb hdb hm'
          simp only [Bool.cond_false, Point.childBind] at hs
          rw [resolve_of_at hb] at hs
          exact ⟨1 + c, (Reaches.step hs).trans hr⟩
  | .exit b, p, K, i, s, ex, s', hl, h, hd, hm => by
    have hlb := Looped.exit hl
    have hb : Node.at_ (Node.eff root) (p.child 0).path = some (Node.eff b) := at_child h 0
    have hfb : depthB b ≤ (p.child 0).fuel := by
      show depthB b ≤ p.fuel - 1
      rw [depthB] at hd
      omega
    rcases hx : (compileEff b (p.child 0)).asExit? with _ | folded
    · rw [compileEff_exit_frame b (fuel_succB hd) hx]
      unfold meaningB at hm
      rw [denoteB] at hm
      obtain ⟨exb, s₁, hmb, hrest⟩ := runP_thenB_inv hm
      obtain ⟨hex, hss⟩ := Prod.mk.inj hrest
      cases hex
      subst hss
      have hmb' : meaningB k b (p.child 0).env s = (some exb, s₁) := hmb
      obtain ⟨cb, hrb⟩ := localRun_compileB k b (p.child 0)
        (Prim.exitFrame (compileEff b (p.child 0)) :: K) i s exb s₁ hlb hb hfb hmb'
      have hpush := Reaches.step (step_push_exitFrame root (compileEff b (p.child 0)) K i s)
      have hpop := Reaches.step (step_ofExit_exitFrame root exb (compileEff b (p.child 0)) K i s₁)
      exact ⟨1 + cb + 1, (hpush.trans hrb).trans hpop⟩
    · -- the fold: the body's compile is already an exit, so the body is straight
      have hsb : Straight (.exit b) = true := straight_of_asExit b (p.child 0) hlb hx
      exact localRun_compileB_straight root k _ p K i s ex s' hsb h hd hm
  | .catchCause b hh, p, K, i, s, ex, s', hl, h, hd, hm => by
    obtain ⟨hlb, hlh⟩ := Looped.catchCause hl
    have hb : Node.at_ (Node.eff root) (p.child 0).path = some (Node.eff b) := at_child h 0
    have hfb : depthB b ≤ (p.child 0).fuel := by
      show depthB b ≤ p.fuel - 1
      rw [depthB] at hd
      have := Nat.le_max_left (depthB b) (depthB hh)
      omega
    rw [compileEff_catchCause b hh (fuel_succB hd)]
    unfold meaningB at hm
    rw [denoteB] at hm
    obtain ⟨exb, s₁, hmb, hrest⟩ := runP_thenB_inv hm
    have hmb' : meaningB k b (p.child 0).env s = (some exb, s₁) := hmb
    obtain ⟨cb, hrb⟩ := localRun_compileB k b (p.child 0)
      (Prim.onFailure (compileEff b (p.child 0)) (EffName.caught p) :: K) i s exb s₁ hlb hb hfb
      hmb'
    have hpush := Reaches.step
      (step_push_onFailure root (compileEff b (p.child 0)) (EffName.caught p) K i s)
    cases exb with
    | success v =>
      obtain ⟨hex, hss⟩ := Prod.mk.inj hrest
      cases hex
      subst hss
      have hpass := Reaches.same s₁ (fun s₀ =>
        step_success_pass_onFailure root v (compileEff b (p.child 0)) (EffName.caught p) K i s₀)
      exact ⟨1 + cb + 0, (hpush.trans hrb).trans hpass⟩
    | failure c =>
      have hh' : Node.at_ (Node.eff root)
          ({ p with completed := [] }.childWith 1 (Val.exitErr c)).path = some (Node.eff hh) :=
        at_childWith h 1 (Val.exitErr c)
      have hfh : depthB hh ≤ ({ p with completed := [] }.childWith 1 (Val.exitErr c)).fuel := by
        show depthB hh ≤ p.fuel - 1
        rw [depthB] at hd
        have := Nat.le_max_right (depthB b) (depthB hh)
        omega
      have hmh : meaningB k hh ({ p with completed := [] }.childWith 1 (Val.exitErr c)).env s₁ =
          (some ex, s') := hrest
      obtain ⟨ch, hrh⟩ := localRun_compileB k hh
        ({ p with completed := [] }.childWith 1 (Val.exitErr c)) K i s₁ ex s' hlh hh' hfh hmh
      have hpop := Reaches.step
        (step_failure_onFailure root c (compileEff b (p.child 0)) (EffName.caught p) K i s₁)
      simp only [interpAt] at hpop
      rw [contEOf_caught, resolve_of_at hh'] at hpop
      exact ⟨1 + cb + 1 + ch, ((hpush.trans hrb).trans hpop).trans hrh⟩
  | .matchCause b v c, p, K, i, s, ex, s', hl, h, hd, hm => by
    obtain ⟨hlb, hlv, hlc⟩ := Looped.matchCause hl
    have hb : Node.at_ (Node.eff root) (p.child 0).path = some (Node.eff b) := at_child h 0
    have hfb : depthB b ≤ (p.child 0).fuel := by
      show depthB b ≤ p.fuel - 1
      rw [depthB] at hd
      have := Nat.le_max_left (depthB b) (max (depthB v) (depthB c))
      omega
    rw [compileEff_matchCause b v c (fuel_succB hd)]
    unfold meaningB at hm
    rw [denoteB] at hm
    obtain ⟨exb, s₁, hmb, hrest⟩ := runP_thenB_inv hm
    have hmb' : meaningB k b (p.child 0).env s = (some exb, s₁) := hmb
    obtain ⟨cb, hrb⟩ := localRun_compileB k b (p.child 0)
      (Prim.onSuccessAndFailure (compileEff b (p.child 0)) (EffName.onValue p)
        (EffName.onCause p) :: K) i s exb s₁ hlb hb hfb hmb'
    have hpush := Reaches.step (step_push_onSuccessAndFailure root (compileEff b (p.child 0))
      (EffName.onValue p) (EffName.onCause p) K i s)
    cases exb with
    | success x =>
      have hv' : Node.at_ (Node.eff root) ({ p with completed := [] }.childWith 1 x).path =
          some (Node.eff v) := at_childWith h 1 x
      have hfv : depthB v ≤ ({ p with completed := [] }.childWith 1 x).fuel := by
        show depthB v ≤ p.fuel - 1
        rw [depthB] at hd
        have h₁ := Nat.le_max_right (depthB b) (max (depthB v) (depthB c))
        have h₂ := Nat.le_max_left (depthB v) (depthB c)
        omega
      have hmv : meaningB k v ({ p with completed := [] }.childWith 1 x).env s₁ = (some ex, s') :=
        hrest
      obtain ⟨cv, hrv⟩ := localRun_compileB k v ({ p with completed := [] }.childWith 1 x) K i s₁
        ex s' hlv hv' hfv hmv
      have hpop := Reaches.step (step_success_onSuccessAndFailure root x
        (compileEff b (p.child 0)) (EffName.onValue p) (EffName.onCause p) K i s₁)
      simp only [interpAt] at hpop
      rw [contAOf_onValue, resolve_of_at hv'] at hpop
      exact ⟨1 + cb + 1 + cv, ((hpush.trans hrb).trans hpop).trans hrv⟩
    | failure cause =>
      have hc' : Node.at_ (Node.eff root)
          ({ p with completed := [] }.childWith 2 (Val.exitErr cause)).path = some (Node.eff c) :=
        at_childWith h 2 (Val.exitErr cause)
      have hfc : depthB c ≤ ({ p with completed := [] }.childWith 2 (Val.exitErr cause)).fuel := by
        show depthB c ≤ p.fuel - 1
        rw [depthB] at hd
        have h₁ := Nat.le_max_right (depthB b) (max (depthB v) (depthB c))
        have h₂ := Nat.le_max_right (depthB v) (depthB c)
        omega
      have hmc : meaningB k c ({ p with completed := [] }.childWith 2 (Val.exitErr cause)).env s₁ =
          (some ex, s') := hrest
      obtain ⟨cc, hrc⟩ := localRun_compileB k c
        ({ p with completed := [] }.childWith 2 (Val.exitErr cause)) K i s₁ ex s' hlc hc' hfc hmc
      have hpop := Reaches.step (step_failure_onSuccessAndFailure root cause
        (compileEff b (p.child 0)) (EffName.onValue p) (EffName.onCause p) K i s₁)
      simp only [interpAt] at hpop
      rw [contEOf_onCause, resolve_of_at hc'] at hpop
      exact ⟨1 + cb + 1 + cc, ((hpush.trans hrb).trans hpop).trans hrc⟩
  | .onExit b f, p, K, i, s, ex, s', hl, h, hd, hm => by
    obtain ⟨hlb, hlf⟩ := Looped.onExit hl
    have hb : Node.at_ (Node.eff root) (p.child 0).path = some (Node.eff b) := at_child h 0
    have hfb : depthB b ≤ (p.child 0).fuel := by
      show depthB b ≤ p.fuel - 1
      rw [depthB] at hd
      have := Nat.le_max_left (depthB b) (depthB f)
      omega
    rw [compileEff_onExit b f (fuel_succB hd)]
    unfold meaningB at hm
    rw [denoteB] at hm
    obtain ⟨exb, s₁, hmb, hrest⟩ := runP_thenB_inv hm
    obtain ⟨fex, s₂, hmf, hlast⟩ := runP_thenB_inv hrest
    obtain ⟨hex, hss⟩ := Prod.mk.inj hlast
    cases hex
    subst hss
    have hmb' : meaningB k b (p.child 0).env s = (some exb, s₁) := hmb
    obtain ⟨cb, hrb⟩ := localRun_compileB k b (p.child 0)
      (Prim.onExit (compileEff b (p.child 0)) (EffName.fin p) false :: K) i s exb s₁ hlb hb hfb
      hmb'
    have hpush := Reaches.step
      (step_push_onExit root (compileEff b (p.child 0)) (EffName.fin p) false K i s)
    -- the body's exit meets the frame: the finalizer runs under the mask
    have hf' : Node.at_ (Node.eff root)
        ({ p with completed := [] }.childWith 1 (reifyExitVal exb)).path = some (Node.eff f) :=
      at_childWith h 1 (reifyExitVal exb)
    have hff : depthB f ≤ ({ p with completed := [] }.childWith 1 (reifyExitVal exb)).fuel := by
      show depthB f ≤ p.fuel - 1
      rw [depthB] at hd
      have := Nat.le_max_right (depthB b) (depthB f)
      omega
    have hmf' : meaningB k f ({ p with completed := [] }.childWith 1 (reifyExitVal exb)).env s₁ =
        (some fex, s₂) := hmf
    have hmeet := Reaches.step (step_ofExit_onExit root exb (compileEff b (p.child 0)) p K i s₁)
    rw [resolve_of_at hf'] at hmeet
    have hunmask (result : ExitV) (state : Stores) : Reaches root 0
        (fiberOf (Prim.ofExit result) (maskStack i K) false) state
        (fiberOf (Prim.ofExit result) K i) state := by
      cases i
      · exact Reaches.refl root _ state
      · exact Reaches.same state (fun s => step_ofExit_pass_setInterruptible root _ K false s)
    cases exb with
    | success value =>
      let program := compileEff f ({ p with completed := [] }.childWith 1
        (reifyExitVal (.success value)))
      let restore := EffName.restore (.success value)
      have hpush₂ := Reaches.step
        (step_push_onSuccess root program restore (maskStack i K) false s₁)
      obtain ⟨cf, hrf⟩ := localRun_compileB k f
        ({ p with completed := [] }.childWith 1 (reifyExitVal (.success value)))
        (Prim.onSuccess program restore :: maskStack i K) false s₁ fex s₂ hlf hf' hff hmf'
      cases fex with
      | success finValue =>
        have hfin := Reaches.step
          (step_success_onSuccess root finValue program restore (maskStack i K) false s₂)
        change Reaches root 1 _ s₂ (fiberOf (Prim.success value) (maskStack i K) false) s₂ at hfin
        exact ⟨1 + cb + 1 + 1 + cf + 1 + 0,
          (((((hpush.trans hrb).trans hmeet).trans hpush₂).trans hrf).trans hfin).trans
            (hunmask (.success value) s₂)⟩
      | failure finCause =>
        have hpass := Reaches.same s₂ (fun s =>
          step_failure_pass_onSuccess root finCause program restore (maskStack i K) false s)
        exact ⟨1 + cb + 1 + 1 + cf + 0 + 0,
          (((((hpush.trans hrb).trans hmeet).trans hpush₂).trans hrf).trans hpass).trans
            (hunmask (.failure finCause) s₂)⟩
    | failure cause =>
      let program := compileEff f ({ p with completed := [] }.childWith 1
        (reifyExitVal (.failure cause)))
      let restore := EffName.restore (.failure cause)
      let merge := EffName.merge (.failure cause)
      let outer := Prim.onSuccess (Prim.onFailure program merge) restore
      have hpush₂ := Reaches.step
        (step_push_onSuccess root (Prim.onFailure program merge) restore (maskStack i K) false s₁)
      have hpush₃ := Reaches.step
        (step_push_onFailure root program merge (outer :: maskStack i K) false s₁)
      obtain ⟨cf, hrf⟩ := localRun_compileB k f
        ({ p with completed := [] }.childWith 1 (reifyExitVal (.failure cause)))
        (Prim.onFailure program merge :: outer :: maskStack i K) false s₁ fex s₂ hlf hf' hff hmf'
      cases fex with
      | success finValue =>
        have hpass := Reaches.same s₂ (fun s =>
          step_success_pass_onFailure root finValue program merge (outer :: maskStack i K) false s)
        have hfin := Reaches.step (step_success_onSuccess root finValue
          (Prim.onFailure program merge) restore (maskStack i K) false s₂)
        change Reaches root 1 _ s₂ (fiberOf (Prim.failure cause) (maskStack i K) false) s₂ at hfin
        exact ⟨1 + cb + 1 + 1 + 1 + cf + 0 + 1 + 0,
          (((((((hpush.trans hrb).trans hmeet).trans hpush₂).trans hpush₃).trans hrf).trans
            hpass).trans hfin).trans (hunmask (.failure cause) s₂)⟩
      | failure finCause =>
        have hmerge := Reaches.step
          (step_failure_onFailure root finCause program merge (outer :: maskStack i K) false s₂)
        change Reaches root 1 _ s₂
          (fiberOf (Prim.failure (Cause.combine cause finCause)) (outer :: maskStack i K) false)
            s₂ at hmerge
        have hpass := Reaches.same s₂ (fun s => step_failure_pass_onSuccess root
          (Cause.combine cause finCause) (Prim.onFailure program merge) restore (maskStack i K)
          false s)
        exact ⟨1 + cb + 1 + 1 + 1 + cf + 1 + 0 + 0,
          (((((((hpush.trans hrb).trans hmeet).trans hpush₂).trans hpush₃).trans hrf).trans
            hmerge).trans hpass).trans (hunmask (.failure (Cause.combine cause finCause)) s₂)⟩
  | .succeed _, p, K, i, s, ex, s', hl, h, hd, hm | .fail _, p, K, i, s, ex, s', hl, h, hd, hm
  | .failCause _, p, K, i, s, ex, s', hl, h, hd, hm
  | .yieldError _, p, K, i, s, ex, s', hl, h, hd, hm | .sync _, p, K, i, s, ex, s', hl, h, hd, hm
  | .perform _ _, p, K, i, s, ex, s', hl, h, hd, hm | .gen _, p, K, i, s, ex, s', hl, h, hd, hm
  | .uninterruptible _, p, K, i, s, ex, s', hl, h, hd, hm
  | .interruptible _, p, K, i, s, ex, s', hl, h, hd, hm
  | .whileLoop _ _ _ _, p, K, i, s, ex, s', hl, h, hd, hm
  | .yieldNow _, p, K, i, s, ex, s', hl, h, hd, hm | .callback _ _, p, K, i, s, ex, s', hl, h, hd, hm
  | .awaitFiber _ _, p, K, i, s, ex, s', hl, h, hd, hm
  | .withFiber _, p, K, i, s, ex, s', hl, h, hd, hm | .scoped _, p, K, i, s, ex, s', hl, h, hd, hm
  | .acquireRelease _ _, p, K, i, s, ex, s', hl, h, hd, hm
  | .provideLayer _ _ _, p, K, i, s, ex, s', hl, h, hd, hm
  | .service _, p, K, i, s, ex, s', hl, h, hd, hm
  | .provideService _ _ _, p, K, i, s, ex, s', hl, h, hd, hm
  | .catchIf _ _ _, p, K, i, s, ex, s', hl, h, hd, hm =>
    localRun_compileB_straight root k _ p K i s ex s' hl h hd hm

/-- **At the root.** When the budgeted meaning of a `Looped` program finishes, the local run
from the empty stack and the empty stores finishes with that exit and those stores, at some
step count and at every larger one. -/
theorem localRun_rootB (e : NativeEff) (fuel k : Nat) (hl : Looped e = true)
    (hd : depthB e ≤ fuel) {ex : ExitV} {s' : Stores}
    (hm : meaningB k e [] Stores.empty = (some ex, s')) :
    ∃ n, ∀ m, localRun e (n + m) (fiberOf (compile e fuel) []) Stores.empty = some (ex, s') := by
  obtain ⟨c, hr⟩ :=
    localRun_compileB e k e (rootPoint fuel []) [] true Stores.empty ex s' hl rfl hd hm
  refine ⟨1 + c, fun m => ?_⟩
  have h₁ := hr 1
  have h₂ := localRun_finished (step_exit_empty e ex true s') 0
  exact localRun_mono (h₁.trans h₂) m

end Effect4.Program.Agreement
