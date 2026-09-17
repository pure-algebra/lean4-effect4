import Effect4.Laws.Program.Intro.Equations

/-!
# Intro.Identity: `prepareR` is the identity on a denotation

The term's construction heads never sit at the head of a denotation, so resolving a
completed-exit view leaves `denoteR` unchanged (`prepareR_denoteR`).
-/

set_option autoImplicit false

namespace Effect4.Program.Sched

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote Effect4.Program.Agreement

/-! ## `prepareR` is the identity on a denotation -/

/-- Preparing completed exits leaves an asynchronous registration's denotation unchanged. -/
theorem prepareR_denoteAsyncRoute (op : NativeOp) (r : Term) (p : Point)
    (completed : List (FiberId × ExitV)) :
    prepareR completed (denoteAsyncRoute op r p) = denoteAsyncRoute op r p := by
  unfold denoteAsyncRoute
  cases op with
  | external i => exact prepareR_denoteForeign (.external i) r p completed
  | sleep => exact prepareR_denoteSleep r p completed
  | deferredAwait => exact prepareR_denoteAsync r p completed
  | scopeMake strategy => cases strategy <;> rfl
  | _ => rfl

theorem prepareR_denoteR (root : NativeEff) (e : NativeEff) (p : Point)
    (completed : List (FiberId × ExitV)) :
    prepareR completed (denoteR root e p) = denoteR root e p := by
    cases hf : p.fuel with
    | zero => rw [denoteR_zero root e p hf]; rfl
    | succ k =>
      have hpos : p.fuel ≠ 0 := by rw [hf]; exact Nat.succ_ne_zero k
      cases e with
      | succeed t => rw [denoteR_succeed root t hpos]; rfl
      | fail t => rw [denoteR_fail root t hpos]; rfl
      | failCause c => rw [denoteR_failCause root c hpos]; rfl
      | sync t => rw [denoteR_sync root t hpos]; rfl
      | suspend b => rw [denoteR_suspend root b p hpos]; rfl
      | perform op r =>
        by_cases hk : (NativeOp.row op).kind = .sync
        · rw [denoteR_perform_sync root op r hpos hk]
          cases (evalTerm p.env r).bind (NativeOp.syncOpOf op) <;> rfl
        · rw [denoteR_perform_nonsync root op r hpos hk]
          exact prepareR_denoteAsyncRoute op r p completed
      | bind a b =>
        rw [denoteR_bind root a b p hpos, prepareR_guardR_bind,
          prepareR_denoteR root a (p.child 0) completed]
      | gen ss => rw [denoteR_gen root ss p hpos]; rfl
      | catchCause b hd =>
        rw [denoteR_catchCause root b hd hpos, prepareR_guardR_bind,
          prepareR_denoteR root b (p.child 0) completed]
      | catchIf test b hd =>
        rw [denoteR_catchIf root test b hd hpos, prepareR_guardR_bind,
          prepareR_denoteR root b (p.child 0) completed]
      | matchCause b v c =>
        rw [denoteR_matchCause root b v c hpos, prepareR_guardR_bind,
          prepareR_denoteR root b (p.child 0) completed]
      | onExit b f =>
        rw [denoteR_onExit root b f hpos]
        unfold onExitR
        rw [prepareR_guardR_bind, prepareR_denoteR root b (p.child 0) completed]
      | exit b =>
        rw [denoteR_exit root b p hpos]
        cases inlineYield b (p.child 0) with
        | some ex => rfl
        | none =>
          show prepareR completed ((guardR .all (denoteR root b (p.child 0))).bind _) = _
          rw [prepareR_guardR_bind, prepareR_denoteR root b (p.child 0) completed]
      | uninterruptible b =>
        rw [denoteR_uninterruptible root b hpos]; exact prepareR_denoteAction root p completed
      | interruptible b =>
        rw [denoteR_interruptible root b hpos]; exact prepareR_denoteAction root p completed
      | select s d a0 a1 => rw [denoteR_select root s d a0 a1 p hpos]; rfl
      | whileLoop i t s b => rw [denoteR_whileLoop root i t s b p hpos]; rfl
      | iterate c i t s r b => rw [denoteR_iterate root c i t s r b p hpos]; rfl
      | yieldNow priority => rw [denoteR_yieldNow root priority hpos]; rfl
      | callback op r =>
        rw [denoteR_callback root op r hpos]
        cases op with
        | external i => exact prepareR_denoteForeign (.external i) r p completed
        | sleep => exact prepareR_denoteSleep r p completed
        | deferredAwait => exact prepareR_denoteAsync r p completed
        | scopeMake strategy => cases strategy <;> rfl
        | _ => rfl
      | awaitFiber t mode =>
        rw [denoteR_awaitFiber root t mode hpos]
        cases evalTerm p.env t with
        | none => rfl
        | some v =>
          -- the value is a fiber handle or it is not; both sides match on that
          cases hfib : Val.fiber? v with
          | some id =>
            obtain ⟨id⟩ := id
            have hv := Val.fiber?_exact hfib
            subst hv
            simp only
            cases p.awaitExit ⟨id⟩ mode with
            | some ex => rfl
            | none => cases mode <;> rfl
          | none =>
            -- one `split` settles both sides: they match on the same discriminant
            have hb : ∀ id, v ≠ Val.fiber ⟨id⟩ := fun id => Val.fiber?_none hfib ⟨id⟩
            split
            · next id heq => exact absurd (Option.some.inj heq) (hb id)
            · rfl
      | withFiber a =>
        rw [denoteR_withFiber root a p hpos]; exact prepareR_denoteAction root p completed
      | «scoped» b => rw [denoteR_scoped root b hpos]; rfl
      | acquireRelease a r => rw [denoteR_acquireRelease root a r hpos, prepareR_guardR_bind]; rfl
      | provideLayer l i b => rw [denoteR_provideLayer root l i b hpos]; rfl
      | service key => rw [denoteR_service root key hpos, prepareR_guardR_bind]; rfl
      | provideService key value b =>
        rw [denoteR_provideService root key value b hpos]
        cases evalTerm p.env value with
        | some v => unfold updateContextR; rw [prepareR_guardR_bind]; rfl
        | none => rfl
termination_by structural e

end Effect4.Program.Sched
