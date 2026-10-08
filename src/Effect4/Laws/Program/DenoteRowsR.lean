import Effect4.Laws.Program.DenoteRows
import Effect4.Laws.Program.DenoteR

/-!
# Program.DenoteRowsR — the reference machine's term, erased, is the call tree (DI-69)

Slice H3 of `docs/research/2026-10-07-packet-host-meaning.md` (decisions row 310). On the
fragment `StraightRows` (which admits `catchIf`), the reference machine's term `denoteR`, with
its control nodes erased, is the call tree `denoteRows` read into the reference machine's
signature (`denoteR_straightRows`). It is a step of the proof of the goal of DI-69 on the
reference route (the packet, section 5.2).
-/

set_option autoImplicit false

/-! ## The reference's term, erased, is the tree over the stores and the rows -/

namespace Effect4.Program.Sched

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote

/-- The tree over the stores and the rows, read as a term of the reference machine: a store
operation is itself, and a host call is the external registration with its request
(`denoteForeign`, `Laws/Program/DenoteR.lean`), at the empty address that the erasure leaves
(`controlErasure`). -/
def toRef (table : RowTable) : Effects.Handler (RowsSig table) (Effects.Program RSig) where
  handle
    | .inl o => Effects.Program.vis (.inl o) Effects.Program.pure
    | .inr op =>
      Effects.Program.vis (.inr (.async (.external (.external op.1.val) op.2 []) op.2))
        Effects.Program.pure

/-- Reading as a reference term commutes with sequencing. -/
theorem toRef_bind (table : RowTable) {A B : Type} (p : Effects.Program (RowsSig table) A)
    (k : A → Effects.Program (RowsSig table) B) :
    Effects.interpret (toRef table) (p.bind k) =
      (Effects.interpret (toRef table) p).bind fun a => Effects.interpret (toRef table) (k a) :=
  Effects.interpret_bind (toRef table) p k

/-- The depth that the compile budget must cover on the wider fragment: `Agreement.depth`, with
the children of `catchIf` counted. -/
def depthRows : NativeEff → Nat
  | .suspend b => depthRows b + 1
  | .bind a b => max (depthRows a) (depthRows b) + 1
  | .select _ _ a b => max (depthRows a) (depthRows b) + 1
  | .exit b => depthRows b + 1
  | .catchCause b h => max (depthRows b) (depthRows h) + 1
  | .catchIf _ b h => max (depthRows b) (depthRows h) + 1
  | .matchCause b v c => max (depthRows b) (max (depthRows v) (depthRows c)) + 1
  | .onExit b f => max (depthRows b) (depthRows f) + 1
  | _ => 1

theorem depthRows_pos (e : NativeEff) : 1 ≤ depthRows e := by
  cases e <;> simp only [depthRows, Nat.le_add_left, Nat.le_refl]

theorem fuel_ne_zero_of_depthRows {e : NativeEff} {p : Point} (hp : depthRows e ≤ p.fuel) :
    p.fuel ≠ 0 := by
  have := depthRows_pos e
  omega

/-- A form of the fragment that `inlineYield` classifies as an immediate exit denotes to exactly
that exit. It extends `denote_of_inlineYield` by the one arm of a host call: a host call is an
immediate exit only when its request does not evaluate. A step of `denoteR_straightRows`. -/
theorem denoteRows_of_inlineYield (table : RowTable) : ∀ (b : NativeEff) (q : Point) {exit : ExitV},
    StraightRows table b = true → inlineYield b q = some exit →
    denoteRows table b q.env = Effects.Program.pure exit
  | .succeed t, q, exit, _, h => by
    simp only [inlineYield] at h
    split at h
    · cases h
    · simp only [Option.some.injEq] at h
      subst h
      rfl
  | .fail t, q, exit, _, h => by
    simp only [inlineYield] at h
    split at h
    · cases h
    · simp only [Option.some.injEq] at h
      subst h
      rfl
  | .failCause c, q, exit, _, h => by
    simp only [inlineYield] at h
    split at h
    · cases h
    · simp only [Option.some.injEq] at h
      subst h
      rfl
  | .perform op r, q, exit, hs, h => by
    cases op with
    | external i =>
      simp only [inlineYield, inlineAsyncYield] at h
      split at h
      · cases h
      · rcases hx : evalTerm q.env r with _ | x
        · simp only [hx, Option.some.injEq] at h
          subst h
          simp only [denoteRows, hx]
          rfl
        · simp only [hx, reduceCtorEq] at h
    | _ =>
      have hk := StraightRows.perform_sync hs (fun i hc => by cases hc)
      rw [inlineYield_perform_sync _ r q hk] at h
      rw [denoteRows_perform_sync table _ r q.env hk]
      split at h
      · cases h
      · rcases hx : (evalTerm q.env r).bind (NativeOp.syncOpOf _ q.env) with _ | o
        · simp only [hx, Option.some.injEq] at h
          subst h
          rfl
        · simp only [hx, reduceCtorEq] at h
  | .exit b, q, exit, hs, h => by
    simp only [inlineYield] at h
    split at h
    · cases h
    · rcases hy : inlineYield b (q.child 0) with _ | inner
      · simp only [hy, Option.map_none, reduceCtorEq] at h
      · simp only [hy, Option.map, Option.some.injEq] at h
        subst h
        have hd : denoteRows table b q.env = Effects.Program.pure inner :=
          denoteRows_of_inlineYield table b (q.child 0) hs hy
        rw [denoteRows, hd]
        rfl
  | .sync _, q, exit, _, h | .suspend _, q, exit, _, h | .bind _ _, q, exit, _, h
  | .select _ _ _ _, q, exit, _, h | .catchCause _ _, q, exit, _, h
  | .catchIf _ _ _, q, exit, _, h
  | .matchCause _ _ _, q, exit, _, h | .onExit _ _, q, exit, _, h => by
    simp only [inlineYield] at h
    split at h <;> cases h
  | .gen _, _, _, hs, _ | .uninterruptible _, _, _, hs, _ | .interruptible _, _, _, hs, _
  | .iterate _ _ _ _ _ _, _, _, hs, _ | .yieldNow _, _, _, hs, _
  | .awaitFiber _ _, _, _, hs, _ | .withFiber _, _, _, hs, _ | .«scoped» _, _, _, hs, _
  | .acquireRelease _ _, _, _, hs, _
  | .provideLayer _ _ _, _, _, hs, _ | .service _, _, _, hs, _
  | .provideService _ _ _, _, _, hs, _
  | .restore _ _, _, _, hs, _ => by
    simp only [StraightRows, Bool.false_eq_true] at hs

/-- **The reference's term of a program of the fragment, with its control markers erased, is
the program's tree over the stores and the rows**, when the compile budget covers its depth.
It extends `denoteR_straight` by the one arm of a host call. -/
theorem denoteR_straightRows (root : NativeEff) (table : RowTable) :
    ∀ (e : NativeEff) (p : Point),
    StraightRows table e = true → depthRows e ≤ p.fuel →
    eraseControl (denoteR root e p) = Effects.interpret (toRef table) (denoteRows table e p.env)
  | .succeed t, p, _, hp => by
    cases hf : p.fuel with
    | zero => exact (fuel_ne_zero_of_depthRows hp hf).elim
    | succ f => simp only [denoteR, hf, denoteRWith, denoteEffBody]; rw [denoteRows]; rfl
  | .fail t, p, _, hp => by
    cases hf : p.fuel with
    | zero => exact (fuel_ne_zero_of_depthRows hp hf).elim
    | succ f => simp only [denoteR, hf, denoteRWith, denoteEffBody]; rw [denoteRows]; rfl
  | .failCause t, p, _, hp => by
    cases hf : p.fuel with
    | zero => exact (fuel_ne_zero_of_depthRows hp hf).elim
    | succ f => simp only [denoteR, hf, denoteRWith, denoteEffBody]; rw [denoteRows]; rfl
  | .sync t, p, _, hp => by
    cases hf : p.fuel with
    | zero => exact (fuel_ne_zero_of_depthRows hp hf).elim
    | succ f => simp only [denoteR, hf, denoteRWith, denoteEffBody]; rw [denoteRows]; rfl
  | .suspend b, p, hs, hp => by
    cases hf : p.fuel with
    | zero => exact (fuel_ne_zero_of_depthRows hp hf).elim
    | succ f =>
      have ih := denoteR_straightRows root table b
        ({ p with fuel := f + 1, completed := [] }.child 0) hs
        (by simp only [depthRows] at hp; simp only [Point.child]; omega)
      simp only [denoteR, Point.child_fuel, Nat.add_sub_cancel] at ih
      simp only [denoteR, hf, denoteRWith, denoteEffBody]
      rw [eraseControl_suspendR, eraseControl_constructR, denoteRows]
      exact ih
  | .perform op request, p, hs, hp => by
    cases hf : p.fuel with
    | zero => exact (fuel_ne_zero_of_depthRows hp hf).elim
    | succ f =>
      have hpos : p.fuel ≠ 0 := by rw [hf]; exact Nat.succ_ne_zero f
      cases op with
      | external i =>
        have hi : i < table.length := lt_of_dataRow hs
        rw [denoteR_perform root (.external i) request hpos]
        simp only [denoteAsyncRoute, denoteForeign, denoteRows, hi, dite_true]
        cases evalTerm p.env request <;> rfl
      | _ =>
        have hk := StraightRows.perform_sync hs (fun i hc => by cases hc)
        rw [denoteR_perform_sync root _ request hpos hk, denoteRows_perform_sync table _ request p.env hk]
        cases (evalTerm p.env request).bind (NativeOp.syncOpOf _ p.env) <;> rfl
  | .bind a b, p, hs, hp => by
    have hpos : p.fuel ≠ 0 := by have := depthRows_pos (.bind a b); omega
    have hab : StraightRows table a = true ∧ StraightRows table b = true := by
      simpa only [StraightRows, Bool.and_eq_true] using hs
    have ha := denoteR_straightRows root table a (p.child 0) hab.1
      (by simp only [depthRows] at hp; simp only [Point.child]; omega)
    rw [denoteR_bind root a b p hpos, eraseControl_bind, eraseControl_guardR,
      ha, denoteRows, toRef_bind]
    congr 1
    funext ex
    cases ex with
    | failure c => rfl
    | success v =>
      exact denoteR_straightRows root table b ({ p with completed := [] }.childWith 1 v) hab.2
        (by simp only [depthRows] at hp; simp only [Point.childWith]; omega)
  | .select s d a0 a1, p, hs, hp => by
    have hpos : p.fuel ≠ 0 := by have := depthRows_pos (.select s d a0 a1); omega
    have hab : StraightRows table a0 = true ∧ StraightRows table a1 = true := by
      simpa only [StraightRows, Bool.and_eq_true] using hs
    rw [denoteR_select root s d a0 a1 p hpos, eraseControl_suspendR, eraseControl_constructR,
      denoteRows]
    rcases hd : (evalTerm p.env s).bind d.decide with _ | ⟨first, bound⟩
    · rfl
    · cases first with
      | true =>
        cases bound with
        | none =>
          simp only [Point.childBind, Option.toList, List.append_nil]
          exact denoteR_straightRows root table a0 ({ p with completed := [] }.child 0) hab.1
            (by simp only [depthRows] at hp; simp only [Point.child]; omega)
        | some v =>
          simp only [Point.childBind, Option.toList]
          exact denoteR_straightRows root table a0 ({ p with completed := [] }.childWith 0 v) hab.1
            (by simp only [depthRows] at hp; simp only [Point.childWith]; omega)
      | false =>
        cases bound with
        | none =>
          simp only [Point.childBind, Option.toList, List.append_nil]
          exact denoteR_straightRows root table a1 ({ p with completed := [] }.child 1) hab.2
            (by simp only [depthRows] at hp; simp only [Point.child]; omega)
        | some v =>
          simp only [Point.childBind, Option.toList]
          exact denoteR_straightRows root table a1 ({ p with completed := [] }.childWith 1 v) hab.2
            (by simp only [depthRows] at hp; simp only [Point.childWith]; omega)
  | .gen _, _, hs, _ | .uninterruptible _, _, hs, _ | .interruptible _, _, hs, _
  | .iterate _ _ _ _ _ _, _, hs, _ | .yieldNow _, _, hs, _
  | .awaitFiber _ _, _, hs, _ | .withFiber _, _, hs, _ | .«scoped» _, _, hs, _
  | .acquireRelease _ _, _, hs, _
  | .provideLayer _ _ _, _, hs, _ | .service _, _, hs, _
  | .provideService _ _ _, _, hs, _
  | .restore _ _, _, hs, _ => by
    simp only [StraightRows, Bool.false_eq_true] at hs
  | .exit b, p, hs, hp => by
    have hpos : p.fuel ≠ 0 := by have := depthRows_pos (.exit b); omega
    have hb := denoteR_straightRows root table b (p.child 0) hs
      (by simp only [depthRows] at hp; simp only [Point.child]; omega)
    rw [denoteR_exit root b p hpos]
    cases hy : inlineYield b (p.child 0) with
    | none =>
      dsimp only
      rw [eraseControl_bind, eraseControl_guardR, hb, denoteRows, toRef_bind]
      rfl
    | some ex =>
      dsimp only
      have hd : denoteRows table b p.env = Effects.Program.pure ex :=
        denoteRows_of_inlineYield table b (p.child 0) hs hy
      rw [eraseControl_pure, denoteRows, hd]
      rfl
  | .catchCause b h, p, hs, hp => by
    cases hf : p.fuel with
    | zero => exact (fuel_ne_zero_of_depthRows hp hf).elim
    | succ f =>
      have hbh : StraightRows table b = true ∧ StraightRows table h = true := by
        simpa only [StraightRows, Bool.and_eq_true] using hs
      have hb := denoteR_straightRows root table b (p.child 0) hbh.1
        (by simp only [depthRows] at hp; simp only [Point.child]; omega)
      simp only [denoteR, Point.child_fuel, hf, Nat.add_sub_cancel] at hb
      simp only [denoteR, hf, denoteRWith, denoteEffBody]
      rw [eraseControl_bind, eraseControl_guardR, hb, denoteRows, toRef_bind]
      congr 1
      funext ex
      cases ex with
      | success v => rfl
      | failure c =>
        have ih := denoteR_straightRows root table h
          ({ p with fuel := f + 1, completed := [] }.childWith 1 (.exitErr c)) hbh.2
          (by simp only [depthRows] at hp; simp only [Point.childWith]; omega)
        simp only [denoteR, Point.childWith_fuel, Nat.add_sub_cancel] at ih
        exact ih
  | .catchIf test b h, p, hs, hp => by
    cases hf : p.fuel with
    | zero => exact (fuel_ne_zero_of_depthRows hp hf).elim
    | succ f =>
      have hbh : StraightRows table b = true ∧ StraightRows table h = true := by
        simpa only [StraightRows, Bool.and_eq_true] using hs
      have hb := denoteR_straightRows root table b (p.child 0) hbh.1
        (by simp only [depthRows] at hp; simp only [Point.child]; omega)
      simp only [denoteR, Point.child_fuel, hf, Nat.add_sub_cancel] at hb
      simp only [denoteR, hf, denoteRWith, denoteEffBody]
      rw [eraseControl_bind, eraseControl_guardR, hb, denoteRows, toRef_bind]
      congr 1
      funext ex
      cases ex with
      | success v => rfl
      | failure cause =>
        dsimp only
        rw [eraseControl_constructR]
        cases hc : caughtErrorValue? p.env test cause with
        | none => rfl
        | some value =>
          have ih := denoteR_straightRows root table h
            ({ p with fuel := f + 1, completed := [] }.childWith 1 value) hbh.2
            (by simp only [depthRows] at hp; simp only [Point.childWith]; omega)
          simp only [denoteR, Point.childWith_fuel, Nat.add_sub_cancel] at ih
          exact ih
  | .matchCause b v c, p, hs, hp => by
    cases hf : p.fuel with
    | zero => exact (fuel_ne_zero_of_depthRows hp hf).elim
    | succ f =>
      have hparts : StraightRows table b = true ∧ StraightRows table v = true ∧
          StraightRows table c = true := by
        simpa only [StraightRows, Bool.and_eq_true, and_assoc] using hs
      have hb := denoteR_straightRows root table b (p.child 0) hparts.1
        (by simp only [depthRows] at hp; simp only [Point.child]; omega)
      simp only [denoteR, Point.child_fuel, hf, Nat.add_sub_cancel] at hb
      simp only [denoteR, hf, denoteRWith, denoteEffBody]
      rw [eraseControl_bind, eraseControl_guardR, hb, denoteRows, toRef_bind]
      congr 1
      funext ex
      cases ex with
      | success value =>
        have ih := denoteR_straightRows root table v
          ({ p with fuel := f + 1, completed := [] }.childWith 1 value) hparts.2.1
          (by simp only [depthRows] at hp; simp only [Point.childWith]; omega)
        simp only [denoteR, Point.childWith_fuel, Nat.add_sub_cancel] at ih
        exact ih
      | failure cause =>
        have ih := denoteR_straightRows root table c
          ({ p with fuel := f + 1, completed := [] }.childWith 2 (.exitErr cause)) hparts.2.2
          (by simp only [depthRows] at hp; simp only [Point.childWith]; omega)
        simp only [denoteR, Point.childWith_fuel, Nat.add_sub_cancel] at ih
        exact ih
  | .onExit b fin, p, hs, hp => by
    cases hf : p.fuel with
    | zero => exact (fuel_ne_zero_of_depthRows hp hf).elim
    | succ f =>
      have hparts : StraightRows table b = true ∧ StraightRows table fin = true := by
        simpa only [StraightRows, Bool.and_eq_true] using hs
      have hb := denoteR_straightRows root table b (p.child 0) hparts.1
        (by simp only [depthRows] at hp; simp only [Point.child]; omega)
      simp only [denoteR, Point.child_fuel, hf, Nat.add_sub_cancel] at hb
      simp only [denoteR, hf, denoteRWith, denoteEffBody]
      rw [eraseControl_onExitR, hb, denoteRows, toRef_bind]
      congr 1
      funext ex
      have hfin := denoteR_straightRows root table fin
        ({ p with completed := [] }.childWith 1 (reifyExitVal ex)) hparts.2
        (by simp only [depthRows] at hp; simp only [Point.childWith]; omega)
      simp only [denoteR, Point.childWith_fuel, hf, Nat.add_sub_cancel] at hfin
      rw [eraseControl_constructR, hfin, toRef_bind]
      rfl

end Effect4.Program.Sched
