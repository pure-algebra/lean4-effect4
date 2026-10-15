import Effect4.Laws.Program.DenoteCtl

/-!
# Probe: M1's missing link, the control algebra commutes with the left injection

Concept: initial-algebras-folds (two folds agree when their algebras do), serving the claim that
the block meaning is the one meaning (decisions row 389 (1)). Question: the overwatch's §5.1 route
(`docs/research/2026-10-14-meanings/overwatch.md`). The four store meanings (`denote`, `denoteB`,
`denoteWith`, `denoteBWith`, over `StoreSig`) reach a row meaning (over `RowsSig = StoreSig ⊕
RowSig`) only through `Effects.Program.inl`. Consumer: the M1 connectors from each store meaning
to `denoteRows` and `denoteRowsB`, then to `denoteBlockB`.

Reach. Every signature pair, every control parameter whose leaf, `catchIf` policy, budget,
wrong-shape exit and loop step commute with the injection, every program and environment.

Does not establish. The congruence on `Straight` programs between the injected store leaf and the
row leaf (the overwatch's second link), the caller moves, or the deletion of `DenoteCtl.lean`.
-/

set_option autoImplicit false

namespace Effect4.Program.Denote.RemainingWork

open Effect4 Effect4.Machine Effect4.Program

variable {S T : Effects.Signature.{0, 0}}

/-- The injection commutes with `>>=`, the form the meanings write their sequences in. -/
theorem inl_bindOp {A B : Type} (p : Effects.Program S A) (k : A → Effects.Program S B) :
    Effects.Program.inl (T := T) (p >>= k) =
      Effects.Program.inl (T := T) p >>= fun a => Effects.Program.inl (T := T) (k a) :=
  Effects.Program.inl_bind p k

/-- The injection commutes with `<$>`. -/
theorem inl_map {A B : Type} (f : A → B) (p : Effects.Program S A) :
    Effects.Program.inl (T := T) (f <$> p) = f <$> Effects.Program.inl (T := T) p :=
  Effects.Program.inl_bind p (fun a => Effects.Program.pure (f a))

/-- The injection commutes with budgeted iteration. -/
theorem iter_inl {X Y : Type} (f : X → Effects.Program S (Y ⊕ X)) :
    ∀ (k : Nat) (x : X), Effects.Program.inl (T := T) (iter f k x) =
      iter (fun x => Effects.Program.inl (T := T) (f x)) k x
  | 0, _ => rfl
  | k + 1, x => by
    rw [iter_succ, iter_succ, inl_bindOp]
    congr 1
    funext r
    cases r with
    | inl y => rfl
    | inr next => exact iter_inl f k next

/-- The injection commutes with sequencing at a budget. -/
theorem inl_thenOpt (p : Effects.Program S (Option ExitV))
    (rest : ExitV → Effects.Program S (Option ExitV)) :
    Effects.Program.inl (T := T) (thenOpt p rest) =
      thenOpt (Effects.Program.inl (T := T) p) (fun ex => Effects.Program.inl (T := T) (rest ex)) := by
  unfold thenOpt
  rw [inl_bindOp]
  congr 1
  funext o
  cases o with
  | none => rfl
  | some ex => rfl

/-- **A control parameter carried along the left injection.** -/
structure CtlInl (c : Ctl S) (c' : Ctl (Effects.Signature.sum S T)) : Prop where
  leaf : ∀ e env, Effects.Program.inl (T := T) (c.leaf e env) = c'.leaf e env
  reads : c.readsCatchIf = c'.readsCatchIf
  budget : c.budget = c'.budget
  bad : c.bad = c'.bad
  step : ∀ (body : List Val → Effects.Program S (Option ExitV)) env test next result v,
    Effects.Program.inl (T := T) (c.step body env test next result v) =
      c'.step (fun env => Effects.Program.inl (T := T) (body env)) env test next result v

/-- **The control algebra commutes with the left injection** (the overwatch's `denoteCtl_inl`).
One structural recursion, case for case `denoteCtl`'s. -/
theorem denoteCtl_inl (c : Ctl S) (c' : Ctl (Effects.Signature.sum S T)) (hc : CtlInl c c') :
    ∀ (e : NativeEff) (env : List Val),
      Effects.Program.inl (T := T) (denoteCtl c e env) = denoteCtl c' e env
  | .iterate ty initial test next result body, env => by
    rw [denoteCtl, denoteCtl, ← hc.budget, ← hc.bad]
    cases c.budget with
    | some k =>
      cases evalTerm env initial with
      | some c₀ =>
        dsimp only
        rw [inl_map, iter_inl]
        congr 2
        funext x
        rw [hc.step]
        congr 1
        funext env'
        exact denoteCtl_inl c c' hc body env'
      | none => rfl
    | none => exact hc.leaf _ _
  | .suspend b, env => by
    rw [denoteCtl, denoteCtl]
    exact denoteCtl_inl c c' hc b env
  | .bind a b, env => by
    rw [denoteCtl, denoteCtl, inl_thenOpt, denoteCtl_inl c c' hc a env]
    congr 1
    funext ex
    cases ex with
    | success v => exact denoteCtl_inl c c' hc b _
    | failure cause => rfl
  | .select t d a b, env => by
    rw [denoteCtl, denoteCtl, ← hc.bad]
    rcases (evalTerm env t).bind d.decide with _ | ⟨first, bound⟩
    · rfl
    · cases first with
      | true => exact denoteCtl_inl c c' hc a _
      | false => exact denoteCtl_inl c c' hc b _
  | .exit b, env => by
    rw [denoteCtl, denoteCtl, inl_thenOpt, denoteCtl_inl c c' hc b env]
    rfl
  | .catchCause b h, env => by
    rw [denoteCtl, denoteCtl, inl_thenOpt, denoteCtl_inl c c' hc b env]
    congr 1
    funext ex
    cases ex with
    | success v => rfl
    | failure cause => exact denoteCtl_inl c c' hc h _
  | .catchIf test b h, env => by
    rw [denoteCtl, denoteCtl, ← hc.reads]
    cases c.readsCatchIf with
    | true =>
      rw [if_pos rfl, if_pos rfl, inl_thenOpt, denoteCtl_inl c c' hc b env]
      congr 1
      funext ex
      cases ex with
      | success v => rfl
      | failure cause =>
        dsimp only
        cases caughtErrorValue? env test cause with
        | some value => exact denoteCtl_inl c c' hc h _
        | none => rfl
    | false => exact hc.leaf _ _
  | .matchCause b v cv, env => by
    rw [denoteCtl, denoteCtl, inl_thenOpt, denoteCtl_inl c c' hc b env]
    congr 1
    funext ex
    cases ex with
    | success x => exact denoteCtl_inl c c' hc v _
    | failure cause => exact denoteCtl_inl c c' hc cv _
  | .onExit b f, env => by
    rw [denoteCtl, denoteCtl, inl_thenOpt, denoteCtl_inl c c' hc b env]
    congr 1
    funext ex
    rw [inl_thenOpt, denoteCtl_inl c c' hc f _]
    rfl
  | .succeed _, _ | .fail _, _ | .failCause _, _ | .sync _, _ | .perform _ _, _ | .gen _, _
  | .uninterruptible _, _ | .interruptible _, _ | .yieldNow _, _ | .awaitFiber _ _, _
  | .withFiber _, _ | .scoped _, _ | .acquireRelease _ _, _ | .provideLayer _ _ _, _
  | .service _, _ | .provideService _ _ _, _
  | .restore _ _, _ | .defs _ _ _ _, _ | .invoke _ _ _, _ | .provideContext _ _, _ => hc.leaf _ _

end Effect4.Program.Denote.RemainingWork

namespace Effect4.Program.Denote.RemainingWork

open Effect4 Effect4.Machine Effect4.Program

/-- The loop round commutes with the left injection: `iterateStep` is `loopStep` at the stores,
and the injected round is `loopStep` at the sum. -/
theorem iterateStep_inl {T : Effects.Signature.{0, 0}}
    (body : List Val → Effects.Program StoreSig (Option ExitV)) (env : List Val)
    (test next result : Term) (v : Val) :
    Effects.Program.inl (T := T) (iterateStep body env test next result v) =
      loopStep (fun env => Effects.Program.inl (T := T) (body env)) env test next result v := by
  unfold iterateStep loopStep
  cases evalTerm (env ++ [v]) test with
  | none => rfl
  | some answer =>
    cases answer with
    | bool flag =>
      cases flag with
      | true =>
        dsimp only
        rw [inl_bindOp]
        congr 1
        funext o
        rcases o with _ | ⟨a | cause⟩
        · rfl
        · dsimp only
          cases evalTerm (env ++ [v, a]) next with
          | none => rfl
          | some c' => rfl
        · rfl
      | false => rfl
    | _ => rfl

/-- The stores' budgeted parameters, carried to a sum signature: the injected straight leaf and
the generic loop round. -/
def storeCtlInl (T : Effects.Signature.{0, 0}) (k : Nat) : Ctl (Effects.Signature.sum StoreSig T) :=
  { leaf := fun e env => Effects.Program.inl (T := T) (leafB e env), readsCatchIf := false,
    budget := some k, step := loopStep }

/-- The stores' budgeted parameters commute with the injection. -/
theorem storeCtl_inl (T : Effects.Signature.{0, 0}) (k : Nat) : CtlInl (T := T) (storeCtl k) (storeCtlInl T k) where
  leaf _ _ := rfl
  reads := rfl
  budget := rfl
  bad := rfl
  step body env test next result v := iterateStep_inl body env test next result v

/-- **The stores' budgeted meaning, injected, is the control algebra at the injected leaf**: the
first M1 link, from `denoteB` to the row signature, for every program and environment. -/
theorem denoteB_inl (T : Effects.Signature.{0, 0}) (k : Nat) (e : NativeEff) (env : List Val) :
    Effects.Program.inl (T := T) (denoteB k e env) = denoteCtl (storeCtlInl T k) e env := by
  rw [denoteB_eq_ctl]
  exact denoteCtl_inl (storeCtl k) (storeCtlInl T k) (storeCtl_inl T k) e env

end Effect4.Program.Denote.RemainingWork
