import Effect4.Laws.Program.Intro.Layer

/-!
# Intro.Elementary: the async dispatcher and the pure and elementary family

`asyncRoute_means` (DI-61) and the introductions of `succeed`, `fail`, `failCause`,
`sync` and `perform`.
-/

set_option autoImplicit false

namespace Effect4.Program.Sched

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote Effect4.Program.Agreement

theorem asyncRoute_means (root : NativeEff) (op : NativeOp) (r : Term) (p : Point) :
    CodeMeans root (asyncRoute op r p) (denoteAsyncRoute op r p) := by
  unfold asyncRoute denoteAsyncRoute
  cases op with
  | external i =>
    simp only [denoteForeign]
    cases evalTerm p.env r with
    | none => exact codeMeans_badShape root
    | some v => exact CodeMeans.asyncForeign (.external i) v _ delivers_pure
  | sleep =>
    unfold denoteSleep
    cases (evalTerm p.env r).bind NativeOp.sleepMillisOf with
    | none => exact codeMeans_badShape root
    | some n =>
      cases n with
      | zero => exact CodeMeans.yieldNow 0 _ delivers_seqR_pure
      | succ n => exact CodeMeans.asyncSleep (ClockMillis.ofNat (n + 1)) (Val.nat (n + 1)) _ delivers_pure
  | deferredAwait =>
    unfold denoteAsync
    cases evalTerm p.env r with
    | none => exact codeMeans_badShape root
    | some v =>
      dsimp only [Option.bind]
      cases NativeOp.awaitCellOf v with
      | some cell => exact CodeMeans.asyncAwait cell v _ delivers_pure
      | none => exact codeMeans_badShape root
  | scopeMake strategy => cases strategy <;> exact codeMeans_badShape root
  | _ => exact codeMeans_badShape root

/-! ### Constructor families for source introduction -/

/-! #### 1. Pure & Elementary family -/

theorem intro_succeed (root : NativeEff) (t : Term) (p : Point) (k : Nat)
    (hf : p.fuel = k + 1) (hpos : p.fuel ≠ 0) :
    CodeMeans root (compileEff (.succeed t) p) (denoteR root (.succeed t) p) := by
  rw [compileEff_succeed t hf, denoteR_succeed root t hpos]
  cases evalTerm p.env t with
  | some v => exact CodeMeans.success v
  | none => exact codeMeans_badShape root

theorem intro_fail (root : NativeEff) (t : Term) (p : Point) (k : Nat)
    (hf : p.fuel = k + 1) (hpos : p.fuel ≠ 0) :
    CodeMeans root (compileEff (.fail t) p) (denoteR root (.fail t) p) := by
  rw [compileEff_fail t hf, denoteR_fail root t hpos]
  cases evalTerm p.env t with
  | some v => exact CodeMeans.failure _
  | none => exact codeMeans_badShape root

theorem intro_failCause (root : NativeEff) (c : CauseTerm) (p : Point) (k : Nat)
    (hf : p.fuel = k + 1) (hpos : p.fuel ≠ 0) :
    CodeMeans root (compileEff (.failCause c) p) (denoteR root (.failCause c) p) := by
  rw [compileEff_failCause c hf, denoteR_failCause root c hpos]
  cases causeOf p.env c with
  | some cause => exact CodeMeans.failure _
  | none => exact codeMeans_badShape root

theorem intro_sync (root : NativeEff) (t : Term) (p : Point) (k : Nat)
    (hf : p.fuel = k + 1) (hpos : p.fuel ≠ 0)
    (h : Node.at_ (.eff root) p.path = some (.eff (.sync t))) :
    CodeMeans root (compileEff (.sync t) p) (denoteR root (.sync t) p) := by
  rw [compileEff_sync t hf, denoteR_sync root t hpos, ← syncValueAt_pure h]
  exact CodeMeans.syncPure p _ (CodeMeans.success _)

theorem intro_perform (root : NativeEff) (op : NativeOp) (r : Term) (p : Point) (k : Nat)
    (hf : p.fuel = k + 1) (hpos : p.fuel ≠ 0) :
    CodeMeans root (compileEff (.perform op r) p) (denoteR root (.perform op r) p) := by
  by_cases hk : (NativeOp.row op).kind = .sync
  · rw [compileEff_perform_sync op r hf hk, denoteR_perform_sync root op r hpos hk]
    cases evalTerm p.env r with
    | none => exact codeMeans_badShape root
    | some v =>
      dsimp only [Option.bind]
      cases NativeOp.syncOpOf op v with
      | some o => exact CodeMeans.syncOp o _ (successV root)
      | none => exact codeMeans_badShape root
  · rw [compileEff_perform_nonsync op r hf hk, denoteR_perform_nonsync root op r hpos hk]
    exact asyncRoute_means root op r p

end Effect4.Program.Sched
