import Effect4.Laws.Program.Intro.Scope

/-!
# Source-address introduction (P3, step 3)

Packet: `Test/contracts/program-runtime-r.contract.md` (the P3 relation). The relation of
`Means.lean` is inhabited at every source address: the frame's compile and the term's
denotation of one node at one point are related (`code_intro`), and so are the programs the
names and thunks of `interpOf` build from addresses (`resolve_intro`). The descent is on
the point's weight (its fuel plus its tape): every child point spends one unit of fuel,
so no structural recursion into the mutual source family is
needed. The term's construction heads never sit at the head of a denotation, so `prepareR`
is the identity on it (`prepareR_denoteR`); the guard clauses' continuations resolve their
constructions against the view the frame's refreshed names read.
-/

set_option autoImplicit false

namespace Effect4.Program.Sched

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote Effect4.Program.Agreement
/-! ## The introduction

The families live in `Intro/*.lean` (one module per constructor family, the join and the
layer build); the induction on the weight assembles them here. -/

theorem code_intro_aux (root : NativeEff) : ∀ (n : Nat) (p : Point), p.weight < n →
    ∀ (e : NativeEff), Node.at_ (.eff root) p.path = some (.eff e) →
      CodeMeans root (compileEff e p) (denoteR root e p) := by
  intro n
  induction n with
  | zero => intro p hp; exact absurd hp (Nat.not_lt_zero _)
  | succ n ih =>
  intro p hp e h
  have hle : p.weight ≤ n := Nat.lt_succ_iff.mp hp
  cases hf : p.fuel with
  | zero =>
    rw [compileEff_at_zero e hf, denoteR_zero root e p hf]
    exact CodeMeans.frontier p p _ _ ⟨rfl, rfl, rfl, rfl, rfl⟩ fun completed => by
      rw [suspendBodyAt_zero' (q := { p with completed }) hf]; rfl
  | succ k =>
  have hpos : p.fuel ≠ 0 := by rw [hf]; exact Nat.succ_ne_zero k
  have hres : ∀ q : Point, q.weight < n → CodeMeans root (resolve root q) (denoteAt root q) :=
    resolve_intro_of root n ih
  have hw0 : ∀ i, (p.child i).weight < n := fun i =>
    Nat.lt_of_lt_of_le (weight_child_lt p i hpos) hle
  have hw00 : ((p.child 0).child 0).weight < n :=
    Nat.lt_of_le_of_lt (weight_child (p.child 0) 0) (hw0 0)
  have hwc : ∀ (c : List (FiberId × ExitV)) (i : Nat),
      (({ p with completed := c } : Point).child i).weight < n := fun c i =>
    Nat.lt_of_lt_of_le (weight_child_lt { p with completed := c } i hpos) hle
  have hwcw : ∀ (c : List (FiberId × ExitV)) (i : Nat) (v : Val),
      (({ p with completed := c } : Point).childWith i v).weight < n := fun c i v =>
    Nat.lt_of_lt_of_le (weight_childWith_lt { p with completed := c } i v hpos) hle
  cases e with
  | succeed t => exact intro_succeed root t p k hf hpos
  | fail t => exact intro_fail root t p k hf hpos
  | failCause c => exact intro_failCause root c p k hf hpos
  | yieldError t => exact intro_yieldError root t p k hf hpos
  | sync t => exact intro_sync root t p k hf hpos h
  | suspend b => exact intro_suspend root n b p k hf hpos hwc h ih
  | perform op r => exact intro_perform root op r p k hf hpos
  | bind a b => exact intro_bind root n a b p k hf hpos hw0 hwcw h ih
  | gen ss => exact intro_gen root ss p k hf hpos h
  | catchCause b hd => exact intro_catchCause root n b hd p k hf hpos hw0 hwcw h ih
  | catchIf test b hd => exact intro_catchIf root n test b hd p k hf hpos hw0 hwcw h ih
  | matchCause b v c => exact intro_matchCause root n b v c p k hf hpos hw0 hwcw h ih
  | onExit b f => exact intro_onExit root n b f p k hf hpos hw0 hwcw h ih
  | exit b => exact intro_exit root n b p k hf hpos hw0 h ih
  | uninterruptible b => exact intro_uninterruptible root n b p k hf hpos hw0 h hres
  | interruptible b => exact intro_interruptible root n b p k hf hpos hw0 h hres
  | select s d a0 a1 => exact intro_select root n s d a0 a1 p k hf hpos hwc hwcw h ih
  | whileLoop i t s b => exact intro_whileLoop root i t s b p k hf hpos h
  | iterate c i t s r b => exact intro_iterate root c i t s r b p k hf hpos h
  | yieldNow priority => exact intro_yieldNow root priority p k hf hpos
  | callback op r => exact intro_callback root op r p k hf hpos
  | awaitFiber t mode => exact intro_awaitFiber root t mode p k hf hpos
  | withFiber a => exact intro_withFiber root n a p k hf hpos hw00 h hres ih
  | «scoped» b => exact intro_scoped root b p k hf hpos h
  | acquireRelease a r => exact intro_acquireRelease root n a r p k hf hpos hle hw0 hres
  | provideLayer l i b => exact intro_provideLayer root n l i b p k hf hpos hle h hres
  | service key => exact intro_service root key p k hf hpos
  | provideService key value b => exact intro_provideService root n key value b p k hf hpos hw0 h ih

/-- **Introduction.** At every source address, the compile and the denotation are related. -/
theorem code_intro (root : NativeEff) (e : NativeEff) (p : Point)
    (h : Node.at_ (.eff root) p.path = some (.eff e)) :
    CodeMeans root (compileEff e p) (denoteR root e p) :=
  code_intro_aux root (p.weight + 1) p (Nat.lt_succ_self _) e h

/-- Every point resolves to related programs (the fallbacks are the same refusal). -/
theorem resolve_intro (root : NativeEff) (q : Point) :
    CodeMeans root (resolve root q) (denoteAt root q) :=
  resolve_intro_of root (q.weight + 1) (fun p _ e h => code_intro root e p h) q (Nat.lt_succ_self _)

/-- Every layer point resolves to related builds (the fallbacks are the same refusal). -/
theorem layerBuild_intro (root : NativeEff) (q : Point) (m : MemoMapId) (scope : Nat) :
    CodeMeans root (resolveLayer root q m scope) (layerBuildR root q m scope) := by
  unfold resolveLayer layerBuildR
  rcases hn : Node.at_ (.eff root) q.path with _ | node
  · exact codeMeans_badShape root
  · cases node with
    | layer l =>
      exact layer_intro root (q.weight + 1) (fun q' _ => resolve_intro root q') l q m scope
        (Nat.lt_succ_self _) hn
    | _ => exact codeMeans_badShape root

/-- The loaded roots are related. -/
theorem compile_intro (root : NativeEff) (fuel : Nat) (tape : List Bool) :
    CodeMeans root (compile root fuel tape) (denoteR root root (rootPoint fuel tape)) :=
  code_intro root root (rootPoint fuel tape) rfl

end Effect4.Program.Sched
