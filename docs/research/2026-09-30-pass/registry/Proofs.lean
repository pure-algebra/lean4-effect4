import registry.Core

/-! Registry seat: kernel-checked facts about `staticEnvAt`.

Research evidence outside the Test root. Base `be15b062`.

The main theorem, `envAlong_checks`: if a node checks under a state, then along any path from it
the fold is defined, and the node reached checks under the fold's state. At the root of a
well-typed program this says: every node of the program checks in `staticEnvAt`'s environment
at its path, so the registry's `checkedAt` answers at every fork site and race cell of a
well-typed program (`declared_fork`, `declared_race`), and a fork's declaration is exactly the
`fiberOf` the checker gives its handle there (`fork_handle`).

This is the soundness half of "`staticEnvAt` is the checker's environment": the child checks in
it. That it is the very environment the checker's recursion passes is by construction (each arm
of `stepEnv` transcribes the rule) and is validated, not proved, by the refusal oracle
(`StaticEnv.lean`). -/

set_option autoImplicit false

namespace Research.Pass.Registry.Proofs
open Effect4 Effect4.Machine Effect4.Program Research.Pass.Registry

variable {Op : Type}

/-- A node checks under a state: the checker's success for that node's sort. A statement
list is checked with no preceding `return`, as every rule that reaches one does except the rest
after a `return`, which must then be empty. -/
def NodeChecks (sig : Signature Op) (st : TyEnv × Bool) (p : List Nat) : Node Op → Prop
  | .eff e => (Checker.check sig st.1 p e).toOption.isSome
  | .stmts ss => (Checker.checkStmts sig st.1 st.2 none p ss).toOption.isSome
  | .stmt s => (Checker.checkStmt sig st.1 st.2 p s).toOption.isSome
  | .action a => (Checker.checkAction sig st.1 p a).toOption.isSome
  | .effs es => (Checker.checkEffs sig st.1 p es).toOption.isSome
  | .layer l => (Checker.checkLayer sig p l).toOption.isSome
  | .layers ls => (Checker.checkLayers sig p ls).toOption.isSome

/-! ## `Except` bookkeeping -/

theorem ok_of_bind {α β ε : Type} {x : Except ε α} {f : α → Except ε β}
    (h : (x >>= f).toOption.isSome = true) : ∃ a, x = .ok a ∧ (f a).toOption.isSome = true := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem isSome_of_ok {α ε : Type} {x : Except ε α} {a : α} (h : x = .ok a) :
    x.toOption.isSome = true := by
  rw [h]
  rfl

theorem expect_ok {α : Type} {r : TypeRefusal} {o : Option α} {a : α}
    (h : Checker.expect r o = .ok a) : o = some a := by
  cases o with
  | none => cases h
  | some b =>
    cases h
    rfl

theorem term_ok (sig : Signature Op) (env : TyEnv) (p : List Nat) (t : Term) {ty : Ty}
    (h : Checker.term? sig env p t = .ok ty) : termTy sig env t = some ty :=
  expect_ok h

theorem throw_not_some {α : Type} (r : TypeRefusal)
    (h : (throw r : Except TypeRefusal α).toOption.isSome = true) : False := by
  cases h

/-- A statement list checked after a `return` is empty, and so checks with none. -/
theorem stmts_after_ret (sig : Signature Op) (env : TyEnv) (inLoop : Bool) (ret p : List Nat)
    (rest : Stmts Op) (h : (Checker.checkStmts sig env inLoop (some ret) p rest).toOption.isSome) :
    (Checker.checkStmts sig env inLoop none p rest).toOption.isSome := by
  cases rest with
  | nil => rfl
  | cons head tail =>
    simp only [Checker.checkStmts] at h
    exact (throw_not_some _ h).elim

/-! ## One step -/

/-- If a node checks under a state and has child `i`, the fold steps to a state under which
that child checks. One case per clause of `Node.child`. -/
theorem stepEnv_checks (sig : Signature Op) (st : TyEnv × Bool) (p : List Nat) (n : Node Op)
    (i : Nat) (hn : NodeChecks sig st p n) :
    ∀ c, n.child i = some c →
      ∃ st', stepEnv sig st p n i = some st' ∧ NodeChecks sig st' (p ++ [i]) c := by
  fun_cases Node.child n i
  -- eff (.suspend a0), 0
  · intro c hc
    cases hc
    exact ⟨st, rfl, hn⟩
  -- eff (.bind a0 _), 0
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.check] at hn
    obtain ⟨f, hf, _⟩ := ok_of_bind hn
    exact ⟨st, rfl, isSome_of_ok hf⟩
  -- eff (.bind _ a1), 1
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.check] at hn
    obtain ⟨f, hf, hn⟩ := ok_of_bind hn
    obtain ⟨r, hr, _⟩ := ok_of_bind hn
    refine ⟨(st.1 ++ [f.answer], st.2), ?_, isSome_of_ok hr⟩
    simp only [stepEnv, hf, Except.toOption, Option.map]
  -- eff (.gen a0), 0
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.check] at hn
    obtain ⟨g, hg, _⟩ := ok_of_bind hn
    exact ⟨(st.1, false), rfl, isSome_of_ok hg⟩
  -- eff (.catchCause a0 _), 0
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.check] at hn
    obtain ⟨b, hb, _⟩ := ok_of_bind hn
    exact ⟨st, rfl, isSome_of_ok hb⟩
  -- eff (.catchCause _ a1), 1
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.check] at hn
    obtain ⟨b, hb, hn⟩ := ok_of_bind hn
    obtain ⟨h, hh, _⟩ := ok_of_bind hn
    refine ⟨(st.1 ++ [.causeOf b.error], st.2), ?_, isSome_of_ok hh⟩
    simp only [stepEnv, hb, Except.toOption, Option.map]
  -- eff (.matchCause a0 _ _), 0
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.check] at hn
    obtain ⟨b, hb, _⟩ := ok_of_bind hn
    exact ⟨st, rfl, isSome_of_ok hb⟩
  -- eff (.matchCause _ a1 _), 1
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.check] at hn
    obtain ⟨b, hb, hn⟩ := ok_of_bind hn
    obtain ⟨v, hv, _⟩ := ok_of_bind hn
    refine ⟨(st.1 ++ [b.answer], st.2), ?_, isSome_of_ok hv⟩
    simp only [stepEnv, hb, Except.toOption, Option.map]
  -- eff (.matchCause _ _ a2), 2
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.check] at hn
    obtain ⟨b, hb, hn⟩ := ok_of_bind hn
    obtain ⟨v, _, hn⟩ := ok_of_bind hn
    obtain ⟨k, hk, _⟩ := ok_of_bind hn
    refine ⟨(st.1 ++ [.causeOf b.error], st.2), ?_, isSome_of_ok hk⟩
    simp only [stepEnv, hb, Except.toOption, Option.map]
  -- eff (.onExit a0 _), 0
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.check] at hn
    obtain ⟨b, hb, _⟩ := ok_of_bind hn
    exact ⟨st, rfl, isSome_of_ok hb⟩
  -- eff (.onExit _ a1), 1
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.check] at hn
    obtain ⟨b, hb, hn⟩ := ok_of_bind hn
    obtain ⟨f, hf, _⟩ := ok_of_bind hn
    refine ⟨(st.1 ++ [.exitOf b.answer b.error], st.2), ?_, isSome_of_ok hf⟩
    simp only [stepEnv, hb, Except.toOption, Option.map]
  -- eff (.exit a0), 0
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.check] at hn
    obtain ⟨b, hb, _⟩ := ok_of_bind hn
    exact ⟨st, rfl, isSome_of_ok hb⟩
  -- eff (.uninterruptible a0), 0
  · intro c hc
    cases hc
    exact ⟨st, rfl, hn⟩
  -- eff (.interruptible a0), 0
  · intro c hc
    cases hc
    exact ⟨st, rfl, hn⟩
  -- eff (.withFiber a0), 0
  · intro c hc
    cases hc
    exact ⟨st, rfl, hn⟩
  -- eff (.scoped a0), 0
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.check] at hn
    obtain ⟨t, ht, _⟩ := ok_of_bind hn
    exact ⟨st, rfl, isSome_of_ok ht⟩
  -- eff (.acquireRelease a0 _), 0
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.check] at hn
    obtain ⟨a, ha, _⟩ := ok_of_bind hn
    exact ⟨st, rfl, isSome_of_ok ha⟩
  -- eff (.acquireRelease _ a1), 1
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.check] at hn
    obtain ⟨a, ha, hn⟩ := ok_of_bind hn
    obtain ⟨r, hr, _⟩ := ok_of_bind hn
    refine ⟨(st.1 ++ [a.answer, .exitOf .unknown .unknown], st.2), ?_, isSome_of_ok hr⟩
    simp only [stepEnv, ha, Except.toOption, Option.map]
  -- eff (.provideLayer a0 _ _), 0
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.check] at hn
    obtain ⟨l, hl, _⟩ := ok_of_bind hn
    exact ⟨([], false), rfl, isSome_of_ok hl⟩
  -- eff (.provideLayer _ _ a2), 1
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.check] at hn
    obtain ⟨l, _, hn⟩ := ok_of_bind hn
    obtain ⟨b, hb, _⟩ := ok_of_bind hn
    exact ⟨st, rfl, isSome_of_ok hb⟩
  -- eff (.provideService _ _ a2), 0
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.check] at hn
    obtain ⟨ty, _, hn⟩ := ok_of_bind hn
    obtain ⟨v, _, hn⟩ := ok_of_bind hn
    obtain ⟨b, hb, _⟩ := ok_of_bind hn
    exact ⟨st, rfl, isSome_of_ok hb⟩
  -- eff (.catchIf _ a1 _), 0
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.check] at hn
    obtain ⟨b, hb, _⟩ := ok_of_bind hn
    exact ⟨st, rfl, isSome_of_ok hb⟩
  -- eff (.catchIf _ _ a2), 1
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.check] at hn
    obtain ⟨b, hb, hn⟩ := ok_of_bind hn
    obtain ⟨predicate, _, hn⟩ := ok_of_bind hn
    split at hn
    · obtain ⟨h, hh, _⟩ := ok_of_bind hn
      refine ⟨(st.1 ++ [b.error], st.2), ?_, isSome_of_ok hh⟩
      simp only [stepEnv, hb, Except.toOption, Option.map]
    · exact (throw_not_some _ hn).elim
  -- eff (.select _ _ a2 _), 0
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.check] at hn
    obtain ⟨t, ht, hn⟩ := ok_of_bind hn
    obtain ⟨arms, harms, hn⟩ := ok_of_bind hn
    obtain ⟨t0, ht0, _⟩ := ok_of_bind hn
    refine ⟨(st.1 ++ arms.1, st.2), ?_, isSome_of_ok ht0⟩
    simp only [stepEnv, term_ok sig st.1 p _ ht, expect_ok harms, Option.bind, Option.map]
  -- eff (.select _ _ _ a3), 1
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.check] at hn
    obtain ⟨t, ht, hn⟩ := ok_of_bind hn
    obtain ⟨arms, harms, hn⟩ := ok_of_bind hn
    obtain ⟨t0, _, hn⟩ := ok_of_bind hn
    obtain ⟨t1, ht1, _⟩ := ok_of_bind hn
    refine ⟨(st.1 ++ arms.2, st.2), ?_, isSome_of_ok ht1⟩
    simp only [stepEnv, term_ok sig st.1 p _ ht, expect_ok harms, Option.bind, Option.map]
  -- eff (.iterate _ _ _ _ _ a5), 0
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.check] at hn
    obtain ⟨c0, hc0, hn⟩ := ok_of_bind hn
    obtain ⟨t, _, hn⟩ := ok_of_bind hn
    obtain ⟨b, hb, _⟩ := ok_of_bind hn
    refine ⟨(st.1 ++ [_], st.2), ?_, isSome_of_ok hb⟩
    simp only [stepEnv, term_ok sig st.1 p _ hc0, Option.map]
  -- action (.fork a0 _), 0
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.checkAction] at hn
    obtain ⟨t, ht, _⟩ := ok_of_bind hn
    exact ⟨st, rfl, isSome_of_ok ht⟩
  -- action (.forkIn a0 _ _), 0
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.checkAction] at hn
    obtain ⟨t, ht, _⟩ := ok_of_bind hn
    exact ⟨st, rfl, isSome_of_ok ht⟩
  -- action (.forkScoped a0 _), 0
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.checkAction] at hn
    obtain ⟨t, ht, _⟩ := ok_of_bind hn
    exact ⟨st, rfl, isSome_of_ok ht⟩
  -- action (.raceAll a0), 0
  · intro c hc
    cases hc
    exact ⟨st, rfl, hn⟩
  -- layer (.effect _ a1), 0
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.checkLayer] at hn
    obtain ⟨t, ht, _⟩ := ok_of_bind hn
    exact ⟨([], false), rfl, isSome_of_ok ht⟩
  -- layer (.effectDiscard a0), 0
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.checkLayer] at hn
    obtain ⟨t, ht, _⟩ := ok_of_bind hn
    exact ⟨([], false), rfl, isSome_of_ok ht⟩
  -- layer (.provide a0 _), 0
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.checkLayer] at hn
    obtain ⟨s, hs, _⟩ := ok_of_bind hn
    exact ⟨([], false), rfl, isSome_of_ok hs⟩
  -- layer (.provide _ a1), 1
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.checkLayer] at hn
    obtain ⟨s, _, hn⟩ := ok_of_bind hn
    obtain ⟨t, ht, _⟩ := ok_of_bind hn
    exact ⟨([], false), rfl, isSome_of_ok ht⟩
  -- layer (.provideMerge a0 _), 0
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.checkLayer] at hn
    obtain ⟨s, hs, _⟩ := ok_of_bind hn
    exact ⟨([], false), rfl, isSome_of_ok hs⟩
  -- layer (.provideMerge _ a1), 1
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.checkLayer] at hn
    obtain ⟨s, _, hn⟩ := ok_of_bind hn
    obtain ⟨t, ht, _⟩ := ok_of_bind hn
    exact ⟨([], false), rfl, isSome_of_ok ht⟩
  -- layer (.merge a0 _), 0
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.checkLayer] at hn
    obtain ⟨a, ha, _⟩ := ok_of_bind hn
    exact ⟨([], false), rfl, isSome_of_ok ha⟩
  -- layer (.merge _ a1), 1
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.checkLayer] at hn
    obtain ⟨a, _, hn⟩ := ok_of_bind hn
    obtain ⟨b, hb, _⟩ := ok_of_bind hn
    exact ⟨([], false), rfl, isSome_of_ok hb⟩
  -- layer (.fresh a0), 0
  · intro c hc
    cases hc
    exact ⟨([], false), rfl, hn⟩
  -- layer (.orDie a0), 0
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.checkLayer] at hn
    obtain ⟨l, hl, _⟩ := ok_of_bind hn
    exact ⟨([], false), rfl, isSome_of_ok hl⟩
  -- layer (.mergeAll a0), 0
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.checkLayer] at hn
    obtain ⟨ls, hls, _⟩ := ok_of_bind hn
    exact ⟨([], false), rfl, isSome_of_ok hls⟩
  -- stmts (.cons a0 _), 0
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.checkStmts] at hn
    obtain ⟨s, hs, _⟩ := ok_of_bind hn
    exact ⟨st, rfl, isSome_of_ok hs⟩
  -- stmts (.cons _ a1), 1
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.checkStmts] at hn
    obtain ⟨s, hs, hn⟩ := ok_of_bind hn
    cases s with
    | step g binds =>
      simp only [StmtTy.fold] at hn
      obtain ⟨r, hr, _⟩ := ok_of_bind hn
      refine ⟨(st.1 ++ binds, st.2), ?_, isSome_of_ok hr⟩
      simp only [stepEnv, hs, Except.toOption, Option.map, StmtTy.fold]
    | ret answer =>
      simp only [StmtTy.fold] at hn
      obtain ⟨r, hr, _⟩ := ok_of_bind hn
      refine ⟨st, ?_, stmts_after_ret sig st.1 st.2 _ _ _ (isSome_of_ok hr)⟩
      simp only [stepEnv, hs, Except.toOption, Option.map, StmtTy.fold]
    | pass =>
      simp only [StmtTy.fold] at hn
      refine ⟨st, ?_, hn⟩
      simp only [stepEnv, hs, Except.toOption, Option.map, StmtTy.fold]
  -- stmt (.bindYield a0), 0
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.checkStmt] at hn
    obtain ⟨t, ht, _⟩ := ok_of_bind hn
    exact ⟨st, rfl, isSome_of_ok ht⟩
  -- stmt (.yieldDiscard a0), 0
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.checkStmt] at hn
    obtain ⟨t, ht, _⟩ := ok_of_bind hn
    exact ⟨st, rfl, isSome_of_ok ht⟩
  -- stmt (.ifElse _ a1 _), 0
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.checkStmt] at hn
    obtain ⟨t, _, hn⟩ := ok_of_bind hn
    split at hn
    · obtain ⟨a, ha, _⟩ := ok_of_bind hn
      exact ⟨st, rfl, isSome_of_ok ha⟩
    · exact (throw_not_some _ hn).elim
  -- stmt (.ifElse _ _ a2), 1
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.checkStmt] at hn
    obtain ⟨t, _, hn⟩ := ok_of_bind hn
    split at hn
    · obtain ⟨a, _, hn⟩ := ok_of_bind hn
      obtain ⟨b, hb, _⟩ := ok_of_bind hn
      exact ⟨st, rfl, isSome_of_ok hb⟩
    · exact (throw_not_some _ hn).elim
  -- stmt (.whileTrue a0), 0
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.checkStmt] at hn
    obtain ⟨b, hb, _⟩ := ok_of_bind hn
    exact ⟨(st.1, true), rfl, isSome_of_ok hb⟩
  -- effs (.cons a0 _), 0
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.checkEffs] at hn
    obtain ⟨h, hh, _⟩ := ok_of_bind hn
    exact ⟨st, rfl, isSome_of_ok hh⟩
  -- effs (.cons _ a1), 1
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.checkEffs] at hn
    obtain ⟨h, _, hn⟩ := ok_of_bind hn
    obtain ⟨t, ht, _⟩ := ok_of_bind hn
    exact ⟨st, rfl, isSome_of_ok ht⟩
  -- layers (.cons a0 _), 0
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.checkLayers] at hn
    obtain ⟨h, hh, _⟩ := ok_of_bind hn
    exact ⟨([], false), rfl, isSome_of_ok hh⟩
  -- layers (.cons _ a1), 1
  · intro c hc
    cases hc
    simp only [NodeChecks, Checker.checkLayers] at hn
    obtain ⟨h, _, hn⟩ := ok_of_bind hn
    obtain ⟨t, ht, _⟩ := ok_of_bind hn
    exact ⟨([], false), rfl, isSome_of_ok ht⟩
  -- no child
  · intro c hc
    cases hc

/-! ## Along a path -/

/-- If a node checks under a state, the fold is defined along every path from it, and the node
the path reaches checks under the fold's state. -/
theorem envAlong_checks (sig : Signature Op) :
    ∀ (path : List Nat) (n : Node Op) (p : List Nat) (st : TyEnv × Bool) (c : Node Op),
      NodeChecks sig st p n → Node.at_ n path = some c →
      ∃ st', envAlong sig n p st path = some st' ∧ NodeChecks sig st' (p ++ path) c
  | [], n, p, st, c, hn, hc => by
    simp only [Node.at_, Option.some.injEq] at hc
    cases hc
    refine ⟨st, rfl, ?_⟩
    rw [List.append_nil]
    exact hn
  | i :: rest, n, p, st, c, hn, hc => by
    simp only [Node.at_] at hc
    cases hci : n.child i with
    | none =>
      rw [hci] at hc
      cases hc
    | some c1 =>
      rw [hci, Option.bind_some] at hc
      obtain ⟨st1, hst1, hc1⟩ := stepEnv_checks sig st p n i hn c1 hci
      obtain ⟨st', hst', hc'⟩ := envAlong_checks sig rest c1 (p ++ [i]) st1 c hc1 hc
      refine ⟨st', ?_, ?_⟩
      · simp only [envAlong, hst1, hci, Option.bind_some, hst']
      · rw [List.append_assoc, List.singleton_append] at hc'
        exact hc'

/-- At the root of a program that checks, the fold reaches every node, and the node checks in
the fold's state. -/
theorem staticEnv_checks (sig : Signature Op) (root : Eff Op) (T : EffTy)
    (hroot : Checker.check sig [] [] root = .ok T) (path : List Nat) (c : Node Op)
    (hc : Node.at_ (.eff root) path = some c) :
    ∃ st, envAlong sig (.eff root) [] ([], false) path = some st ∧ NodeChecks sig st path c := by
  obtain ⟨st, hst, hcs⟩ := envAlong_checks sig path (.eff root) [] ([], false) c
    (isSome_of_ok hroot) hc
  rw [List.nil_append] at hcs
  exact ⟨st, hst, hcs⟩

/-! ## The registry answers at every creation site of a well-typed program -/

/-- A fork's declaration is exactly the `fiberOf` the checker gives its handle at that site, in
the site's static environment. -/
theorem fork_handle (sig : Signature Op) (root : Eff Op) (T : EffTy)
    (hroot : Checker.check sig [] [] root = .ok T) (site : List Nat) (body : Eff Op)
    (o : Supervision.ForkOptions)
    (hsite : Node.at_ (.eff root) site = some (.action (.fork body o))) :
    ∃ env d, staticEnvAt sig root site = some env ∧ checkedAt sig root site body = some d ∧
      Checker.checkAction sig env site (.fork body o) =
        .ok ⟨.fiberOf d.answer d.error, .never, d.requires⟩ := by
  obtain ⟨st, hst, hcs⟩ := staticEnv_checks sig root T hroot site _ hsite
  simp only [NodeChecks, Checker.checkAction] at hcs
  obtain ⟨t, ht, _⟩ := ok_of_bind hcs
  have henv : staticEnvAt sig root site = some st.1 := by
    simp only [staticEnvAt, hst, Option.map_some]
  refine ⟨st.1, t, henv, ?_, ?_⟩
  · simp only [checkedAt, henv, Option.bind_some, ht, Except.toOption]
  · simp only [Checker.checkAction, ht]
    rfl

theorem declared_fork (sig : Signature Op) (root : Eff Op) (T : EffTy)
    (hroot : Checker.check sig [] [] root = .ok T) (child parent : FiberId) (daemon : Bool)
    (site : List Nat) (body : Eff Op) (o : Supervision.ForkOptions)
    (hsite : Node.at_ (.eff root) site = some (.action (.fork body o))) :
    (ForkRecord.declared sig root ⟨child, parent, daemon, site, .action⟩).isSome := by
  obtain ⟨_, d, _, hd, _⟩ := fork_handle sig root T hroot site body o hsite
  simp only [ForkRecord.declared, hsite, hd, Option.isSome_some]

theorem declared_forkIn (sig : Signature Op) (root : Eff Op) (T : EffTy)
    (hroot : Checker.check sig [] [] root = .ok T) (child parent : FiberId) (daemon : Bool)
    (site : List Nat) (body : Eff Op) (o : Supervision.ForkOptions) (scope : Term)
    (hsite : Node.at_ (.eff root) site = some (.action (.forkIn body o scope))) :
    (ForkRecord.declared sig root ⟨child, parent, daemon, site, .action⟩).isSome := by
  obtain ⟨st, hst, hcs⟩ := staticEnv_checks sig root T hroot site _ hsite
  simp only [NodeChecks, Checker.checkAction] at hcs
  obtain ⟨t, ht, _⟩ := ok_of_bind hcs
  simp only [ForkRecord.declared, hsite, checkedAt, staticEnvAt, hst, Option.map_some,
    Option.bind_some, ht, Except.toOption, Option.isSome_some]

theorem declared_forkScoped (sig : Signature Op) (root : Eff Op) (T : EffTy)
    (hroot : Checker.check sig [] [] root = .ok T) (child parent : FiberId) (daemon : Bool)
    (site : List Nat) (body : Eff Op) (o : Supervision.ForkOptions)
    (hsite : Node.at_ (.eff root) site = some (.action (.forkScoped body o))) :
    (ForkRecord.declared sig root ⟨child, parent, daemon, site, .action⟩).isSome := by
  obtain ⟨st, hst, hcs⟩ := staticEnv_checks sig root T hroot site _ hsite
  simp only [NodeChecks, Checker.checkAction] at hcs
  obtain ⟨t, ht, _⟩ := ok_of_bind hcs
  simp only [ForkRecord.declared, hsite, checkedAt, staticEnvAt, hst, Option.map_some,
    Option.bind_some, ht, Except.toOption, Option.isSome_some]

theorem declared_race (sig : Signature Op) (root : Eff Op) (T : EffTy)
    (hroot : Checker.check sig [] [] root = .ok T) (child parent : FiberId) (daemon : Bool)
    (site : List Nat) (head : Eff Op) (tail : Effs Op)
    (hsite : Node.at_ (.eff root) site = some (.effs (.cons head tail))) :
    (ForkRecord.declared sig root ⟨child, parent, daemon, site, .raceEntrant⟩).isSome := by
  obtain ⟨st, hst, hcs⟩ := staticEnv_checks sig root T hroot site _ hsite
  simp only [NodeChecks, Checker.checkEffs] at hcs
  obtain ⟨t, ht, _⟩ := ok_of_bind hcs
  simp only [ForkRecord.declared, hsite, checkedAt, staticEnvAt, hst, Option.map_some,
    Option.bind_some, ht, Except.toOption, Option.isSome_some]

theorem declared_layer (sig : Signature Op) (root : Eff Op) (T : EffTy)
    (hroot : Checker.check sig [] [] root = .ok T) (child parent : FiberId) (daemon : Bool)
    (site : List Nat) (l : LayerTerm Op)
    (hsite : Node.at_ (.eff root) site = some (.layer l)) :
    (ForkRecord.declared sig root ⟨child, parent, daemon, site, .action⟩).isSome := by
  obtain ⟨_, _, hcs⟩ := staticEnv_checks sig root T hroot site _ hsite
  simp only [NodeChecks] at hcs
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hcs
  simp only [ForkRecord.declared, hsite, ht, Option.map_some, Option.isSome_some]

theorem declared_finalizer (sig : Signature Op) (root : Eff Op) (child parent : FiberId)
    (daemon : Bool) (site : List Nat) :
    ForkRecord.declared sig root ⟨child, parent, daemon, site, .finalizer⟩ =
      some ⟨.unknown, .never, Env.Requirement.empty⟩ := rfl

/-- The whole-program typing the API uses (`Api.typeOf`, `typeOfProgram`) is the checker's
success on the program with its layer references expanded: the root these theorems take. -/
theorem check_of_typeOfProgram (sig : Signature Op) (program : Eff Op) (T : EffTy)
    (h : typeOfProgram sig program = some T) :
    Checker.check sig [] [] program.expandRefs = .ok T := by
  unfold typeOfProgram at h
  split at h
  · unfold typeOf effTy at h
    cases hc : Checker.check sig [] [] program.expandRefs with
    | error r =>
      rw [hc] at h
      cases h
    | ok t =>
      rw [hc] at h
      cases h
      rfl
  · cases h

/-- The API-level statement: for a program the API types, every fork at a site of its
expanded tree is declared, at exactly its handle's `fiberOf`. -/
theorem api_fork_handle (table : RowTable) (program : Eff NativeOp) (T : EffTy)
    (h : Api.typeOf program table = some T) (site : List Nat) (body : Eff NativeOp)
    (o : Supervision.ForkOptions)
    (hsite : Node.at_ (.eff program.expandRefs) site = some (.action (.fork body o))) :
    ∃ env d, staticEnvAt (nativeSignature table) program.expandRefs site = some env ∧
      checkedAt (nativeSignature table) program.expandRefs site body = some d ∧
      Checker.checkAction (nativeSignature table) env site (.fork body o) =
        .ok ⟨.fiberOf d.answer d.error, .never, d.requires⟩ :=
  fork_handle _ _ T (check_of_typeOfProgram _ _ T h) site body o hsite

#print axioms ok_of_bind
#print axioms isSome_of_ok
#print axioms expect_ok
#print axioms term_ok
#print axioms throw_not_some
#print axioms stmts_after_ret
#print axioms stepEnv_checks
#print axioms envAlong_checks
#print axioms staticEnv_checks
#print axioms fork_handle
#print axioms declared_fork
#print axioms declared_forkIn
#print axioms declared_forkScoped
#print axioms declared_race
#print axioms declared_layer
#print axioms declared_finalizer
#print axioms check_of_typeOfProgram
#print axioms api_fork_handle

end Research.Pass.Registry.Proofs
