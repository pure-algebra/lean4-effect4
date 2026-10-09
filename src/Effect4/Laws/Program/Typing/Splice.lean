import Effect4.Program.Typing.Splice
import Effect4.Laws.Program.Typing.Annotate
import Effect4.Laws.Program.Typing.Replace
import Effect4.Laws.Program.Typing.Focus
import Effect4.Laws.Program.Typing.Table
import Effect4.Laws.Auto.Semantics

/-!
# Laws.Program.Typing.Splice — an edit that keeps its focus's type splices the address table

## Placement

Concept `initial-algebras-folds`; property: the address table is a fold, and an edit is a lens
update, so an edit that keeps its focus's type changes the table only inside the edited subtree.
Requirement R14. The claim `edit-splices-table`, role preservation, pointer `table_splice`.

- Reach: one signature; a program that the checker types, with no block; an edit of a program
  node at the focus that `focusAt` answers, by a program of the focus's type in the focus's
  environment. The parts (`Program/Typing/Parts.lean`) lift it to a whole program one part at a
  time; no law states that lift yet.
- Not established: an edit that changes the type, which must check again; layer references (an
  edit of equal layer type may remove a referenced target); a program that the checker refuses;
  the cost, which no theorem counts.
- Unlocks: R14, live editing at the cost of the edited subtree: the edit session's coherence, the
  query tool's `fill` without a new check of the context, and the view's repaint set.
- Route: `tableAt_eq_cons` unfolds the table one node at a time along the path. `child_step`
  gives the edited child's type; the other children keep their environments, because a step reads
  only the types of earlier siblings and the node's terms, and the edited child keeps its type.
-/

set_option autoImplicit false

namespace Effect4.Program

open Conform.Effect4.Typing

variable {Op : Type}

/-! ## The splice as a list function -/

/-- A `takeWhile` as long as its list keeps every element. A step of
`Table.splice_append_out_right`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem List.all_of_takeWhile_length {α : Type} {p : α → Bool} :
    ∀ {l : List α}, (l.takeWhile p).length = l.length → ∀ x ∈ l, p x = true
  | [], _, x, hx => by cases hx
  | y :: l, h, x, hx => by
    cases hy : p y with
    | false =>
      rw [List.takeWhile_cons_of_neg (by rw [hy]; exact Bool.false_ne_true)] at h
      cases h
    | true =>
      rw [List.takeWhile_cons_of_pos hy, List.length_cons, List.length_cons] at h
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hy
      · exact List.all_of_takeWhile_length (Nat.add_right_cancel h) x hx

/-- A `dropWhile` that drops every element: every element satisfied the test. A step of
`Table.splice_append_out_right`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem List.all_of_dropWhile_nil {α : Type} {p : α → Bool} :
    ∀ {l : List α}, l.dropWhile p = [] → ∀ x ∈ l, p x = true
  | [], _, x, hx => by cases hx
  | y :: l, h, x, hx => by
    cases hy : p y with
    | false =>
      rw [List.dropWhile_cons_of_neg (by rw [hy]; exact Bool.false_ne_true)] at h
      cases h
    | true =>
      rw [List.dropWhile_cons_of_pos hy] at h
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hy
      · exact List.all_of_dropWhile_nil h x hx

/-- A `dropWhile` of a list whose every element satisfies the test is empty. A step of
`Table.splice_all_under`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem List.dropWhile_eq_nil_of_all {α : Type} {p : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = true) → l.dropWhile p = []
  | [], _ => rfl
  | y :: l, h => by
    rw [List.dropWhile_cons_of_pos (h y List.mem_cons_self)]
    exact List.dropWhile_eq_nil_of_all fun x hx => h x (List.mem_cons_of_mem y hx)

/-- An address is inside its own subtree, and so is each extension of it. A step of
`tableAt_splice`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Table.under_append (a b : List Nat) : Table.under a (a ++ b) = true := by
  unfold Table.under
  exact List.isPrefixOf_iff_prefix.mpr (List.prefix_append a b)

/-- A node's own address is outside the subtree at a strict extension of it. A step of
`tableAt_splice`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Table.under_prefix_false (pre rest : List Nat) (i : Nat) :
    Table.under (pre ++ i :: rest) pre = false := by
  unfold Table.under
  cases h : (pre ++ i :: rest).isPrefixOf pre with
  | false => rfl
  | true =>
    have hl := (List.isPrefixOf_iff_prefix.mp h).length_le
    simp only [List.length_append, List.length_cons] at hl
    omega

/-- A sibling's subtree is outside the subtree at another child. A step of `tableAt_splice`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Table.under_sibling_false (pre rest b : List Nat) {i j : Nat} (hj : j ≠ i) :
    Table.under (pre ++ i :: rest) (pre ++ j :: b) = false := by
  unfold Table.under
  cases h : (pre ++ i :: rest).isPrefixOf (pre ++ j :: b) with
  | false => rfl
  | true =>
    have hp := (List.prefix_append_right_inj pre).mp (List.isPrefixOf_iff_prefix.mp h)
    exact absurd (List.cons_prefix_cons.mp hp).1.symm hj

/-- Entries before the subtree stay in front. A step of `tableAt_splice`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Table.splice_append_out_left {a : List Nat} {X Y sub : List Table.Entry}
    (hX : ∀ e ∈ X, Table.under a e.path = false) :
    Table.splice (X ++ Y) a sub = X ++ Table.splice Y a sub := by
  unfold Table.splice
  have hp : ∀ e ∈ X, (!Table.under a e.path) = true := fun e he => by
    rw [hX e he]
    rfl
  rw [List.takeWhile_append_of_pos hp, List.dropWhile_append_of_pos hp]
  simp only [List.append_assoc]

/-- Entries after the subtree stay behind, once the subtree has begun. A step of
`tableAt_splice`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Table.splice_append_out_right {a : List Nat} {Y Z sub : List Table.Entry}
    (hY : ∃ e ∈ Y, Table.under a e.path = true) (hZ : ∀ e ∈ Z, Table.under a e.path = false) :
    Table.splice (Y ++ Z) a sub = Table.splice Y a sub ++ Z := by
  obtain ⟨y, hy, hyu⟩ := hY
  unfold Table.splice
  have hny : (!Table.under a y.path) = false := by rw [hyu]; rfl
  have htake : (Y.takeWhile fun e => !Table.under a e.path).length ≠ Y.length := fun h =>
    absurd (List.all_of_takeWhile_length h y hy) (by rw [hny]; exact Bool.false_ne_true)
  have hdrop : (Y.dropWhile fun e => !Table.under a e.path).isEmpty = false := by
    cases hd : (Y.dropWhile fun e => !Table.under a e.path) with
    | nil => exact absurd (List.all_of_dropWhile_nil hd y hy) (by rw [hny]; exact Bool.false_ne_true)
    | cons _ _ => rfl
  have hZ' : (Z.dropWhile fun e => Table.under a e.path) = Z := by
    cases Z with
    | nil => rfl
    | cons z Z => exact List.dropWhile_cons_of_neg (by rw [hZ z List.mem_cons_self]; exact Bool.false_ne_true)
  rw [List.takeWhile_append, if_neg htake, List.dropWhile_append, hdrop, if_neg Bool.false_ne_true,
    List.dropWhile_append]
  split
  · rename_i hnil
    rw [hZ', List.isEmpty_iff.mp hnil]
    simp only [List.append_nil, List.append_assoc]
  · simp only [List.append_assoc]

/-- A table that is all inside the subtree is replaced whole. A step of `tableAt_splice`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Table.splice_all_under {a : List Nat} {L sub : List Table.Entry}
    (h : ∀ e ∈ L, Table.under a e.path = true) : Table.splice L a sub = sub := by
  unfold Table.splice
  cases L with
  | nil => simp only [List.takeWhile_nil, List.dropWhile_nil, List.nil_append, List.append_nil]
  | cons e L =>
    have he : Table.under a e.path = true := h e List.mem_cons_self
    rw [List.takeWhile_cons_of_neg (by rw [he]; exact Bool.false_ne_true),
      List.dropWhile_cons_of_neg (by rw [he]; exact Bool.false_ne_true),
      List.dropWhile_eq_nil_of_all h]
    simp only [List.nil_append, List.append_nil]

/-! ## The table's addresses -/

/-- Every entry of the table at a node stands at an extension of the node's address. A step of
`tableAt_splice`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem tableAt_path {s : Signature Op} {ctx : Option NodeEnv} {n : Node Op} {pre : List Nat}
    {e : Table.Entry} (he : e ∈ tableAt s ctx n pre) : ∃ b, e.path = pre ++ b := by
  unfold tableAt at he
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp he
  exact ⟨b, rfl⟩

/-- The table at a node holds an entry at every address of its subtree. A step of
`tableAt_splice`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem tableAt_mem_path {s : Signature Op} {ctx : Option NodeEnv} {n x : Node Op}
    {pre b : List Nat} (h : n.at_ b = some x) : ∃ e ∈ tableAt s ctx n pre, e.path = pre ++ b := by
  have hb : b ∈ Node.addresses n := (mem_addresses_iff n b).mpr (by rw [h]; rfl)
  exact ⟨_, List.mem_map.mpr ⟨b, hb, rfl⟩, rfl⟩

/-- A node has at most three children. A step of `tableAt_splice`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Node.child_add_three (n : Node Op) (i : Nat) : n.child (i + 3) = none := by
  rcases n with x | x | x | x | x | x | x <;> cases x <;> rfl

/-! ## What an edit that keeps its focus's type keeps -/

/-- **A statement list's head keeps what its tail's environment reads**: a type-kept edit
inside the head statement leaves the environment of the list's tail as it was. The tail reads the
type of the head's program only after a `bindYield`, and that program keeps its type. A step of
`Node.childEnv_replace_kept`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Node.stmtsHead_replace_kept {s : Signature Op} {a0 x : Stmt Op} {a1 : Stmts Op}
    {τ : NodeTy Op} {rest : List Nat} {q q' : Eff Op} {env : TyEnv} {t : EffTy}
    (hn : NodeHasTy s (.stmts (.cons a0 a1)) τ) (hat : (Node.stmt a0).at_ rest = some (.eff q))
    (henv : (Node.stmts (.cons a0 a1)).envAt s τ.env (0 :: rest) = some (.env env))
    (hq : HasTy s env q t) (hq' : HasTy s env q' t)
    (hrc : (Node.stmt a0).replaceAt rest (.eff q') = some (.stmt x)) :
    (Node.stmts (.cons x a1)).childEnv s τ.env 1 = (Node.stmts (.cons a0 a1)).childEnv s τ.env 1 := by
  obtain ⟨τc, hc, hcenv, -⟩ := hn.child_step (i := 0) (c := .stmt a0) rfl ⟨rest, q, hat⟩
  have henvc : (Node.stmt a0).envAt s τc.env rest = some (.env env) := by
    simpa only [Node.envAt, Node.child, Option.bind_some, hcenv] using henv
  cases rest with
  | nil =>
    simp only [Node.at_, Option.some.injEq] at hat
    cases hat
  | cons k r =>
    cases hck : (Node.stmt a0).child k with
    | none => simp only [Node.at_, hck, Option.bind_none, reduceCtorEq] at hat
    | some m0 =>
      cases hm : m0.replaceAt r (.eff q') with
      | none =>
        simp only [Node.replaceAt, hck, Option.bind_some, hm, Option.bind_none,
          reduceCtorEq] at hrc
      | some m =>
        have hset : (Node.stmt a0).setChild k m = some (.stmt x) := by
          simpa only [Node.replaceAt, hck, Option.bind_some, hm] using hrc
        cases a0 with
        | bindYield e =>
          rcases k with _ | k <;> cases m <;> cases hset
          simp only [Node.child, Option.some.injEq] at hck
          subst hck
          have hat' : (Node.eff e).at_ r = some (.eff q) := by
            simpa only [Node.at_, Node.child, Option.bind_some] using hat
          obtain ⟨τe, hce, hcenv2, -⟩ := hc.child_step (i := 0) (c := .eff e) rfl ⟨r, q, hat'⟩
          have henve : (Node.eff e).envAt s τe.env r = some (.env env) := by
            simpa only [Node.envAt, Node.child, Option.bind_some, hcenv2] using henvc
          obtain ⟨env1, t1, henv1, hq1, hrebuild⟩ := NodeHasTy.replace_envAt r hce hat'
          have hsame : NodeEnv.env env = NodeEnv.env env1 :=
            Option.some.inj (henve.symm.trans henv1)
          injection hsame with henv2
          subst henv2
          have ht : t = t1 := Option.some.inj ((effTy_complete s q env t hq).symm.trans
            (effTy_complete s q env t1 hq1))
          subst ht
          have hy := hrebuild (SigExtends.refl s) hq' hm
          cases hce with
          | eff he =>
            cases hy with
            | eff hy' =>
              simp only [Node.childEnv, Option.some.injEq] at hcenv hcenv2
              rw [← hcenv] at hcenv2
              injection hcenv2 with hE
              subst hE
              have he2 : HasTy s τ.env.tyEnv e _ := he
              have hy2 : HasTy s τ.env.tyEnv _ _ := hy'
              simp only [Node.childEnv, effTy_complete _ _ _ _ he2, effTy_complete _ _ _ _ hy2]
        | _ => rcases k with _ | _ | k <;> cases m <;> cases hset <;> rfl

set_option maxHeartbeats 1600000 in
/-- **No child's environment changes**: a step reads the types of earlier siblings and the
node's terms, and the edited child keeps its type. A step of `tableAt_splice`.

The proof is casework over the 56 arms of `Node.setChild` and the four indices of
`Node.childEnv`, and it raises the heartbeat bound for that unfolding (a finding: a law of
`childEnv` by its reads would remove the casework). -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Node.childEnv_replace_kept {s : Signature Op} {n n' c c' : Node Op} {τ : NodeTy Op}
    {i : Nat} {rest : List Nat} {q q' : Eff Op} {env : TyEnv} {t : EffTy}
    (hn : NodeHasTy s n τ) (hci : n.child i = some c) (hat : c.at_ rest = some (.eff q))
    (henv : n.envAt s τ.env (i :: rest) = some (.env env)) (hq : HasTy s env q t)
    (hq' : HasTy s env q' t) (hrc : c.replaceAt rest (.eff q') = some c')
    (hset : n.setChild i c' = some n') :
    ∀ j, n'.childEnv s τ.env j = n.childEnv s τ.env j := by
  obtain ⟨τc, hc, hcenv, -⟩ := hn.child_step hci ⟨rest, q, hat⟩
  have henvc : c.envAt s τc.env rest = some (.env env) := by
    simpa only [Node.envAt, hci, Option.bind_some, hcenv] using henv
  obtain ⟨env1, t1, henv1, hq1, hrebuild⟩ := NodeHasTy.replace_envAt rest hc hat
  have hsame : NodeEnv.env env = NodeEnv.env env1 := Option.some.inj (henvc.symm.trans henv1)
  injection hsame with henv2
  subst henv2
  have ht : t = t1 := Option.some.inj ((effTy_complete s q env t hq).symm.trans
    (effTy_complete s q env t1 hq1))
  subst ht
  have hc' : NodeHasTy s c' τc := hrebuild (SigExtends.refl s) hq' hrc
  -- the edited child, where it is a program, keeps its type
  have hK : ∀ a b, c = .eff a → c' = .eff b →
      effTy s τc.env.tyEnv b = effTy s τc.env.tyEnv a := by
    intro a b ha hb
    subst ha
    subst hb
    cases hc with
    | eff ha' =>
      cases hc' with
      | eff hb' =>
        simp only [NodeTy.env, NodeEnv.tyEnv]
        rw [effTy_complete _ _ _ _ ha', effTy_complete _ _ _ _ hb']
  intro j
  unfold Node.setChild at hset
  split at hset <;> cases hset
  -- the arms whose later child reads the edited first child's type
  case h_2 | h_5 | h_7 | h_10 | h_17 | h_22 =>
    simp only [Node.child, Option.some.injEq] at hci
    have hk := hK _ _ hci.symm rfl
    simp only [Node.childEnv, Option.some.injEq] at hcenv
    rw [← hcenv] at hk
    change effTy s τ.env.tyEnv _ = effTy s τ.env.tyEnv _ at hk
    rcases j with _ | _ | _ | j <;> simp only [Node.childEnv, hk]
  -- a statement list's head: the tail reads a `bindYield`'s program
  case h_45 =>
    simp only [Node.child, Option.some.injEq] at hci
    subst hci
    rcases j with _ | _ | _ | j
    · rfl
    · exact Node.stmtsHead_replace_kept hn hat henv hq hq' hrc
    · rfl
    · rfl
  -- a statement list's tail: the tail's environment reads the head, which stays
  case h_46 => rcases j with _ | _ | _ | j <;> cases ‹Stmt Op› <;> rfl
  all_goals rcases j with _ | _ | _ | j <;> rfl

/-- **The node's own entry is kept**: the edited node has the node's type, so the checker's
answer there is the same. A step of `tableAt_splice`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem nodeAnswer_replace_kept {s : Signature Op} {n n' : Node Op} {τ : NodeTy Op}
    {path pre : List Nat} {q q' : Eff Op} {env : TyEnv} {t : EffTy}
    (hn : NodeHasTy s n τ) (hat : n.at_ path = some (.eff q))
    (henv : n.envAt s τ.env path = some (.env env)) (hq : HasTy s env q t)
    (hq' : HasTy s env q' t) (hrep : n.replaceAt path (.eff q') = some n') :
    nodeAnswer s (some τ.env) n' pre = nodeAnswer s (some τ.env) n pre := by
  obtain ⟨env', t', henv', hq0, hrebuild⟩ := NodeHasTy.replace_envAt path hn hat
  have hsame : NodeEnv.env env = NodeEnv.env env' := Option.some.inj (henv.symm.trans henv')
  injection hsame with henv''
  subst henv''
  have ht : t = t' := Option.some.inj ((effTy_complete s q env t hq).symm.trans
    (effTy_complete s q env t' hq0))
  subst ht
  have hn' : NodeHasTy s n' τ := hrebuild (SigExtends.refl s) hq' hrep
  have hnone : ∀ m : Node Op, (∀ p, m ≠ .eff p) → nodeAnswer s (some τ.env) m pre = none := by
    intro m hm
    cases m with
    | eff p => exact absurd rfl (hm p)
    | _ => rfl
  cases hn with
  | eff hp =>
    cases hn' with
    | eff hp' =>
      simp only [nodeAnswer, NodeTy.env, check_complete s _ _ _ hp pre,
        check_complete s _ _ _ hp' pre]
  | _ =>
    rw [hnone n' (fun _ h => by subst h; cases hn'), hnone _ (fun _ h => by cases h)]

/-- The splice of a table in three segments: the entries before the subtree, a segment that the
subtree begins in, and the entries after it. A step of `tableAt_splice`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Table.splice_three {a : List Nat} {X Y Z sub : List Table.Entry}
    (hX : ∀ e ∈ X, Table.under a e.path = false) (hY : ∃ e ∈ Y, Table.under a e.path = true)
    (hZ : ∀ e ∈ Z, Table.under a e.path = false) :
    Table.splice (X ++ (Y ++ Z)) a sub = X ++ (Table.splice Y a sub ++ Z) := by
  rw [Table.splice_append_out_left hX, Table.splice_append_out_right hY hZ]

/-- **Every entry of a splice is an entry of the new subtree's table or of the old table.** A step
of `edit-repaint-set`. Its consumer is `EditSession.feed_repaint` (`Laws/Program/Edit.lean`). -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Table.mem_splice {old sub : List Table.Entry} {a : List Nat} {x : Table.Entry}
    (hx : x ∈ Table.splice old a sub) : x ∈ sub ∨ x ∈ old := by
  unfold Table.splice at hx
  rcases List.mem_append.mp hx with hx | hx
  · rcases List.mem_append.mp hx with hx | hx
    · exact .inr ((List.takeWhile_sublist _).subset hx)
    · exact .inl hx
  · exact .inr ((List.dropWhile_sublist _).subset ((List.dropWhile_sublist _).subset hx))

/-! ## The splice law -/

/-- **The splice at a node**, by induction along the path: the table of the edited node is the
old table with the subtree at the path replaced by the new sub-program's table. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem tableAt_splice {s : Signature Op} :
    ∀ (path : List Nat) {n n' : Node Op} {τ : NodeTy Op} {pre : List Nat} {q q' : Eff Op}
      {env : TyEnv} {t : EffTy},
      NodeHasTy s n τ → n.at_ path = some (.eff q) → n.envAt s τ.env path = some (.env env) →
      HasTy s env q t → HasTy s env q' t → n.replaceAt path (.eff q') = some n' →
      tableAt s (some τ.env) n' pre =
        Table.splice (tableAt s (some τ.env) n pre) (pre ++ path)
          (tableAt s (some (.env env)) (.eff q') (pre ++ path))
  | [], n, n', τ, pre, q, q', env, t, _, hat, henv, _, _, hrep => by
    have hnq : n = .eff q := by simpa only [Node.at_, Option.some.injEq] using hat
    subst hnq
    have hτ : τ.env = .env env := by simpa only [Node.envAt, Option.some.injEq] using henv
    have hn' : n' = .eff q' := by
      have hidx : (Node.eff q').ctorIdx = (Node.eff q).ctorIdx := rfl
      simp only [Node.replaceAt, if_pos hidx, Option.some.injEq] at hrep
      exact hrep.symm
    subst hn'
    rw [hτ, List.append_nil]
    refine (Table.splice_all_under fun e he => ?_).symm
    obtain ⟨b, hb⟩ := tableAt_path he
    rw [hb]
    exact Table.under_append pre b
  | i :: rest, n, n', τ, pre, q, q', env, t, hn, hat, henv, hq, hq', hrep => by
    cases hci : n.child i with
    | none => simp only [Node.at_, hci, Option.bind_none, reduceCtorEq] at hat
    | some c =>
      have hat' : c.at_ rest = some (.eff q) := by
        simpa only [Node.at_, hci, Option.bind_some] using hat
      obtain ⟨τc, hc, hcenv, -⟩ := hn.child_step hci ⟨rest, q, hat'⟩
      have henv' : c.envAt s τc.env rest = some (.env env) := by
        simpa only [Node.envAt, hci, Option.bind_some, hcenv] using henv
      cases hrc : c.replaceAt rest (.eff q') with
      | none =>
        simp only [Node.replaceAt, hci, Option.bind_some, hrc, Option.bind_none,
          reduceCtorEq] at hrep
      | some c' =>
        have hset : n.setChild i c' = some n' := by
          simpa only [Node.replaceAt, hci, Option.bind_some, hrc] using hrep
        have ih := tableAt_splice rest hc hat' henv' hq hq' hrc (pre := pre ++ [i])
        have hkeep := Node.childEnv_replace_kept hn hci hat' henv hq hq' hrc hset
        have hans := nodeAnswer_replace_kept (pre := pre) hn hat henv hq hq' hrep
        have hpath : pre ++ [i] ++ rest = pre ++ i :: rest := by
          rw [List.append_assoc, List.singleton_append]
        rw [hpath] at ih
        -- the edited child's table, and every other child's
        have hCi : childTableAt s (some τ.env) n' pre i =
            Table.splice (childTableAt s (some τ.env) n pre i) (pre ++ i :: rest)
              (tableAt s (some (.env env)) (.eff q') (pre ++ i :: rest)) := by
          unfold childTableAt
          rw [(Node.setChild_spec hset).1, hci]
          simp only [Option.bind_some, hkeep i, hcenv]
          exact ih
        have hCj : ∀ j, j ≠ i → childTableAt s (some τ.env) n' pre j =
            childTableAt s (some τ.env) n pre j := by
          intro j hj
          unfold childTableAt
          rw [Node.child_setChild_ne hset hj]
          simp only [Option.bind_some, hkeep j]
        -- the facts the list laws read
        have hout : ∀ j, j ≠ i → ∀ e ∈ childTableAt s (some τ.env) n pre j,
            Table.under (pre ++ i :: rest) e.path = false := by
          intro j hj e he
          unfold childTableAt at he
          split at he
          · obtain ⟨b, hb⟩ := tableAt_path he
            rw [hb, List.append_assoc, List.singleton_append]
            exact Table.under_sibling_false pre rest b hj
          · cases he
        have hin : ∃ e ∈ childTableAt s (some τ.env) n pre i,
            Table.under (pre ++ i :: rest) e.path = true := by
          unfold childTableAt
          rw [hci]
          obtain ⟨e, he, hpe⟩ := tableAt_mem_path (s := s)
            (ctx := (some τ.env).bind fun x => n.childEnv s x i) (pre := pre ++ [i]) hat'
          have hu := Table.under_append (pre ++ i :: rest) []
          rw [List.append_nil] at hu
          refine ⟨e, he, ?_⟩
          rw [hpe, hpath]
          exact hu
        have hhead : Table.under (pre ++ i :: rest) pre = false :=
          Table.under_prefix_false pre rest i
        rw [tableAt_eq_cons, tableAt_eq_cons, hans]
        have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ 3 ≤ i := by omega
        rcases hcases with rfl | rfl | rfl | h3
        · rw [hCi, hCj 1 (by decide), hCj 2 (by decide)]
          refine (Table.splice_three (X := [_]) ?_ hin ?_).symm
          · intro e he
            rw [List.mem_singleton] at he
            rw [he]
            exact hhead
          · intro e he
            rcases List.mem_append.mp he with h | h
            · exact hout 1 (by decide) e h
            · exact hout 2 (by decide) e h
        · rw [hCi, hCj 0 (by decide), hCj 2 (by decide)]
          refine (Table.splice_three (X := _ :: childTableAt s (some τ.env) n pre 0) ?_ hin
            (hout 2 (by decide))).symm
          intro e he
          rcases List.mem_cons.mp he with h | h
          · rw [h]
            exact hhead
          · exact hout 0 (by decide) e h
        · rw [hCi, hCj 0 (by decide), hCj 1 (by decide)]
          have hX : ∀ e ∈ ⟨pre, some τ.env, nodeAnswer s (some τ.env) n pre⟩ ::
              (childTableAt s (some τ.env) n pre 0 ++ childTableAt s (some τ.env) n pre 1),
              Table.under (pre ++ 2 :: rest) e.path = false := by
            intro e he
            rcases List.mem_cons.mp he with h | h
            · rw [h]
              exact hhead
            · rcases List.mem_append.mp h with h | h
              · exact hout 0 (by decide) e h
              · exact hout 1 (by decide) e h
          have hsplit := Table.splice_three (sub := tableAt s (some (.env env)) (.eff q')
            (pre ++ 2 :: rest)) hX hin (Z := []) (fun _ he => by cases he)
          simp only [List.append_nil, List.cons_append, List.append_assoc] at hsplit
          exact hsplit.symm
        · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h3
          rw [hk, Nat.add_comm, Node.child_add_three] at hci
          cases hci

/-- **An edit that keeps its focus's type splices the address table** (the claim
`edit-splices-table`). In a program that the checker types, take the focus that `focusAt`
answers at an address. Replace the sub-program there by a program of the focus's type in the
focus's environment. The edited program's table is the old table with the subtree at the address
replaced by the new sub-program's table, at the focus's environment and at the subtree's own
addresses. Nothing outside the subtree is checked again. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem table_splice {s : Signature Op} {env0 : TyEnv} {p p' q' : Eff Op} {T : EffTy}
    {path : List Nat} {f : Focus Op} (hp : HasTy s env0 p T)
    (hf : focusAt s env0 p path = some f) (hq' : HasTy s f.env q' f.ty)
    (hrep : (Node.eff p).replaceAt path (.eff q') = some (.eff p')) :
    table s env0 p' = Table.splice (table s env0 p) path
      (tableAt s (some (.env f.env)) (.eff q') path) := by
  obtain ⟨hat, henv, hty⟩ := focusAt_eq_some.mp hf
  rw [table_eq_tableAt, table_eq_tableAt]
  have h := tableAt_splice path (NodeHasTy.eff hp) hat henv (effTy_sound s _ _ _ hty) hq' hrep
    (pre := [])
  rw [List.nil_append] at h
  exact h

end Effect4.Program
