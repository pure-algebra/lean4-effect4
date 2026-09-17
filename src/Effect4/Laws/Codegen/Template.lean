import Effect4.Codegen.Template
import Effect4.Laws.Auto.Inversion

/-!
# Laws.Codegen.Template — the two engine lemmas of the printed boundary (R4.1)

Proved once, over skeletons; a table row inherits both.

* `match_inst`: what `inst` prints, `matchT` reads back as the arguments along the holes.
* `inst_of_match`: what `matchT` reads from a skeleton with distinct holes, `inst` prints back.

The converse is stated with a context on both sides (`pre ++ σ ++ post`, the skeleton's holes
fresh for `keys pre`), so every compound case is re-association. It needs `match_keys`: what a
match collects is keyed by the holes, left to right.

Axiom note: `beq_self_eq_true` in a `simp only` set brings `Classical.choice`; `(i == i) = true`
is `decide_eq_true rfl` here.
-/

set_option autoImplicit false

namespace Effect4.Codegen.Template

open TypeScript

/-! ## Substitutions -/

theorem keys_append (a b : Subst) : keys (a ++ b) = keys a ++ keys b := List.map_append

theorem lookup_cons_self (i : Nat) (a : Arg) (rest : Subst) : lookup ((i, a) :: rest) i = some a := by
  have hb : (i == i) = true := decide_eq_true rfl
  unfold lookup
  rw [List.find?_cons_of_pos (l := rest) (a := (i, a)) (p := fun x => x.1 == i) hb]
  rfl

theorem lookup_append_of_not_mem (pre rest : Subst) (i : Nat) (h : i ∉ keys pre) :
    lookup (pre ++ rest) i = lookup rest i := by
  induction pre with
  | nil => rfl
  | cons p pre ih =>
    have hp : (p.1 == i) = false := by
      apply beq_false_of_ne
      intro hEq
      exact h (by simp only [keys, List.map_cons, hEq, List.mem_cons, true_or])
    have hrest : i ∉ keys pre := fun hm => h (by
      simp only [keys, List.map_cons, List.mem_cons] at hm ⊢
      exact Or.inr hm)
    simp only [lookup, List.cons_append, List.find?_cons, hp] at ih ⊢
    exact ih hrest

/-- What a match of an instance returns: the substitution read along the holes. -/
def along (σ : Subst) (hs : List Nat) : Option Subst :=
  hs.mapM fun i => (lookup σ i).map fun a => (i, a)

theorem along_nil (σ : Subst) : along σ [] = some [] := rfl

theorem along_append (σ : Subst) (xs ys : List Nat) :
    along σ (xs ++ ys) = (do let a ← along σ xs; let b ← along σ ys; some (a ++ b)) := by
  unfold along
  rw [List.mapM_append]
  rfl

theorem along_single (σ : Subst) (i : Nat) (a : Arg) (h : lookup σ i = some a) :
    along σ [i] = some [(i, a)] := by
  simp only [along, List.mapM_cons, List.mapM_nil, h]
  rfl

/-! ## Law 11's engine: reading an instance gives back the arguments -/

theorem matchAnn_instAnn (σ : Subst) : ∀ (ann : Option Nat) (ty : Option TypeRef),
    instAnn σ ann = some ty → matchAnn ann ty = along σ (holesAnn ann)
  | none, ty, h => by
    simp only [instAnn, Option.some.injEq] at h
    subst h
    rfl
  | some i, ty, h => by
    simp only [instAnn] at h
    split at h
    · rename_i t hl
      simp only [Option.some.injEq] at h
      subst h
      simp only [matchAnn, holesAnn, along_single σ i _ hl]
    · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])

/-! The cases below are closed by `aesop` (`Laws/Auto/Inversion.lean`): the definitions of the
calculus are unfolded at the former in hand, the successful instantiation is inverted, and the
induction hypotheses, introduced by hand as its README asks, do the rest. A statement case first
states what the instantiation gives and substitutes it: rewriting the statement VARIABLE under
`matchStmt`'s dependent matcher makes `simp` build a term the kernel rejects. -/

attribute [local simp] inst insts instFields instStmt instStmts matchT matchTs matchFields
  matchStmt matchStmts holes holesTs holesFields holesStmt holesStmts along_append along_nil
  along_single

mutual
  theorem match_inst (n : Nat) (σ : Subst) : ∀ (t : Tpl) (e : Expr),
      inst n σ t = some e → matchT n t e = along σ (holes t)
    | .hole i, e, h => by aesop
    | .strHole i, e, h => by aesop
    | .intHole i, e, h => by aesop
    | .arrHole i, e, h => by aesop
    | .binderRef k, e, h => by aesop
    | .ident s, e, h => by aesop
    | .str s, e, h => by aesop
    | .int v, e, h => by aesop
    | .bool b, e, h => by aesop
    | .call hd args, e, h => by
      have ih1 := match_inst n σ hd
      have ih2 := matchs_inst n σ args
      aesop
    | .callSpread hd i, e, h => by
      have ih1 := match_inst n σ hd
      aesop
    | .arr items, e, h => by
      have ih := matchs_inst n σ items
      aesop
    | .object fields, e, h => by
      have ih := matchFields_inst n σ fields
      aesop
    | .arrow b, e, h => by
      have ih := match_inst n σ b
      aesop
    | .lambda bs b, e, h => by
      have ih := match_inst n σ b
      aesop
    | .cond t a b, e, h => by
      have ih1 := match_inst n σ t
      have ih2 := match_inst n σ a
      have ih3 := match_inst n σ b
      aesop
    | .method target name args, e, h => by
      have ih1 := match_inst n σ target
      have ih2 := matchs_inst n σ args
      aesop
    | .arrowBlock bs body, e, h => by
      have ih := matchStmts_inst n σ body
      aesop
    | .generator body, e, h => by
      have ih := matchStmts_inst n σ body
      aesop
  theorem matchs_inst (n : Nat) (σ : Subst) : ∀ (ts : Tpls) (es : List Expr),
      insts n σ ts = some es → matchTs n ts es = along σ (holesTs ts)
    | .nil, es, h => by aesop
    | .cons hd tl, es, h => by
      have ih1 := match_inst n σ hd
      have ih2 := matchs_inst n σ tl
      aesop
  theorem matchFields_inst (n : Nat) (σ : Subst) : ∀ (fs : Fields) (es : List (String × Expr)),
      instFields n σ fs = some es → matchFields n fs es = along σ (holesFields fs)
    | .nil, es, h => by aesop
    | .cons key v tl, es, h => by
      have ih1 := match_inst n σ v
      have ih2 := matchFields_inst n σ tl
      aesop
  theorem matchStmt_inst (n : Nat) (σ : Subst) : ∀ (t : StmtTpl) (s : Stmt),
      instStmt n σ t = some s → matchStmt n t s = along σ (holesStmt t)
    | .letInit k v ann, s, h => by
      simp only [instStmt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨v', hv, ann', hann, rfl⟩ := h
      simp only [matchStmt, holesStmt, along_append, ↓reduceIte, match_inst n σ v v' hv,
        matchAnn_instAnn σ ann ann' hann]
    | .assign k v, s, h => by
      have ih := match_inst n σ v
      obtain ⟨v', hv, rfl⟩ : ∃ v', inst n σ v = some v' ∧ Stmt.assign (varName (n + k)) v' = s := by
        aesop
      aesop
    | .ret v, s, h => by
      have ih := match_inst n σ v
      obtain ⟨v', hv, rfl⟩ : ∃ v', inst n σ v = some v' ∧ Stmt.ret v' = s := by aesop
      aesop
    | .exprStmt v, s, h => by
      have ih := match_inst n σ v
      obtain ⟨v', hv, rfl⟩ : ∃ v', inst n σ v = some v' ∧ Stmt.exprStmt v' = s := by aesop
      aesop
    | .constYield k v, s, h => by
      have ih := match_inst n σ v
      obtain ⟨v', hv, rfl⟩ :
          ∃ v', inst n σ v = some v' ∧ Stmt.constYield (varName (n + k)) v' none = s := by aesop
      aesop
    | .yieldDiscard v, s, h => by
      have ih := match_inst n σ v
      obtain ⟨v', hv, rfl⟩ : ∃ v', inst n σ v = some v' ∧ Stmt.yieldDiscard v' = s := by aesop
      aesop
    | .ifElse t a b, s, h => by
      have ih1 := match_inst n σ t
      have ih2 := matchStmts_inst n σ a
      have ih3 := matchStmts_inst n σ b
      obtain ⟨t', a', b', ht, ha, hb, rfl⟩ : ∃ t' a' b', inst n σ t = some t' ∧
          instStmts n σ a = some a' ∧ instStmts n σ b = some b' ∧ Stmt.ifElse t' a' b' = s := by
        aesop
      aesop
    | .whileTrue body, s, h => by
      have ih := matchStmts_inst n σ body
      obtain ⟨b', hb, rfl⟩ : ∃ b', instStmts n σ body = some b' ∧ Stmt.whileTrue none b' = s := by
        aesop
      aesop
    | .breakTo, s, h => by
      obtain rfl : Stmt.breakTo none = s := by aesop
      aesop
  theorem matchStmts_inst (n : Nat) (σ : Subst) : ∀ (ts : StmtTpls) (ss : List Stmt),
      instStmts n σ ts = some ss → matchStmts n ts ss = along σ (holesStmts ts)
    | .hole i, ss, h => by aesop
    | .nil, ss, h => by aesop
    | .cons hd tl, ss, h => by
      have ih1 := matchStmt_inst n σ hd
      have ih2 := matchStmts_inst n σ tl
      aesop
end

/-! ## What a match collects is keyed by the holes, left to right -/

theorem matchAnn_keys : ∀ (ann : Option Nat) (ty : Option TypeRef) (σ : Subst),
    matchAnn ann ty = some σ → keys σ = holesAnn ann
  | none, none, σ, h => by
    simp only [matchAnn, Option.some.injEq] at h
    subst h
    rfl
  | some i, some t, σ, h => by
    simp only [matchAnn, Option.some.injEq] at h
    subst h
    rfl

/-! Here an induction hypothesis names a tree its conclusion does not mention, so it cannot act
as a rewrite: it is given to `aesop` as a forward rule. -/

attribute [local simp] keys_append keys matchAnn

mutual
  theorem match_keys (n : Nat) : ∀ (t : Tpl) (e : Expr) (σ : Subst),
      matchT n t e = some σ → keys σ = holes t
    | .hole i, e, σ, h => by
      aesop
    | .strHole i, .str s, σ, h => by
      aesop
    | .intHole i, .int v, σ, h => by
      aesop
    | .arrHole i, .arr es, σ, h => by
      aesop
    | .binderRef k, .ident s, σ, h => by
      aesop
    | .ident s, .ident s', σ, h => by
      aesop
    | .str s, .str s', σ, h => by
      aesop
    | .int v, .int v', σ, h => by
      aesop
    | .bool b, .bool b', σ, h => by
      aesop
    | .call hd args, .call hd' args', σ, h => by
      have ih1 := match_keys n hd
      have ih2 := matchs_keys n args
      aesop (add safe forward [ih1, ih2])
    | .callSpread hd i, .call hd' es, σ, h => by
      have ih1 := match_keys n hd
      aesop (add safe forward [ih1])
    | .arr items, .arr items', σ, h => by
      have ih1 := matchs_keys n items
      aesop (add safe forward [ih1])
    | .object fields, .object fields', σ, h => by
      have ih1 := matchFields_keys n fields
      aesop (add safe forward [ih1])
    | .arrow b, .arrow none b', σ, h => by
      have ih1 := match_keys n b
      aesop (add safe forward [ih1])
    | .lambda bs b, .lambda ps b' none, σ, h => by
      have ih1 := match_keys n b
      aesop (add safe forward [ih1])
    | .cond t a b, .cond t' a' b', σ, h => by
      have ih1 := match_keys n t
      have ih2 := match_keys n a
      have ih3 := match_keys n b
      aesop (add safe forward [ih1, ih2, ih3])
    | .method target name args, .method target' name' args', σ, h => by
      have ih1 := match_keys n target
      have ih2 := matchs_keys n args
      aesop (add safe forward [ih1, ih2])
    | .generator body, .generator body', σ, h => by
      have ih1 := matchStmts_keys n body
      aesop (add safe forward [ih1])
    | .arrowBlock bs body, .arrowBlock ps body' none, σ, h => by
      have ih1 := matchStmts_keys n body
      aesop (add safe forward [ih1])
  theorem matchs_keys (n : Nat) : ∀ (ts : Tpls) (es : List Expr) (σ : Subst),
      matchTs n ts es = some σ → keys σ = holesTs ts
    | .nil, [], σ, h => by
      aesop
    | .cons hd tl, e :: es, σ, h => by
      have ih1 := match_keys n hd
      have ih2 := matchs_keys n tl
      aesop (add safe forward [ih1, ih2])
  theorem matchFields_keys (n : Nat) : ∀ (fs : Fields) (es : List (String × Expr)) (σ : Subst),
      matchFields n fs es = some σ → keys σ = holesFields fs
    | .nil, [], σ, h => by
      aesop
    | .cons key v tl, (key', e) :: es, σ, h => by
      have ih1 := match_keys n v
      have ih2 := matchFields_keys n tl
      aesop (add safe forward [ih1, ih2])
  theorem matchStmt_keys (n : Nat) : ∀ (t : StmtTpl) (s : Stmt) (σ : Subst),
      matchStmt n t s = some σ → keys σ = holesStmt t
    | .letInit k v ann, .letInit name e ty, σ, h => by
      have ih1 := match_keys n v
      have ih2 := matchAnn_keys ann
      aesop (add safe forward [ih1, ih2])
    | .assign k v, .assign name e, σ, h => by
      have ih1 := match_keys n v
      aesop (add safe forward [ih1])
    | .ret v, .ret e, σ, h => by
      have ih1 := match_keys n v
      aesop (add safe forward [ih1])
    | .exprStmt v, .exprStmt e, σ, h => by
      have ih1 := match_keys n v
      aesop (add safe forward [ih1])
    | .constYield k v, .constYield name e none, σ, h => by
      have ih1 := match_keys n v
      aesop (add safe forward [ih1])
    | .yieldDiscard v, .yieldDiscard e, σ, h => by
      have ih1 := match_keys n v
      aesop (add safe forward [ih1])
    | .ifElse t a b, .ifElse t' a' b', σ, h => by
      have ih1 := match_keys n t
      have ih2 := matchStmts_keys n a
      have ih3 := matchStmts_keys n b
      aesop (add safe forward [ih1, ih2, ih3])
    | .whileTrue body, .whileTrue none body', σ, h => by
      have ih1 := matchStmts_keys n body
      aesop (add safe forward [ih1])
    | .breakTo, .breakTo none, σ, h => by
      aesop
  theorem matchStmts_keys (n : Nat) : ∀ (ts : StmtTpls) (ss : List Stmt) (σ : Subst),
      matchStmts n ts ss = some σ → keys σ = holesStmts ts
    | .hole i, ss, σ, h => by
      aesop
    | .nil, [], σ, h => by
      aesop
    | .cons hd tl, s :: ss, σ, h => by
      have ih1 := matchStmt_keys n hd
      have ih2 := matchStmts_keys n tl
      aesop (add safe forward [ih1, ih2])
end

/-! ## Law 12's engine: a match of a skeleton with distinct holes instantiates back -/

/-- The holes `hs` avoid the keys of `pre`. -/
def Fresh (pre : Subst) (hs : List Nat) : Prop := ∀ i ∈ hs, i ∉ keys pre

theorem Fresh.left {pre : Subst} {xs ys : List Nat} (h : Fresh pre (xs ++ ys)) : Fresh pre xs :=
  fun i hi => h i (List.mem_append_left ys hi)

theorem Fresh.right {pre : Subst} {xs ys : List Nat} (h : Fresh pre (xs ++ ys)) : Fresh pre ys :=
  fun i hi => h i (List.mem_append_right xs hi)

/-- Past a block whose keys are `xs`, the later holes `ys` are still fresh when `xs ++ ys` has
no duplicate. -/
theorem Fresh.past {pre a : Subst} {xs ys : List Nat} (h : Fresh pre (xs ++ ys))
    (hk : keys a = xs) (nd : (xs ++ ys).Nodup) : Fresh (pre ++ a) ys := by
  intro i hi hmem
  simp only [keys_append, List.mem_append] at hmem
  cases hmem with
  | inl hp => exact h i (List.mem_append_right xs hi) hp
  | inr ha =>
    rw [hk] at ha
    exact (List.nodup_append.mp nd).2.2 i ha i hi rfl

/-- The lookup of a hole that a match just collected, in any context fresh for it. -/
theorem lookup_mid (pre post : Subst) (i : Nat) (a : Arg) (h : i ∉ keys pre) :
    lookup (pre ++ [(i, a)] ++ post) i = some a := by
  rw [List.append_assoc, lookup_append_of_not_mem pre _ i h]
  exact lookup_cons_self i a post

theorem instAnn_match (pre post : Subst) : ∀ (ann : Option Nat) (ty : Option TypeRef) (σ : Subst),
    matchAnn ann ty = some σ → Fresh pre (holesAnn ann) → instAnn (pre ++ σ ++ post) ann = some ty
  | none, none, σ, _, _ => rfl
  | some i, some t, σ, h, fr => by
    simp only [matchAnn, Option.some.injEq] at h
    subst h
    simp only [instAnn, lookup_mid pre post i _ (fr i (List.mem_cons_self ..))]

mutual
  theorem inst_match (n : Nat) : ∀ (t : Tpl) (e : Expr) (σ pre post : Subst),
      matchT n t e = some σ → (holes t).Nodup → Fresh pre (holes t) →
      inst n (pre ++ σ ++ post) t = some e
    | .hole i, e, σ, pre, post, h, _, fr => by
      simp only [matchT, Option.some.injEq] at h
      subst h
      simp only [inst, lookup_mid pre post i _ (fr i (List.mem_cons_self ..))]
    | .strHole i, .str s, σ, pre, post, h, _, fr => by
      simp only [matchT, Option.some.injEq] at h
      subst h
      simp only [inst, lookup_mid pre post i _ (fr i (List.mem_cons_self ..))]
    | .intHole i, .int v, σ, pre, post, h, _, fr => by
      simp only [matchT, Option.some.injEq] at h
      subst h
      simp only [inst, lookup_mid pre post i _ (fr i (List.mem_cons_self ..))]
    | .arrHole i, .arr es, σ, pre, post, h, _, fr => by
      simp only [matchT, Option.some.injEq] at h
      subst h
      simp only [inst, lookup_mid pre post i _ (fr i (List.mem_cons_self ..))]
    | .binderRef k, .ident s, σ, pre, post, h, _, _ => by
      simp only [matchT] at h
      split at h
      · rename_i hs
        simp only [inst, hs]
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
    | .ident s, .ident s', σ, pre, post, h, _, _ => by
      simp only [matchT] at h
      split at h
      · rename_i hs
        simp only [inst, hs]
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
    | .str s, .str s', σ, pre, post, h, _, _ => by
      simp only [matchT] at h
      split at h
      · rename_i hs
        simp only [inst, hs]
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
    | .int v, .int v', σ, pre, post, h, _, _ => by
      simp only [matchT] at h
      split at h
      · rename_i hs
        simp only [inst, hs]
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
    | .bool b, .bool b', σ, pre, post, h, _, _ => by
      simp only [matchT] at h
      split at h
      · rename_i hs
        simp only [inst, hs]
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
    | .call hd args, .call hd' args', σ, pre, post, h, nd, fr => by
      simp only [matchT, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨a, ha, b, hb, rfl⟩ := h
      simp only [holes] at nd fr
      have h1 := inst_match n hd hd' a pre (b ++ post) ha (List.nodup_append.mp nd).1 fr.left
      have h2 := insts_match n args args' b (pre ++ a) post hb (List.nodup_append.mp nd).2.1
        (fr.past (match_keys n hd hd' a ha) nd)
      simp only [List.append_assoc] at h1 h2 ⊢
      simp only [inst, h1, h2, Option.bind_eq_bind, Option.bind_some]
    | .callSpread hd i, .call hd' es, σ, pre, post, h, nd, fr => by
      simp only [matchT, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨a, ha, rfl⟩ := h
      simp only [holes] at nd fr
      have h1 := inst_match n hd hd' a pre ([(i, Arg.exprs es)] ++ post) ha
        (List.nodup_append.mp nd).1 fr.left
      have hfr : Fresh (pre ++ a) [i] := fr.past (match_keys n hd hd' a ha) nd
      have h2 := lookup_mid (pre ++ a) post i (Arg.exprs es) (hfr i (List.mem_cons_self ..))
      simp only [List.append_assoc] at h1 h2 ⊢
      simp only [inst, h1, h2, Option.bind_eq_bind, Option.bind_some]
    | .arr items, .arr items', σ, pre, post, h, nd, fr => by
      simp only [matchT] at h
      simp only [holes] at nd fr
      simp only [inst, insts_match n items items' σ pre post h nd fr, Option.bind_eq_bind,
        Option.bind_some]
    | .object fields, .object fields', σ, pre, post, h, nd, fr => by
      simp only [matchT] at h
      simp only [holes] at nd fr
      simp only [inst, instFields_match n fields fields' σ pre post h nd fr, Option.bind_eq_bind,
        Option.bind_some]
    | .arrow b, .arrow none b', σ, pre, post, h, nd, fr => by
      simp only [matchT] at h
      simp only [holes] at nd fr
      simp only [inst, inst_match n b b' σ pre post h nd fr, Option.bind_eq_bind, Option.bind_some]
    | .lambda bs b, .lambda ps b' none, σ, pre, post, h, nd, fr => by
      simp only [matchT] at h
      simp only [holes] at nd fr
      split at h
      · rename_i hps
        simp only [inst, inst_match n b b' σ pre post h nd fr, Option.bind_eq_bind,
          Option.bind_some, hps]
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
    | .cond t a b, .cond t' a' b', σ, pre, post, h, nd, fr => by
      simp only [matchT, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨x, hx, y, hy, z, hz, rfl⟩ := h
      simp only [holes] at nd fr
      have ndab := (List.nodup_append.mp nd).2.1
      have h1 := inst_match n t t' x pre (y ++ z ++ post) hx (List.nodup_append.mp nd).1 fr.left
      have frab : Fresh (pre ++ x) (holes a ++ holes b) := fr.past (match_keys n t t' x hx) nd
      have h2 := inst_match n a a' y (pre ++ x) (z ++ post) hy (List.nodup_append.mp ndab).1
        frab.left
      have h3 := inst_match n b b' z (pre ++ x ++ y) post hz (List.nodup_append.mp ndab).2.1
        (frab.past (match_keys n a a' y hy) ndab)
      simp only [List.append_assoc] at h1 h2 h3 ⊢
      simp only [inst, h1, h2, h3, Option.bind_eq_bind, Option.bind_some]
    | .method target name args, .method target' name' args', σ, pre, post, h, nd, fr => by
      simp only [matchT] at h
      split at h
      · rename_i hname
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨a, ha, b, hb, rfl⟩ := h
        simp only [holes] at nd fr
        have h1 := inst_match n target target' a pre (b ++ post) ha (List.nodup_append.mp nd).1
          fr.left
        have h2 := insts_match n args args' b (pre ++ a) post hb (List.nodup_append.mp nd).2.1
          (fr.past (match_keys n target target' a ha) nd)
        simp only [List.append_assoc] at h1 h2 ⊢
        simp only [inst, h1, h2, Option.bind_eq_bind, Option.bind_some, hname]
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
    | .generator body, .generator body', σ, pre, post, h, nd, fr => by
      simp only [matchT] at h
      simp only [holes] at nd fr
      simp only [inst, instStmts_match n body body' σ pre post h nd fr, Option.bind_eq_bind,
        Option.bind_some]
    | .arrowBlock bs body, .arrowBlock ps body' none, σ, pre, post, h, nd, fr => by
      simp only [matchT] at h
      simp only [holes] at nd fr
      split at h
      · rename_i hps
        simp only [inst, instStmts_match n body body' σ pre post h nd fr, Option.bind_eq_bind,
          Option.bind_some, hps]
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  theorem insts_match (n : Nat) : ∀ (ts : Tpls) (es : List Expr) (σ pre post : Subst),
      matchTs n ts es = some σ → (holesTs ts).Nodup → Fresh pre (holesTs ts) →
      insts n (pre ++ σ ++ post) ts = some es
    | .nil, [], σ, pre, post, _, _, _ => by
      simp only [insts]
    | .cons hd tl, e :: es, σ, pre, post, h, nd, fr => by
      simp only [matchTs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨a, ha, b, hb, rfl⟩ := h
      simp only [holesTs] at nd fr
      have h1 := inst_match n hd e a pre (b ++ post) ha (List.nodup_append.mp nd).1 fr.left
      have h2 := insts_match n tl es b (pre ++ a) post hb (List.nodup_append.mp nd).2.1
        (fr.past (match_keys n hd e a ha) nd)
      simp only [List.append_assoc] at h1 h2 ⊢
      simp only [insts, h1, h2, Option.bind_eq_bind, Option.bind_some]
  theorem instFields_match (n : Nat) :
      ∀ (fs : Fields) (es : List (String × Expr)) (σ pre post : Subst),
      matchFields n fs es = some σ → (holesFields fs).Nodup → Fresh pre (holesFields fs) →
      instFields n (pre ++ σ ++ post) fs = some es
    | .nil, [], σ, pre, post, _, _, _ => by
      simp only [instFields]
    | .cons key v tl, (key', e) :: es, σ, pre, post, h, nd, fr => by
      simp only [matchFields] at h
      split at h
      · rename_i hkey
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨a, ha, b, hb, rfl⟩ := h
        simp only [holesFields] at nd fr
        have h1 := inst_match n v e a pre (b ++ post) ha (List.nodup_append.mp nd).1 fr.left
        have h2 := instFields_match n tl es b (pre ++ a) post hb (List.nodup_append.mp nd).2.1
          (fr.past (match_keys n v e a ha) nd)
        simp only [List.append_assoc] at h1 h2 ⊢
        simp only [instFields, h1, h2, Option.bind_eq_bind, Option.bind_some, hkey]
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  theorem instStmt_match (n : Nat) : ∀ (t : StmtTpl) (s : Stmt) (σ pre post : Subst),
      matchStmt n t s = some σ → (holesStmt t).Nodup → Fresh pre (holesStmt t) →
      instStmt n (pre ++ σ ++ post) t = some s
    | .letInit k v ann, .letInit name e ty, σ, pre, post, h, nd, fr => by
      simp only [matchStmt] at h
      split at h
      · rename_i hname
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨a, ha, b, hb, rfl⟩ := h
        simp only [holesStmt] at nd fr
        have h1 := inst_match n v e a pre (b ++ post) ha (List.nodup_append.mp nd).1 fr.left
        have h2 := instAnn_match (pre ++ a) post ann ty b hb
          (fr.past (match_keys n v e a ha) nd)
        simp only [List.append_assoc] at h1 h2 ⊢
        simp only [instStmt, h1, h2, Option.bind_eq_bind, Option.bind_some, hname]
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
    | .assign k v, .assign name e, σ, pre, post, h, nd, fr => by
      simp only [matchStmt] at h
      simp only [holesStmt] at nd fr
      split at h
      · rename_i hname
        simp only [instStmt, inst_match n v e σ pre post h nd fr, Option.bind_eq_bind,
          Option.bind_some, hname]
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
    | .ret v, .ret e, σ, pre, post, h, nd, fr => by
      simp only [matchStmt] at h
      simp only [holesStmt] at nd fr
      simp only [instStmt, inst_match n v e σ pre post h nd fr, Option.bind_eq_bind,
        Option.bind_some]
    | .exprStmt v, .exprStmt e, σ, pre, post, h, nd, fr => by
      simp only [matchStmt] at h
      simp only [holesStmt] at nd fr
      simp only [instStmt, inst_match n v e σ pre post h nd fr, Option.bind_eq_bind,
        Option.bind_some]
    | .constYield k v, .constYield name e none, σ, pre, post, h, nd, fr => by
      simp only [matchStmt] at h
      simp only [holesStmt] at nd fr
      split at h
      · rename_i hname
        simp only [instStmt, inst_match n v e σ pre post h nd fr, Option.bind_eq_bind,
          Option.bind_some, hname]
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
    | .yieldDiscard v, .yieldDiscard e, σ, pre, post, h, nd, fr => by
      simp only [matchStmt] at h
      simp only [holesStmt] at nd fr
      simp only [instStmt, inst_match n v e σ pre post h nd fr, Option.bind_eq_bind,
        Option.bind_some]
    | .ifElse t a b, .ifElse t' a' b', σ, pre, post, h, nd, fr => by
      simp only [matchStmt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨x, hx, y, hy, z, hz, rfl⟩ := h
      simp only [holesStmt] at nd fr
      have ndab := (List.nodup_append.mp nd).2.1
      have h1 := inst_match n t t' x pre (y ++ z ++ post) hx (List.nodup_append.mp nd).1 fr.left
      have frab : Fresh (pre ++ x) (holesStmts a ++ holesStmts b) :=
        fr.past (match_keys n t t' x hx) nd
      have h2 := instStmts_match n a a' y (pre ++ x) (z ++ post) hy
        (List.nodup_append.mp ndab).1 frab.left
      have h3 := instStmts_match n b b' z (pre ++ x ++ y) post hz
        (List.nodup_append.mp ndab).2.1 (frab.past (matchStmts_keys n a a' y hy) ndab)
      simp only [List.append_assoc] at h1 h2 h3 ⊢
      simp only [instStmt, h1, h2, h3, Option.bind_eq_bind, Option.bind_some]
    | .whileTrue body, .whileTrue none body', σ, pre, post, h, nd, fr => by
      simp only [matchStmt] at h
      simp only [holesStmt] at nd fr
      simp only [instStmt, instStmts_match n body body' σ pre post h nd fr, Option.bind_eq_bind,
        Option.bind_some]
    | .breakTo, .breakTo none, σ, pre, post, _, _, _ => by
      simp only [instStmt]
  theorem instStmts_match (n : Nat) : ∀ (ts : StmtTpls) (ss : List Stmt) (σ pre post : Subst),
      matchStmts n ts ss = some σ → (holesStmts ts).Nodup → Fresh pre (holesStmts ts) →
      instStmts n (pre ++ σ ++ post) ts = some ss
    | .hole i, ss, σ, pre, post, h, _, fr => by
      simp only [matchStmts, Option.some.injEq] at h
      subst h
      simp only [instStmts, lookup_mid pre post i _ (fr i (List.mem_cons_self ..))]
    | .nil, [], σ, pre, post, _, _, _ => by
      simp only [instStmts]
    | .cons hd tl, s :: ss, σ, pre, post, h, nd, fr => by
      simp only [matchStmts, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨a, ha, b, hb, rfl⟩ := h
      simp only [holesStmts] at nd fr
      have h1 := instStmt_match n hd s a pre (b ++ post) ha (List.nodup_append.mp nd).1 fr.left
      have h2 := instStmts_match n tl ss b (pre ++ a) post hb (List.nodup_append.mp nd).2.1
        (fr.past (matchStmt_keys n hd s a ha) nd)
      simp only [List.append_assoc] at h1 h2 ⊢
      simp only [instStmts, h1, h2, Option.bind_eq_bind, Option.bind_some]
end

/-- The converse as the table uses it: no context. -/
theorem inst_of_match (n : Nat) (t : Tpl) (e : Expr) (σ : Subst)
    (h : matchT n t e = some σ) (nd : Linear t) : inst n σ t = some e := by
  have hfresh : Fresh [] (holes t) := fun _ _ hm => by
    simp only [keys, List.map_nil, List.not_mem_nil] at hm
  have := inst_match n t e σ [] [] h nd hfresh
  simpa only [List.nil_append, List.append_nil] using this

/-- The same of a statement skeleton, as a statement row uses it. -/
theorem instStmt_of_match (n : Nat) (t : StmtTpl) (s : Stmt) (σ : Subst)
    (h : matchStmt n t s = some σ) (nd : (holesStmt t).Nodup) : instStmt n σ t = some s := by
  have hfresh : Fresh [] (holesStmt t) := fun _ _ hm => by
    simp only [keys, List.map_nil, List.not_mem_nil] at hm
  have := instStmt_match n t s σ [] [] h nd hfresh
  simpa only [List.nil_append, List.append_nil] using this

end Effect4.Codegen.Template
