import Effect4.Codegen.Template

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

mutual
  theorem match_inst (n : Nat) (σ : Subst) : ∀ (t : Tpl) (e : Expr),
      inst n σ t = some e → matchT n t e = along σ (holes t)
    | .hole i, e, h => by
      simp only [inst] at h
      split at h
      · rename_i e' hl
        simp only [Option.some.injEq] at h
        subst h
        simp only [matchT, holes, along_single σ i _ hl]
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
    | .strHole i, e, h => by
      simp only [inst] at h
      split at h
      · rename_i s hl
        simp only [Option.some.injEq] at h
        subst h
        simp only [matchT, holes, along_single σ i _ hl]
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
    | .intHole i, e, h => by
      simp only [inst] at h
      split at h
      · rename_i v hl
        simp only [Option.some.injEq] at h
        subst h
        simp only [matchT, holes, along_single σ i _ hl]
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
    | .arrHole i, e, h => by
      simp only [inst] at h
      split at h
      · rename_i es hl
        simp only [Option.some.injEq] at h
        subst h
        simp only [matchT, holes, along_single σ i _ hl]
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
    | .binderRef k, e, h => by
      simp only [inst, Option.some.injEq] at h
      subst h
      simp only [matchT, holes, along_nil, ↓reduceIte]
    | .ident s, e, h => by
      simp only [inst, Option.some.injEq] at h
      subst h
      simp only [matchT, holes, along_nil, ↓reduceIte]
    | .str s, e, h => by
      simp only [inst, Option.some.injEq] at h
      subst h
      simp only [matchT, holes, along_nil, ↓reduceIte]
    | .int v, e, h => by
      simp only [inst, Option.some.injEq] at h
      subst h
      simp only [matchT, holes, along_nil, ↓reduceIte]
    | .bool b, e, h => by
      simp only [inst, Option.some.injEq] at h
      subst h
      simp only [matchT, holes, along_nil, ↓reduceIte]
    | .call hd args, e, h => by
      simp only [inst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨h', hh, a', ha, rfl⟩ := h
      simp only [matchT, holes, along_append, match_inst n σ hd h' hh, matchs_inst n σ args a' ha]
    | .callSpread hd i, e, h => by
      simp only [inst, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨h', hh, hm⟩ := h
      split at hm
      · rename_i es hl
        simp only [Option.some.injEq] at hm
        subst hm
        simp only [matchT, holes, along_append, match_inst n σ hd h' hh, along_single σ i _ hl]
        cases along σ (holes hd) <;> rfl
      · exact absurd hm (by simp only [reduceCtorEq, not_false_eq_true])
    | .arr items, e, h => by
      simp only [inst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨a', ha, rfl⟩ := h
      simp only [matchT, holes, matchs_inst n σ items a' ha]
    | .object fields, e, h => by
      simp only [inst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨a', ha, rfl⟩ := h
      simp only [matchT, holes, matchFields_inst n σ fields a' ha]
    | .arrow b, e, h => by
      simp only [inst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨b', hb, rfl⟩ := h
      simp only [matchT, holes, match_inst n σ b b' hb]
    | .lambda bs b, e, h => by
      simp only [inst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨b', hb, rfl⟩ := h
      simp only [matchT, holes, ↓reduceIte, match_inst n σ b b' hb]
    | .cond t a b, e, h => by
      simp only [inst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨t', ht, a', ha, b', hb, rfl⟩ := h
      simp only [matchT, holes, along_append, match_inst n σ t t' ht, match_inst n σ a a' ha,
        match_inst n σ b b' hb]
      cases along σ (holes t) <;> cases along σ (holes a) <;> cases along σ (holes b) <;> rfl
    | .method target name args, e, h => by
      simp only [inst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨t', ht, a', ha, rfl⟩ := h
      simp only [matchT, holes, along_append, ↓reduceIte, match_inst n σ target t' ht,
        matchs_inst n σ args a' ha]
    | .arrowBlock bs body, e, h => by
      simp only [inst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨b', hb, rfl⟩ := h
      simp only [matchT, holes, ↓reduceIte, matchStmts_inst n σ body b' hb]
    | .generator body, e, h => by
      simp only [inst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨b', hb, rfl⟩ := h
      simp only [matchT, holes, matchStmts_inst n σ body b' hb]
  theorem matchs_inst (n : Nat) (σ : Subst) : ∀ (ts : Tpls) (es : List Expr),
      insts n σ ts = some es → matchTs n ts es = along σ (holesTs ts)
    | .nil, es, h => by
      simp only [insts, Option.some.injEq] at h
      subst h
      simp only [matchTs, holesTs, along_nil]
    | .cons hd tl, es, h => by
      simp only [insts, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨h', hh, t', ht, rfl⟩ := h
      simp only [matchTs, holesTs, along_append, match_inst n σ hd h' hh, matchs_inst n σ tl t' ht]
  theorem matchFields_inst (n : Nat) (σ : Subst) : ∀ (fs : Fields) (es : List (String × Expr)),
      instFields n σ fs = some es → matchFields n fs es = along σ (holesFields fs)
    | .nil, es, h => by
      simp only [instFields, Option.some.injEq] at h
      subst h
      simp only [matchFields, holesFields, along_nil]
    | .cons key v tl, es, h => by
      simp only [instFields, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨v', hv, t', ht, rfl⟩ := h
      simp only [matchFields, holesFields, along_append, ↓reduceIte, match_inst n σ v v' hv,
        matchFields_inst n σ tl t' ht]
  theorem matchStmt_inst (n : Nat) (σ : Subst) : ∀ (t : StmtTpl) (s : Stmt),
      instStmt n σ t = some s → matchStmt n t s = along σ (holesStmt t)
    | .letInit k v ann, s, h => by
      simp only [instStmt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨v', hv, ann', hann, rfl⟩ := h
      simp only [matchStmt, holesStmt, along_append, ↓reduceIte, match_inst n σ v v' hv,
        matchAnn_instAnn σ ann ann' hann]
    | .assign k v, s, h => by
      simp only [instStmt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨v', hv, rfl⟩ := h
      simp only [matchStmt, holesStmt, ↓reduceIte, match_inst n σ v v' hv]
    | .ret v, s, h => by
      simp only [instStmt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨v', hv, rfl⟩ := h
      simp only [matchStmt, holesStmt, match_inst n σ v v' hv]
    | .exprStmt v, s, h => by
      simp only [instStmt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨v', hv, rfl⟩ := h
      simp only [matchStmt, holesStmt, match_inst n σ v v' hv]
    | .constYield k v, s, h => by
      simp only [instStmt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨v', hv, rfl⟩ := h
      simp only [matchStmt, holesStmt, ↓reduceIte, match_inst n σ v v' hv]
    | .yieldDiscard v, s, h => by
      simp only [instStmt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨v', hv, rfl⟩ := h
      simp only [matchStmt, holesStmt, match_inst n σ v v' hv]
    | .ifElse t a b, s, h => by
      simp only [instStmt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨t', ht, a', ha, b', hb, rfl⟩ := h
      simp only [matchStmt, holesStmt, along_append, match_inst n σ t t' ht,
        matchStmts_inst n σ a a' ha, matchStmts_inst n σ b b' hb]
      cases along σ (holes t) <;> cases along σ (holesStmts a) <;> cases along σ (holesStmts b) <;> rfl
    | .whileTrue body, s, h => by
      simp only [instStmt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨b', hb, rfl⟩ := h
      simp only [matchStmt, holesStmt, matchStmts_inst n σ body b' hb]
    | .breakTo, s, h => by
      simp only [instStmt, Option.some.injEq] at h
      subst h
      simp only [matchStmt, holesStmt, along_nil]
  theorem matchStmts_inst (n : Nat) (σ : Subst) : ∀ (ts : StmtTpls) (ss : List Stmt),
      instStmts n σ ts = some ss → matchStmts n ts ss = along σ (holesStmts ts)
    | .hole i, ss, h => by
      simp only [instStmts] at h
      split at h
      · rename_i ss' hl
        simp only [Option.some.injEq] at h
        subst h
        simp only [matchStmts, holesStmts, along_single σ i _ hl]
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
    | .nil, ss, h => by
      simp only [instStmts, Option.some.injEq] at h
      subst h
      simp only [matchStmts, holesStmts, along_nil]
    | .cons hd tl, ss, h => by
      simp only [instStmts, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨h', hh, t', ht, rfl⟩ := h
      simp only [matchStmts, holesStmts, along_append, matchStmt_inst n σ hd h' hh,
        matchStmts_inst n σ tl t' ht]
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

mutual
  theorem match_keys (n : Nat) : ∀ (t : Tpl) (e : Expr) (σ : Subst),
      matchT n t e = some σ → keys σ = holes t
    | .hole i, e, σ, h => by
      simp only [matchT, Option.some.injEq] at h
      subst h
      rfl
    | .strHole i, .str s, σ, h => by
      simp only [matchT, Option.some.injEq] at h
      subst h
      rfl
    | .intHole i, .int v, σ, h => by
      simp only [matchT, Option.some.injEq] at h
      subst h
      rfl
    | .arrHole i, .arr es, σ, h => by
      simp only [matchT, Option.some.injEq] at h
      subst h
      rfl
    | .binderRef k, .ident s, σ, h => by
      simp only [matchT] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        rfl
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
    | .ident s, .ident s', σ, h => by
      simp only [matchT] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        rfl
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
    | .str s, .str s', σ, h => by
      simp only [matchT] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        rfl
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
    | .int v, .int v', σ, h => by
      simp only [matchT] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        rfl
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
    | .bool b, .bool b', σ, h => by
      simp only [matchT] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        rfl
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
    | .call hd args, .call hd' args', σ, h => by
      simp only [matchT, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨a, ha, b, hb, rfl⟩ := h
      simp only [keys_append, holes, match_keys n hd hd' a ha, matchs_keys n args args' b hb]
    | .callSpread hd i, .call hd' es, σ, h => by
      simp only [matchT, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨a, ha, rfl⟩ := h
      simp only [keys_append, holes, match_keys n hd hd' a ha]
      rfl
    | .arr items, .arr items', σ, h => by
      simp only [matchT] at h
      simp only [holes, matchs_keys n items items' σ h]
    | .object fields, .object fields', σ, h => by
      simp only [matchT] at h
      simp only [holes, matchFields_keys n fields fields' σ h]
    | .arrow b, .arrow none b', σ, h => by
      simp only [matchT] at h
      simp only [holes, match_keys n b b' σ h]
    | .lambda bs b, .lambda ps b' none, σ, h => by
      simp only [matchT] at h
      split at h
      · simp only [holes, match_keys n b b' σ h]
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
    | .cond t a b, .cond t' a' b', σ, h => by
      simp only [matchT, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨x, hx, y, hy, z, hz, rfl⟩ := h
      simp only [keys_append, holes, match_keys n t t' x hx, match_keys n a a' y hy,
        match_keys n b b' z hz]
    | .method target name args, .method target' name' args', σ, h => by
      simp only [matchT] at h
      split at h
      · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨a, ha, b, hb, rfl⟩ := h
        simp only [keys_append, holes, match_keys n target target' a ha,
          matchs_keys n args args' b hb]
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
    | .generator body, .generator body', σ, h => by
      simp only [matchT] at h
      simp only [holes, matchStmts_keys n body body' σ h]
    | .arrowBlock bs body, .arrowBlock ps body' none, σ, h => by
      simp only [matchT] at h
      split at h
      · simp only [holes, matchStmts_keys n body body' σ h]
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  theorem matchs_keys (n : Nat) : ∀ (ts : Tpls) (es : List Expr) (σ : Subst),
      matchTs n ts es = some σ → keys σ = holesTs ts
    | .nil, [], σ, h => by
      simp only [matchTs, Option.some.injEq] at h
      subst h
      rfl
    | .cons hd tl, e :: es, σ, h => by
      simp only [matchTs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨a, ha, b, hb, rfl⟩ := h
      simp only [keys_append, holesTs, match_keys n hd e a ha, matchs_keys n tl es b hb]
  theorem matchFields_keys (n : Nat) : ∀ (fs : Fields) (es : List (String × Expr)) (σ : Subst),
      matchFields n fs es = some σ → keys σ = holesFields fs
    | .nil, [], σ, h => by
      simp only [matchFields, Option.some.injEq] at h
      subst h
      rfl
    | .cons key v tl, (key', e) :: es, σ, h => by
      simp only [matchFields] at h
      split at h
      · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨a, ha, b, hb, rfl⟩ := h
        simp only [keys_append, holesFields, match_keys n v e a ha, matchFields_keys n tl es b hb]
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  theorem matchStmt_keys (n : Nat) : ∀ (t : StmtTpl) (s : Stmt) (σ : Subst),
      matchStmt n t s = some σ → keys σ = holesStmt t
    | .letInit k v ann, .letInit name e ty, σ, h => by
      simp only [matchStmt] at h
      split at h
      · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨a, ha, b, hb, rfl⟩ := h
        simp only [keys_append, holesStmt, match_keys n v e a ha, matchAnn_keys ann ty b hb]
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
    | .assign k v, .assign name e, σ, h => by
      simp only [matchStmt] at h
      split at h
      · simp only [holesStmt, match_keys n v e σ h]
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
    | .ret v, .ret e, σ, h => by
      simp only [matchStmt] at h
      simp only [holesStmt, match_keys n v e σ h]
    | .exprStmt v, .exprStmt e, σ, h => by
      simp only [matchStmt] at h
      simp only [holesStmt, match_keys n v e σ h]
    | .constYield k v, .constYield name e none, σ, h => by
      simp only [matchStmt] at h
      split at h
      · simp only [holesStmt, match_keys n v e σ h]
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
    | .yieldDiscard v, .yieldDiscard e, σ, h => by
      simp only [matchStmt] at h
      simp only [holesStmt, match_keys n v e σ h]
    | .ifElse t a b, .ifElse t' a' b', σ, h => by
      simp only [matchStmt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨x, hx, y, hy, z, hz, rfl⟩ := h
      simp only [keys_append, holesStmt, match_keys n t t' x hx, matchStmts_keys n a a' y hy,
        matchStmts_keys n b b' z hz]
    | .whileTrue body, .whileTrue none body', σ, h => by
      simp only [matchStmt] at h
      simp only [holesStmt, matchStmts_keys n body body' σ h]
    | .breakTo, .breakTo none, σ, h => by
      simp only [matchStmt, Option.some.injEq] at h
      subst h
      rfl
  theorem matchStmts_keys (n : Nat) : ∀ (ts : StmtTpls) (ss : List Stmt) (σ : Subst),
      matchStmts n ts ss = some σ → keys σ = holesStmts ts
    | .hole i, ss, σ, h => by
      simp only [matchStmts, Option.some.injEq] at h
      subst h
      rfl
    | .nil, [], σ, h => by
      simp only [matchStmts, Option.some.injEq] at h
      subst h
      rfl
    | .cons hd tl, s :: ss, σ, h => by
      simp only [matchStmts, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨a, ha, b, hb, rfl⟩ := h
      simp only [keys_append, holesStmts, matchStmt_keys n hd s a ha, matchStmts_keys n tl ss b hb]
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
