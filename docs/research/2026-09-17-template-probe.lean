import TypeScript.Syntax

/-! Probe for R4/R5: a printed clause as a template with numbered holes; `inst` prints,
`matchT` reads. Both engine lemmas are proved once, over templates: `match_inst` (reading an
instance gives back the arguments: law 11's engine) and `inst_of_match` (a match of a template
with distinct holes instantiates back to what it matched: law 12's engine). -/

set_option autoImplicit false

namespace TplProbe
open TypeScript

mutual
  inductive Tpl
    | hole (i : Nat)
    | binderRef (k : Nat)
    | ident (s : String)
    | call (head : Tpl) (args : Tpls)
    | arrow (body : Tpl)
    | lambda (binders : List Nat) (body : Tpl)
    | cond (t a b : Tpl)
  inductive Tpls
    | nil
    | cons (head : Tpl) (tail : Tpls)
end

def varName (i : Nat) : String := "a" ++ toString i

abbrev Subst := List (Nat × Expr)

def lookup (σ : Subst) (i : Nat) : Option Expr := (σ.find? (·.1 == i)).map (·.2)

mutual
  def inst (n : Nat) (σ : Subst) : Tpl → Option Expr
    | .hole i => lookup σ i
    | .binderRef k => some (.ident (varName (n + k)))
    | .ident s => some (.ident s)
    | .call h args => do
      let h' ← inst n σ h
      let a' ← insts n σ args
      some (.call h' a')
    | .arrow b => do some (.arrow none (← inst n σ b))
    | .lambda bs b => do
      some (.lambda (bs.map fun k => ⟨varName (n + k), none⟩) (← inst n σ b))
    | .cond t a b => do
      some (.cond (← inst n σ t) (← inst n σ a) (← inst n σ b))
  def insts (n : Nat) (σ : Subst) : Tpls → Option (List Expr)
    | .nil => some []
    | .cons h t => do some ((← inst n σ h) :: (← insts n σ t))
end

mutual
  /-- Match an expression against a template, collecting the holes left to right. -/
  def matchT (n : Nat) : Tpl → Expr → Option Subst
    | .hole i, e => some [(i, e)]
    | .binderRef k, .ident s => if s = varName (n + k) then some [] else none
    | .ident s, .ident s' => if s = s' then some [] else none
    | .call h args, .call h' args' => do
      let a ← matchT n h h'
      let b ← matchTs n args args'
      some (a ++ b)
    | .arrow b, .arrow none b' => matchT n b b'
    | .lambda bs b, .lambda ps b' none =>
      if ps = bs.map (fun k => (⟨varName (n + k), none⟩ : Parameter)) then matchT n b b' else none
    | .cond t a b, .cond t' a' b' => do
      let x ← matchT n t t'
      let y ← matchT n a a'
      let z ← matchT n b b'
      some (x ++ y ++ z)
    | _, _ => none
  def matchTs (n : Nat) : Tpls → List Expr → Option Subst
    | .nil, [] => some []
    | .cons h t, e :: es => do
      let a ← matchT n h e
      let b ← matchTs n t es
      some (a ++ b)
    | _, _ => none
end

mutual
  /-- The holes of a template, left to right. -/
  def holes : Tpl → List Nat
    | .hole i => [i]
    | .binderRef _ | .ident _ => []
    | .call h args => holes h ++ holess args
    | .arrow b => holes b
    | .lambda _ b => holes b
    | .cond t a b => holes t ++ holes a ++ holes b
  def holess : Tpls → List Nat
    | .nil => []
    | .cons h t => holes h ++ holess t
end

/-- What a match of an instance returns: the substitution read along the holes. -/
def along (σ : Subst) (hs : List Nat) : Option Subst :=
  hs.mapM fun i => (lookup σ i).map fun e => (i, e)

theorem along_append (σ : Subst) (xs ys : List Nat) :
    along σ (xs ++ ys) = (do let a ← along σ xs; let b ← along σ ys; some (a ++ b)) := by
  unfold along
  rw [List.mapM_append]
  rfl

mutual
  /-- Law 11's engine: matching an instance gives back the arguments along the holes. -/
  theorem match_inst (n : Nat) (σ : Subst) : ∀ (t : Tpl) (e : Expr),
      inst n σ t = some e → matchT n t e = along σ (holes t)
    | .hole i, e, h => by
      simp only [inst] at h
      simp only [matchT, holes, along, List.mapM_cons, List.mapM_nil, h]
      rfl
    | .binderRef k, e, h => by
      simp only [inst, Option.some.injEq] at h
      subst h
      simp only [matchT, holes, along, List.mapM_nil, if_true]
      rfl
    | .ident s, e, h => by
      simp only [inst, Option.some.injEq] at h
      subst h
      simp only [matchT, holes, along, List.mapM_nil, if_true]
      rfl
    | .call hd args, e, h => by
      simp only [inst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨h', hh, a', ha, rfl⟩ := h
      simp only [matchT, holes, along_append, match_inst n σ hd h' hh, matchs_inst n σ args a' ha]
    | .arrow b, e, h => by
      simp only [inst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨b', hb, rfl⟩ := h
      simp only [matchT, holes, match_inst n σ b b' hb]
    | .lambda bs b, e, h => by
      simp only [inst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨b', hb, rfl⟩ := h
      simp only [matchT, holes, if_true, match_inst n σ b b' hb]
    | .cond t a b, e, h => by
      simp only [inst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨t', ht, a', ha, b', hb, rfl⟩ := h
      simp only [matchT, holes, along_append, match_inst n σ t t' ht, match_inst n σ a a' ha,
        match_inst n σ b b' hb]
      cases along σ (holes t) <;> cases along σ (holes a) <;> cases along σ (holes b) <;> rfl
  theorem matchs_inst (n : Nat) (σ : Subst) : ∀ (ts : Tpls) (es : List Expr),
      insts n σ ts = some es → matchTs n ts es = along σ (holess ts)
    | .nil, es, h => by
      simp only [insts, Option.some.injEq] at h
      subst h
      simp only [matchTs, holess, along, List.mapM_nil]
      rfl
    | .cons hd tl, es, h => by
      simp only [insts, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨h', hh, t', ht, rfl⟩ := h
      simp only [matchTs, holess, along_append, match_inst n σ hd h' hh, matchs_inst n σ tl t' ht]
end

/-! ## The converse engine lemma (law 12's engine): a match of a LINEAR template instantiates back

Stated with a context on both sides (`pre ++ σ ++ post`) so the append bookkeeping of the
compound cases is re-association only. -/

def keys (σ : Subst) : List Nat := σ.map (·.1)

theorem keys_append (a b : Subst) : keys (a ++ b) = keys a ++ keys b := List.map_append

theorem lookup_cons_self (i : Nat) (e : Expr) (rest : Subst) : lookup ((i, e) :: rest) i = some e := by
  have hb : (i == i) = true := decide_eq_true rfl
  unfold lookup
  rw [List.find?_cons_of_pos (l := rest) (a := (i, e)) (p := fun x => x.1 == i) hb]
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

mutual
  /-- What a match collects is keyed by the template's holes, left to right. -/
  theorem match_keys (n : Nat) : ∀ (t : Tpl) (e : Expr) (σ : Subst),
      matchT n t e = some σ → keys σ = holes t
    | .hole i, e, σ, h => by
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
    | .call hd args, .call hd' args', σ, h => by
      simp only [matchT, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨a, ha, b, hb, rfl⟩ := h
      simp only [keys_append, holes, match_keys n hd hd' a ha, matchs_keys n args args' b hb]
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
    | .binderRef _, .call _ _, _, h | .binderRef _, .arrow _ _, _, h
    | .binderRef _, .cond _ _ _, _, h => by simp only [matchT, reduceCtorEq] at h
  theorem matchs_keys (n : Nat) : ∀ (ts : Tpls) (es : List Expr) (σ : Subst),
      matchTs n ts es = some σ → keys σ = holess ts
    | .nil, [], σ, h => by
      simp only [matchTs, Option.some.injEq] at h
      subst h
      rfl
    | .cons hd tl, e :: es, σ, h => by
      simp only [matchTs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨a, ha, b, hb, rfl⟩ := h
      simp only [keys_append, holess, match_keys n hd e a ha, matchs_keys n tl es b hb]
    | .nil, _ :: _, _, h => by simp only [matchTs, reduceCtorEq] at h
    | .cons _ _, [], _, h => by simp only [matchTs, reduceCtorEq] at h
end

/-- The holes of `t` avoid the keys of `pre`. -/
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

mutual
  /-- Law 12's engine: a match of a template with distinct holes instantiates back to the
  expression it matched, in any context whose earlier keys avoid the template's holes. -/
  theorem inst_match (n : Nat) : ∀ (t : Tpl) (e : Expr) (σ pre post : Subst),
      matchT n t e = some σ → (holes t).Nodup → Fresh pre (holes t) →
      inst n (pre ++ σ ++ post) t = some e
    | .hole i, e, σ, pre, post, h, _, fr => by
      simp only [matchT, Option.some.injEq] at h
      subst h
      have hi : i ∉ keys pre := fr i (List.mem_cons_self ..)
      rw [List.append_assoc]
      simp only [inst]
      rw [lookup_append_of_not_mem pre _ i hi]
      exact lookup_cons_self i e post
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
    | .call hd args, .call hd' args', σ, pre, post, h, nd, fr => by
      simp only [matchT, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨a, ha, b, hb, rfl⟩ := h
      simp only [holes] at nd fr
      have h1 := inst_match n hd hd' a pre (b ++ post) ha (List.nodup_append.mp nd).1 fr.left
      have h2 := insts_match n args args' b (pre ++ a) post hb (List.nodup_append.mp nd).2.1
        (fr.past (match_keys n hd hd' a ha) nd)
      simp only [List.append_assoc] at h1 h2 ⊢
      simp only [inst, h1, h2, Option.bind_eq_bind, Option.bind_some]
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
      simp only [holes, List.append_assoc] at nd fr
      have ndt := (List.nodup_append.mp nd).1
      have ndab := (List.nodup_append.mp nd).2.1
      have h1 := inst_match n t t' x pre (y ++ z ++ post) hx ndt fr.left
      have frab : Fresh (pre ++ x) (holes a ++ holes b) := fr.past (match_keys n t t' x hx) nd
      have h2 := inst_match n a a' y (pre ++ x) (z ++ post) hy (List.nodup_append.mp ndab).1 frab.left
      have h3 := inst_match n b b' z (pre ++ x ++ y) post hz (List.nodup_append.mp ndab).2.1
        (frab.past (match_keys n a a' y hy) ndab)
      simp only [List.append_assoc] at h1 h2 h3 ⊢
      simp only [inst, h1, h2, h3, Option.bind_eq_bind, Option.bind_some]
    | .binderRef _, .call _ _, _, _, _, h, _, _ | .binderRef _, .arrow _ _, _, _, _, h, _, _
    | .binderRef _, .cond _ _ _, _, _, _, h, _, _ => by simp only [matchT, reduceCtorEq] at h
  theorem insts_match (n : Nat) : ∀ (ts : Tpls) (es : List Expr) (σ pre post : Subst),
      matchTs n ts es = some σ → (holess ts).Nodup → Fresh pre (holess ts) →
      insts n (pre ++ σ ++ post) ts = some es
    | .nil, [], σ, pre, post, h, _, _ => by
      simp only [insts]
    | .cons hd tl, e :: es, σ, pre, post, h, nd, fr => by
      simp only [matchTs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨a, ha, b, hb, rfl⟩ := h
      simp only [holess] at nd fr
      have h1 := inst_match n hd e a pre (b ++ post) ha (List.nodup_append.mp nd).1 fr.left
      have h2 := insts_match n tl es b (pre ++ a) post hb (List.nodup_append.mp nd).2.1
        (fr.past (match_keys n hd e a ha) nd)
      simp only [List.append_assoc] at h1 h2 ⊢
      simp only [insts, h1, h2, Option.bind_eq_bind, Option.bind_some]
    | .nil, _ :: _, _, _, _, h, _, _ => by simp only [matchTs, reduceCtorEq] at h
    | .cons _ _, [], _, _, _, h, _, _ => by simp only [matchTs, reduceCtorEq] at h
end

/-- The converse as R5.2 uses it: no context. -/
theorem inst_of_match (n : Nat) (t : Tpl) (e : Expr) (σ : Subst)
    (h : matchT n t e = some σ) (nd : (holes t).Nodup) : inst n σ t = some e := by
  have := inst_match n t e σ [] [] h nd (fun _ _ hm => by simp only [keys, List.map_nil, List.not_mem_nil] at hm)
  simpa only [List.nil_append, List.append_nil] using this

/-- `Effect.flatMap(first, (aN) => rest)` as data. -/
def flatMapT : Tpl :=
  .call (.ident "Effect.flatMap") (.cons (.hole 0) (.cons (.lambda [0] (.hole 1)) .nil))

#guard (inst 3 [(0, .ident "X"), (1, .ident "Y")] flatMapT).bind (matchT 3 flatMapT)
  == some [(0, Expr.ident "X"), (1, Expr.ident "Y")]

#print axioms match_inst
#print axioms match_keys
#print axioms inst_of_match

end TplProbe
