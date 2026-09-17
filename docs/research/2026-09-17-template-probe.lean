import TypeScript.Syntax

/-! Probe for R4/R5: a printed clause as a template with numbered holes; `inst` prints,
`matchT` reads, and reading an instance gives back the arguments, proved once. -/

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

/-- `Effect.flatMap(first, (aN) => rest)` as data. -/
def flatMapT : Tpl :=
  .call (.ident "Effect.flatMap") (.cons (.hole 0) (.cons (.lambda [0] (.hole 1)) .nil))

#guard (inst 3 [(0, .ident "X"), (1, .ident "Y")] flatMapT).bind (matchT 3 flatMapT)
  == some [(0, Expr.ident "X"), (1, Expr.ident "Y")]

#print axioms match_inst

end TplProbe
