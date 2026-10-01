/-! Verifier of seat PROGRAMS (2026-10-01): does the mutual spine really turn every `Ty`
induction into a mutual theorem pair (PROG-D8)? The seat's `ProbeSpine.lean` pins that the plain
`induction t` tactic refuses a mutually inductive type. This probe tries the routes the seat did
not: `induction t using T.rec` with the second motive named, the recursor in term mode, and
functional induction over a mutual function. Same `T`/`Fs`/`V`/`fitsT`/`defT` as the seat's
probe, copied so the comparison is like for like. Scratch, not in the tree. -/

set_option autoImplicit false

namespace Verify.Spine

mutual
  inductive T where
    | nat
    | str
    | prod (a b : T)
    | record (fs : Fs)
  inductive Fs where
    | nil
    | cons (name : String) (type : T) (rest : Fs)
end

inductive V where
  | nat (n : Nat)
  | str (s : String)
  | list (xs : List V)

mutual
  def fitsT : T → V → Bool
    | .nat, .nat _ => true
    | .str, .str _ => true
    | .prod a b, .list [x, y] => fitsT a x && fitsT b y
    | .record fs, .list vs => fitsFs fs vs
    | _, _ => false
  def fitsFs : Fs → List V → Bool
    | .nil, [] => true
    | .cons _ t rest, v :: vs => fitsT t v && fitsFs rest vs
    | _, _ => false
end

mutual
  def defT : T → V
    | .nat => .nat 0
    | .str => .str ""
    | .prod a b => .list [defT a, defT b]
    | .record fs => .list (defFs fs)
  def defFs : Fs → List V
    | .nil => []
    | .cons _ t rest => defT t :: defFs rest
end

-- Route 1: ONE theorem, the `induction` tactic with the recursor named and the second motive
-- supplied. If this compiles, a `Ty` induction on the spine is one theorem with two added
-- cases (`nil`, `cons`) and one motive, not a mutual pair.
theorem fitsT_defT_using (t : T) : fitsT t (defT t) = true := by
  induction t using T.rec (motive_2 := fun fs => fitsFs fs (defFs fs) = true) with
  | nat => rfl
  | str => rfl
  | prod a b iha ihb => simp only [defT, fitsT, iha, ihb, Bool.and_self]
  | record fs ih => simp only [defT, fitsT, ih]
  | nil => rfl
  | cons _ t rest iht ihr => simp only [defFs, fitsFs, iht, ihr, Bool.and_self]

-- Route 2: ONE theorem, the recursor in term mode.
theorem fitsT_defT_term (t : T) : fitsT t (defT t) = true :=
  T.rec (motive_1 := fun t => fitsT t (defT t) = true)
    (motive_2 := fun fs => fitsFs fs (defFs fs) = true)
    rfl rfl
    (fun a b iha ihb => by simp only [defT, fitsT, iha, ihb, Bool.and_self])
    (fun fs ih => by simp only [defT, fitsT, ih])
    rfl
    (fun _ t rest iht ihr => by simp only [defFs, fitsFs, iht, ihr, Bool.and_self])
    t

#print axioms fitsT_defT_using
#print axioms fitsT_defT_term

/-! Route 3: the tree's own idiom for its nested `Json` (`src/Effect4/Data/Json.lean:313-330`, a
single-motive companion built from `Json.rec (motive_1 := …) (motive_2 := …)`), registered as the
default eliminator, so the plain `induction t` keeps working on the spine and only the record case
is new. The fields' facts arrive as a membership hypothesis. -/

def Fs.toList : Fs → List (String × T)
  | .nil => []
  | .cons n t r => (n, t) :: r.toList

@[induction_eliminator]
theorem T.ind {motive : T → Prop}
    (nat : motive .nat) (str : motive .str)
    (prod : ∀ a b, motive a → motive b → motive (.prod a b))
    (record : ∀ fs, (∀ p ∈ fs.toList, motive p.2) → motive (.record fs)) (t : T) : motive t :=
  T.rec (motive_1 := motive) (motive_2 := fun fs => ∀ p ∈ fs.toList, motive p.2)
    nat str prod record
    (fun _ h => nomatch h)
    (fun n t r iht ihr p h => by
      simp only [Fs.toList, List.mem_cons] at h
      rcases h with rfl | h
      · exact iht
      · exact ihr p h)
    t

/-- The one helper the record case needs: field-wise facts give the fields' fact. -/
theorem fitsFs_defFs_of : ∀ fs : Fs, (∀ p ∈ fs.toList, fitsT p.2 (defT p.2) = true) →
    fitsFs fs (defFs fs) = true
  | .nil, _ => rfl
  | .cons n t r, h => by
    have ht : fitsT t (defT t) = true := h (n, t) (by simp only [Fs.toList, List.mem_cons, true_or])
    have hr := fitsFs_defFs_of r (fun p hp => h p (by simp only [Fs.toList, List.mem_cons, hp, or_true]))
    simp only [defFs, fitsFs, ht, hr, Bool.and_self]

/-- The plain `induction t`, as every `Ty` proof in the tree is written today. -/
theorem fitsT_defT_plain (t : T) : fitsT t (defT t) = true := by
  induction t with
  | nat => rfl
  | str => rfl
  | prod a b iha ihb => simp only [defT, fitsT, iha, ihb, Bool.and_self]
  | record fs ih => simp only [defT, fitsT, fitsFs_defFs_of fs ih]

#print axioms T.ind
#print axioms fitsFs_defFs_of
#print axioms fitsT_defT_plain

end Verify.Spine
