import Lean

/-! Seat PROGRAMS of the data probe (2026-10-01), probe 4: the two encodings of records, in
miniature, on this toolchain (no tree import). The type algebra note
(`docs/research/2026-09-18-research-type-algebra.md` §0, §1.2) read facts F1-F3 from the
toolchain's source and ran no Lean; this probe runs them on the two candidates the record stage
must choose between:

* `T`/`Fs`, the mutual spine sibling (row 2's `Ty`/`Fields`, R3's wording);
* `U`, one inductive with a binary row extension (`extend label field rest`, `empty`), the
  shape of row-polymorphic record calculi; an `extend` over a non-record is junk that a
  well-formedness predicate refuses, as `Normal` refuses junk unions today.

What is measured: whether `DecidableEq` and `Repr` derive, whether the derived `Repr` is
`partial` (the trust gate refuses `partial` in `src`, F3+F4), whether the `induction` tactic
accepts the type, and what one law (DI-67's inhabitance, in miniature) costs on each. Scratch,
not in the tree. -/

set_option autoImplicit false

namespace Probe.Spine

/-! ## The mutual spine -/

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

deriving instance DecidableEq for T, Fs
deriving instance Repr for T, Fs

/-! ## The binary row extension -/

inductive U where
  | nat
  | str
  | prod (a b : U)
  | empty
  | extend (name : String) (type : U) (rest : U)
deriving DecidableEq, Repr

/-! ## Values, as the tree's carrier spells products (`.list [x, y]`) -/

inductive V where
  | nat (n : Nat)
  | str (s : String)
  | list (xs : List V)

/-! ## Membership, structural on both -/

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

/-- A record over the extension: the field values in label order, the same `.list` layout. -/
def fitsU : U → V → Bool
  | .nat, .nat _ => true
  | .str, .str _ => true
  | .prod a b, .list [x, y] => fitsU a x && fitsU b y
  | .empty, .list [] => true
  | .extend _ t rest, .list (v :: vs) => fitsU t v && fitsU rest (.list vs)
  | _, _ => false

/-! ## Inhabitance in miniature (DI-67 over the membership): every type has a member -/

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

-- On the spine: two theorems for one property, by structural mutual recursion.
mutual
  theorem fitsT_defT : ∀ t : T, fitsT t (defT t) = true
    | .nat => rfl
    | .str => rfl
    | .prod a b => by simp only [defT, fitsT, fitsT_defT a, fitsT_defT b, Bool.and_self]
    | .record fs => by simp only [defT, fitsT, fitsFs_defFs fs]
  theorem fitsFs_defFs : ∀ fs : Fs, fitsFs fs (defFs fs) = true
    | .nil => rfl
    | .cons _ t rest => by simp only [defFs, fitsFs, fitsT_defT t, fitsFs_defFs rest, Bool.and_self]
end

/-- A record chain: `empty`, or an extension of one. -/
def RecU : U → Bool
  | .empty => true
  | .extend _ _ r => RecU r
  | _ => false

/-- Well-formed: every extension extends a record chain. -/
def WF : U → Bool
  | .nat | .str | .empty => true
  | .prod a b => WF a && WF b
  | .extend _ t r => WF t && RecU r && WF r

def defU : U → V
  | .nat => .nat 0
  | .str => .str ""
  | .prod a b => .list [defU a, defU b]
  | .empty => .list []
  | .extend _ t r =>
    match defU r with
    | .list vs => .list (defU t :: vs)
    | other => other

theorem defU_list (u : U) (h : RecU u = true) : ∃ vs, defU u = .list vs := by
  induction u with
  | empty => exact ⟨[], rfl⟩
  | extend l t r _ ihr =>
    obtain ⟨vs, hvs⟩ := ihr h
    exact ⟨defU t :: vs, by simp only [defU, hvs]⟩
  | nat => exact absurd h (by decide)
  | str => exact absurd h (by decide)
  | prod a b _ _ => exact absurd h (by simp only [RecU, Bool.false_eq_true, not_false_eq_true])

-- On the extension: one theorem with `induction`, but a well-formedness premise and a helper.
theorem fitsU_defU (u : U) (h : WF u = true) : fitsU u (defU u) = true := by
  induction u with
  | nat => rfl
  | str => rfl
  | empty => rfl
  | prod a b iha ihb =>
    simp only [WF, Bool.and_eq_true] at h
    simp only [defU, fitsU, iha h.1, ihb h.2, Bool.and_self]
  | extend l t r iht ihr =>
    simp only [WF, Bool.and_eq_true] at h
    obtain ⟨vs, hvs⟩ := defU_list r h.1.2
    have hr := ihr h.2
    rw [hvs] at hr
    simp only [defU, hvs, fitsU, iht h.1.1, hr, Bool.and_self]

-- RED CONTROL: without the premise the law is false on the extension (junk exists).
#guard fitsU (.extend "a" .nat .nat) (defU (.extend "a" .nat .nat)) = false

#print axioms fitsT_defT
#print axioms fitsFs_defFs
#print axioms defU_list
#print axioms fitsU_defU

end Probe.Spine

/-! ## RED CONTROL: the `induction` tactic on the mutual spine

Every `induction t` over `Ty` in the tree (about thirty, counted in the note) would have to be
rewritten as a mutual recursive theorem pair, as `fitsT_defT`/`fitsFs_defFs` are above. -/

namespace Probe.Spine
/--
error: The `induction` tactic does not support the type `Probe.Spine.T` because it is mutually inductive

Hint: Consider using the `cases` tactic instead
-/
#guard_msgs (error) in
example (t : T) : fitsT t (defT t) = true := by
  induction t
end Probe.Spine

/-! ## Whether a derived `Repr` is `partial` -/

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut rows : Array String := #[]
  for (n, ci) in env.constants.toList do
    if (`Probe.Spine).isPrefixOf n && (n.toString.splitOn "repr").length > 1 then
      let kind := match ci with
        | .opaqueInfo _ => "opaque (partial)"
        | .defnInfo _ => "def"
        | _ => "other"
      rows := rows.push s!"{n}: {kind}"
  for r in rows.qsort (· < ·) do
    logInfo r
