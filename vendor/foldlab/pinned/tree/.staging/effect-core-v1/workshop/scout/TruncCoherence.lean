/-
FORWARD SCOUT PROBE — `EC1-T039 approx_coherent`, and what it forces on `truncate`.

Row (PROOF-DAG.md §6):
  `approx_coherent : (h : m<=n) -> truncate h (approx n c) = approx m c`
  Status PENDING THEOREM, classed NO ANCHOR by the local-anchor lane, whose
  nearest corpus shape is the list-level truncation family
  `Cas/IR/View.lean:181 lastK_lastK` (`j <= k -> lastK j (lastK k l) = lastK j l`).

That family composes because cutting a LIST relabels nothing. An approximation
is a TREE WITH LABELLED LEAVES, and a cut has to put something where the subtree
was. This probe asks which fill makes the row true, and shows the row is FALSE
for the other one.

Not a promotion. No packet name is introduced. Deliberately carrier-free: the
question is about `truncate`'s definition, so the model is the smallest thing
that has a depth-bounded unfolding and a leaf label.
-/

namespace Scout

/-- The two leaf observations the packet already distinguishes: a terminal
result, and a live frontier (`EC1-CE003` proved fuel exhaustion is NOT a
refusal, so the frontier arm is forced to exist). -/
inductive Leaf where
  | halt
  | frontier
deriving DecidableEq, Repr

/-- Smallest carrier with a depth: a unary spine of steps ending in a leaf.
Branching is irrelevant to this question — a cut is a cut on every child. -/
inductive Tree where
  | leaf (l : Leaf)
  | step (t : Tree)
deriving DecidableEq, Repr

/-- The source: a computation that halts after exactly `k` more steps. -/
abbrev Src := Nat

/-- Depth-bounded observation. Running out of DEPTH yields a frontier; running
to completion yields a halt. This is the packet's own `FinApprox` shape. -/
def approx : Nat → Src → Tree
  | 0,     _     => .leaf .frontier
  | _ + 1, 0     => .leaf .halt
  | d + 1, k + 1 => .step (approx d k)

/-- Truncation parameterised by WHAT IS WRITTEN AT THE CUT. This is the whole
design question: the packet says `truncate` and does not say the fill. -/
def truncAt (fill : Leaf) : Nat → Tree → Tree
  | 0,     _        => .leaf fill
  | _ + 1, .leaf l  => .leaf l
  | d + 1, .step t  => .step (truncAt fill d t)

/-! ## 1. The row is TRUE when the cut is filled with the frontier -/

/-- `EC1-T039` holds — with the fill forced to `.frontier`.
Note the quantifier: no `m <= n` premise is needed. Cutting BELOW what was
computed and cutting ABOVE it agree, because both write the same frontier. -/
theorem approx_coherent_frontier (m : Nat) : ∀ (n k : Nat),
    m ≤ n → truncAt .frontier m (approx n k) = approx m k := by
  induction m with
  | zero => intro n k _; cases n <;> cases k <;> rfl
  | succ m ih =>
    intro n k h
    match n, k with
    | 0, _ => exact absurd h (by omega)
    | _ + 1, 0 => rfl
    | n + 1, k + 1 =>
        show Tree.step (truncAt .frontier m (approx n k)) = Tree.step (approx m k)
        rw [ih n k (by omega)]

/-! ## 2. The row is FALSE for the other fill -/

/-- Filling the cut with `.halt` breaks the row at the smallest possible
witness: depth 0 against a computation with a step still to run. The truncation
claims the computation FINISHED when it was only cut off. -/
theorem approx_coherent_halt_is_false :
    ¬ (∀ m n k : Nat, m ≤ n → truncAt .halt m (approx n k) = approx m k) := by
  intro h
  have := h 0 1 1 (by omega)
  exact Leaf.noConfusion (Tree.leaf.inj this)

/-- The witness spelled out, so the failure is readable rather than inferred:
one step remaining, cut at depth 0. -/
theorem halt_fill_witness :
    truncAt .halt 0 (approx 1 1) = .leaf .halt
      ∧ approx 0 1 = .leaf .frontier := ⟨rfl, rfl⟩

/-! ## 3. Why this is not bookkeeping: the fill is observable

A cut node and a halted node are distinguished by the very predicate the packet
needs for `EC1-T044 diverges_iff_live_prefixes`. If `truncate` fills with
`.halt`, a live computation is reported terminated at every depth below its
completion, and `Live` becomes unsound on truncated trees. -/

def Live : Tree → Prop
  | .leaf .frontier => True
  | .leaf .halt     => False
  | .step t         => Live t

/-- Liveness is DOWNWARD closed in depth: still live after `n` steps means you
were live at every shallower view. This is the direction `EC1-T044`'s `forall n,
Live (execN n ...)` formulation actually needs. -/
theorem live_downward (m : Nat) : ∀ (n k : Nat),
    m ≤ n → Live (approx n k) → Live (approx m k) := by
  induction m with
  | zero => intro n k _ _; trivial
  | succ m ih =>
    intro n k h hl
    match n, k with
    | 0, _ => exact absurd h (by omega)
    | _ + 1, 0 => exact absurd hl (by simp [approx, Live])
    | n + 1, k + 1 => exact ih n k (by omega) hl

/-- The UPWARD direction is false, and this is the shape a `Diverges` proof will
reach for by mistake: live at depth 0 says nothing, because every computation is
live at depth 0 — including one that halts at depth 1. -/
theorem live_upward_is_false :
    ¬ (∀ m n k : Nat, m ≤ n → Live (approx m k) → Live (approx n k)) := by
  intro h
  exact (by simp [approx, Live] : ¬ Live (approx 1 0)) (h 0 1 0 (by omega) trivial)


/-! ## 4. Does the constraint survive the observation mask? NOT SETTLED HERE.

`EC1-T042 semEq_approx_iff` compares `mask O (approx n ...)` on both sides. §1
forced `truncate` to write `.frontier` at a cut; that is worthless if the MASK
then forgets the leaf label. The estate has this exact hazard on record one
carrier down — `Cas/Lang/Representation.lean:198 ObsEq.run_refused` deliberately
drops the partial word on a refusing branch (`EC1-CE010`).

I tried to exhibit the hazard here and COULD NOT, for a reason worth recording:
in a unary spine the shape already determines the label, so a shape-only mask is
not lossy on this axis. The theorem below is the obstruction, not a success. -/

/-- A mask that keeps the spine and forgets the leaf label. -/
def maskShape : Tree → Nat
  | .leaf _  => 0
  | .step t  => maskShape t + 1

/-- In THIS carrier the shape mask is not lossy: at a fixed depth, spine length
already decides whether the leaf is a halt or a frontier. A computation is cut
exactly when it outlasts the depth, and then the spine is the depth. -/
theorem shape_determines_the_leaf (d : Nat) : ∀ k : Nat,
    (maskShape (approx d k) = d ∧ approx d k ≠ .leaf .halt)
      ∨ (maskShape (approx d k) = k ∧ k < d) := by
  induction d with
  | zero => intro k; exact Or.inl ⟨rfl, by simp [approx]⟩
  | succ d ih =>
    intro k
    match k with
    | 0 => exact Or.inr ⟨rfl, by omega⟩
    | k + 1 =>
      rcases ih k with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨by simp [approx, maskShape, h1], by simp [approx]⟩
      · exact Or.inr ⟨by simp [approx, maskShape, h1], by omega⟩

/-! Consequence for the scout report: the mask constraint is OWED, not proved.
Exhibiting it needs a carrier where two programs share a masked shape and differ
in liveness — which this unary spine cannot express. Branching, or a leaf
payload, is required. Recorded so nobody reads §1 as having settled §4. -/

end Scout

#print axioms Scout.approx_coherent_frontier
#print axioms Scout.approx_coherent_halt_is_false
#print axioms Scout.halt_fill_witness
#print axioms Scout.live_downward
#print axioms Scout.live_upward_is_false
#print axioms Scout.shape_determines_the_leaf
