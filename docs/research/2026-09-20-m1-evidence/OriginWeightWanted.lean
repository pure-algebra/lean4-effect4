import Effect4.Laws.Auto.Obligations
import Effect4.Laws.Program.Intro.Identity

/-!
# Intro.Weight: addresses, the descent measure and the shared introductions

A point's weight (fuel plus tape) descends with every child. The address lemmas, what a
suspension returns with its point kept whole, the race entrants, the action a `withFiber`
node answers (`actionAt_shape`) and the finalizer frame (`finalizer_intro`).
-/

set_option autoImplicit false

namespace Effect4.Program.Sched

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote Effect4.Program.Agreement

/-! ## Addresses and weights -/

theorem at_child_of {root : NativeEff} {p : Point} {n : Node NativeOp}
    (h : Node.at_ (Node.eff root) p.path = some n) (i : Nat) :
    Node.at_ (Node.eff root) (p.child i).path = n.child i := by
  simp only [Point.child, Node.at_append, h, Option.bind]

theorem at_childWith_of {root : NativeEff} {p : Point} {n : Node NativeOp}
    (h : Node.at_ (Node.eff root) p.path = some n) (i : Nat) (v : Val) :
    Node.at_ (Node.eff root) (p.childWith i v).path = n.child i := by
  simp only [Point.childWith, Node.at_append, h, Option.bind]

theorem denoteAt_of_at {root : NativeEff} {q : Point} {e : NativeEff}
    (h : Node.at_ (Node.eff root) q.path = some (Node.eff e)) :
    denoteAt root q = denoteR root e q := by
  simp [denoteAt, h]

/-- The measure the introduction descends: every child point spends a unit of fuel. -/
def _root_.Effect4.Program.Point.weight (p : Point) : Nat := p.fuel + p.tape.length

theorem weight_child (p : Point) (i : Nat) : (p.child i).weight ≤ p.weight := by
  simp only [Point.weight, Point.child]; omega

theorem weight_child_lt (p : Point) (i : Nat) (h : p.fuel ≠ 0) : (p.child i).weight < p.weight := by
  simp only [Point.weight, Point.child]; omega

theorem weight_childWith_lt (p : Point) (i : Nat) (v : Val) (h : p.fuel ≠ 0) :
    (p.childWith i v).weight < p.weight := by
  simp only [Point.weight, Point.childWith]; omega

theorem weight_completed (p : Point) (completed : List (FiberId × ExitV)) :
    ({ p with completed } : Point).weight = p.weight := rfl

theorem fuel_child_le (p : Point) (i : Nat) : (p.child i).fuel ≤ p.fuel := by
  rw [Point.child_fuel]; exact Nat.sub_le _ _

/-- A reference's hop keeps the tape and spends one fuel: no heavier than its point. -/
theorem weight_redirect_le (p : Point) (target : List Nat) :
    (p.redirect target).weight ≤ p.weight := by
  simp only [Point.weight, Point.redirect]; omega

/-- The spine of a `mergeAll` walked `i` steps in from a point (`Node.child`'s
`layers (.cons _ t), 1`), peeled from the head, so that a statement about the spine descends
with its term. -/
def _root_.Effect4.Program.Point.spineWalk : Nat → Point → Point
  | 0, p => p
  | i + 1, p => Point.spineWalk i (p.child 1)

theorem foldl_child_eq_spineWalk {α : Type} : ∀ (l : List α) (p : Point),
    l.foldl (fun acc _ => acc.child 1) p = Point.spineWalk l.length p
  | [], _ => rfl
  | _ :: l, p => foldl_child_eq_spineWalk l (p.child 1)

/-- `Point.spineChild` is the walk from the spine's head. -/
theorem Point.spineChild_eq (q : Point) (i : Nat) :
    q.spineChild i = (Point.spineWalk i (q.child 0)).child 0 := by
  unfold Point.spineChild
  rw [foldl_child_eq_spineWalk, List.length_range]

/-! ## What a suspension returns, with the point kept whole -/

theorem suspendBodyAt_zero' {root : NativeEff} {q : Point} (hf : q.fuel = 0) :
    suspendBodyAt root (EffThunk.body q) = frontier q := by
  simp [suspendBodyAt, hf]

theorem suspendBodyAt_gen {root : NativeEff} {q : Point} {k : Nat} {ss : Stmts NativeOp}
    (hf : q.fuel = k + 1) (h : Node.at_ (Node.eff root) q.path = some (Node.eff (.gen ss))) :
    suspendBodyAt root (EffThunk.body q) = Prim.iterator (EffName.gen q [] false) Val.unit := by
  simp [suspendBodyAt, hf, h]

theorem suspendBodyAt_iterate {root : NativeEff} {q : Point} {k : Nat} {c : Option Ty}
    {i t s r : Term} {b : NativeEff} (hf : q.fuel = k + 1)
    (h : Node.at_ (Node.eff root) q.path = some (Node.eff (.iterate c i t s r b))) :
    suspendBodyAt root (EffThunk.body q) =
      (match evalTerm q.env i with
       | some cursor => Prim.whileLoop (EffName.loop q) cursor
       | none => badShape) := by
  simp [suspendBodyAt, hf, h]; rfl

/-- `resolve` and `denoteAt` are related at every point of weight below the induction's bound. -/
theorem resolve_intro_of (root : NativeEff) (n : Nat)
    (ih : ∀ (p : Point), p.weight < n → ∀ (e : NativeEff),
      Node.at_ (.eff root) p.path = some (.eff e) →
        CodeMeans root (compileEff e p) (denoteR root e p))
    (q : Point) (hq : q.weight < n) : CodeMeans root (resolve root q) (denoteAt root q) := by
  unfold resolve denoteAt
  rcases hn : Node.at_ (.eff root) q.path with _ | m
  · exact codeMeans_badShape root
  · cases m with
    | eff e => exact ih q hq e hn
    | _ => exact codeMeans_badShape root

/-- The race entrants, each compiled and denoted at its own list address. -/
theorem entrants_intro (root : NativeEff) (n : Nat)
    (ih : ∀ (p : Point), p.weight < n → ∀ (e : NativeEff),
      Node.at_ (.eff root) p.path = some (.eff e) →
        CodeMeans root (compileEff e p) (denoteR root e p)) :
    ∀ (es : Effs NativeOp) (q : Point), q.weight < n →
      Node.at_ (.eff root) q.path = some (.effs es) →
      (actionAt.entrants es q).length = (entrantPoints es q).length ∧
        ∀ x ∈ (actionAt.entrants es q).zip ((entrantPoints es q).map (denoteAt root)),
          CodeMeans root x.1 x.2
  | .nil, _, _, _ => ⟨rfl, fun _ hx => by simp [actionAt.entrants, entrantPoints] at hx⟩
  | .cons e rest, q, hq, h => by
    have h0 : Node.at_ (.eff root) (q.child 0).path = some (.eff e) := at_child_of h 0
    have h1 : Node.at_ (.eff root) (q.child 1).path = some (.effs rest) := at_child_of h 1
    have tail := entrants_intro root n ih rest (q.child 1) (Nat.lt_of_le_of_lt (weight_child q 1) hq) h1
    refine ⟨by simp only [actionAt.entrants, entrantPoints, List.length_cons, tail.1], ?_⟩
    intro x hx
    simp only [actionAt.entrants, entrantPoints, List.map_cons, List.zip_cons_cons,
      List.mem_cons] at hx
    rcases hx with rfl | hx
    · show CodeMeans root (compileEff e (q.child 0)) (denoteAt root (q.child 0))
      rw [denoteAt_of_at h0]
      exact ih _ (Nat.lt_of_le_of_lt (weight_child q 0) hq) e h0
    · exact tail.2 x hx

/-! What `actionAt` puts in the program-carrying fields of the action of a `withFiber` node,
and the actions it never answers there: one lemma per fact, each by the node's term. -/

section actionShape

variable {root : NativeEff} {p : Point} {a : ActionTerm NativeOp}
  (h : Node.at_ (.eff root) p.path = some (.eff (.withFiber a)))

include h

def M1Origin.actionAt_fork {site : List Nat} {program : NCode} {options : Supervision.ForkOptions}
    (_hact : actionAt root p = some (.fork program options site)) : ProofGraph.Obligation (program = resolve root ((p.child 0).child 0)) := ⟨⟩
#proof_wanted M1Origin.actionAt_fork

theorem actionAt_fork {site : List Nat} {program : NCode} {options : Supervision.ForkOptions}
    (hact : actionAt root p = some (.fork program options site)) :
    program = resolve root ((p.child 0).child 0) := by
  cases a <;> simp only [actionAt, h, Option.some.injEq] at hact <;> (repeat' split at hact) <;>
    cases hact; rfl

def M1Origin.actionAt_forkIn {site : List Nat} {program : NCode} {options : Supervision.ForkOptions} {scope : Nat}
    (_hact : actionAt root p = some (.forkIn program options scope site)) : ProofGraph.Obligation (program = resolve root ((p.child 0).child 0)) := ⟨⟩
#proof_wanted M1Origin.actionAt_forkIn

theorem actionAt_forkIn {site : List Nat} {program : NCode} {options : Supervision.ForkOptions} {scope : Nat}
    (hact : actionAt root p = some (.forkIn program options scope site)) :
    program = resolve root ((p.child 0).child 0) := by
  cases a <;> simp only [actionAt, h, Option.some.injEq] at hact <;> (repeat' split at hact) <;>
    cases hact; rfl

def M1Origin.actionAt_not_forkScoped {site : List Nat} {program : NCode} {options : Supervision.ForkOptions}
    (_hact : actionAt root p = some (.forkScoped program options site)) : ProofGraph.Obligation (False) := ⟨⟩
#proof_wanted M1Origin.actionAt_not_forkScoped

theorem actionAt_not_forkScoped {site : List Nat} {program : NCode} {options : Supervision.ForkOptions}
    (hact : actionAt root p = some (.forkScoped program options site)) : False := by
  cases a <;> simp only [actionAt, h, Option.some.injEq] at hact <;> (repeat' split at hact) <;>
    cases hact

def M1Origin.actionAt_raceAll {site : Option (List Nat)} {entrants : List NCode}
    (_hact : actionAt root p = some (.raceAll entrants site)) : ProofGraph.Obligation (∃ es, a = .raceAll es ∧ entrants = actionAt.entrants es ((p.child 0).child 0)) := ⟨⟩
#proof_wanted M1Origin.actionAt_raceAll

theorem actionAt_raceAll {site : Option (List Nat)} {entrants : List NCode}
    (hact : actionAt root p = some (.raceAll entrants site)) :
    ∃ es, a = .raceAll es ∧ entrants = actionAt.entrants es ((p.child 0).child 0) := by
  cases a <;> simp only [actionAt, h, Option.some.injEq] at hact <;> (repeat' split at hact) <;>
    cases hact; exact ⟨_, rfl, rfl⟩

theorem actionAt_not_setInterruptible {body : NCode} {flag : Bool}
    (hact : actionAt root p = some (.setInterruptible body flag)) : False := by
  cases a <;> simp only [actionAt, h, Option.some.injEq] at hact <;> (repeat' split at hact) <;>
    cases hact

theorem actionAt_ambientScope (hact : actionAt root p = some .ambientScope) :
    ∃ child options, a = .forkScoped child options := by
  cases a <;> simp only [actionAt, h, Option.some.injEq] at hact <;> (repeat' split at hact) <;>
    cases hact; exact ⟨_, _, rfl⟩

theorem actionAt_not_closePar {fins : List NCode}
    (hact : actionAt root p = some (.closePar fins)) : False := by
  cases a <;> simp only [actionAt, h, Option.some.injEq] at hact <;> (repeat' split at hact) <;>
    cases hact

end actionShape

/-- `finalizerCode` and `finalizerR` are related whenever the finalizer programs are, at
the view the term resolves its construction with. -/
theorem finalizer_intro (root : NativeEff) (completed : List (FiberId × ExitV)) (ex : ExitV)
    {program : NCode} {cleanup : RProgram}
    (hc : CodeMeans root program (prepareR completed cleanup)) :
    CodeMeans root (finalizerCodeAt root completed ex program)
      (prepareR completed (finalizerR ex cleanup)) := by
  cases ex with
  | success v =>
    show CodeMeans root (Prim.onSuccess program (EffName.restore (.success v)))
      (prepareR completed ((guardR .onSuccess cleanup).bind (seqR fun _ =>
        @Effects.Program.vis RSig ExitV (Sum.inr (FiberOp.finishFinalizer (.success v)))
          Effects.Program.pure)))
    rw [prepareR_guardR_bind, guardR_bind]
    refine CodeMeans.onSuccess _ _ _ (prepareR completed cleanup) _ hc ?_ rfl (fun _ => rfl)
    intro completed' v'
    exact codeMeans_finish root (.success v) Effects.Program.pure
  | failure c =>
    show CodeMeans root
      (Prim.onSuccess (Prim.onFailure program (EffName.merge (.failure c)))
        (EffName.restore (.failure c)))
      (prepareR completed ((guardR .onSuccess ((guardR .onFailure cleanup).bind fun
          | .success v => Effects.Program.pure (.success v)
          | .failure c' =>
            Effects.Program.pure (Exit.restoreAfterFinalizer (.failure c) (.failure c')))).bind
        (seqR fun _ =>
          @Effects.Program.vis RSig ExitV (Sum.inr (FiberOp.finishFinalizer (.failure c)))
            Effects.Program.pure)))
    rw [prepareR_guardR_bind, prepareR_guardR_bind, guardR_bind]
    refine CodeMeans.onSuccess _ _ _ ((guardR .onFailure (prepareR completed cleanup)).bind _) _
      ?_ ?_ rfl (fun _ => rfl)
    · rw [guardR_bind]
      refine CodeMeans.onFailure _ _ _ (prepareR completed cleanup) _ hc ?_ rfl (fun _ => rfl)
      intro completed' c'
      exact codeMeans_ofExit_pure root (Exit.restoreAfterFinalizer (.failure c) (.failure c'))
    · intro completed' v'
      exact codeMeans_finish root (.failure c) Effects.Program.pure


end Effect4.Program.Sched
