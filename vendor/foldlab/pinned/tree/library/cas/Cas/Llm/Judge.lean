/-!
# The semantic judge — human meaning as an uninterpreted function

The trunk's derived names are produced by a naming homomorphism into
strings: a structure's name is its parent's name concatenated with its
own segment, so names live in the free monoid `(String, ++, "")`. A
SEMANTIC JUDGE is a frozen human-meaning judgment over those strings —
operationally one pinned, receipted completion call.

The judge is an UNINTERPRETED FUNCTION, exactly as the store
quantifies over the hash `H`. Its trust contribution is empty: nothing
proves it right, and every theorem here is conditional on a NAMED
hypothesis about it. That is the judge-hypothesis lattice, parallel to
the hash-hypothesis lattice (CAS-003).

- **Level 0 — nothing assumed.** `J` is an arbitrary predicate on
  names; acceptance is a bare filter and no structure survives it.
- **Level 1 — STABLE** (`Judge.Stable`, defined in `JudgeRate`):
  invariance under semantically-inert variation of a name. Everything
  above presupposes it.
- **Level 2 — `Judge.Compositional`.** Frege's principle stated OF the
  judge: the empty name is accepted, and a compound is judged by its
  parts. Equivalently `J` is a monoid morphism
  `(String, ++, "") → (Bool, &&, true)` — a functor between the
  one-object categories, which is where the word functor is earned.
- **Level 3 — LIMIT-STABLE** (owed(judge-limit-stable): definition): acceptance survives the
  directed growth of accepted prefixes — the closure a bounded-context
  judge fails on unbounded input. The ladder was renumbered 2026-08-30
  (decision 38) on two independent literature votes.

Under Level 2 acceptance carves a SUBALGEBRA out of any named algebra
(`Judge.accepts_op`), rejection propagates upward
(`Judge.rejects_infects`), and it localizes (`Judge.blame`), so a
front end may bisect a nonsensical label to the segment that fails.
Nothing above Level 2 is stated here.

A practical judgment is a UNION OF PARALLEL CHEAP CALLS — a `Panel`,
which freezes to one judge through its AGGREGATOR, so the lattice
applies to the aggregate rather than to the members. The aggregator is
what decides whether Level 2 survives: `Panel.all` (intersection)
preserves it, `Panel.any` (union) demonstrably does not, and the union
is the shape practice reaches for. For a union panel Level 2 is
re-MEASURED of the aggregate, never inherited.

Verdicts SELECT, never prove. The accepted set is human-legible by
MEASUREMENT: Level 2 is an empirical property of one frozen judge on
one name fragment, carried here as a premise in exactly the way an
injectivity premise on `H` is carried.

The naming function is a PARAMETER throughout, so this module depends
on nothing in the store — the same move `Word.columnBy` makes with its
classifier.
-/

namespace Cas.Llm

/-- One FROZEN judgment: a pinned model, prompt and parameters — a
receipted call, and the same name always gets the same verdict. A real
LLM is a DISTRIBUTION over judges; the distribution is a later level of
the lattice and is never modeled here. -/
def Judge : Type := String → Bool

/-- Level 2 of the judge-hypothesis lattice (renumbered 2026-08-30,
decision 38: STABLE sits below this, LIMIT-STABLE above): Frege's
principle stated of the judge. The two clauses are exactly the monoid-morphism
conditions for `(String, ++, "") → (Bool, &&, true)` — unit and
multiplication — so a compositional judge is a functor between the
one-object categories. This is a hypothesis ABOUT a measured artifact,
never a fact about one. -/
def Judge.Compositional (J : Judge) : Prop :=
  J "" = true ∧ ∀ s t : String, J (s ++ t) = (J s && J t)

/-- Acceptance of a named thing, through whatever naming function the
algebra supplies. `name` is a parameter, so what follows holds of every
naming homomorphism a front end derives — grammar word, view relation,
alias table — and of no fixed one. -/
def Judge.accepts (J : Judge) {α : Type} (name : α → String) (x : α) : Prop :=
  J (name x) = true

/-- The SUBALGEBRA closure: where names concatenate along an operation,
accepted structures compose to accepted structures. The front end reads
this as licence to build with `op` inside the accepted region without
leaving it. Conditional on Level 2, which for a real judge is measured,
not given. -/
theorem Judge.accepts_op {J : Judge} (hJ : J.Compositional) {α : Type}
    {op : α → α → α} {name : α → String}
    (hname : ∀ a b, name (op a b) = name a ++ name b)
    {a b : α} (ha : J.accepts name a) (hb : J.accepts name b) :
    J.accepts name (op a b) := by
  have ha' : J (name a) = true := ha
  have hb' : J (name b) = true := hb
  show J (name (op a b)) = true
  rw [hname, hJ.2, ha', hb']
  rfl

/-- Poisoning: one meaningless segment rejects every compound it enters.
The front end reads this as the reason to surface a rejected segment at
its origin — no compound built over it recovers. Level 2 again. -/
theorem Judge.rejects_infects {J : Judge} (hJ : J.Compositional) {s t : String}
    (h : J s = false) : J (s ++ t) = false := by
  rw [hJ.2, h, Bool.false_and]

/-- Blame localizes: a rejected compound has a rejected part, so a front
end may BISECT a nonsensical label down to the segment that fails —
semantic debugging as binary search. Level 2 again, and the bisection is
only ever as good as that measurement. -/
theorem Judge.blame {J : Judge} (hJ : J.Compositional) {s t : String}
    (h : J (s ++ t) = false) : J s = false ∨ J t = false := by
  rw [hJ.2] at h
  exact Bool.and_eq_false_iff.mp h

/-! ## The panel — a judgment as parallel cheap calls -/

-- `abbrev`, not `def`: `∀ J ∈ P` resolves `Membership Judge Panel` by
-- instance search, which only a reducible alias supplies.
/-- A practical judgment is a UNION OF PARALLEL CHEAP CALLS. A panel
FREEZES to one judge through its aggregator, so the judge-hypothesis
lattice above applies to the AGGREGATE and not to the members — and
which aggregator is chosen is what decides whether Level 2 survives. -/
abbrev Panel : Type := List Judge

/-- The union aggregator: accepted when ANY member accepts. This is the
practical shape — coverage and robustness, one member's blind spot
covered by another's competence — and `any_not_compositional` is what it
costs. -/
def Panel.any (P : Panel) : Judge := fun s => List.any P (fun J => J s)

/-- The unanimity aggregator: accepted when EVERY member accepts.
Intersection, and intersection is what preserves Level 2. The empty
panel accepts everything. -/
def Panel.all (P : Panel) : Judge := fun s => List.all P (fun J => J s)

/-- INTERSECTION PRESERVES LEVEL 2: a panel of compositional members
aggregates to a compositional judge, so a unanimity panel keeps the
subalgebra closure and the blame bisection whole. The induction runs
over the panel, and the empty panel is compositional for free. -/
theorem Panel.all_compositional {P : Panel} (h : ∀ J ∈ P, J.Compositional) :
    (Panel.all P).Compositional := by
  induction P with
  | nil => exact ⟨rfl, fun _ _ => rfl⟩
  | cons J rest ih =>
    have hJ : J.Compositional := h J (List.mem_cons_self ..)
    obtain ⟨hε, hcat⟩ := ih fun K hK => h K (List.mem_cons_of_mem J hK)
    refine ⟨?_, fun s t => ?_⟩
    · show (J "" && Panel.all rest "") = true
      rw [hJ.1, Bool.true_and]
      exact hε
    · show (J (s ++ t) && Panel.all rest (s ++ t))
          = ((J s && Panel.all rest s) && (J t && Panel.all rest t))
      rw [hJ.2, hcat]
      cases J s <;> cases J t <;> cases Panel.all rest s <;>
        cases Panel.all rest t <;> rfl

/-- Coverage: the union accepts whatever any member accepts. That is the
whole benefit of the union shape, and it is Level 0 — no hypothesis on
any member. -/
theorem Panel.any_accepts {P : Panel} {J : Judge} (hJ : J ∈ P) {s : String}
    (h : J s = true) : Panel.any P s = true :=
  List.any_eq_true.mpr ⟨J, hJ, h⟩

/-- UNION DOES NOT PRESERVE LEVEL 2, exhibited rather than asserted: two
members that each accept only their own letter are both compositional,
both single letters are accepted by the union, and the two-letter
compound is accepted by neither. So for a union panel — the practical
shape — Level 2 must be re-MEASURED of the aggregate, and the members'
compositionality buys none of it. Quorum and majority aggregators carry
the same caveat; neither is defined here. -/
theorem Panel.any_not_compositional :
    ∃ (P : Panel) (s t : String), (∀ J ∈ P, J.Compositional) ∧
      Panel.any P s = true ∧ Panel.any P t = true ∧
      Panel.any P (s ++ t) = false := by
  have letter : ∀ c : Char,
      Judge.Compositional (fun s => s.toList.all (· == c)) := by
    intro c
    refine ⟨rfl, fun s t => ?_⟩
    show (s ++ t).toList.all (· == c)
        = (s.toList.all (· == c) && t.toList.all (· == c))
    rw [String.toList_append, List.all_append]
  refine ⟨[fun s => s.toList.all (· == 'a'), fun s => s.toList.all (· == 'b')],
    "a", "b", ?_, rfl, rfl, ?_⟩
  · intro J hJ
    cases hJ with
    | head => exact letter 'a'
    | tail _ hJ' =>
      cases hJ' with
      | head => exact letter 'b'
      | tail _ hJ'' => cases hJ''
  · show ((("a" ++ "b").toList.all (· == 'a'))
      || ((("a" ++ "b").toList.all (· == 'b')) || false)) = false
    rw [String.toList_append]
    rfl

end Cas.Llm
