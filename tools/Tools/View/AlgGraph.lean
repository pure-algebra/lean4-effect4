/-!
# The algebraic graph (slice D1)

Slice D1 of `docs/research/2026-10-09-program-graph-design.md`, placed in its section 6. A graph
is built from four constructors: the empty graph, a vertex, the overlay of two graphs, and the
connection of two, which adds an edge from each vertex of the first to each vertex of the second
(Mokhov, *Algebraic graphs with class*, Haskell Symposium 2017). No expression denotes a malformed
graph: an edge's ends are always vertices of the graph.

**The model.** A graph denotes its vertices and its edges, as predicates (`AGraph.denote`): the
edge-set model of the paper, which is a fold of the four constructors. Two graphs are equal when
they denote the same vertices and edges.

**The laws.** The eight axioms of the paper hold of the model, as equalities: overlay is
commutative and associative; connect is associative and has the empty graph on both sides as its
unit; connect distributes over overlay on both sides; and a chain of three connects decomposes
into its three pairs. The paper derives idempotence of overlay and absorption from them; both are
stated here of the model too. Each is a tool's named law (decisions row 336, point 8), serving
concept 7 of `docs/core/semantics.md` (`initial-algebras-folds`). The consumer is the order of a
flow (`Tools.View.Flow.Flow.order`), a fold of the flow into this algebra, and the law that the
layout keeps it (`Tools.View.Flow.lay_keeps_order`).
-/

namespace Tools.View

/-- **An algebraic graph** over vertices of `α`. -/
inductive AGraph (α : Type) where
  | empty
  | vertex (a : α)
  | overlay (x y : AGraph α)
  | connect (x y : AGraph α)

/-- A graph as its vertices and its edges. -/
structure Rel (α : Type) where
  has : α → Prop
  edge : α → α → Prop

namespace AGraph

variable {α : Type}

/-- **The edge-set model**: the vertices and the edges a graph denotes. -/
def denote : AGraph α → Rel α
  | .empty => ⟨fun _ => False, fun _ _ => False⟩
  | .vertex a => ⟨fun b => b = a, fun _ _ => False⟩
  | .overlay x y => ⟨fun b => (denote x).has b ∨ (denote y).has b,
      fun a b => (denote x).edge a b ∨ (denote y).edge a b⟩
  | .connect x y => ⟨fun b => (denote x).has b ∨ (denote y).has b,
      fun a b => (denote x).edge a b ∨ (denote y).edge a b ∨ ((denote x).has a ∧ (denote y).has b)⟩

/-- Two models are equal when they have the same vertices and the same edges. -/
theorem Rel.ext' {r s : Rel α} (h1 : ∀ a, r.has a ↔ s.has a) (h2 : ∀ a b, r.edge a b ↔ s.edge a b) : r = s := by
  cases r; cases s
  congr
  · funext a; exact propext (h1 a)
  · funext a b; exact propext (h2 a b)

/-- An edge's ends are vertices of the graph: no expression denotes a malformed graph. -/
theorem edge_has : ∀ (x : AGraph α) {a b : α}, (denote x).edge a b → (denote x).has a ∧ (denote x).has b
  | .empty, _, _, h => h.elim
  | .vertex _, _, _, h => h.elim
  | .overlay x y, _, _, h => by
    rcases h with h | h
    · exact ⟨.inl (edge_has x h).1, .inl (edge_has x h).2⟩
    · exact ⟨.inr (edge_has y h).1, .inr (edge_has y h).2⟩
  | .connect x y, _, _, h => by
    rcases h with h | h | ⟨ha, hb⟩
    · exact ⟨.inl (edge_has x h).1, .inl (edge_has x h).2⟩
    · exact ⟨.inr (edge_has y h).1, .inr (edge_has y h).2⟩
    · exact ⟨.inl ha, .inr hb⟩

/-! ## Mokhov's eight axioms, of the model -/

theorem overlay_comm (x y : AGraph α) : denote (overlay x y) = denote (overlay y x) :=
  Rel.ext' (fun _ => Or.comm) (fun _ _ => Or.comm)

theorem overlay_assoc (x y z : AGraph α) :
    denote (overlay x (overlay y z)) = denote (overlay (overlay x y) z) :=
  Rel.ext' (fun _ => or_assoc.symm) (fun _ _ => or_assoc.symm)

theorem empty_connect (x : AGraph α) : denote (connect empty x) = denote x := by
  refine Rel.ext' (fun _ => ⟨fun h => h.elim False.elim id, .inr⟩) (fun _ _ => ⟨fun h => ?_, fun h => .inr (.inl h)⟩)
  rcases h with h | h | ⟨h, _⟩
  · exact h.elim
  · exact h
  · exact h.elim

theorem connect_empty (x : AGraph α) : denote (connect x empty) = denote x := by
  refine Rel.ext' (fun _ => ⟨fun h => h.elim id False.elim, .inl⟩) (fun _ _ => ⟨fun h => ?_, fun h => .inl h⟩)
  rcases h with h | h | ⟨_, h⟩
  · exact h
  · exact h.elim
  · exact h.elim

theorem connect_assoc (x y z : AGraph α) :
    denote (connect x (connect y z)) = denote (connect (connect x y) z) := by
  refine Rel.ext' (fun _ => or_assoc.symm) (fun a b => ⟨fun h => ?_, fun h => ?_⟩)
  · rcases h with h | (h | h | ⟨ha, hb⟩) | ⟨ha, hb | hb⟩
    · exact .inl (.inl h)
    · exact .inl (.inr (.inl h))
    · exact .inr (.inl h)
    · exact .inr (.inr ⟨.inr ha, hb⟩)
    · exact .inl (.inr (.inr ⟨ha, hb⟩))
    · exact .inr (.inr ⟨.inl ha, hb⟩)
  · rcases h with (h | h | ⟨ha, hb⟩) | h | ⟨ha | ha, hb⟩
    · exact .inl h
    · exact .inr (.inl (.inl h))
    · exact .inr (.inr ⟨ha, .inl hb⟩)
    · exact .inr (.inl (.inr (.inl h)))
    · exact .inr (.inr ⟨ha, .inr hb⟩)
    · exact .inr (.inl (.inr (.inr ⟨ha, hb⟩)))

theorem connect_overlay (x y z : AGraph α) :
    denote (connect x (overlay y z)) = denote (overlay (connect x y) (connect x z)) := by
  refine Rel.ext' (fun a => ⟨fun h => ?_, fun h => ?_⟩) (fun a b => ⟨fun h => ?_, fun h => ?_⟩)
  · rcases h with h | h | h
    · exact .inl (.inl h)
    · exact .inl (.inr h)
    · exact .inr (.inr h)
  · rcases h with (h | h) | (h | h)
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inl h
    · exact .inr (.inr h)
  · rcases h with h | (h | h) | ⟨ha, hb | hb⟩
    · exact .inl (.inl h)
    · exact .inl (.inr (.inl h))
    · exact .inr (.inr (.inl h))
    · exact .inl (.inr (.inr ⟨ha, hb⟩))
    · exact .inr (.inr (.inr ⟨ha, hb⟩))
  · rcases h with (h | h | ⟨ha, hb⟩) | (h | h | ⟨ha, hb⟩)
    · exact .inl h
    · exact .inr (.inl (.inl h))
    · exact .inr (.inr ⟨ha, .inl hb⟩)
    · exact .inl h
    · exact .inr (.inl (.inr h))
    · exact .inr (.inr ⟨ha, .inr hb⟩)

theorem overlay_connect (x y z : AGraph α) :
    denote (connect (overlay x y) z) = denote (overlay (connect x z) (connect y z)) := by
  refine Rel.ext' (fun a => ⟨fun h => ?_, fun h => ?_⟩) (fun a b => ⟨fun h => ?_, fun h => ?_⟩)
  · rcases h with (h | h) | h
    · exact .inl (.inl h)
    · exact .inr (.inl h)
    · exact .inl (.inr h)
  · rcases h with (h | h) | (h | h)
    · exact .inl (.inl h)
    · exact .inr h
    · exact .inl (.inr h)
    · exact .inr h
  · rcases h with (h | h) | h | ⟨ha | ha, hb⟩
    · exact .inl (.inl h)
    · exact .inr (.inl h)
    · exact .inl (.inr (.inl h))
    · exact .inl (.inr (.inr ⟨ha, hb⟩))
    · exact .inr (.inr (.inr ⟨ha, hb⟩))
  · rcases h with (h | h | ⟨ha, hb⟩) | (h | h | ⟨ha, hb⟩)
    · exact .inl (.inl h)
    · exact .inr (.inl h)
    · exact .inr (.inr ⟨.inl ha, hb⟩)
    · exact .inl (.inr h)
    · exact .inr (.inl h)
    · exact .inr (.inr ⟨.inr ha, hb⟩)

theorem decompose (x y z : AGraph α) :
    denote (connect (connect x y) z) =
      denote (overlay (overlay (connect x y) (connect x z)) (connect y z)) := by
  refine Rel.ext' (fun a => ⟨fun h => ?_, fun h => ?_⟩) (fun a b => ⟨fun h => ?_, fun h => ?_⟩)
  · rcases h with (h | h) | h
    · exact .inl (.inl (.inl h))
    · exact .inl (.inl (.inr h))
    · exact .inr (.inr h)
  · rcases h with ((h | h) | (h | h)) | (h | h)
    · exact .inl (.inl h)
    · exact .inl (.inr h)
    · exact .inl (.inl h)
    · exact .inr h
    · exact .inl (.inr h)
    · exact .inr h
  · rcases h with (h | h | ⟨ha, hb⟩) | h | ⟨ha | ha, hb⟩
    · exact .inl (.inl (.inl h))
    · exact .inl (.inl (.inr (.inl h)))
    · exact .inl (.inl (.inr (.inr ⟨ha, hb⟩)))
    · exact .inr (.inr (.inl h))
    · exact .inl (.inr (.inr (.inr ⟨ha, hb⟩)))
    · exact .inr (.inr (.inr ⟨ha, hb⟩))
  · rcases h with ((h | h | ⟨ha, hb⟩) | (h | h | ⟨ha, hb⟩)) | (h | h | ⟨ha, hb⟩)
    · exact .inl (.inl h)
    · exact .inl (.inr (.inl h))
    · exact .inl (.inr (.inr ⟨ha, hb⟩))
    · exact .inl (.inl h)
    · exact .inr (.inl h)
    · exact .inr (.inr ⟨.inl ha, hb⟩)
    · exact .inl (.inr (.inl h))
    · exact .inr (.inl h)
    · exact .inr (.inr ⟨.inr ha, hb⟩)

/-! ## Two consequences, of the model -/

theorem overlay_idem (x : AGraph α) : denote (overlay x x) = denote x :=
  Rel.ext' (fun _ => or_self_iff) (fun _ _ => or_self_iff)

theorem absorb (x y : AGraph α) : denote (overlay (overlay (connect x y) x) y) = denote (connect x y) := by
  refine Rel.ext' (fun a => ⟨fun h => ?_, fun h => ?_⟩) (fun a b => ⟨fun h => ?_, fun h => ?_⟩)
  · rcases h with (h | h) | h
    · exact h
    · exact .inl h
    · exact .inr h
  · exact .inl (.inl h)
  · rcases h with (h | h) | h
    · exact h
    · exact .inl h
    · exact .inr (.inl h)
  · exact .inl (.inl h)

end AGraph

end Tools.View
