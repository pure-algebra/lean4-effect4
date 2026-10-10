/-!
# Checked finite paths

`Walk` keeps the consumer's edge occurrences and fixes their endpoints in its type.
The consumer supplies the edge alphabet and its endpoint interpretation.
The library introduces no graph or program representation.

These named tool laws serve `initial-algebras-folds`, concept 7, and R14 navigation.
Decisions row 336, point 8, places them outside registry claims.
The placement is `docs/research/2026-10-10-checked-graph-tools/PLAN.md`.
Flow wait-cycle explanations consume admission and composition.
Proof dependency explanations may reuse the same operations.

A refused supplied path is malformed for the requested endpoints.
It establishes no absence of other paths and no scheduler property.
-/

namespace Tools.Graph

universe u v w

/-- Finite path data over an existing edge alphabet, indexed by both endpoints. -/
inductive Walk {V : Type u} {E : Type v} (endpoints : E → V × V) : V → V → Type (max u v) where
  | refl (a : V) : Walk endpoints a a
  | cons (e : E) {b : V} (tail : Walk endpoints (endpoints e).2 b) :
      Walk endpoints (endpoints e).1 b

namespace Walk

variable {V : Type u} {E : Type v} {endpoints : E → V × V}
variable {a b c : V}

/-- Interpret a path in an endpoint-indexed carrier.
This helper serves composition, admission, and the Flow reachability interpreter. -/
def fold (C : V → V → Sort w) (onRefl : ∀ a, C a a)
    (onCons : ∀ (e : E) {b : V}, C (endpoints e).2 b → C (endpoints e).1 b) :
    {a b : V} → Walk endpoints a b → C a b
  | _, _, .refl a => onRefl a
  | _, _, .cons e tail => onCons e (fold C onRefl onCons tail)

/-- Forget endpoint evidence, retaining every edge occurrence in order. -/
def edges (path : Walk endpoints a b) : List E :=
  path.fold (fun _ _ => List E) (fun _ => []) (fun e _ tail => e :: tail)

/-- One edge as a path between its interpreted endpoints. -/
def edge (endpoints : E → V × V) (e : E) :
    Walk endpoints (endpoints e).1 (endpoints e).2 :=
  .cons e (.refl _)

/-- Compose at a shared endpoint without changing either component's occurrences. -/
def append (first : Walk endpoints a b) (second : Walk endpoints b c) :
    Walk endpoints a c :=
  first.fold (fun x y => Walk endpoints y c → Walk endpoints x c)
    (fun _ second => second) (fun e _ tail second => .cons e (tail second)) second

/-- Path composition retains the first list followed by the second list. -/
theorem edges_append (first : Walk endpoints a b) (second : Walk endpoints b c) :
    (append first second).edges = first.edges ++ second.edges := by
  induction first with
  | refl => rfl
  | cons e tail ih =>
      exact congrArg (List.cons e) (ih second)

/-- Admit precisely the supplied occurrences when their endpoints form the requested path. -/
def read? [DecidableEq V] (endpoints : E → V × V) (a b : V) :
    List E → Option (Walk endpoints a b)
  | [] => if h : a = b then some (h ▸ .refl a) else none
  | e :: rest =>
      if h : a = (endpoints e).1 then
        match read? endpoints (endpoints e).2 b rest with
        | none => none
        | some tail => some (h.symm ▸ .cons e tail)
      else none

/-- Every path is accepted from its own edge list, including repeated occurrences. -/
theorem read?_edges [DecidableEq V] (path : Walk endpoints a b) :
    read? endpoints a b path.edges = some path := by
  induction path with
  | refl a =>
      change read? endpoints a a [] = some (.refl a)
      simp only [read?, ↓reduceDIte]
  | cons e tail ih =>
      change read? endpoints (endpoints e).1 _ (e :: tail.edges) = some (.cons e tail)
      simp only [read?, ↓reduceDIte, ih]

/-- A successful reader retains the supplied edge list exactly. -/
theorem edges_of_read? [DecidableEq V] (supplied : List E)
    (path : Walk endpoints a b) (accepted : read? endpoints a b supplied = some path) :
    path.edges = supplied := by
  induction supplied generalizing a with
  | nil =>
      simp only [read?] at accepted
      split at accepted
      next h =>
        cases h
        cases accepted
        rfl
      next => cases accepted
  | cons e rest ih =>
      simp only [read?] at accepted
      split at accepted
      next h =>
        cases h
        cases ht : read? endpoints (endpoints e).2 b rest with
        | none => simp only [ht] at accepted; cases accepted
        | some tail =>
            simp only [ht] at accepted
            cases accepted
            exact congrArg (List.cons e) (ih tail ht)
      next => cases accepted

end Walk
end Tools.Graph
