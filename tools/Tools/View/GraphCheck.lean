import Tools.View.Graph

/-! # Located checks before graph rendering

Input admission checks node keys, edge keys, and edge positions.
Layout admission checks allocated rectangles and every route's endpoint lookup.
Keys use the renderer's Boolean String comparison.
The observations concern finite rendering data, not program typing or scheduling.
Placement: `docs/research/2026-10-13-graph-check-plan.md`, R14, concept 7, row 334 (3).
-/

namespace Tools.View.GraphCheck

inductive Site where
  | canvas | node | edge | placed | route | region
  deriving BEq

inductive Field where
  | key | source | target | vertex (index : Nat)
  | width | height | x | y | right | bottom | length | downward (index : Nat)
  deriving BEq

inductive Reason where
  | emptyKey | duplicateKey
  | endpointOutside (position count : Nat)
  | unresolvedKey (key : Key)
  | tooShort
  | negative (value : Int)
  | outside (far bound : Int)
  | doesNotDescend
  deriving BEq

/-- A refusal locates one finite rendering test, without formatting text. -/
structure Refusal where
  site : Site
  index : Nat
  field : Field
  reason : Reason
  deriving BEq

/-- One located Boolean observation. -/
structure Test where
  holds : Bool
  refusal : Refusal

private def test (site : Site) (index : Nat) (field : Field) (reason : Reason)
    (holds : Bool) : Test := ⟨holds, ⟨site, index, field, reason⟩⟩

/-- The first failing observation is the refusal. -/
def checks : List Test → Except Refusal Unit
  | [] => .ok ()
  | t :: ts => if t.holds then checks ts else .error t.refusal

/-- Admission observes every supplied test. Helper of both rendering admission laws. -/
theorem checks_iff (ts : List Test) :
    checks ts = .ok () ↔ ∀ t ∈ ts, t.holds = true := by
  induction ts with
  | nil =>
    exact ⟨fun _ t h => False.elim (List.not_mem_nil h), fun _ => rfl⟩
  | cons t ts ih =>
    cases ht : t.holds with
    | false =>
      constructor
      · intro accepted
        simp only [checks, ht, Bool.false_eq_true, if_false] at accepted
        cases accepted
      · intro all
        have head := all t (List.mem_cons_self)
        rw [ht] at head
        cases head
    | true =>
      constructor
      · intro accepted a member
        simp only [checks, ht, if_true] at accepted
        rcases List.mem_cons.mp member with rfl | tail
        · exact ht
        · exact ih.mp accepted a tail
      · intro all
        have tail := ih.mpr (fun a member => all a (List.mem_cons_of_mem t member))
        simp only [checks, ht, if_true, tail]

private def keys (site : Site) (ks : List Key) : List Test :=
  ks.zipIdx.flatMap fun (key, i) =>
    [test site i .key .emptyKey (!key.isEmpty),
     test site i .key .duplicateKey (!(ks.take i).any (· == key))]

private def inputTests (g : Graph) : List Test :=
  keys .node (g.nodes.toList.map (·.key)) ++
  keys .edge (g.edges.toList.map (·.key)) ++ g.edges.toList.zipIdx.flatMap fun (e, i) =>
    [test .edge i .source (.endpointOutside e.src g.nodes.size) (e.src < g.nodes.size),
     test .edge i .target (.endpointOutside e.dst g.nodes.size) (e.dst < g.nodes.size)]

/-- All finite input observations hold. Empty graphs are admitted. -/
def InputOK (g : Graph) : Prop := ∀ t ∈ inputTests g, t.holds = true

/-- Refuse empty or repeated node or edge keys, or endpoints outside the node array. -/
def input (g : Graph) : Except Refusal Unit := checks (inputTests g)

/-- The input arrow accepts exactly the named finite input observation. -/
theorem input_iff (g : Graph) : input g = .ok () ↔ InputOK g := checks_iff _

private def rectangle (site : Site) (index : Nat) (W H x y w h : Int) : List Test :=
  [test site index .x (.negative x) (0 ≤ x),
   test site index .y (.negative y) (0 ≤ y),
   test site index .width (.negative w) (0 ≤ w),
   test site index .height (.negative h) (0 ≤ h),
   test site index .right (.outside (x + w) W) (x + w ≤ W),
   test site index .bottom (.outside (y + h) H) (y + h ≤ H)]

private def resolves (l : Laid) (i : Nat) (field : Field) (key : Key) : Test :=
  test .route i field (.unresolvedKey key) (l.find key).isSome

private def routeTests (l : Laid) (i : Nat) : Route → List Test
  | .down _ ks _ _ =>
    test .route i .length .tooShort (2 ≤ ks.length) ::
      ks.zipIdx.map (fun (key, j) => resolves l i (.vertex j) key) ++
      (ks.zip ks.tail).zipIdx.map fun ((a, b), j) =>
        test .route i (.downward j) .doesNotDescend (l.segmentDescends a b)
  | .back _ a b _ _ => [resolves l i .source a, resolves l i .target b]
  | .loop _ a _ => [resolves l i (.vertex 0) a]

private def laidTests (l : Laid) : List Test :=
  [test .canvas 0 .width (.negative l.width) (0 ≤ l.width),
   test .canvas 0 .height (.negative l.height) (0 ≤ l.height)] ++
  keys .placed (l.placed.toList.map (·.key)) ++
  l.placed.toList.zipIdx.flatMap (fun (p, i) =>
    rectangle .placed i l.width l.height p.x p.y p.w
      (if p.node.isSome then ROWH * BOXROWS else 0)) ++
  l.regions.toList.zipIdx.flatMap (fun (r, i) =>
    rectangle .region i l.width l.height r.x r.y r.w r.h) ++
  l.routes.toList.zipIdx.flatMap fun (r, i) => routeTests l i r

/-- Every allocated rectangle and route lookup satisfies its finite rendering test.
This observation excludes curve, stroke, text and mark ink bounds. -/
def LaidOK (l : Laid) : Prop := ∀ t ∈ laidTests l, t.holds = true

/-- Refuse invalid allocation data or unresolved routes, including back and loop routes. -/
def laid (l : Laid) : Except Refusal Unit := checks (laidTests l)

/-- The layout arrow accepts exactly the named finite rendering observation. -/
theorem laid_iff (l : Laid) : laid l = .ok () ↔ LaidOK l := checks_iff _

/-- Rendering data with input and allocation evidence, independent of its layout producer.
Placement: `docs/research/2026-10-13-graph-library-plan.md`, R14, concept 7, row 334 (3). -/
structure Checked (g : Graph) where
  value : Laid
  input_ok : InputOK g
  allocation_ok : LaidOK value

end Tools.View.GraphCheck
