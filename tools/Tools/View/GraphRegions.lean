import Tools.View.Picture
import Tools.View.KeyMap

/-!
# Explicit region membership and finite display projection

The parent-before-child region array and direct owner array contain caller data.
Projection retains every edge occurrence, including hidden internal edges.
No path or execution interpretation follows from a display quotient.
Placement: `docs/research/2026-10-13-graph-regions-plan.md`, concept 7, R14.
-/

namespace Tools.View.GraphRegions

structure RegionDecl where
  key : Key
  parent : Option Nat := none
  deriving DecidableEq, Repr

structure Membership where
  regions : Array RegionDecl
  owner : Array (Option Nat)
  deriving DecidableEq, Repr

inductive Representative where
  | node (index : Nat)
  | region (index : Nat)
  deriving DecidableEq, Repr

inductive Refusal where
  | selectionSize (actual expected : Nat)
  | emptyKey (region : Nat)
  | duplicateKey (region : Nat) (key : Key)
  | parentNotEarlier (region parent : Nat)
  | ownerOutside (vertex owner count : Nat)
  | endpointOutside (edge : Nat) (source : Bool) (endpoint count : Nat)
  | unresolvedVisible (vertex visible count : Nat)
  deriving DecidableEq, Repr

/-- One finite metadata observation and its located refusal. -/
structure Test where
  holds : Bool
  refusal : Refusal

/-- Admission observes each supplied test in order. -/
def checks : List Test → Except Refusal Unit
  | [] => .ok ()
  | test :: rest => if test.holds then checks rest else .error test.refusal

/-- Admission accepts exactly the finite observations it receives.
The membership preparation consumer supplies structural and bound observations. -/
theorem checks_iff (tests : List Test) :
    checks tests = .ok () ↔ ∀ t ∈ tests, t.holds = true := by
  induction tests with
  | nil => exact ⟨fun _ _ member => False.elim (List.not_mem_nil member), fun _ => rfl⟩
  | cons t ts ih =>
    cases h : t.holds with
    | false =>
      constructor
      · intro accepted
        simp only [checks, h, Bool.false_eq_true, if_false] at accepted
        cases accepted
      · intro all
        have head := all t List.mem_cons_self
        rw [h] at head
        cases head
    | true =>
      constructor
      · intro accepted a member
        simp only [checks, h, if_true] at accepted
        rcases List.mem_cons.mp member with rfl | tail
        · exact h
        · exact ih.mp accepted a tail
      · intro all
        have tail := ih.mpr (fun a member => all a (List.mem_cons_of_mem t member))
        simp only [checks, h, if_true, tail]

/-- Finite preparation observations, including first occurrence of each region key. -/
def tests (membership : Membership) (selected : Array Bool) : List Test :=
  let first := KeyMap.firstBy (fun p : RegionDecl × Nat => p.1.key)
    membership.regions.toList.zipIdx
  [⟨selected.size == membership.regions.size,
      .selectionSize selected.size membership.regions.size⟩] ++
    membership.regions.toList.zipIdx.flatMap (fun (decl, i) =>
      [⟨!decl.key.isEmpty, .emptyKey i⟩,
       ⟨((first.get? decl.key).map (·.2)) == some i, .duplicateKey i decl.key⟩] ++
      match decl.parent with
      | none => []
      | some parent => [⟨parent < i, .parentNotEarlier i parent⟩]) ++
    membership.owner.toList.zipIdx.flatMap fun (owner, vertex) =>
      match owner with
      | none => []
      | some region => [⟨region < membership.regions.size,
          .ownerOutside vertex region membership.regions.size⟩]

/-- The named finite structural observation for region preparation. -/
def MembershipOK (membership : Membership) (selected : Array Bool) : Prop :=
  ∀ t ∈ tests membership selected, t.holds = true

/-- Retained display arrays; arbitrary raw records carry no ancestry or partition guarantee.
Only `prepare` performs membership admission; `project` additionally checks endpoint/map bounds. -/
structure Prepared where
  membership : Membership
  selected : Array Bool
  outer : Array (Option Nat)
  visible : Array Representative
  nodeMap : Array Nat
  members : Array (Array Nat)
  deriving Repr

/-- Prepare selected ancestry and stable representative/member arrays after admission. -/
private def prepareData (membership : Membership) (selected : Array Bool) : Prepared := Id.run do
  let mut outer : Array (Option Nat) := #[]
  for (decl, i) in membership.regions.toList.zipIdx do
    let ancestor := decl.parent.bind fun parent => (outer[parent]?).getD none
    outer := outer.push (ancestor.orElse fun _ => if selected[i]?.getD false then some i else none)
  let mut visible : Array Representative := #[]
  let mut nodeMap : Array Nat := #[]
  let mut members : Array (Array Nat) := #[]
  let mut regionPosition : Array (Option Nat) := Array.replicate membership.regions.size none
  for (owner, vertex) in membership.owner.toList.zipIdx do
    let region := owner.bind fun owner => (outer[owner]?).getD none
    match region with
    | none =>
      nodeMap := nodeMap.push visible.size
      visible := visible.push (.node vertex)
      members := members.push #[vertex]
    | some region =>
      match (regionPosition[region]?).getD none with
      | some position =>
        nodeMap := nodeMap.push position
        members := members.modify position (fun xs => xs.push vertex)
      | none =>
        let position := visible.size
        regionPosition := regionPosition.set! region (some position)
        nodeMap := nodeMap.push position
        visible := visible.push (.region region)
        members := members.push #[vertex]
  for i in List.range membership.regions.size do
    if (outer[i]?).getD none == some i && ((regionPosition[i]?).getD none).isNone then
      visible := visible.push (.region i)
      members := members.push #[]
  return ⟨membership, selected, outer, visible, nodeMap, members⟩

/-- Located admission precedes the display projection preparation. -/
def prepare (membership : Membership) (selected : Array Bool) : Except Refusal Prepared :=
  (checks (tests membership selected)).map fun _ => prepareData membership selected

/-- A checked preparation accepts exactly its named finite structural observations. -/
theorem prepare_iff (membership : Membership) (selected : Array Bool) :
    (∃ prepared, prepare membership selected = .ok prepared) ↔ MembershipOK membership selected := by
  unfold prepare MembershipOK
  cases h : checks (tests membership selected) with
  | error refusal =>
    constructor
    · rintro ⟨p, impossible⟩
      cases impossible
    · intro all
      have accepted := (checks_iff _).mpr all
      rw [h] at accepted
      cases accepted
  | ok result =>
    constructor
    · intro _
      apply (checks_iff _).mp
      cases result
      exact h
    · intro _
      exact ⟨prepareData membership selected, rfl⟩

structure EdgeOccurrence (E : Type) where
  occurrence : Nat
  original : E
  originalSource : Nat
  originalTarget : Nat
  source : Nat
  target : Nat
  hidden : Bool
  deriving Repr

/-- Read an admitted source vertex's visible ordinal; reject malformed raw prepared maps. -/
def position (prepared : Prepared) (edge : Nat) (isSource : Bool) (vertex : Nat) : Except Refusal Nat :=
  if vertex < prepared.membership.owner.size then
    match prepared.nodeMap[vertex]? with
    | none => .error (.unresolvedVisible vertex prepared.visible.size prepared.visible.size)
    | some visible => if visible < prepared.visible.size then .ok visible
      else .error (.unresolvedVisible vertex visible prepared.visible.size)
  else .error (.endpointOutside edge isSource vertex prepared.membership.owner.size)

/-- Only an edge whose ends share one collapsed region hides; original self-loops remain visible. -/
def hidden (prepared : Prepared) (source target : Nat) : Bool :=
  source == target && match prepared.visible[source]? with
    | some (.region _) => true
    | _ => false

/-- Project one edge occurrence and retain its complete original payload and endpoints. -/
def projectEdge {E : Type} (prepared : Prepared) (source target : E → Nat)
    (index : Nat) (edge : E) : Except Refusal (EdgeOccurrence E) := do
  let a := source edge
  let b := target edge
  let src ← position prepared index true a
  let dst ← position prepared index false b
  return ⟨index, edge, a, b, src, dst, hidden prepared src dst⟩

private def projectList {E : Type} (prepared : Prepared) (source target : E → Nat) :
    Nat → List E → Except Refusal (List (EdgeOccurrence E))
  | _, [] => .ok []
  | i, edge :: rest => do
    let projected ← projectEdge prepared source target i edge
    let tail ← projectList prepared source target (i + 1) rest
    return projected :: tail

/-- Every accepted occurrence retains its original payload.
Helper of `project_originals`, consumed by the graph materializer. -/
theorem projectEdge_original {E : Type} (prepared : Prepared) (source target : E → Nat)
    (index : Nat) (edge : E) (projected : EdgeOccurrence E)
    (accepted : projectEdge prepared source target index edge = .ok projected) :
    projected.original = edge := by
  unfold projectEdge at accepted
  cases ha : position prepared index true (source edge) <;>
    cases hb : position prepared index false (target edge) <;>
    simp only [ha, hb] at accepted
  · cases accepted
  · cases accepted
  · cases accepted
  · cases accepted
    rfl

/-- The original occurrence observation, independent of display endpoints. -/
def EdgeOccurrence.provenance {E : Type} (edge : EdgeOccurrence E) : Nat × E × Nat × Nat :=
  (edge.occurrence, edge.original, edge.originalSource, edge.originalTarget)

/-- One accepted edge retains its complete original occurrence observation.
Helper of `project_provenance`, consumed by the graph adapter. -/
theorem projectEdge_provenance {E : Type} (prepared : Prepared) (source target : E → Nat)
    (index : Nat) (edge : E) (projected : EdgeOccurrence E)
    (accepted : projectEdge prepared source target index edge = .ok projected) :
    projected.provenance = (index, edge, source edge, target edge) := by
  unfold projectEdge at accepted
  cases ha : position prepared index true (source edge) <;>
    cases hb : position prepared index false (target edge) <;>
    simp only [ha, hb] at accepted
  · cases accepted
  · cases accepted
  · cases accepted
  · cases accepted
    rfl

private theorem projectList_provenance {E : Type} (prepared : Prepared) (source target : E → Nat)
    (index : Nat) (edges : List E) (projected : List (EdgeOccurrence E))
    (accepted : projectList prepared source target index edges = .ok projected) :
    projected.map EdgeOccurrence.provenance =
      (edges.zipIdx index).map (fun (e, i) => (i, e, source e, target e)) := by
  induction edges generalizing index projected with
  | nil =>
    cases accepted
    rfl
  | cons edge edges ih =>
    cases head : projectEdge prepared source target index edge with
    | error refusal =>
      simp only [projectList, head] at accepted
      cases accepted
    | ok first =>
      cases tail : projectList prepared source target (index + 1) edges with
      | error refusal =>
        simp only [projectList, head, tail] at accepted
        cases accepted
      | ok rest =>
        simp only [projectList, head, tail] at accepted
        cases accepted
        simp only [List.map_cons, List.zipIdx_cons,
          projectEdge_provenance prepared source target index edge first head,
          ih (index + 1) rest tail]

/-- Preserve every edge occurrence, in source order, including hidden internal edges. -/
def project {E : Type} (prepared : Prepared) (edges : Array E) (source target : E → Nat) :
    Except Refusal (Array (EdgeOccurrence E)) :=
  (projectList prepared source target 0 edges.toList).map List.toArray

/-- Accepted projection retains every original edge occurrence, endpoint, and payload in order.
This observation supplies no agreement of paths through collapsed regions. -/
theorem project_provenance {E : Type} (prepared : Prepared) (edges : Array E) (source target : E → Nat)
    (projected : Array (EdgeOccurrence E))
    (accepted : project prepared edges source target = .ok projected) :
    projected.toList.map EdgeOccurrence.provenance =
      (edges.toList.zipIdx).map (fun (e, i) => (i, e, source e, target e)) := by
  unfold project at accepted
  cases found : projectList prepared source target 0 edges.toList with
  | error refusal =>
    simp only [found] at accepted
    cases accepted
  | ok result =>
    simp only [found] at accepted
    cases accepted
    exact projectList_provenance prepared source target 0 edges.toList result found

/-- The graph materializer can read the full original edge array back from retained occurrences. -/
theorem project_originals {E : Type} (prepared : Prepared) (edges : Array E) (source target : E → Nat)
    (projected : Array (EdgeOccurrence E))
    (accepted : project prepared edges source target = .ok projected) :
    projected.toList.map (·.original) = edges.toList := by
  have preserved := project_provenance prepared edges source target projected accepted
  have payloads := congrArg (List.map (fun p : Nat × E × Nat × Nat => p.2.1)) preserved
  simp only [List.map_map, EdgeOccurrence.provenance, Function.comp_def] at payloads
  rw [List.zipIdx_map_fst] at payloads
  exact payloads

/-- Accepted projection retains the complete ordinal sequence, even for repeated payloads. -/
theorem project_indices {E : Type} (prepared : Prepared) (edges : Array E) (source target : E → Nat)
    (projected : Array (EdgeOccurrence E))
    (accepted : project prepared edges source target = .ok projected) :
    projected.toList.map (·.occurrence) = List.range' 0 edges.size := by
  have kept := congrArg (List.map (fun p : Nat × E × Nat × Nat => p.1))
    (project_provenance prepared edges source target projected accepted)
  simp only [List.map_map, EdgeOccurrence.provenance, Function.comp_def] at kept
  rw [List.zipIdx_map_snd, Array.length_toList] at kept
  exact kept

/-- Hidden and visible edge occurrences together retain the source array's size. -/
theorem project_size {E : Type} (prepared : Prepared) (edges : Array E) (source target : E → Nat)
    (projected : Array (EdgeOccurrence E))
    (accepted : project prepared edges source target = .ok projected) : projected.size = edges.size := by
  have kept := congrArg List.length (project_provenance prepared edges source target projected accepted)
  simp only [List.length_map, List.length_zipIdx, Array.length_toList] at kept
  exact kept

end Tools.View.GraphRegions
