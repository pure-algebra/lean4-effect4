import Effect4.Laws.Program.TracedMoves
import Effect4.Laws.Machine.RefFootprint
import Effect4.Laws.Contracts.FramePath

/-!
Concept: store-typing R4 and reactive-scheduling R11.
Question: cell-invariant-from-write-sites, serving the original application accounting goals.
Consumer: the shared primitive producer's actual store projection and its RefTransfer reader.
This probe annotates existing labels, using Contracts.Path over existing reference heaps.
Each executed operation retains its actual answer. A quiet annotation retains the whole heap.
The fold observes references only. It supplies no source permission, progress, or host agreement.
-/
set_option autoImplicit false
namespace Effect4.Program.Moves.RefWordsProbe
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Moves

abbrev Annotation := MoveLabel × Option (SyncOp × Val)

/-- The reference reading is total. The edge certificate admits only actual successful operations. -/
def applyRow (heap : RefHeap) (row : Option (SyncOp × Val)) : RefHeap :=
  match row with
  | none => heap
  | some (op, _) => match refStep op heap with
    | none => heap
    | some (_, next) => next

inductive Edge : RefHeap → RefHeap → Annotation → Prop where
  | quiet (label : MoveLabel) (heap : RefHeap) : Edge heap heap (label, none)
  | sync (label : MoveLabel) (op : SyncOp) (answer : Val) (before after : Stores)
      (source : label.kind = .answer (.sync (.op op)) (.success answer) ∨
        label.kind = .answer (.sync (.store (.op op))) (.success answer))
      (actual : syncOpStep op before = some (after, answer)) :
      Edge before.refs after.refs (label, some (op, answer))

theorem Edge.applies {before after : RefHeap} {label : Annotation}
    (edge : Edge before after label) : applyRow before label.2 = after := by
  cases edge with
  | quiet => rfl
  | sync label op answer before after source actual =>
    have projected := syncOpStep_refProjection actual
    cases result : refStep op before.refs with
    | none =>
      rw [result] at projected
      simpa only [applyRow, result] using projected.symm
    | some pair =>
      rw [result] at projected
      simp only [applyRow, result]
      exact congrArg Prod.snd projected

def run (labels : List Annotation) (heap : RefHeap) : RefHeap :=
  labels.foldl (fun current label => applyRow current label.2) heap

def cells (labels : List Annotation) : List RefKey :=
  labels.filterMap fun label => label.2.bind fun row => row.1.refFootprint row.2

theorem cells_append (left right : List Annotation) :
    cells (left ++ right) = cells left ++ cells right := by
  simp only [cells, List.filterMap_append]

theorem path_fold {before after : RefHeap} {labels : List Annotation}
    (path : Contracts.Path Edge before after labels) : run labels before = after := by
  induction path with
  | nil => rfl
  | cons edge tail ih =>
    change run _ (applyRow _ _) = _
    rw [edge.applies]
    exact ih

theorem Edge.refPeek_other {before after : RefHeap} {label : Annotation}
    (edge : Edge before after label) (cell : RefKey)
    (outside : label.2.bind (fun row => row.1.refFootprint row.2) ≠ some cell) :
    refPeek after cell = refPeek before cell := by
  cases edge with
  | quiet => rfl
  | sync label op answer before after source actual =>
    exact syncOpStep_refPeek_other actual cell outside

theorem path_refPeek_other {before after : RefHeap} {labels : List Annotation}
    (path : Contracts.Path Edge before after labels) (cell : RefKey)
    (outside : cell ∉ cells labels) : refPeek after cell = refPeek before cell := by
  induction path with
  | nil => rfl
  | @cons before middle after label labels edge tail ih =>
    have missing : label.2.bind (fun row => row.1.refFootprint row.2) ≠ some cell := by
      intro present
      apply outside
      exact List.mem_filterMap.mpr ⟨label, List.mem_cons_self, present⟩
    have rest : cell ∉ cells labels := by
      intro member
      apply outside
      obtain ⟨other, held, found⟩ := List.mem_filterMap.mp member
      exact List.mem_filterMap.mpr ⟨other, List.mem_cons_of_mem _ held, found⟩
    exact (ih rest).trans (edge.refPeek_other cell missing)

/-- The annotation strengthens the existing labelled word without changing its frame relation. -/
def Certified (m : NativeMachine) (f : NFrame) (n : NativeMachine) (g : NFrame) : Prop :=
  ∃ labels : List Annotation,
    LabelledMoves (labels.map Prod.fst) f g ∧
    Contracts.Path Edge m.state.refs n.state.refs labels ∧
    n.trace = m.trace ++ events (labels.map Prod.fst)

theorem Certified.traced {m n : NativeMachine} {f g : NFrame}
    (certified : Certified m f n g) : TracedMoves m f n g := by
  obtain ⟨labels, shape, _, trace⟩ := certified
  exact ⟨labels.map Prod.fst, shape, trace⟩

theorem quiet_path {labels : List MoveLabel} (heap : RefHeap) :
    Contracts.Path Edge heap heap (labels.map fun label => (label, none)) := by
  induction labels with
  | nil => exact .nil heap
  | cons label labels ih => exact .cons (.quiet label heap) ih

theorem Certified.of_refs {m n : NativeMachine} {f g : NFrame}
    (shape : TracedMoves m f n g) (refs : n.state.refs = m.state.refs) :
    Certified m f n g := by
  obtain ⟨labels, moves, trace⟩ := shape
  refine ⟨labels.map (fun label => (label, none)), ?_, ?_, ?_⟩
  · simpa only [List.map_map, Function.comp_def, List.map_id'] using moves
  · rw [refs]
    exact quiet_path _
  · simpa only [List.map_map, Function.comp_def, List.map_id'] using trace

theorem Certified.trans {m n o : NativeMachine} {f g h : NFrame}
    (first : Certified m f n g) (second : Certified n g o h) : Certified m f o h := by
  obtain ⟨left, leftMoves, leftPath, leftTrace⟩ := first
  obtain ⟨right, rightMoves, rightPath, rightTrace⟩ := second
  refine ⟨left ++ right, ?_, leftPath.append rightPath, ?_⟩
  · simpa only [List.map_append] using leftMoves.trans rightMoves
  · rw [List.map_append, events_append, rightTrace, leftTrace, List.append_assoc]

/-- A represented synchronous operation supplies its exact answer label and store edge. -/
theorem Certified.sync (m : NativeMachine) (frame : NFrame) (op : SyncOp)
    (answer : Val) (after : Stores)
    (source : frame.current = .sync (.op op) ∨ frame.current = .sync (.store (.op op)))
    (actual : syncOpStep op m.state = some (after, answer)) :
    Certified m frame {m with state := after} {frame with current := .success answer} := by
  let label : MoveLabel := ⟨.answer frame.current (.success answer), []⟩
  refine ⟨[(label, some (op, answer))], .single (.answer frame (.success answer) [] rfl), ?_, ?_⟩
  · apply Contracts.Path.cons (Edge.sync label op answer m.state after ?_ actual) (.nil after.refs)
    rcases source with direct | stored
    · exact .inl (congrArg (fun input => MoveKind.answer input (.success answer)) direct)
    · exact .inr (congrArg (fun input => MoveKind.answer input (.success answer)) stored)
  · exact (List.append_nil _).symm

namespace Reader

def before : Stores := {Stores.empty with refs := [.nat 10, .nat 20]}
def middle : Stores := {before with refs := [.nat 11, .nat 20]}
def after : Stores := {middle with refs := middle.refs ++ [.unit]}
def write : Annotation :=
  (⟨.answer (.sync (.op (.refSet ⟨0⟩ (.nat 11)))) (.success (.cell ⟨0⟩)), []⟩,
    some (.refSet ⟨0⟩ (.nat 11), .cell ⟨0⟩))
def allocate : Annotation :=
  (⟨.answer (.sync (.op (.refMake .unit))) (.success (.cell ⟨2⟩)), []⟩,
    some (.refMake .unit, .cell ⟨2⟩))

theorem actual : Contracts.Path Edge before.refs after.refs [write, allocate] :=
  .cons (.sync _ _ _ before middle (.inl rfl) rfl)
    (.cons (.sync _ _ _ middle after (.inl rfl) rfl) (.nil after.refs))

example : run [write, allocate] before.refs = after.refs := path_fold actual
example : refPeek after.refs ⟨1⟩ = refPeek before.refs ⟨1⟩ :=
  path_refPeek_other actual ⟨1⟩ (by decide)
example : refPeek after.refs ⟨7⟩ = refPeek before.refs ⟨7⟩ :=
  path_refPeek_other actual ⟨7⟩ (by decide)

/-- A successful read still records its actual operation and answer. -/
example : Edge before.refs before.refs
    (⟨.answer (.sync (.op (.refGet ⟨0⟩))) (.success (.nat 10)), []⟩,
      some (.refGet ⟨0⟩, .nat 10)) :=
  .sync _ _ _ before before (.inl rfl) rfl

end Reader

end Effect4.Program.Moves.RefWordsProbe
