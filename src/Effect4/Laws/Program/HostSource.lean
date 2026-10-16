import Effect4.Laws.Program.NativeHeapReplies

/-!
# Sources whose calls use only external rows

Concept: translation-simulation R6, serving `Run.CallTree.request_leads` and Routing authorization.
The generated address census checks the direct fragment and excludes every native operation.
Actual histories therefore retain an empty reference heap, including after admitted host replies.
This source restriction does not itself establish the call-prefix simulation or outside-host agreement.
-/
set_option autoImplicit false
namespace Effect4.Program.SourceScope
open Effect4 Effect4.Machine Effect4.Program Effect4.Run HeapSites

/-- A direct source head whose operation, if present, is an external row. -/
def externalHead (node : Node NativeOp) : Bool :=
  directHead node && match node with
    | .eff (.perform (.external _) _) => true
    | .eff (.perform _ _) => false
    | _ => true

/-- The existing address census checks every source head, without another program traversal. -/
def ExternalOnly (root : NativeEff) : Prop :=
  (Node.addresses (.eff root)).all (fun path =>
    (Node.at_ (.eff root) path).all externalHead) = true

/-- The table-only reply tape uses closed answer and error columns.
Generic instances require their own call-indexed admission judgment. -/
def ConcreteReplies (table : RowTable) : Prop :=
  table.all (fun row => row.answer.closed && row.error.closed) = true

/-- The external-only source retains the existing direct lexical fragment. -/
theorem ExternalOnly.fragment {root : NativeEff} (held : ExternalOnly root) : Fragment root := by
  apply List.all_eq_true.mpr
  intro path member
  have head := List.all_eq_true.mp held path member
  cases found : Node.at_ (.eff root) path with
  | none => rfl
  | some node =>
    rw [found] at head
    change externalHead node = true at head
    unfold externalHead at head
    simp only [Bool.and_eq_true] at head
    exact head.1

/-- Every operation at an actual source address names an external row. -/
theorem ExternalOnly.operation {root : NativeEff} (held : ExternalOnly root)
    (path : List Nat) (op : NativeOp) (request : Term)
    (found : Node.at_ (.eff root) path = some (.eff (.perform op request))) :
    ∃ index, op = .external index := by
  have member : path ∈ Node.addresses (.eff root) :=
    (mem_addresses_iff (.eff root) path).mpr (by rw [found]; rfl)
  have head := List.all_eq_true.mp held path member
  rw [found] at head
  cases op with
  | external index => exact ⟨index, rfl⟩
  | _ => cases head

/-- No external row produces a native store operation, so every cell predicate satisfies its site law. -/
theorem ExternalOnly.sites {root : NativeEff} (held : ExternalOnly root) (P : Val → Prop) :
    SitesKeep root P := by
  intro path op request env value operation found _ _ step
  obtain ⟨index, rfl⟩ := held.operation path op request found
  cases step

/-- Actual admitted histories of this source retain an empty reference heap at every budget. -/
theorem ExternalOnly.empty_heap {b : Api.Built} (held : ExternalOnly b.program)
    (compileFuel : Nat) (m : NativeMachine) (history : HistoryOf b compileFuel m) :
    m.state.refs = [] := by
  have heap := admitted_heap_history b held.fragment compileFuel (fun _ => False)
    (held.sites _) m history
  cases cells : m.state.refs with
  | nil => rfl
  | cons value rest =>
    apply False.elim
    apply heap 0 value
    rw [cells]
    rfl

/-- The actual row admission refuses every delayed reference read when the heap is empty. -/
theorem empty_heap_refused (decls : TyDecls) (row : Row) (m : NativeMachine) (fiber : FiberId)
    (token : Nat) (cell : RefKey) (empty : m.state.refs = []) :
    admitAnswer decls row m fiber token (.ofRefGet cell) = some (.unknownCell cell) := by
  simp only [admitAnswer, empty, List.getElem?_nil]

end Effect4.Program.SourceScope
