import Effect4.Machine.Stores
import ProofGraph.AxiomAudit

/-!
# Probe: a world with a protocol state per name, at the Deferred store

A finite probe for `../README.md` §2.9. A handle has a life as well as an allocation. A Deferred
cell is pending, then completed with one effect forever. Order each cell by that protocol and
each store by its cells. Then:

1. every Deferred operation of the real store (`make`, `register`, `cancel`, `complete`,
   `wakeBatch`, `drainDue`) moves forward in the order, one theorem each;
2. a fact that the order keeps is kept by every operation and every sequence of operations, with
   no proof per fact and operation. "Allocated" and "completed with `e`" are two such facts.

A control shows that an operation that clears a completion is not forward.

It is not a library module. It compiles with `lake env lean` against the built
`Effect4.Machine.Stores`, and its last command walks its own declarations with the axiom gate's
walk.
-/

set_option autoImplicit false

namespace Effect4.Machine.ProtocolsProbe

open Effect4.Machine

variable {κ : Type}

/-! ## The protocol order -/

/-- One cell moves forward: a stored completion stays, unchanged. -/
def CellLe (c c' : DeferredCell κ) : Prop := ∀ e, c.completion = some e → c'.completion = some e

/-- A store moves forward: every allocated cell stays allocated and moves forward. -/
def StoreLe (s s' : DeferredStore κ) : Prop :=
  ∀ k c, s.cellAt k = some c → ∃ c', s'.cellAt k = some c' ∧ CellLe c c'

theorem StoreLe.refl (s : DeferredStore κ) : StoreLe s s :=
  fun _ c h => ⟨c, h, fun _ same => same⟩

theorem StoreLe.trans {s s' s'' : DeferredStore κ} (h : StoreLe s s') (h' : StoreLe s' s'') :
    StoreLe s s'' := by
  intro k c hc
  obtain ⟨c', hc', le⟩ := h k c hc
  obtain ⟨c'', hc'', le'⟩ := h' k c' hc'
  exact ⟨c'', hc'', fun e same => le' e (le e same)⟩

/-! ## The one store write, and a forward replacement -/

/-- Replacing a cell by one ahead of it moves the store forward. -/
theorem setCell_le (s : DeferredStore κ) (k : DeferredKey) (v : DeferredCell κ)
    (ahead : ∀ c, s.cellAt k = some c → CellLe c v) : StoreLe s (s.setCell k v) := by
  intro j c hc
  rcases Nat.decEq k.index j.index with differ | same
  · refine ⟨c, ?_, fun _ held => held⟩
    show (s.cells.set k.index v)[j.index]? = some c
    rw [List.getElem?_set_ne differ]
    exact hc
  · have key : k = j := by
      cases k
      cases j
      cases same
      rfl
    subst key
    have bound : k.index < s.cells.length := (List.getElem?_eq_some_iff.mp hc).1
    refine ⟨v, ?_, ahead c hc⟩
    show (s.cells.set k.index v)[k.index]? = some v
    rw [List.getElem?_set_self bound]

/-- A cell with only its waiters changed is not ahead or behind: the completion is the same. -/
theorem wake_ahead (c : DeferredCell κ) (wake : WakeList Unit) : CellLe c { c with wake := wake } :=
  fun _ held => held

/-! ## Every Deferred operation moves forward -/

theorem make_le (s : DeferredStore κ) : StoreLe s s.make.2 := by
  intro j c hc
  refine ⟨c, ?_, fun _ held => held⟩
  show (s.cells ++ [⟨none, WakeList.empty⟩])[j.index]? = some c
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hc).1]
  exact hc

theorem register_le (s : DeferredStore κ) (k : DeferredKey) (waiter : FiberId) (token : Nat) :
    StoreLe s (s.register k waiter token).1 := by
  unfold DeferredStore.register
  split
  next => exact StoreLe.refl s
  next c found =>
    split
    next => exact StoreLe.refl s
    next =>
      exact setCell_le s k _ fun c' hc' => by
        rw [found] at hc'
        cases hc'
        exact wake_ahead _ _

theorem cancel_le (s : DeferredStore κ) (k : DeferredKey) (waiter : FiberId) (token : Nat) :
    StoreLe s (s.cancel k waiter token) := by
  unfold DeferredStore.cancel
  split
  next => exact StoreLe.refl s
  next c found =>
    exact setCell_le s k _ fun c' hc' => by
      rw [found] at hc'
      cases hc'
      exact wake_ahead _ _

theorem complete_le (s : DeferredStore κ) (k : DeferredKey) (effect : κ) :
    StoreLe s (s.complete k effect).1 := by
  unfold DeferredStore.complete
  split
  next => exact StoreLe.refl s
  next c found =>
    split
    next => exact StoreLe.refl s
    next pending =>
      exact setCell_le s k _ fun c' hc' => by
        rw [found] at hc'
        cases hc'
        intro e held
        rw [pending] at held
        cases held

theorem wakeBatch_le (s : DeferredStore κ) (k : DeferredKey) : StoreLe s (s.wakeBatch k) := by
  unfold DeferredStore.wakeBatch
  split
  next => exact StoreLe.refl s
  next c found =>
    split
    next =>
      exact setCell_le s k _ fun c' hc' => by
        rw [found] at hc'
        cases hc'
        exact wake_ahead _ _
    next =>
      exact setCell_le s k _ fun c' hc' => by
        rw [found] at hc'
        cases hc'
        exact wake_ahead _ _

theorem drainDue_le (s : DeferredStore κ) : StoreLe s s.drainDue.2 := StoreLe.refl s

/-! ## Stable facts: one theorem each, kept by every operation -/

/-- A fact the order keeps. -/
def Stable (P : DeferredStore κ → Prop) : Prop := ∀ s s', StoreLe s s' → P s → P s'

/-- The cell exists: the allocation fact of `Laws/Machine/Handles.lean`, a protocol fact. -/
def Allocated (k : DeferredKey) (s : DeferredStore κ) : Prop := ∃ c, s.cellAt k = some c

/-- The cell is completed with `e`. -/
def CompletedWith (k : DeferredKey) (e : κ) (s : DeferredStore κ) : Prop :=
  ∃ c, s.cellAt k = some c ∧ c.completion = some e

theorem allocated_stable (k : DeferredKey) : Stable (κ := κ) (Allocated k) := by
  intro s s' le ⟨c, hc⟩
  obtain ⟨c', hc', _⟩ := le k c hc
  exact ⟨c', hc'⟩

theorem completedWith_stable (k : DeferredKey) (e : κ) : Stable (CompletedWith k e) := by
  intro s s' le ⟨c, hc, done⟩
  obtain ⟨c', hc', ahead⟩ := le k c hc
  exact ⟨c', hc', ahead e done⟩

/-- **One theorem for every fact and every operation.** A run of forward operations keeps every
stable fact. -/
theorem stable_run (P : DeferredStore κ → Prop) (stable : Stable P)
    (ops : List (DeferredStore κ → DeferredStore κ)) (forward : ∀ op ∈ ops, ∀ s, StoreLe s (op s)) :
    ∀ s, P s → P (ops.foldl (fun s op => op s) s) := by
  induction ops with
  | nil => exact fun _ held => held
  | cons op rest ih =>
    intro s held
    exact ih (fun op' member => forward op' (List.mem_cons_of_mem op member)) (op s)
      (stable s (op s) (forward op List.mem_cons_self s) held)

/-- A reader: a completion survives a later registration, cancellation and batch wake. -/
example (s : DeferredStore κ) (k j : DeferredKey) (e : κ) (waiter : FiberId) (token : Nat)
    (done : CompletedWith k e s) :
    CompletedWith k e ((s.register j waiter token).1.cancel j waiter token |>.wakeBatch j) :=
  completedWith_stable k e _ _
    ((register_le s j waiter token).trans ((cancel_le _ j waiter token).trans (wakeBatch_le _ j)))
    done

/-- A control: clearing a completion is not forward. -/
example : ¬ StoreLe (⟨[⟨some 0, WakeList.empty⟩], []⟩ : DeferredStore Nat)
    ⟨[⟨none, WakeList.empty⟩], []⟩ := by
  intro le
  obtain ⟨c', hc', ahead⟩ := le ⟨0⟩ ⟨some 0, WakeList.empty⟩ rfl
  cases hc'
  exact nomatch ahead 0 rfl

end Effect4.Machine.ProtocolsProbe

/-! ## The audit: every declaration of this probe, by the gate's walk -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.map₂.toList.filterMap fun (n, _) =>
    if (`Effect4.Machine.ProtocolsProbe).isPrefixOf n && !n.isInternal then some n else none
  let (results, _) := ProofGraph.reachedAxiomsMany env names.toArray {} (ProofGraph.isGoal env)
  let mut outside : Array Name := #[]
  for (n, r) in names.toArray.zip results do
    match r with
    | none => outside := outside.push n
    | some reached =>
      if reached.any (fun a => !ProofGraph.trustedAxioms.contains a) then outside := outside.push n
  unless outside.isEmpty do
    throwError m!"probe audit: outside [propext, Quot.sound]: {outside}"
  logInfo m!"probe audit: {names.length} declarations within [propext, Quot.sound]"
