import Effect4.Laws.Machine.MaskRuns
import Effect4.Laws.Machine.ControlWeights
import Effect4.Laws.Machine.Keeps

/-!
# Laws.Machine.FiberSum — a weight summed over the fiber table, and its frame rule

The fiber table is a finite map from ids to fibers. A weight on fibers, summed over the table, splits
as the weight of one owner plus the weight of the rest: `machine = owner ∗ rest`, the frame rule of
separation logic read on a sum. This module states that split once, for every fiber weight:

* `total`, `atFiber` (the owner's weight, nothing when the id is missing) and `outside` (the rest);
* `split`: the rest plus the owner is the total, under distinct ids;
* `outside_update`: installing the owner keeps the rest;
* `outside_update_le`: a lighter replacement of another fiber keeps the rest no heavier;
* `install`: writing the owner back gives the rest plus the new row;
* `update_bound` and `update_debit`: a keyed replacement spends the old row and holds the new one;
* the edits that keep the table: `emit`, `state`, and a pointwise edit that keeps the weight.

The goals lane proves this split three times, once per weight: `ReleaseCustody/Outside`
(`outside_split`, `outside_update`, `outside_update_le`, `outside_install`),
`SourceOpportunityMachine` (`fibers`, `outside`, `outside_split`, `outside_update`, `update_debit`),
and `WriterWeights` (`fibers`, `outside`). Each becomes an instance: its `fibers` is `total`, and its
`outside` is `outside` (the machine-models note, `CODEX-PROMPT.md`, item 3). `StackLedger.total` and
`atFiber` are `total` and `atFiber` at its `held`.

Placement (AGENTS.md, Trust): concept `reactive-scheduling` (invariants over execution traces); a
helper of the proposed claim `ledger-run`, consumed by every ledger's settlement. Reach: every
machine with distinct fiber ids, every weight. It establishes no weight's local debit.
-/

set_option autoImplicit false

namespace Effect4.Machine.FiberSum

universe u v

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable (w : RunFiber ν σ β ε δ ι α χ → Nat)

/-- The weight of the machine's fibers. -/
def total (m : RunMachine ν σ β ε δ ι α χ St) : Nat := (m.fibers.map w).sum

/-- The weight of the fiber an id names; nothing when the id is missing. -/
def atFiber (m : RunMachine ν σ β ε δ ι α χ St) (id : FiberId) : Nat := ((m.fiber? id).map w).getD 0

/-- The weight of every fiber but the owner. -/
def outside (owner : FiberId) (m : RunMachine ν σ β ε δ ι α χ St) : Nat :=
  (m.fibers.map (ControlWeights.omitted RunFiber.id w owner)).sum

/-- **The split.** The rest plus the owner is the total. -/
theorem split (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ)
    (unique : (m.fibers.map RunFiber.id).Nodup) (member : f ∈ m.fibers) :
    outside w f.id m + w f = total w m :=
  ControlWeights.omit_sum RunFiber.id w f m.fibers unique member

/-- The split at a looked-up id. -/
theorem split_found (m : RunMachine ν σ β ε δ ι α χ St) (id : FiberId) (f : RunFiber ν σ β ε δ ι α χ)
    (unique : (m.fibers.map RunFiber.id).Nodup) (found : m.fiber? id = some f) :
    outside w id m + atFiber w m id = total w m := by
  have parts := split w m f unique (RunMachine.mem_of_fiber? found)
  rw [RunMachine.id_of_fiber? found] at parts
  simp only [atFiber, found, Option.map_some, Option.getD_some]
  exact parts

/-- **Installing the owner keeps the rest.** -/
theorem outside_update (m : RunMachine ν σ β ε δ ι α χ St) (owner : FiberId)
    (next : RunFiber ν σ β ε δ ι α χ) (key : next.id = owner) :
    outside w owner (m.update next) = outside w owner m :=
  ControlWeights.replace_omitted RunFiber.id w owner next key m.fibers

/-- A lighter replacement of a fiber keeps every rest no heavier. -/
theorem outside_update_le (m : RunMachine ν σ β ε δ ι α χ St) (owner : FiberId)
    (old next : RunFiber ν σ β ε δ ι α χ) (unique : (m.fibers.map RunFiber.id).Nodup)
    (found : m.fiber? old.id = some old) (key : next.id = old.id) (lighter : w next ≤ w old) :
    outside w owner (m.update next) ≤ outside w owner m :=
  ControlWeights.replace_omitted_le RunFiber.id w owner old next key lighter m.fibers unique
    (RunMachine.mem_of_fiber? found)

/-- **The frame rule of a replacement.** It spends the weight its id held and holds the new one's. -/
theorem update_bound (m : RunMachine ν σ β ε δ ι α χ St) (next : RunFiber ν σ β ε δ ι α χ)
    (unique : (m.fibers.map RunFiber.id).Nodup) :
    total w (m.update next) + atFiber w m next.id ≤ total w m + w next := by
  cases found : m.fiber? next.id with
  | none =>
    have unchanged : (m.fibers.map fun g => if g.id = next.id then next else g) = m.fibers := by
      calc
        _ = m.fibers.map id := List.map_congr_left fun g member => by
          have no := List.find?_eq_none.mp found g member
          exact if_neg (fun equal => no (decide_eq_true equal))
        _ = m.fibers := List.map_id _
    change ((m.fibers.map fun g => if g.id = next.id then next else g).map w).sum +
      ((m.fiber? next.id).map w).getD 0 ≤ _
    rw [unchanged, found]
    exact Nat.le_add_right _ _
  | some old =>
    have changed := ControlWeights.replace_sum RunFiber.id w old next
      (RunMachine.id_of_fiber? found).symm m.fibers unique (RunMachine.mem_of_fiber? found)
    change _ + ((m.fiber? next.id).map w).getD 0 ≤ _
    rw [found]
    exact Nat.le_of_eq changed

/-- **Writing the owner back** gives the rest plus the new row. -/
theorem install (m : RunMachine ν σ β ε δ ι α χ St) (id : FiberId) (old next : RunFiber ν σ β ε δ ι α χ)
    (unique : (m.fibers.map RunFiber.id).Nodup) (found : m.fiber? id = some old) (key : next.id = id) :
    total w (m.update next) = outside w id m + w next := by
  have changed := ControlWeights.replace_sum RunFiber.id w old next
    (key.trans (RunMachine.id_of_fiber? found).symm) m.fibers unique (RunMachine.mem_of_fiber? found)
  have parts := split_found w m id old unique found
  simp only [atFiber, found, Option.map_some, Option.getD_some] at parts
  change total w (m.update next) + w old = total w m + w next at changed
  omega

/-- A keyed replacement that costs `cost` below its old row. -/
theorem update_debit (m : RunMachine ν σ β ε δ ι α χ St) (old next : RunFiber ν σ β ε δ ι α χ)
    (key : next.id = old.id) (unique : (m.fibers.map RunFiber.id).Nodup) (member : old ∈ m.fibers)
    (cost : Nat) (bounded : w next + cost ≤ w old) : total w (m.update next) + cost ≤ total w m := by
  have installed := ControlWeights.replace_sum RunFiber.id w old next key m.fibers unique member
  change total w (m.update next) + w old = total w m + w next at installed
  omega

/-- Emitting events keeps the table. -/
theorem total_emit (m : RunMachine ν σ β ε δ ι α χ St) (events : List (RunEvent ν σ β ε δ ι α χ)) :
    total w (m.emit events) = total w m := rfl

/-- Emitting events keeps every rest. -/
theorem outside_emit (m : RunMachine ν σ β ε δ ι α χ St) (owner : FiberId)
    (events : List (RunEvent ν σ β ε δ ι α χ)) : outside w owner (m.emit events) = outside w owner m := rfl

/-- A pointwise edit that keeps ids and weights keeps the total. -/
theorem total_map (m : RunMachine ν σ β ε δ ι α χ St)
    (edit : RunFiber ν σ β ε δ ι α χ → RunFiber ν σ β ε δ ι α χ) (weights : ∀ f, w (edit f) = w f) :
    total w { m with fibers := m.fibers.map edit } = total w m := by
  simp only [total, List.map_map, Function.comp_def, weights]

/-- A pointwise edit that keeps ids and weights keeps every rest. -/
theorem outside_map (m : RunMachine ν σ β ε δ ι α χ St) (owner : FiberId)
    (edit : RunFiber ν σ β ε δ ι α χ → RunFiber ν σ β ε δ ι α χ)
    (ids : ∀ f, (edit f).id = f.id) (weights : ∀ f, w (edit f) = w f) :
    outside w owner { m with fibers := m.fibers.map edit } = outside w owner m := by
  simp only [outside, List.map_map, Function.comp_def, ControlWeights.omitted, ids, weights]
  rfl

end Effect4.Machine.FiberSum
