import Effect4.Semantics.Logic
import Effect4Test.Flow.RunnerContract

/-!
# Logic contract (DB-06)

Receipts for `Effect4/Semantics/Logic.lean`: the modalities on a two-answer
signature, the point DB-06 makes (the liberal reading can hold vacuously where
the total one fails), and the flow reading against a deterministic oracle on
the runner contract's `incr` and `chooser` flows, where `wp` is decided by
evaluating the fuelled denotation (`Flow.wp_ofOracle_iff`).
-/

namespace Effect4Test.Semantics.LogicContract

open Effects Effect4 Effect4.Flow Effect4.Logic Effect4.Target.EffectV4
open Effects.Trace (Val)
open Effect4Test.Flow.RunnerContract

/-! ## The modalities on a coin -/

/-- One operation answering a `Bool`. -/
abbrev Coin : Signature := ⟨Unit, fun _ => Bool⟩

def flip : Program Coin Bool := .vis () .pure

/-- Two flips, counted. -/
def twice : Program Coin Nat :=
  .vis () fun a => .vis () fun b => .pure (cond a 1 0 + cond b 1 0)

-- Every path of `twice` counts at most two, under any specification.
example : Logic.wlp (Spec.any Coin) (fun n => n ≤ 2) twice := by
  unfold Logic.wlp twice
  simp only [box]
  intro a _ b _
  cases a <;> cases b <;> decide

-- And it is total under `Spec.any`, so the total reading holds too (DB-06).
example : Logic.wp (Spec.any Coin) (fun n => n ≤ 2) twice :=
  (wp_iff_wlp_and_total _ _ _).2 ⟨by
    unfold Logic.wlp twice
    simp only [box]
    intro a _ b _
    cases a <;> cases b <;> decide, by
    unfold twice
    simp only [Logic.total]
    exact ⟨⟨true, trivial⟩, fun _ _ => ⟨⟨true, trivial⟩, fun _ _ => trivial⟩⟩⟩

-- The heads-only specification: the box decides the count exactly.
def headsOnly : Spec Coin := fun _ answer => answer = true

example : Logic.wlp headsOnly (fun n => n = 2) twice := by
  unfold Logic.wlp twice
  simp only [box]
  intro a ha b hb
  cases ha; cases hb
  decide

-- DB-06's point: with no admissible answer the liberal reading of *anything*
-- holds, and the total reading of *nothing* does — `wp` is not `wlp`.
def unanswerable : Spec Coin := fun _ _ => False

example : Logic.wlp unanswerable (fun _ => False) flip := fun _ h => h.elim
example : ¬ Logic.total unanswerable flip := fun ⟨⟨_, h⟩, _⟩ => h
example : ¬ Logic.wp unanswerable (fun _ => True) flip := fun ⟨⟨_, h⟩, _⟩ => h

-- The oracle reading evaluates.
#guard evalOracle (fun _ => true) twice = 2
#guard evalOracle (fun _ => false) twice = 0

/-! ## The flow reading on `incr` and `chooser` -/

/-- A state-free family: `get` answers `41` (the state the runner contract
starts from), everything else `unit`. -/
def oracleFamily : String → Val → Val
  | "get", _ => .nat 41
  | _, _ => .unit

/-- The oracle mirroring `tableService` without state: literals answer
themselves, atoms evaluate, the family answers by `oracleFamily`, and every
decision answers its unit. -/
def oracle (table : List OpSpec) :
    (operation : (FullSig (tableAlphabet ⟨0⟩ table)).Op) →
      (FullSig (tableAlphabet ⟨0⟩ table)).Answer operation
  | .inl ⟨op, request⟩ =>
      (match (OpSpec.at table op).kind with
        | .lit value => value
        | .atom => cellAtom (OpSpec.at table op).name request
        | .family => oracleFamily (OpSpec.at table op).name request : Val)
  | .inr _ => ()

/-- The fuelled denotation of an embedded flow, evaluated against the oracle. -/
def evalFlow (table : List OpSpec) (flow : CheckedFlow (tableAlphabet ⟨0⟩ table)) (tape : Tape)
    (input : Val) : RunResult × Tape :=
  evalOracle (oracle table)
    (denoteFuel (fuelFor flow.erase tape) flow.erase flow.erase.entry [input] tape)

-- `incr` reads, writes the successor, and reads again. Against the *stateful*
-- service from `41` the second read answers `42` (`DenotationContract`); against
-- the oracle every `get` answers `41`, so the flow answers `41`. A specification
-- is per operation, never per state — this receipt pins that reading.
#guard (embedded.map fun ⟨table, flow⟩ => (evalFlow table flow [] (.nat 0)).1) =
  some (RunResult.done (.nat 41))

/-- The `wp` instance on `incr`, through `Flow.wp_ofOracle_iff` and the
evaluation above. -/
theorem incr_wp (table : List OpSpec) (flow : CheckedFlow (tableAlphabet ⟨0⟩ table))
    (h : embedded = some ⟨table, flow⟩) :
    Flow.wp (Spec.ofOracle (oracle table)) flow [] (.nat 0) (fun value => value = .nat 41) := by
  rw [Flow.wp_ofOracle_iff]
  refine ⟨.nat 41, ?_, rfl⟩
  have fact : (embedded.map fun ⟨table, flow⟩ =>
      decide ((evalFlow table flow [] (.nat 0)).1 = RunResult.done (.nat 41))) = some true := by
    decide
  rw [h] at fact
  exact of_decide_eq_true (Option.some.inj fact)

/-- `chooser` admitted against the empty table. -/
def chooserFlow : Option (CheckedFlow (tableAlphabet ⟨0⟩ [])) :=
  match admit (tableAlphabet ⟨0⟩ []) chooser with
  | .ok flow => some flow
  | .error _ => none

-- An answered tape reaches a value; the empty tape stops at the unanswered
-- frontier, which is outside the liberal reading and inside `total`'s.
def answersB (result : RunResult × Tape) : Bool :=
  match result.1 with
  | .done _ => true
  | _ => false

#guard (chooserFlow.map fun flow => answersB (evalFlow [] flow [⟨⟨7⟩, true⟩] (.nat 5))) = some true
#guard (chooserFlow.map fun flow => (evalFlow [] flow [] (.nat 5)).1) =
  some (RunResult.frontier (.unansweredDecision ⟨7⟩))

/-- `total` fails on the empty tape: the run is unanswered, not wrong. -/
theorem chooser_not_total_empty (flow : CheckedFlow (tableAlphabet ⟨0⟩ []))
    (h : chooserFlow = some flow) :
    ¬ Flow.total (Spec.ofOracle (oracle [])) flow [] (.nat 5) := by
  rw [Flow.total_ofOracle_iff]
  intro ⟨value, hv⟩
  have fact : (chooserFlow.map fun flow =>
      decide ((evalFlow [] flow [] (.nat 5)).1 = RunResult.frontier (.unansweredDecision ⟨7⟩))) =
        some true := by
    decide
  rw [h] at fact
  have stopped := of_decide_eq_true (Option.some.inj fact)
  unfold evalFlow at stopped
  rw [stopped] at hv
  cases hv

/-- And `wlp` holds there vacuously — DB-06's separation, on a flow. -/
theorem chooser_wlp_empty (flow : CheckedFlow (tableAlphabet ⟨0⟩ []))
    (h : chooserFlow = some flow) :
    Flow.wlp (Spec.ofOracle (oracle [])) flow [] (.nat 5) (fun _ => False) := by
  rw [Flow.wlp_ofOracle_iff]
  intro value hv
  have fact : (chooserFlow.map fun flow =>
      decide ((evalFlow [] flow [] (.nat 5)).1 = RunResult.frontier (.unansweredDecision ⟨7⟩))) =
        some true := by
    decide
  rw [h] at fact
  have stopped := of_decide_eq_true (Option.some.inj fact)
  unfold evalFlow at stopped
  rw [stopped] at hv
  cases hv

end Effect4Test.Semantics.LogicContract
