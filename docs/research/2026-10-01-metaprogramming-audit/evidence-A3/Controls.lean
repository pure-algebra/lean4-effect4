/- UNCOMPILED controls. Expected numbers below are expectations, not measured results.
   Compile this small file first, in the coordinator's single bounded compiler lane. -/
import A3Instrumentation

theorem a3_control_select : True := by
  first
  | a3_arm "control" / "failed" => exact (0 : Nat)
  | a3_arm "control" / "selected" => exact True.intro

-- `discarded` locally succeeds but its enclosing first arm fails afterwards.
theorem a3_control_rollback : True := by
  first
  | (a3_arm "control" / "discarded" => exact True.intro
     fail "force enclosing rollback")
  | a3_arm "control" / "after-rollback" => exact True.intro

-- A normal tactic return need not solve its goal.
theorem a3_control_partial : True := by
  a3_arm "control" / "partial" => skip
  exact True.intro

theorem a3_control_multigoal : True ∧ True := by
  first
  | (constructor
     · a3_arm "control" / "discarded-multigoal" => exact True.intro
     · fail "force later-goal rollback")
  | constructor <;> a3_arm "control" / "multi-selected" => exact True.intro

-- Parent and child family counts overlap: never sum them as distinct proof steps.
theorem a3_control_nested : True := by
  a3_arm "parent" / "nested" => a3_arm "child" / "leaf" => exact True.intro

/- Expected retained success messages: 7. Specifically `discarded` and
   `discarded-multigoal` must not survive; `failed` never emits a success message.
   Breakdown: select 1, rollback 1, partial 1, multigoal 2, nested 2 = 7 retained.
   These are predictions awaiting a compiler run, not observed counts. -/
