import Effects.Trace

/-!
# Semantics.Observation

Owner: the Effect v4 profile's instance of the shared trace alphabet and the
agreement judgment over it.

`Effects.Trace.Event` is parametric; this module fixes the profile's carriers:
operation names are their spellings, values are wire values, decision sites and
regions are numbered. `agree mask left right` is the executable judgment every
golden, host receipt and property run reports. It is a projection equality,
nothing more: `docs/TRACE-DAG.md` records what it does not establish.

This module imports neither `Effect4/Runtime/*` nor `Effect4/Concurrency/*`;
projections from `FrameEvent` and the scheduler `Event` into this alphabet are a
bridge obligation owned by `Effect4/Target/TypeScript/Simulation.lean`.
-/

namespace Effect4

open Effects

namespace Trace

/-- The profile's event: spelled operation names, wire values, numbered
decision sites and regions. -/
abbrev Event := Effects.Trace.Event String Effects.Trace.Val Nat Nat

abbrev Log := List Event

abbrev Mask := Effects.Trace.Mask

/-- The named masks a golden or receipt may cite. Generated projections of this
table (`generated/traces/masks.tsv`) are the only mask spellings a host may use. -/
def maskTable : List (String × Mask) :=
  [ ("outcome", Effects.Trace.Mask.outcomeOnly)
  , ("m1", Effects.Trace.Mask.m1)
  , ("m2", Effects.Trace.Mask.m2) ]

/-- Two logs agree under a mask when their projections are equal. -/
def agree (mask : Mask) (left right : Log) : Bool :=
  decide (Effects.Trace.project mask left = Effects.Trace.project mask right)

theorem agree_refl (mask : Mask) (log : Log) : agree mask log log = true := by
  simp [agree]

theorem agree_symm (mask : Mask) (left right : Log) :
    agree mask left right = agree mask right left := by
  simp [agree, eq_comm]

/-- Agreement under `m2` implies agreement under `m1`. -/
theorem agree_m1_of_agree_m2 {left right : Log}
    (h : agree Effects.Trace.Mask.m2 left right = true) :
    agree Effects.Trace.Mask.m1 left right = true := by
  simp only [agree, decide_eq_true_eq] at h ⊢
  exact Effects.Trace.agree_of_agree_m2 h

end Trace

end Effect4
