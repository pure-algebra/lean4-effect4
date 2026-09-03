/-
Counterexamples for the interrupt runner (`test/counterexamples/REGISTER.md`,
`E4-FLOW-CE-022` and `E4-FLOW-CE-023`). Each attack names a reading the runner
must refuse; the executable witness is a `#guard` over the actual runner
(`Effect4/Flow/Interrupt.lean`).
-/

import Effect4.Flow.Interrupt
import Effect4.Meta.Derive

namespace Effect4Test.Counterexamples.Flow.Interrupt

open Effects Effect4 Effect4.Flow Effect4.Meta Effect4.Target.EffectV4
open Effects.Trace (Val)

effect_signature RCell where
  | get : Nat ⟪ "read the cell" ⟫
  | put (n : Nat) : Unit ⟪ "write the cell" ⟫
  | acquire (n : Nat) : Nat ⟪ "acquire a resource named by a number" ⟫
  | release (n : Nat) : Unit ⟪ "release a resource" ⟫

def rcellFamily : String → Val → StateT Nat Id (Except Val Val)
  | "get", _ => do let n ← get; pure (.ok (.nat n))
  | "put", .nat n => do set n; pure (.ok .unit)
  | "acquire", v => pure (.ok v)
  | "release", _ => pure (.ok .unit)
  | _, _ => pure (.ok .unit)

def table : List OpSpec := familyTable RCell.rows
def opPut : OperationId := ⟨1⟩
def opAcquire : OperationId := ⟨2⟩
def opRelease : OperationId := ⟨3⟩

def rblock (id : Nat) (region : Option Nat) (params : List String) (term : RegionTerm) :
    RegionBlock String :=
  { id := ⟨id⟩, region := region.map RegionId.mk, params := params, term := term }

def rregion (id : Nat) (parent : Option Nat) (continue_ : Nat) : RegionRow String :=
  { id := ⟨id⟩, parent := parent.map RegionId.mk, continue_ := ⟨continue_⟩, resultTy := "number" }

def regionFlow (regions : List (RegionRow String)) (blocks : List (RegionBlock String)) :
    RegionFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩, inputTy := "number", resultTy := "number",
    regions := regions, blocks := blocks }

def vars (n : Nat) : List Var := (List.range n).map Var.mk

/-- A resource in region 1, a `perform` inside it, then a `perform` outside. -/
def guarded : RegionFlow String := regionFlow [rregion 1 none 4]
  [ rblock 0 none ["number"] (.enter ⟨1⟩ ⟨1⟩ (vars 1))
  , rblock 1 (some 1) ["number"] (.acquire opAcquire ⟨0⟩ opRelease ⟨2⟩ (vars 1))
  , rblock 2 (some 1) ["number", "number"] (.plain (.perform opPut ⟨0⟩ ⟨3⟩ (vars 2)))
  , rblock 3 (some 1) ["number", "number", "void"] (.leave ⟨1⟩)
  , rblock 4 none ["number"] (.plain (.perform opPut ⟨0⟩ ⟨5⟩ (vars 1)))
  , rblock 5 none ["number", "void"] (.plain (.ret ⟨0⟩)) ]

def run (raw : RegionFlow String) (masked : List RegionId) (itape : Tape) :
    Option (InterruptResult × Effect4.Trace.Log) :=
  match admitRegions (tableAlphabet ⟨0⟩ table) raw with
  | .ok flow =>
      let r := ((Flow.runInterruptsDefault flow masked
        (Flow.tableRegionService ⟨0⟩ table rcellFamily fun _ v => v)
        (tableNameOf ⟨0⟩ table) [] itape (.nat 5)).run []).run 41
      some (r.1.1.1, r.1.2)
  | .error _ => none

/-- The tape delivers at the interrupt point of block 2, which is inside
region 1. -/
def deliverInside : Tape := [⟨(Point.perform ⟨2⟩).site, true⟩]

/-! ## E4-FLOW-CE-022: an interrupt delivered under a mask

Attack: deliver the interrupt where the tape answers it, whatever the mask
says — dropping it, or interrupting inside an uninterruptible region. Repair:
the mask defers (rc.112 `_deferredInterrupt`, `Effect4/Runtime/Runtime.lean`):
the answer is kept pending and delivered at the first point that is not masked.
The two runs below differ only in the `masked` list. -/

-- Unmasked, the same tape delivers at that point: the `perform` never runs and
-- the region closes with `interrupted`.
#guard run guarded [] deliverInside =
  some (.interrupted,
    [ .enter 1
    , .op "acquire" (.nat 5), .answer "acquire" (.nat 5)
    , .decide 1000005 true
    , .leave 1 .interrupted
    , .finalizer 1 .interrupted
    , .op "release" (.nat 5), .answer "release" .unit
    , .done .interrupted ])

-- Masked, the same tape does not deliver there: the `perform` runs, the region
-- closes with `success`, and the run is interrupted only at the point after it.
#guard run guarded [⟨1⟩] deliverInside =
  some (.interrupted,
    [ .enter 1
    , .op "acquire" (.nat 5), .answer "acquire" (.nat 5)
    , .decide 1000005 true
    , .op "put" (.nat 5), .answer "put" .unit
    , .decide 1000002 false
    , .leave 1 (.success (.nat 5))
    , .finalizer 1 (.success (.nat 5))
    , .op "release" (.nat 5), .answer "release" .unit
    , .decide 1000009 false
    , .done .interrupted ])

-- The delivered answer is not dropped by the mask: the run still ends
-- interrupted, and the point that delivers it is the one after the mask.
#guard (run guarded [⟨1⟩] deliverInside).map (·.1) = some .interrupted

-- No region closes with `interrupted` while masked: every `leave` and
-- `finalizer` row of the masked run carries the clean exit.
#guard ((run guarded [⟨1⟩] deliverInside).map fun r => r.2.any fun event =>
  match event with
  | .leave _ .interrupted | .finalizer _ .interrupted => true
  | _ => false) = some false

-- The mask is inherited by the region's own `leave` point: site 1000002 is
-- answered while region 1 is still open, so it defers too.
#guard isMasked (alphabet := tableAlphabet ⟨0⟩ table) [⟨1⟩]
  [{ region := ⟨1⟩, releases := [] }] = true
#guard isMasked (alphabet := tableAlphabet ⟨0⟩ table) [⟨1⟩] [] = false

/-! ## E4-FLOW-CE-023: a finalizer that does not see `interrupted`

Attack: hand the releases of an interrupted close the exit the body would have
had (`success v`), or the failure arm, because `Outcome.interrupted` has no
payload to carry. Repair: an interrupted close is `closeFrame … .interrupted`,
so every `finalizer` row carries `{"interrupted":true}` — the arm A1 added and
M2 made producible. -/

-- Every finalizer row of the delivered run carries `interrupted`, and none
-- carries a success or a failure.
#guard ((run guarded [] deliverInside).map fun r => r.2.filterMap fun event =>
  match event with | .finalizer _ outcome => some outcome | _ => none)
  = some [Effects.Trace.Outcome.interrupted]

#guard ((run guarded [] deliverInside).map fun r => r.2.any fun event =>
  match event with
  | .finalizer _ (.success _) | .finalizer _ (.failure _) | .finalizer _ (.defect _) => true
  | _ => false) = some false

-- The same release on an uninterrupted run sees `success`: the arm is not a
-- constant, it is the closing exit.
#guard ((run guarded [] []).map fun r => r.2.filterMap fun event =>
  match event with | .finalizer _ outcome => some outcome | _ => none)
  = some [Effects.Trace.Outcome.success (.nat 5)]

-- The exit the reified `Scope` is closed with is the one-reason interrupt
-- cause: the wire drops the interruptor identity and the model has none.
#guard frameExit .interrupted =
  Effect4.Exit.failure ⟨[.interrupt none Effect4.ReasonAnnotations.empty]⟩

end Effect4Test.Counterexamples.Flow.Interrupt
