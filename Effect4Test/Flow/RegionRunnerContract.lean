/-
Contract packet: `test/contracts/flow-regions-runner.contract.md` (P-T7, light
ceremony D2). The region runner over Effects v0.5.0 region flows: the events a
`leave` and a failure produce, the order and the exit every release observes,
and how a release failure combines with the closing exit. Doc comments cannot
precede `#guard`, so the receipts carry line comments.
-/

import Effect4.Flow.Region
import Effect4.Runtime.Scope
import Effect4.Meta.Derive

namespace Effect4Test.Flow.RegionRunnerContract

open Effects Effect4 Effect4.Flow Effect4.Meta Effect4.Target.EffectV4
open Effects.Trace (Val)

#check @Effect4.Flow.RegionService
#check @Effect4.Flow.tableRegionService
#check @Effect4.Flow.Frame
#check @Effect4.Flow.closeFrame
#check @Effect4.Flow.unwind
#check @Effect4.Flow.regionLoop
#check @Effect4.Flow.runRegions
#check @Effect4.Flow.runRegionsDefault
#check (@Effect4.Flow.RunResult.failed : Val → RunResult)

effect_signature RCell where
  | get : Nat ⟪ "read the cell" ⟫
  | put (n : Nat) : Unit ⟪ "write the cell" ⟫
  | acquire (n : Nat) : Nat ⟪ "acquire a resource named by a number" ⟫
  | release (n : Nat) : Unit ⟪ "release a resource" ⟫
  | boom (n : Nat) : Nat !! String ⟪ "fail with a string" ⟫
  | releaseBoom (n : Nat) : Unit !! String ⟪ "a release that fails" ⟫

def rcellFamily : String → Val → StateT Nat Id (Except Val Val)
  | "get", _ => do let n ← get; pure (.ok (.nat n))
  | "put", .nat n => do set n; pure (.ok .unit)
  | "acquire", v => pure (.ok v)
  | "release", _ => pure (.ok .unit)
  | "boom", _ => pure (.error (.str "boom"))
  | "releaseBoom", _ => pure (.error (.str "boom"))
  | _, _ => pure (.ok .unit)

def table : List OpSpec := familyTable RCell.rows
def opAcquire : OperationId := ⟨2⟩
def opRelease : OperationId := ⟨3⟩
def opBoom : OperationId := ⟨4⟩
def opReleaseBoom : OperationId := ⟨5⟩

def rblock (id : Nat) (region : Option Nat) (params : List String) (term : RegionTerm) : RegionBlock String :=
  { id := ⟨id⟩, region := region.map RegionId.mk, params := params, term := term }

def rregion (id : Nat) (parent : Option Nat) (continue_ : Nat) : RegionRow String :=
  { id := ⟨id⟩, parent := parent.map RegionId.mk, continue_ := ⟨continue_⟩, resultTy := "number" }

def regionFlow (regions : List (RegionRow String)) (blocks : List (RegionBlock String)) : RegionFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩, inputTy := "number", resultTy := "number",
    regions := regions, blocks := blocks }

def vars (n : Nat) : List Var := (List.range n).map Var.mk

/-- Two resources whose second release fails on a clean leave. -/
def releaseFails : RegionFlow String := regionFlow [rregion 1 none 4]
  [ rblock 0 none ["number"] (.enter ⟨1⟩ ⟨1⟩ (vars 1))
  , rblock 1 (some 1) ["number"] (.acquire opAcquire ⟨0⟩ opRelease ⟨2⟩ (vars 1))
  , rblock 2 (some 1) ["number", "number"] (.acquire opAcquire ⟨1⟩ opReleaseBoom ⟨3⟩ (vars 2))
  , rblock 3 (some 1) ["number", "number", "number"] (.leave ⟨2⟩)
  , rblock 4 none ["number"] (.plain (.ret ⟨0⟩)) ]

/-- Two nested regions, each with a resource, the inner body failing. -/
def nested : RegionFlow String := regionFlow [rregion 1 none 7, rregion 2 (some 1) 6]
  [ rblock 0 none ["number"] (.enter ⟨1⟩ ⟨1⟩ (vars 1))
  , rblock 1 (some 1) ["number"] (.acquire opAcquire ⟨0⟩ opRelease ⟨2⟩ (vars 1))
  , rblock 2 (some 1) ["number", "number"] (.enter ⟨2⟩ ⟨3⟩ (vars 2))
  , rblock 3 (some 2) ["number", "number"] (.acquire opAcquire ⟨0⟩ opRelease ⟨4⟩ (vars 2))
  , rblock 4 (some 2) ["number", "number", "number"] (.plain (.perform opBoom ⟨0⟩ ⟨5⟩ (vars 3)))
  , rblock 5 (some 2) ["number", "number", "number", "number"] (.leave ⟨3⟩)
  , rblock 6 (some 1) ["number"] (.leave ⟨0⟩)
  , rblock 7 none ["number"] (.plain (.ret ⟨0⟩)) ]

def run (raw : RegionFlow String) : Option (RunResult × Effect4.Trace.Log) :=
  match admitRegions (tableAlphabet ⟨0⟩ table) raw with
  | .ok flow =>
      let r := ((Flow.runRegionsDefault flow (Flow.tableRegionService ⟨0⟩ table rcellFamily fun _ v => v)
        (tableNameOf ⟨0⟩ table) [] (.nat 5)).run []).run 41
      some (r.1.1.1, r.1.2)
  | .error _ => none

-- Both region flows are admitted.
#guard (run releaseFails).isSome
#guard (run nested).isSome

-- A clean leave closes with `success`; releases run latest-first, each seeing
-- the closing exit even after an earlier release failed; the run fails with
-- the first release failure (E4-FLOW-CE-019, E4-FLOW-CE-020).
#guard run releaseFails = some (.failed (.str "boom"),
  [ .enter 1
  , .op "acquire" (.nat 5), .answer "acquire" (.nat 5)
  , .op "acquire" (.nat 5), .answer "acquire" (.nat 5)
  , .leave 1 (.success (.nat 5))
  , .finalizer 1 (.success (.nat 5)), .op "releaseBoom" (.nat 5), .failed "releaseBoom" (.str "boom")
  , .finalizer 1 (.success (.nat 5)), .op "release" (.nat 5), .answer "release" .unit
  , .done (.failure (.str "boom")) ])

-- A failure closes every open region innermost-first with the failure, and
-- the body's failure is the run's failure.
#guard run nested = some (.failed (.str "boom"),
  [ .enter 1
  , .op "acquire" (.nat 5), .answer "acquire" (.nat 5)
  , .enter 2
  , .op "acquire" (.nat 5), .answer "acquire" (.nat 5)
  , .op "boom" (.nat 5), .failed "boom" (.str "boom")
  , .leave 2 (.failure (.str "boom")), .finalizer 2 (.failure (.str "boom"))
  , .op "release" (.nat 5), .answer "release" .unit
  , .leave 1 (.failure (.str "boom")), .finalizer 1 (.failure (.str "boom"))
  , .op "release" (.nat 5), .answer "release" .unit
  , .done (.failure (.str "boom")) ])

/-! ## The reified Scope agrees on the order and the exits -/

open Effect4 in
-- Registration order `release a` then `releaseBoom b` closes latest-first:
-- the order the runner logged above (`releaseBoom` before `release`).
example : (({ strategy := .sequential, state := .openMap [(1, "release"), (2, "releaseBoom")] } :
    Scope Nat String Unit Unit Unit Unit Unit).closeOrder) = ["releaseBoom", "release"] := rfl

open Effect4 in
-- Every release sees the same closing exit (`closeExits` maps one exit over the order).
example (exit : Exit Unit Unit Unit Unit Unit) :
    (({ strategy := .sequential, state := .openMap [(1, "release"), (2, "releaseBoom")] } :
      Scope Nat String Unit Unit Unit Unit Unit).closeExits (fun _ e => e) exit) = [exit, exit] := rfl

end Effect4Test.Flow.RegionRunnerContract
