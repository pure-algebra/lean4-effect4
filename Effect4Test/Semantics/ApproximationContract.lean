/-
Contract packet: the trace lane (`docs/TRACE-DAG.md`), row `approximation`.
Light ceremony by operator ruling D2: contract, battery and code land together.

Frozen: the DB-04 approximation order (`Observation`, `Observation.le`,
`observe`, `obsLe`) and its two runner instances -- the tape runner
(`loop`/`run`) and the region runner (`regionLoop`/`runRegions`), the latter
over the D2 *merged failure list* carrier.

Executable receipts: the counterexample that forces `obsLe` to be antisymmetric
only up to `observe`, and, on the three harness region programs
(`harness/trace/Generate.lean`) plus one program whose release fails under a
failing body, the four DB-04 facts -- the allotted fuel settles the run, the
fuel one below it is a live frontier whose log is a prefix, more fuel only
climbs the order, and a fuel frontier never touches the merged failure list.

Doc comments cannot precede `#guard`, so the receipts carry line comments.
-/

import Effect4.Semantics.Approximation
import Effect4.Meta.Derive

namespace Effect4Test.Semantics.ApproximationContract

open Effects Effect4 Effect4.Flow Effect4.Meta Effect4.Target.EffectV4
open Effects.Trace (Val)

/-! ## The frozen surface -/

#check @Effect4.Flow.Observation
#check @Effect4.Flow.Observation.le
#check @Effect4.Flow.observe
#check @Effect4.Flow.obsLe
#check @Effect4.Flow.Chain
#check @Effect4.Flow.Chain.colimit

-- the region half: the three properties the laws travel on
#check @Effect4.Flow.Appends
#check @Effect4.Flow.Sound
#check @Effect4.Flow.Below
#check @Effect4.Flow.Settles
#check @Effect4.Flow.NotExhausted
#check @Effect4.Flow.obsOf

-- the region laws
#check @Effect4.Flow.regionStep_log_extends
#check @Effect4.Flow.regionLoop_fuel_stable
#check @Effect4.Flow.regionLoop_frontier_live
#check @Effect4.Flow.regionLoop_failed_head
#check @Effect4.Flow.region_obs_mono
#check @Effect4.Flow.region_obs_chain
#check @Effect4.Flow.regionObservation_stable
#check @Effect4.Flow.runRegions_obs_mono
#check @Effect4.Flow.runRegions_obs_chain
#check @Effect4.Flow.runRegions_obs_stable
#check @Effect4.Flow.runRegionsObservation_wire
#check @Effect4.Flow.runRegionsChain
#check @Effect4.Flow.runRegionsColimit
#check @Effect4.Flow.runRegionsColimitDefault

-- the region fuel formula and its sufficiency
#check @Effect4.Flow.regionFuelFor
#check @Effect4.Flow.regionFuelFor_blocks
#check @Effect4.Flow.lookupBlock_erase
#check @Effect4.Flow.runRegionsCause_fuelFor_finishes
#check @Effect4.Flow.runRegions_fuelFor_finishes
#check @Effect4.Flow.runRegionsDefault_finishes
#check @Effect4.Flow.runRegionsColimitDefault_settled
#check @Effect4.Flow.runRegionsColimit_eq_default

/-! ## Why the order is antisymmetric only up to `observe`

Two fuel frontiers that logged the same events but stopped at different blocks
lie below each other, because the resumption block is not an observation. This
is the counterexample the module docstring names. -/

-- mutually below,
#guard obsLe (.frontier (.fuel ⟨1⟩), []) (.frontier (.fuel ⟨2⟩), [])
#guard obsLe (.frontier (.fuel ⟨2⟩), []) (.frontier (.fuel ⟨1⟩), [])

-- but not equal as raw pairs,
#guard ((RunResult.frontier (.fuel ⟨1⟩), ([] : Effect4.Trace.Log)) !=
  (RunResult.frontier (.fuel ⟨2⟩), ([] : Effect4.Trace.Log)))

-- and equal once observed.
#guard observe (.frontier (.fuel ⟨1⟩)) [] == observe (.frontier (.fuel ⟨2⟩)) []

-- A terminal pair is genuinely antisymmetric: `done 1` and `done 2` are not
-- below one another.
#guard !obsLe (.done (.nat 1), []) (.done (.nat 2), [])

/-! ## The region programs

`regionNested`, `regionTwoFail` and `regionBothSucceed` are the three programs
`harness/trace/Generate.lean` carries goldens for. `regionMerged` is the D2
carrier's own witness: a failing release under a failing body, whose merged
list keeps both, in close order. -/

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

def rcellTable : List OpSpec := familyTable RCell.rows

/-- Operation positions in `rcellTable`. -/
def opAcquire : OperationId := ⟨2⟩
def opRelease : OperationId := ⟨3⟩
def opBoom : OperationId := ⟨4⟩
def opReleaseBoom : OperationId := ⟨5⟩

def rblock (id : Nat) (region : Option Nat) (params : List String) (term : RegionTerm) :
    RegionBlock String :=
  { id := ⟨id⟩, region := region.map RegionId.mk, params := params, term := term }

def rregion (id : Nat) (parent : Option Nat) (continue_ : Nat) : RegionRow String :=
  { id := ⟨id⟩, parent := parent.map RegionId.mk, continue_ := ⟨continue_⟩, resultTy := "number" }

def regionFlowOf (regions : List (RegionRow String)) (blocks : List (RegionBlock String)) :
    RegionFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩, inputTy := "number", resultTy := "number",
    regions := regions, blocks := blocks }

def vars (n : Nat) : List Var := (List.range n).map Var.mk

/-- Two nested regions, each acquiring a resource, the inner body failing. -/
def regionNested : RegionFlow String := regionFlowOf [rregion 1 none 7, rregion 2 (some 1) 6]
  [ rblock 0 none ["number"] (.enter ⟨1⟩ ⟨1⟩ (vars 1))
  , rblock 1 (some 1) ["number"] (.acquire opAcquire ⟨0⟩ opRelease ⟨2⟩ (vars 1))
  , rblock 2 (some 1) ["number", "number"] (.enter ⟨2⟩ ⟨3⟩ (vars 2))
  , rblock 3 (some 2) ["number", "number"] (.acquire opAcquire ⟨0⟩ opRelease ⟨4⟩ (vars 2))
  , rblock 4 (some 2) ["number", "number", "number"] (.plain (.perform opBoom ⟨0⟩ ⟨5⟩ (vars 3)))
  , rblock 5 (some 2) ["number", "number", "number", "number"] (.leave ⟨3⟩)
  , rblock 6 (some 1) ["number"] (.leave ⟨0⟩)
  , rblock 7 none ["number"] (.plain (.ret ⟨0⟩)) ]

/-- Two resources in one region, then a failing body. -/
def regionTwoFail : RegionFlow String := regionFlowOf [rregion 1 none 5]
  [ rblock 0 none ["number"] (.enter ⟨1⟩ ⟨1⟩ (vars 1))
  , rblock 1 (some 1) ["number"] (.acquire opAcquire ⟨0⟩ opRelease ⟨2⟩ (vars 1))
  , rblock 2 (some 1) ["number", "number"] (.acquire opAcquire ⟨1⟩ opRelease ⟨3⟩ (vars 2))
  , rblock 3 (some 1) ["number", "number", "number"] (.plain (.perform opBoom ⟨0⟩ ⟨4⟩ (vars 3)))
  , rblock 4 (some 1) ["number", "number", "number", "number"] (.leave ⟨3⟩)
  , rblock 5 none ["number"] (.plain (.ret ⟨0⟩)) ]

/-- One resource, a clean leave: the release sees success and the run succeeds. -/
def regionBothSucceed : RegionFlow String := regionFlowOf [rregion 1 none 3]
  [ rblock 0 none ["number"] (.enter ⟨1⟩ ⟨1⟩ (vars 1))
  , rblock 1 (some 1) ["number"] (.acquire opAcquire ⟨0⟩ opRelease ⟨2⟩ (vars 1))
  , rblock 2 (some 1) ["number", "number"] (.leave ⟨1⟩)
  , rblock 3 none ["number"] (.plain (.ret ⟨0⟩)) ]

/-- A failing release under a failing body: the merged list keeps both. -/
def regionMerged : RegionFlow String := regionFlowOf [rregion 1 none 4]
  [ rblock 0 none ["number"] (.enter ⟨1⟩ ⟨1⟩ (vars 1))
  , rblock 1 (some 1) ["number"] (.acquire opAcquire ⟨0⟩ opReleaseBoom ⟨2⟩ (vars 1))
  , rblock 2 (some 1) ["number", "number"] (.plain (.perform opBoom ⟨0⟩ ⟨3⟩ (vars 2)))
  , rblock 3 (some 1) ["number", "number", "number"] (.leave ⟨2⟩)
  , rblock 4 none ["number"] (.plain (.ret ⟨0⟩)) ]

def admit? (raw : RegionFlow String) : Option (CheckedRegionFlow (tableAlphabet ⟨0⟩ rcellTable)) :=
  match admitRegions (tableAlphabet ⟨0⟩ rcellTable) raw with
  | .ok flow => some flow
  | .error _ => none

def service : RegionService (tableAlphabet ⟨0⟩ rcellTable) (StateT Nat Id) :=
  tableRegionService ⟨0⟩ rcellTable rcellFamily (fun _ v => v)

def naming : (tableAlphabet ⟨0⟩ rcellTable).Op → String := tableNameOf ⟨0⟩ rcellTable

/-- The observation an admitted region program makes at a given fuel. -/
def obsAt (raw : RegionFlow String) (fuel : Nat) : Option Observation :=
  (admit? raw).map fun flow => runRegionsObservation fuel flow service naming [] (.nat 5) [] 41

/-- The run result and the merged failure list at a given fuel. -/
def causeAt (raw : RegionFlow String) (fuel : Nat) : Option (RunResult × Failures) :=
  (admit? raw).map fun flow =>
    let out := ((runRegionsCause fuel flow service naming [] (.nat 5)).run []).run 41
    (out.1.1.1.1, out.1.1.2)

/-- The fuel `regionFuelFor` allots. -/
def allotAt (raw : RegionFlow String) : Option Nat :=
  (admit? raw).map fun flow => regionFuelFor flow.flow []

/-- The least fuel at which the run settles, searched below the allotment. -/
def settlingFuel (raw : RegionFlow String) : Option Nat :=
  match allotAt raw with
  | none => none
  | some bound => (List.range (bound + 1)).find? fun f => ((obsAt raw f).map Observation.settled).getD false

/-- Whether the observation at `i` is below the observation at `j`. -/
def belowAt (raw : RegionFlow String) (i j : Nat) : Bool :=
  match obsAt raw i, obsAt raw j with
  | some a, some b => Observation.le a b
  | _, _ => false

/-- Whether the log at `i` is a prefix of the log at `j`. -/
def prefixAt (raw : RegionFlow String) (i j : Nat) : Bool :=
  match obsAt raw i, obsAt raw j with
  | some a, some b => logPrefix a.log b.log
  | _, _ => false

/-! ## Receipts -/

-- All four region programs are admitted.
#guard (admit? regionNested).isSome
#guard (admit? regionTwoFail).isSome
#guard (admit? regionBothSucceed).isSome
#guard (admit? regionMerged).isSome

-- `regionFuelFor` is the erased flow's allotment: `(|tape| + 1) * |blocks| + 1`
-- on the empty tape, so one per block plus one.
#guard allotAt regionNested == some 9
#guard allotAt regionTwoFail == some 7
#guard allotAt regionBothSucceed == some 5
#guard allotAt regionMerged == some 6

-- `runRegions_fuelFor_finishes`, instantiated: the allotment settles every run,
-- and it is not tight -- each settles strictly below it.
#guard ((obsAt regionNested 9).map Observation.settled) == some true
#guard ((obsAt regionTwoFail 7).map Observation.settled) == some true
#guard ((obsAt regionBothSucceed 5).map Observation.settled) == some true
#guard ((obsAt regionMerged 6).map Observation.settled) == some true
#guard settlingFuel regionNested == some 5
#guard settlingFuel regionTwoFail == some 4
#guard settlingFuel regionBothSucceed == some 4
#guard settlingFuel regionMerged == some 3

-- `regionLoop_frontier_live`, instantiated: one fuel below the settling fuel
-- the run is a live `fuel` frontier and the merged failure list is untouched.
#guard causeAt regionNested 4 == some (.frontier (.fuel ⟨4⟩), [])
#guard causeAt regionTwoFail 3 == some (.frontier (.fuel ⟨3⟩), [])
#guard causeAt regionBothSucceed 3 == some (.frontier (.fuel ⟨3⟩), [])
#guard causeAt regionMerged 2 == some (.frontier (.fuel ⟨2⟩), [])
#guard ((obsAt regionNested 4).map Observation.isLive) == some true
#guard ((obsAt regionTwoFail 3).map Observation.isLive) == some true
#guard ((obsAt regionBothSucceed 3).map Observation.isLive) == some true
#guard ((obsAt regionMerged 2).map Observation.isLive) == some true

-- The live frontier's log is a prefix of the settled one's: nothing already
-- observed is rewritten when the fuel is raised.
#guard prefixAt regionNested 4 5
#guard prefixAt regionTwoFail 3 4
#guard prefixAt regionBothSucceed 3 4
#guard prefixAt regionMerged 2 3

-- `runRegions_obs_mono`/`_chain`, instantiated: every fuel below the allotment
-- observes below the allotment's observation.
#guard (List.range 10).all fun k => belowAt regionNested k 9
#guard (List.range 8).all fun k => belowAt regionTwoFail k 7
#guard (List.range 6).all fun k => belowAt regionBothSucceed k 5
#guard (List.range 7).all fun k => belowAt regionMerged k 6

-- `runRegions_obs_stable`, instantiated: past the allotment nothing changes.
#guard obsAt regionNested 9 == obsAt regionNested 40
#guard obsAt regionTwoFail 7 == obsAt regionTwoFail 40
#guard obsAt regionBothSucceed 5 == obsAt regionBothSucceed 40
#guard obsAt regionMerged 6 == obsAt regionMerged 40

-- The D2 merged failure carrier. A body failure alone merges to one reason;
-- a failing release under a failing body keeps both, body failure first --
-- the close order `closeFrame_failure_merge` fixes. The wire keeps the head,
-- which is what `RunResult.failed` reports (`regionLoop_failed_head`).
#guard causeAt regionNested 9 == some (.failed (.str "boom"), [.str "boom"])
#guard causeAt regionTwoFail 7 == some (.failed (.str "boom"), [.str "boom"])
#guard causeAt regionMerged 6 ==
  some (.failed (.str "boom"), [.str "boom", .str "boom"])
#guard causeAt regionBothSucceed 5 == some (.done (.nat 5), [])

-- The whole observation of the smallest program, settled and one fuel below.
#guard obsAt regionBothSucceed 5 == some (.terminal (.done (.nat 5))
  [ .enter 1
  , .op "acquire" (.nat 5), .answer "acquire" (.nat 5)
  , .leave 1 (.success (.nat 5))
  , .finalizer 1 (.success (.nat 5))
  , .op "release" (.nat 5), .answer "release" .unit
  , .done (.success (.nat 5)) ])

#guard obsAt regionBothSucceed 3 == some (.live
  [ .enter 1
  , .op "acquire" (.nat 5), .answer "acquire" (.nat 5)
  , .leave 1 (.success (.nat 5))
  , .finalizer 1 (.success (.nat 5))
  , .op "release" (.nat 5), .answer "release" .unit ])

end Effect4Test.Semantics.ApproximationContract
