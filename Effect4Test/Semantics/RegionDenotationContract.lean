/-
Contract packet: `test/contracts/flow-denotation.contract.md` (D1, extended by
the remaining third of D2, `Effect4/Semantics/RegionDenotation.lean`).

Frozen: the scope summand (`ScopeName`, `ScopeFam`, `ScopeSig`), the fallible
alphabet summand (`RegionFam`, `RegionOpSig`), the region signature sum
`RegionSig`, the scope handler and the region handler, the fuelled region
denotation, and the interpreting run. Executable receipts: for the three region
goldens of `harness/trace/Generate.lean` — `regionNested`, `regionTwoFail` and
`regionBothSucceed` — the region runner's result, unconsumed tape, log and
service state equal `interpret (regionHandler …) (denoteRegions …)` run from the
empty stack and closed by the outcome rows, which is `runRegions_eq_interpret`
as an instance. A fourth, region-free program instantiates `runRegions_erase`.
Doc comments cannot precede `#guard`, so the receipts carry line comments.
-/

import Effect4.Semantics.RegionDenotation
import Effect4.Meta.Derive

namespace Effect4Test.Semantics.RegionDenotationContract

open Effects Effect4 Effect4.Flow Effect4.Meta Effect4.Target.EffectV4
open Effects.Trace (Val)

/-! ## The frozen surface -/

#check @Effect4.Flow.RegionFam
#check @Effect4.Flow.RegionOpSig
#check @Effect4.Flow.RegionService.toService
#check @Effect4.Flow.Stack
#check @Effect4.Flow.ScopeName
#check @Effect4.Flow.ScopeName.Param
#check @Effect4.Flow.ScopeName.Answer
#check @Effect4.Flow.ScopeFam
#check @Effect4.Flow.ScopeSig
#check @Effect4.Flow.RegionSig
#check @Effect4.Flow.ScopeM
#check @Effect4.Flow.Handler.overStack
#check @Effect4.Flow.regionTracedService
#check @Effect4.Flow.regionTraceHandler
#check @Effect4.Flow.scopeHandler
#check @Effect4.Flow.regionHandler
#check @Effect4.Flow.denoteRegionsFuel
#check @Effect4.Flow.denoteRegions
#check @Effect4.Flow.closeCause
#check @Effect4.Flow.interpretRegionsFrom
#check @Effect4.Flow.interpretRegions
#check @Effect4.Flow.AllPlain
#check @Effect4.Flow.FlowService.toRegionService

/-! ## The laws -/

#check @Effect4.Flow.regionLoop_eq_interpret
#check @Effect4.Flow.runRegionsCause_eq_interpret
#check @Effect4.Flow.runRegions_eq_interpret
#check @Effect4.Flow.runRegionsDefault_eq_interpret
#check @Effect4.Flow.regionLoop_erase
#check @Effect4.Flow.runRegions_erase

/-! ## The signature sum, spelled out -/

-- The scope summand's four names, with the request and answer each carries.
example : (ScopeName.enter : ScopeName (tableAlphabet ⟨0⟩ [])).Param = RegionId := rfl
example : (ScopeName.enter : ScopeName (tableAlphabet ⟨0⟩ [])).Answer = Unit := rfl
example (op releaser : (tableAlphabet ⟨0⟩ []).Op) :
    (ScopeName.acquire op releaser).Param = Val := rfl
-- `acquire` answers an `Option`: `none` is the runner's stuck arm on an empty stack.
example (op releaser : (tableAlphabet ⟨0⟩ []).Op) :
    (ScopeName.acquire op releaser).Answer = Option (Except Val Val) := rfl
example : (ScopeName.leave : ScopeName (tableAlphabet ⟨0⟩ [])).Param = Val := rfl
-- `leave` answers the merged failure list of `closeFrame`, empty on a clean close.
example : (ScopeName.leave : ScopeName (tableAlphabet ⟨0⟩ [])).Answer = Option Failures := rfl
example : (ScopeName.fail : ScopeName (tableAlphabet ⟨0⟩ [])).Param = Val := rfl
example : (ScopeName.fail : ScopeName (tableAlphabet ⟨0⟩ [])).Answer = Failures := rfl

-- The alphabet summand of a region run answers `Except Val Val`, not `Val`.
example (alphabet : FlowAlphabet String) (op : alphabet.Op) (request : Val) :
    (RegionOpSig alphabet).Answer ⟨op, request⟩ = Except Val Val := rfl

-- The sum is scope, then D1's two summands, definitionally.
example (alphabet : FlowAlphabet String) :
    RegionSig alphabet = ScopeSig alphabet ⊕ₛ (RegionOpSig alphabet ⊕ₛ DecSig) := rfl

-- The decision summand is D1's, unchanged.
example (alphabet : FlowAlphabet String) (site : DecisionId) (branch : Bool) :
    (RegionSig alphabet).Answer (decideOp (alphabet := alphabet) site branch) = Unit := rfl

/-! ## The three region goldens

Copied from `harness/trace/Generate.lean`; the same programs
`Effect4Test/Flow/RegionRunnerContract.lean` pins the runner on. -/

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

/-- Two nested regions, each acquiring a resource, the inner body failing. -/
def regionNested : RegionFlow String := regionFlow [rregion 1 none 7, rregion 2 (some 1) 6]
  [ rblock 0 none ["number"] (.enter ⟨1⟩ ⟨1⟩ (vars 1))
  , rblock 1 (some 1) ["number"] (.acquire opAcquire ⟨0⟩ opRelease ⟨2⟩ (vars 1))
  , rblock 2 (some 1) ["number", "number"] (.enter ⟨2⟩ ⟨3⟩ (vars 2))
  , rblock 3 (some 2) ["number", "number"] (.acquire opAcquire ⟨0⟩ opRelease ⟨4⟩ (vars 2))
  , rblock 4 (some 2) ["number", "number", "number"] (.plain (.perform opBoom ⟨0⟩ ⟨5⟩ (vars 3)))
  , rblock 5 (some 2) ["number", "number", "number", "number"] (.leave ⟨3⟩)
  , rblock 6 (some 1) ["number"] (.leave ⟨0⟩)
  , rblock 7 none ["number"] (.plain (.ret ⟨0⟩)) ]

/-- Two resources in one region, then a failing body. -/
def regionTwoFail : RegionFlow String := regionFlow [rregion 1 none 5]
  [ rblock 0 none ["number"] (.enter ⟨1⟩ ⟨1⟩ (vars 1))
  , rblock 1 (some 1) ["number"] (.acquire opAcquire ⟨0⟩ opRelease ⟨2⟩ (vars 1))
  , rblock 2 (some 1) ["number", "number"] (.acquire opAcquire ⟨1⟩ opRelease ⟨3⟩ (vars 2))
  , rblock 3 (some 1) ["number", "number", "number"] (.plain (.perform opBoom ⟨0⟩ ⟨4⟩ (vars 3)))
  , rblock 4 (some 1) ["number", "number", "number", "number"] (.leave ⟨3⟩)
  , rblock 5 none ["number"] (.plain (.ret ⟨0⟩)) ]

/-- One resource, a clean leave: the release sees success and the run succeeds. -/
def regionBothSucceed : RegionFlow String := regionFlow [rregion 1 none 3]
  [ rblock 0 none ["number"] (.enter ⟨1⟩ ⟨1⟩ (vars 1))
  , rblock 1 (some 1) ["number"] (.acquire opAcquire ⟨0⟩ opRelease ⟨2⟩ (vars 1))
  , rblock 2 (some 1) ["number", "number"] (.leave ⟨1⟩)
  , rblock 3 none ["number"] (.plain (.ret ⟨0⟩)) ]

/-- A region flow that declares no region at all: every block is `plain`. -/
def regionFree : RegionFlow String := regionFlow []
  [ rblock 0 none ["number"] (.plain (.perform opAcquire ⟨0⟩ ⟨1⟩ (vars 1)))
  , rblock 1 none ["number", "number"] (.plain (.ret ⟨1⟩)) ]

def service : RegionService (tableAlphabet ⟨0⟩ table) (StateT Nat Id) :=
  Flow.tableRegionService ⟨0⟩ table rcellFamily fun _ v => v

def nameOf : (tableAlphabet ⟨0⟩ table).Op → String := tableNameOf ⟨0⟩ table

def admitted (raw : RegionFlow String) : Option (CheckedRegionFlow (tableAlphabet ⟨0⟩ table)) :=
  (admitRegions (tableAlphabet ⟨0⟩ table) raw).toOption

/-- The region runner's own run: result, unconsumed tape, log and service state. -/
def runner (raw : RegionFlow String) : Option (((RunResult × Tape) × Effect4.Trace.Log) × Nat) :=
  (admitted raw).map fun flow =>
    ((Flow.runRegions (Flow.fuelFor flow.flow.erase []) flow service nameOf [] (.nat 5)).run
      []).run 41

/-- The same run read through the algebra: `interpret` of the region denotation
under `regionHandler`, from the empty stack, closed by the outcome rows, with
the merged failure projected to the wire face. -/
def denoted (raw : RegionFlow String) : Option (((RunResult × Tape) × Effect4.Trace.Log) × Nat) :=
  (admitted raw).map fun flow =>
    (((·.1) <$> Flow.interpretRegions service nameOf
      (Flow.denoteRegions (Flow.fuelFor flow.flow.erase []) flow [] (.nat 5))).run []).run 41

-- All four programs are admitted.
#guard (admitted regionNested).isSome
#guard (admitted regionTwoFail).isSome
#guard (admitted regionBothSucceed).isSome
#guard (admitted regionFree).isSome

-- T1 for regions on the three goldens: result, tape, log and state all agree.
#guard denoted regionNested = runner regionNested
#guard denoted regionTwoFail = runner regionTwoFail
#guard denoted regionBothSucceed = runner regionBothSucceed

-- And the log the algebra writes is the golden's own: `enter` and `acquire`
-- come from `scopeHandler`, `leave` and `finalizer` from its `leave` arm
-- (which is `closeFrame`, so L1 and L2 are that arm's facts), `op`/`answer`/
-- `failed` from `regionTraceHandler`, and `done` from `outcomeRows`.
#guard (denoted regionNested).map (fun run => run.1.2) = some
  [ .enter 1
  , .op "acquire" (.nat 5), .answer "acquire" (.nat 5)
  , .enter 2
  , .op "acquire" (.nat 5), .answer "acquire" (.nat 5)
  , .op "boom" (.nat 5), .failed "boom" (.str "boom")
  , .leave 2 (.failure (.str "boom")), .finalizer 2 (.failure (.str "boom"))
  , .op "release" (.nat 5), .answer "release" .unit
  , .leave 1 (.failure (.str "boom")), .finalizer 1 (.failure (.str "boom"))
  , .op "release" (.nat 5), .answer "release" .unit
  , .done (.failure (.str "boom")) ]

#guard (denoted regionBothSucceed).map (fun run => run.1.2) = some
  [ .enter 1
  , .op "acquire" (.nat 5), .answer "acquire" (.nat 5)
  , .leave 1 (.success (.nat 5))
  , .finalizer 1 (.success (.nat 5)), .op "release" (.nat 5), .answer "release" .unit
  , .done (.success (.nat 5)) ]

#guard (denoted regionTwoFail).map (fun run => run.1.1.1) =
  some (RunResult.failed (.str "boom"))
#guard (denoted regionBothSucceed).map (fun run => run.1.1.1) =
  some (RunResult.done (.nat 5))

/-! ## The corollary: no regions, and D2 is D1 -/

-- `regionFree` declares no region, so `AllPlain` holds by computation.
example : AllPlain regionFree :=
  allPlain_of_all (by decide)

/-- The plain runner of `Effect4/Semantics/Runs.lean` on the erasure, through
the same table service. -/
def plainRunner (raw : RegionFlow String) :
    Option (((RunResult × Tape) × Effect4.Trace.Log) × Nat) :=
  (admitted raw).map fun flow =>
    ((Flow.runTape (Flow.fuelFor flow.flow.erase []) flow.checked
      (tableService ⟨0⟩ table
        (fun name request => (fun result => result.toOption.getD .unit) <$>
          rcellFamily name request)
        (fun _ v => v))
      nameOf [] (.nat 5)).run []).run 41

-- On a region-free flow the region runner and the plain runner agree on
-- everything the wire can see; this is `runRegions_erase` computed.
#guard runner regionFree = plainRunner regionFree
#guard (runner regionFree).map (fun run => run.1.2) = some
  [ .op "acquire" (.nat 5), .answer "acquire" (.nat 5)
  , .done (.success (.nat 5)) ]

end Effect4Test.Semantics.RegionDenotationContract
