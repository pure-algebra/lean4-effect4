/-
Contract packet: interruption as decisions (M2). The three goldens of
`generated/traces/flow/interrupt/` as `#guard` receipts over the Lean runner,
the two halves of deferral, and the axiom report. The flows are the ones
`harness/trace/Generate.lean` emits, restated here: `Generate.lean` is a script,
not a library, so the receipts carry their own copies and the goldens are the
join. Doc comments cannot precede `#guard`, so the receipts carry line comments.
-/

import Effect4.Flow.Interrupt
import Effect4.Meta.Derive

namespace Effect4Test.Flow.InterruptContract

open Effects Effect4 Effect4.Flow Effect4.Meta Effect4.Target.EffectV4
open Effects.Trace (Val)

#check @Effect4.Flow.Point
#check @Effect4.Flow.Point.site
#check @Effect4.Flow.interruptRead
#check @Effect4.Flow.IState
#check @Effect4.Flow.isMasked
#check @Effect4.Flow.interruptPoint
#check @Effect4.Flow.unwindInterrupt
#check @Effect4.Flow.interruptLoop
#check @Effect4.Flow.runInterrupts
#check @Effect4.Flow.runInterruptsDefault
#check (@Effect4.Flow.InterruptResult.interrupted : InterruptResult)

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

/-- One interrupt tape entry at the point before the `perform` of a block. -/
def deliverAtPerform (block : Nat) : Decision := ⟨(Point.perform ⟨block⟩).site, true⟩

/-- `generated/traces/flow/interrupt/interruptUnmasked.tsv`. -/
def unmasked : RegionFlow String := regionFlow [rregion 1 none 3]
  [ rblock 0 none ["number"] (.enter ⟨1⟩ ⟨1⟩ (vars 1))
  , rblock 1 (some 1) ["number"] (.plain (.perform opPut ⟨0⟩ ⟨2⟩ (vars 1)))
  , rblock 2 (some 1) ["number", "void"] (.leave ⟨0⟩)
  , rblock 3 none ["number"] (.plain (.ret ⟨0⟩)) ]

/-- `generated/traces/flow/interrupt/interruptMasked.tsv`. -/
def masked : RegionFlow String := regionFlow [rregion 1 none 4]
  [ rblock 0 none ["number"] (.enter ⟨1⟩ ⟨1⟩ (vars 1))
  , rblock 1 (some 1) ["number"] (.acquire opAcquire ⟨0⟩ opRelease ⟨2⟩ (vars 1))
  , rblock 2 (some 1) ["number", "number"] (.plain (.perform opPut ⟨0⟩ ⟨3⟩ (vars 2)))
  , rblock 3 (some 1) ["number", "number", "void"] (.leave ⟨1⟩)
  , rblock 4 none ["number"] (.plain (.perform opPut ⟨0⟩ ⟨5⟩ (vars 1)))
  , rblock 5 none ["number", "void"] (.plain (.ret ⟨0⟩)) ]

/-- `generated/traces/flow/interrupt/interruptFinalizer.tsv`. -/
def finalizer : RegionFlow String := regionFlow [rregion 1 none 7, rregion 2 (some 1) 6]
  [ rblock 0 none ["number"] (.enter ⟨1⟩ ⟨1⟩ (vars 1))
  , rblock 1 (some 1) ["number"] (.acquire opAcquire ⟨0⟩ opRelease ⟨2⟩ (vars 1))
  , rblock 2 (some 1) ["number", "number"] (.enter ⟨2⟩ ⟨3⟩ (vars 2))
  , rblock 3 (some 2) ["number", "number"] (.acquire opAcquire ⟨0⟩ opRelease ⟨4⟩ (vars 2))
  , rblock 4 (some 2) ["number", "number", "number"] (.plain (.perform opPut ⟨0⟩ ⟨5⟩ (vars 3)))
  , rblock 5 (some 2) ["number", "number", "number", "void"] (.leave ⟨1⟩)
  , rblock 6 (some 1) ["number"] (.leave ⟨0⟩)
  , rblock 7 none ["number"] (.plain (.ret ⟨0⟩)) ]

def run (raw : RegionFlow String) (maskedRegions : List RegionId) (itape : Tape) :
    Option (InterruptResult × Effect4.Trace.Log) :=
  match admitRegions (tableAlphabet ⟨0⟩ table) raw with
  | .ok flow =>
      let r := ((Flow.runInterruptsDefault flow maskedRegions
        (Flow.tableRegionService ⟨0⟩ table rcellFamily fun _ v => v)
        (tableNameOf ⟨0⟩ table) [] itape (.nat 5)).run []).run 41
      some (r.1.1.1, r.1.2)
  | .error _ => none

-- All three flows are admitted, and their `choose` sites (there are none) lie
-- below the interrupt base, so the two tapes answer disjoint questions.
#guard (run unmasked [] []).isSome
#guard (run masked [⟨1⟩] []).isSome
#guard (run finalizer [] []).isSome
#guard sitesSeparated unmasked && sitesSeparated masked && sitesSeparated finalizer

-- The interrupt sites of the three points the goldens name.
#guard (Point.perform ⟨1⟩).site = ⟨1000003⟩
#guard (Point.perform ⟨2⟩).site = ⟨1000005⟩
#guard (Point.perform ⟨4⟩).site = ⟨1000009⟩
#guard (Point.leave ⟨1⟩).site = ⟨1000002⟩

-- Golden 1, unmasked delivery: the point before the `perform` delivers, the
-- open region closes with `interrupted`, and the run ends `done interrupted`.
-- The `perform` never runs: there is no `op put` row.
#guard run unmasked [] [deliverAtPerform 1] =
  some (.interrupted,
    [ .enter 1
    , .decide 1000003 true
    , .leave 1 .interrupted
    , .done .interrupted ])

-- Golden 2, masked deferral then delivery at unmask. Region 1 is
-- uninterruptible: the delivered answer at site 1000003+2 is kept pending, the
-- region's own `leave` point (1000002) is masked too and the region closes
-- cleanly with `success`, and the first point outside every region (1000009)
-- delivers the interrupt its own tape entry did not answer.
#guard run masked [⟨1⟩] [deliverAtPerform 2] =
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

-- Golden 3, a finalizer seeing `interrupted`: two nested regions, each holding
-- a resource; both close innermost-first with `interrupted` and each release
-- runs with that exit. This is the arm `Outcome.interrupted` had no Lean
-- producer for before M2.
#guard run finalizer [] [deliverAtPerform 4] =
  some (.interrupted,
    [ .enter 1
    , .op "acquire" (.nat 5), .answer "acquire" (.nat 5)
    , .enter 2
    , .op "acquire" (.nat 5), .answer "acquire" (.nat 5)
    , .decide 1000009 true
    , .leave 2 .interrupted, .finalizer 2 .interrupted
    , .op "release" (.nat 5), .answer "release" .unit
    , .leave 1 .interrupted, .finalizer 1 .interrupted
    , .op "release" (.nat 5), .answer "release" .unit
    , .done .interrupted ])

-- The empty interrupt tape is the uninterrupted run: exhaustion answers "not
-- delivered" and every point still writes its row.
#guard run unmasked [] [] =
  some (.done (.nat 5),
    [ .enter 1
    , .decide 1000003 false
    , .op "put" (.nat 5), .answer "put" .unit
    , .decide 1000002 false
    , .leave 1 (.success (.nat 5))
    , .done (.success (.nat 5)) ])

-- A tape entry for another point is not consumed and does not answer this one.
#guard run unmasked [] [deliverAtPerform 9] =
  some (.done (.nat 5),
    [ .enter 1
    , .decide 1000003 false
    , .op "put" (.nat 5), .answer "put" .unit
    , .decide 1000002 false
    , .leave 1 (.success (.nat 5))
    , .done (.success (.nat 5)) ])

/-! ## The site space is disjoint -/

-- No interrupt site is a `choose` site of an admitted flow (they are below the
-- base), and the two shapes of point never share a site.
example (point : Point) (choose : DecisionId) (below : choose.value < interruptBase) :
    point.site ≠ choose := Point.site_ne_choose below

example {left right : Point} (eq : left.site = right.site) : left = right := Point.site_inj eq

/-! ## Axiom report

Expected union: `propext` and `Quot.sound`. -/

#print axioms Effect4.Flow.Point.site_ge
#print axioms Effect4.Flow.Point.site_ne_choose
#print axioms Effect4.Flow.Point.site_inj
#print axioms Effect4.Flow.interruptRead_nil
#print axioms Effect4.Flow.interruptRead_hit
#print axioms Effect4.Flow.interruptRead_miss
#print axioms Effect4.Flow.interruptPoint_masked_defers
#print axioms Effect4.Flow.interruptPoint_unmasked_delivers
#print axioms Effect4.Flow.closeFrame_interrupted_log
#print axioms Effect4.Flow.frameExit_interrupted

end Effect4Test.Flow.InterruptContract
