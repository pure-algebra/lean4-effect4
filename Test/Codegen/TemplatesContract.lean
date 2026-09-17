import Effect4.Codegen.Templates
import Test.Program.Gen

/-!
# Test.Codegen.TemplatesContract — the table-driven printer prints what the hand printer prints

`Codegen/Templates.lean` stands beside `Codegen/Print.lean` until their agreement is a theorem
(R4.3). Until then this battery is the agreement: `printT = print`, the refusals included, on a
sample of every constructor of the three skeleton families under every classifier, at more than
one environment length, and on the 400 programs of the seeded corpus. It also pins the table's own
shape: every skeleton has distinct holes (what `inst_of_match` asks), every row names a real
constructor with a depth per argument, and no program ever reaches the table-defect refusal.
-/

namespace Test.Codegen.TemplatesContract

open Effect4 Effect4.Program
open Effect4.Codegen.Template
open Effect4.Codegen.Templates

def sig : Signature NativeOp := nativeSignature

/-- Agreement of two printings: the same expression, or the same refusal. -/
def same : Except PrintRefusal TypeScript.Expr → Except PrintRefusal TypeScript.Expr → Bool
  | .ok a, .ok b => a == b
  | .error a, .error b => decide (a = b)
  | _, _ => false

def agrees (n : Nat) (e : Eff NativeOp) : Bool := same (printT sig n e) (print sig n e)

def agreesLayer (l : LayerTerm NativeOp) : Bool := same (printLayerT sig l) (printLayer sig l)

private def u : Eff NativeOp := .succeed (.lit .unit)
private def v : Eff NativeOp := .bind u (.succeed (.var 0))
private def t : Term := .lit .unit
private def key : ServiceKey := ⟨⟨7⟩, ⟨4⟩⟩
private def child : Effect4.Supervision.ForkOptions := ⟨false, false, .inherit⟩
private def detached : Effect4.Supervision.ForkOptions := ⟨true, true, .uninterruptible⟩

/-- One program per constructor and classifier of `Eff`. -/
def effSamples : List (Eff NativeOp) :=
  [ u, .fail t, .failCause (.fail t), .sync t, .suspend v, .perform .refMake t, .bind v v
  , .gen (.cons (.bindYield v) (.cons (.yieldDiscard u) (.cons (.ret (.var 0)) .nil)))
  , .gen (.cons (.ifElse t (.cons (.ret t) .nil) (.cons .breakLoop .nil))
      (.cons (.whileTrue (.cons (.bindYield u) (.cons .breakLoop .nil))) .nil))
  , .catchCause v v, .catchIf (.lit (.bool true)) v v, .catchIf (.var 0) v v
  , .matchCause v v v, .onExit v v, .exit v, .uninterruptible v, .interruptible v
  , .select t .bool v v, .select t .option v v, .select t (.tag "cons") v v
  , .iterate none t t t t v, .iterate (some .nat) t t t t v
  , .iterate (some (.handle "no such spelling")) t t t t v
  , .yieldNow 3, .awaitFiber t .joinEffect, .awaitFiber t .awaitValue
  , .scoped v, .acquireRelease v v
  , .provideLayer (.effectDiscard v) true v, .provideLayer (.effectDiscard v) false v
  , .service key, .provideService key t v ]

/-- One action per constructor and classifier, the five refused ones included. -/
def actionSamples : List (ActionTerm NativeOp) :=
  [ .fork v child, .fork v detached, .forkIn v child t, .forkScoped v detached, .runIn t t
  , .interrupt t, .interruptScoped t, .interruptAll t none, .interruptAll t (some t)
  , .awaitAll t, .awaitAllFailFast t, .snapshotChildren, .awaitNewChildren t
  , .raceAll (.cons v (.cons u .nil)), .raceAll .nil, .setContext t, .getContext, .getId
  , .closeScope t t ]

/-- One layer per constructor. -/
def layerSamples : List (LayerTerm NativeOp) :=
  [ .succeed key (.nat 1), .effect key v, .effectDiscard v
  , .provide (.effectDiscard u) (.effectDiscard v), .provideMerge (.effectDiscard u) (.effectDiscard v)
  , .merge (.effectDiscard u) (.effectDiscard v), .fresh (.effectDiscard v), .orDie (.effectDiscard v)
  , .ref [1, 0, 0], .mergeAll (.cons (.effectDiscard u) (.cons (.effectDiscard v) .nil))
  , .mergeAll .nil ]

/-! ## The agreement -/

#guard effSamples.all (agrees 0)
#guard effSamples.all (agrees 5)
#guard actionSamples.all fun a => agrees 0 (.withFiber a) && agrees 2 (.withFiber a)
#guard layerSamples.all agreesLayer
#guard layerSamples.all fun l => agrees 3 (.provideLayer l false u)

-- the corpus: every program the seeded generator writes
#guard (Test.Program.Gen.corpus 400 4).all (agrees 0)

/-! ## The refusals are the hand printer's, and the table's own defect never shows -/

def isTableDefect : Except PrintRefusal TypeScript.Expr → Bool
  | .error (.internalAction name) => name.startsWith "table:"
  | _ => false

#guard same (printT sig 0 (.withFiber (.setContext t))) (.error (.internalAction "setContext"))
#guard same (printT sig 0 (.iterate (some (.handle "no such spelling")) t t t t u))
  (print sig 0 (.iterate (some (.handle "no such spelling")) t t t t u))
#guard !(effSamples.any fun e => isTableDefect (printT sig 0 e))
#guard !(actionSamples.any fun a => isTableDefect (printT sig 0 (.withFiber a)))
#guard !((Test.Program.Gen.corpus 400 4).any fun e => isTableDefect (printT sig 0 e))

/-! ## The table's shape -/

-- every skeleton has distinct holes
#guard table.all fun row => match row.out with
  | .tpl tp => decide (Linear tp)
  | .refuse _ => true

-- every row names a constructor of its family, with one depth per argument
#guard table.all fun row => match argSorts row.fam row.ctor with
  | some sorts => sorts.length == row.depth.length
  | none => false

-- every constructor of the three skeleton families has a row, except the two hand fields
#guard ((ctorNames .eff).filter fun c => !(table.any fun row => row.fam == .eff && row.ctor == c))
  == ["perform", "gen"]
#guard (ctorNames .action).all fun c => table.any fun row => row.fam == .action && row.ctor == c
#guard (ctorNames .layer).all fun c => table.any fun row => row.fam == .layer && row.ctor == c

-- a hole is an argument: no skeleton names a hole past its constructor's arity
#guard table.all fun row => match row.out, argSorts row.fam row.ctor with
  | .tpl tp, some sorts => (holes tp).all (· < sorts.length)
  | _, _ => true

end Test.Codegen.TemplatesContract
