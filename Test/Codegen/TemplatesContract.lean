import Effect4.Codegen.Templates
import Test.Program.Gen

/-!
# Test.Codegen.TemplatesContract — the table of printed clauses: its shape, and that it has no gap

`Codegen/Print.lean`'s `print` is the fold over this table. Before the hand printer was deleted
(2026-09-17) this battery was their agreement: equal, refusals included, on the samples below at
two environment lengths and on the 400 seeded programs. What it pins now is what no other battery
does: every skeleton has distinct holes (what `inst_of_match` asks), every row names a real
constructor with a depth per argument, every constructor is covered, the refusals are the named
ones, and no program ever reaches the table-defect refusal. The printed bytes are pinned by
`Test/Codegen/PrintContract.lean` and the corpus goldens.
-/

namespace Test.Codegen.TemplatesContract

open Effect4 Effect4.Program
open Effect4.Codegen.Template
open Effect4.Codegen.Templates

def sig : Signature NativeOp := nativeSignature

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

/-! ## The refusals are the named ones, and the table's own defect never shows -/

/-- Is the refusal the table's own defect, for some constructor of some family? Compared whole
against `tableDefect`: a prefix test on the string would bring `Classical.choice` through the
string library, and the axiom gate audits this battery too. -/
def isTableDefect : Except PrintRefusal TypeScript.Expr → Bool
  | .error refusal =>
    [EffFam.eff, .stmt, .stmts, .effs, .action, .layer, .layers].any fun fam =>
      (ctorNames fam).any fun ctor => decide (refusal = tableDefect ctor)
  | .ok _ => false

-- the defect is recognised when it is there
#guard isTableDefect (.error (tableDefect "bind"))
#guard !isTableDefect (.error (.internalAction "setContext"))

#guard printT sig 0 (.withFiber (.setContext t)) matches .error (.internalAction "setContext")
#guard printT sig 0 (.iterate (some (.handle "no such spelling")) t t t t u) matches
  .error (.typeSpelling _)
-- every sample prints or is refused by a named refusal, at two environment lengths
#guard layerSamples.all fun l => !isTableDefect (printLayerT sig l)
#guard !(effSamples.any fun e => isTableDefect (printT sig 5 e))
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
