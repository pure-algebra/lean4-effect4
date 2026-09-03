import Effect4.Target.TypeScript.EffectV4

/-!
# Target.TypeScript.Lower

Owner: the lowering rule census. `docs/LOWERING-COVERAGE.md` owns the
vocabulary: a rule is one tagged definition in `Effect4/Target/TypeScript/`
(`lowering: rule.<id>`), and this module is the denominator the ledger joins
tags, goldens, host receipts, property batches, type receipts and proofs to.
`Rule.all` and the tag set must agree in both directions; the gate checks it.

Straight-line lowering from a `Script` lives in
`Effect4/Target/TypeScript/EffectV4.lean` beside the rows; dispatch-form
lowering from a checked flow lives in `FlowLower.lean` and its eight rules
are the second half of the census.
-/

namespace Effect4.Target.EffectV4

/-- The lowering rules, one per tagged definition. -/
inductive Rule where
  | serviceAcquire
  | nullaryValue
  | performCall
  | performBind
  | performDiscard
  | atomCall
  | ret
  | errorAbort
  -- dispatch-form lowering of a checked flow (`FlowLower.lean`)
  | dispatchLoop
  | blockCase
  | paramMove
  | flowPerform
  | flowAtom
  | flowLiteral
  | chooseIf
  | flowRet
deriving DecidableEq, Repr

namespace Rule

/-- The id spelled in the definition's docstring tag and in the ledger. -/
def id : Rule → String
  | serviceAcquire => "service-acquire"
  | nullaryValue => "nullary-value"
  | performCall => "perform-call"
  | performBind => "perform-bind"
  | performDiscard => "perform-discard"
  | atomCall => "atom-call"
  | ret => "ret"
  | errorAbort => "error-abort"
  | dispatchLoop => "dispatch-loop"
  | blockCase => "block-case"
  | paramMove => "param-move"
  | flowPerform => "flow-perform"
  | flowAtom => "flow-atom"
  | flowLiteral => "flow-literal"
  | chooseIf => "choose-if"
  | flowRet => "flow-ret"

/-- Every rule, in ledger order. -/
def all : List Rule :=
  [serviceAcquire, nullaryValue, performCall, performBind, performDiscard, atomCall, ret, errorAbort,
   dispatchLoop, blockCase, paramMove, flowPerform, flowAtom, flowLiteral, chooseIf, flowRet]

theorem all_nodup : all.Nodup := by decide

theorem mem_all (rule : Rule) : rule ∈ all := by
  cases rule <;> decide

/-- Resolve a ledger id. -/
def ofId? (id : String) : Option Rule :=
  all.find? fun rule => rule.id == id

theorem ofId?_id (rule : Rule) : ofId? rule.id = some rule := by
  cases rule <;> rfl

end Rule

/-- The rules a straight-line script exercises, in first-use order. -/
def Script.ruleSet (rows : ServiceRow) (script : Script) : List Rule :=
  let step (acc : List Rule) (rule : Rule) : List Rule :=
    if acc.contains rule then acc else acc ++ [rule]
  let atoms (acc : List Rule) (term : PureTerm) : List Rule :=
    if term.hasApp then step acc .atomCall else acc
  script.steps.foldl (init := [.serviceAcquire]) fun acc s =>
    match s with
    | .perform bind op args =>
        let nullary := (rows.row? op).map (·.params.isEmpty) |>.getD false
        let acc := step acc (if nullary then .nullaryValue else .performCall)
        let acc := step acc (if bind.isNone then .performDiscard else .performBind)
        let acc := if ((rows.row? op).bind (·.error)).isSome then step acc .errorAbort else acc
        args.foldl atoms acc
    | .ret value => atoms (step acc .ret) value

end Effect4.Target.EffectV4
