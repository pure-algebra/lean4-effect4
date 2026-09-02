/-
Contract packet: `test/contracts/flow-diagnostic-precision.contract.md`

Breaker-owned red battery. The implementation phase must not edit this file.
It is red until precise witness-validity declarations and proofs exist.
-/

import Effects.Flow.Admission

namespace Effect4Test.Flow.DiagnosticPrecisionContract

open Effects

universe uA uB uTy uOp

section SurfaceSnapshot

/-! D0: a generic first failure in indexed source order. -/

#check (@FirstFailureAt :
  {alpha : Type uA} -> {beta : Type uB} ->
  List alpha -> (Nat -> alpha -> beta -> Prop) ->
  Nat -> alpha -> beta -> Prop)

#check (@FirstFailureAt.mk :
  forall {alpha : Type uA} {beta : Type uB}
      {source : List alpha} {FailureAt : Nat -> alpha -> beta -> Prop}
      {index : Nat} {item : alpha} {failure : beta},
    source[index]? = some item ->
    FailureAt index item failure ->
    (forall priorIndex priorItem,
      priorIndex < index ->
      source[priorIndex]? = some priorItem ->
      forall priorFailure,
        Not (FailureAt priorIndex priorItem priorFailure)) ->
    FirstFailureAt source FailureAt index item failure)

#check (@FirstFailureAt.source_at :
  forall {alpha : Type uA} {beta : Type uB}
      {source : List alpha} {FailureAt : Nat -> alpha -> beta -> Prop}
      {index : Nat} {item : alpha} {failure : beta},
    FirstFailureAt source FailureAt index item failure ->
    source[index]? = some item)

#check (@FirstFailureAt.fails_at :
  forall {alpha : Type uA} {beta : Type uB}
      {source : List alpha} {FailureAt : Nat -> alpha -> beta -> Prop}
      {index : Nat} {item : alpha} {failure : beta},
    FirstFailureAt source FailureAt index item failure ->
    FailureAt index item failure)

#check (@FirstFailureAt.prior_clear :
  forall {alpha : Type uA} {beta : Type uB}
      {source : List alpha} {FailureAt : Nat -> alpha -> beta -> Prop}
      {index : Nat} {item : alpha} {failure : beta},
    FirstFailureAt source FailureAt index item failure ->
    forall priorIndex priorItem,
      priorIndex < index ->
      source[priorIndex]? = some priorItem ->
      forall priorFailure,
        Not (FailureAt priorIndex priorItem priorFailure))

/-! D1: all eleven ordered local-term failure forms. -/

#check (@TermFailureValid :
  {Ty : Type uTy} ->
  FlowAlphabet.{uTy, uOp} Ty -> RawFlow Ty -> RawBlock Ty ->
  DiagnosticPayload Ty -> Prop)

#check (@TermFailureValid.retTypeMismatch :
  forall {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} {block : RawBlock Ty},
    block.term = .ret ->
    block.inputTy ≠ raw.resultTy ->
    TermFailureValid alphabet raw block
      (.typeMismatch raw.resultTy block.inputTy))

#check (@TermFailureValid.jumpMissing :
  forall {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} {block : RawBlock Ty} {target : BlockId},
    block.term = .jump target ->
    lookupBlock raw target = none ->
    TermFailureValid alphabet raw block (.block target))

#check (@TermFailureValid.jumpTypeMismatch :
  forall {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} {block : RawBlock Ty} {target : BlockId}
      {targetBlock : RawBlock Ty},
    block.term = .jump target ->
    lookupBlock raw target = some targetBlock ->
    targetBlock.inputTy ≠ block.inputTy ->
    TermFailureValid alphabet raw block
      (.typeMismatch block.inputTy targetBlock.inputTy))

#check (@TermFailureValid.performUnknownOperation :
  forall {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} {block : RawBlock Ty}
      {operation : OperationId} {target : BlockId},
    block.term = .perform operation target ->
    alphabet.lookup operation = none ->
    TermFailureValid alphabet raw block (.operation operation))

#check (@TermFailureValid.performMissingTarget :
  forall {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} {block : RawBlock Ty}
      {operation : OperationId} {target : BlockId}
      {operationDef : alphabet.Op},
    block.term = .perform operation target ->
    alphabet.lookup operation = some operationDef ->
    lookupBlock raw target = none ->
    TermFailureValid alphabet raw block (.block target))

#check (@TermFailureValid.performRequestTypeMismatch :
  forall {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} {block : RawBlock Ty}
      {operation : OperationId} {target : BlockId}
      {operationDef : alphabet.Op} {targetBlock : RawBlock Ty},
    block.term = .perform operation target ->
    alphabet.lookup operation = some operationDef ->
    lookupBlock raw target = some targetBlock ->
    block.inputTy ≠ alphabet.requestTy operationDef ->
    TermFailureValid alphabet raw block
      (.typeMismatch (alphabet.requestTy operationDef) block.inputTy))

#check (@TermFailureValid.performAnswerTypeMismatch :
  forall {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} {block : RawBlock Ty}
      {operation : OperationId} {target : BlockId}
      {operationDef : alphabet.Op} {targetBlock : RawBlock Ty},
    block.term = .perform operation target ->
    alphabet.lookup operation = some operationDef ->
    lookupBlock raw target = some targetBlock ->
    block.inputTy = alphabet.requestTy operationDef ->
    targetBlock.inputTy ≠ alphabet.answerTy operationDef ->
    TermFailureValid alphabet raw block
      (.typeMismatch (alphabet.answerTy operationDef) targetBlock.inputTy))

#check (@TermFailureValid.chooseMissingLeft :
  forall {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} {block : RawBlock Ty}
      {decision : DecisionId} {left right : BlockId},
    block.term = .choose decision left right ->
    lookupBlock raw left = none ->
    TermFailureValid alphabet raw block (.block left))

#check (@TermFailureValid.chooseMissingRight :
  forall {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} {block : RawBlock Ty}
      {decision : DecisionId} {left right : BlockId}
      {leftBlock : RawBlock Ty},
    block.term = .choose decision left right ->
    lookupBlock raw left = some leftBlock ->
    lookupBlock raw right = none ->
    TermFailureValid alphabet raw block (.block right))

#check (@TermFailureValid.chooseLeftTypeMismatch :
  forall {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} {block : RawBlock Ty}
      {decision : DecisionId} {left right : BlockId}
      {leftBlock rightBlock : RawBlock Ty},
    block.term = .choose decision left right ->
    lookupBlock raw left = some leftBlock ->
    lookupBlock raw right = some rightBlock ->
    leftBlock.inputTy ≠ block.inputTy ->
    TermFailureValid alphabet raw block
      (.typeMismatch block.inputTy leftBlock.inputTy))

#check (@TermFailureValid.chooseRightTypeMismatch :
  forall {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} {block : RawBlock Ty}
      {decision : DecisionId} {left right : BlockId}
      {leftBlock rightBlock : RawBlock Ty},
    block.term = .choose decision left right ->
    lookupBlock raw left = some leftBlock ->
    lookupBlock raw right = some rightBlock ->
    leftBlock.inputTy = block.inputTy ->
    rightBlock.inputTy ≠ block.inputTy ->
    TermFailureValid alphabet raw block
      (.typeMismatch block.inputTy rightBlock.inputTy))

/-! D2: exact site, payload, and source order for every diagnostic. -/

#check (@Diagnostic.Valid :
  {Ty : Type uTy} ->
  FlowAlphabet.{uTy, uOp} Ty -> RawFlow Ty -> Diagnostic Ty -> Prop)

#check (@Diagnostic.Valid.alphabetMismatch :
  forall {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty},
    raw.alphabet ≠ alphabet.id ->
    Diagnostic.Valid alphabet raw
      { clause := .alphabetMismatch
        site := .flow
        payload := .alphabet alphabet.id raw.alphabet })

#check (@Diagnostic.Valid.duplicateBlockId :
  forall {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} {index : Nat} {block : RawBlock Ty},
    FirstFailureAt raw.blocks
      (fun candidateIndex candidate reported =>
        reported = candidate.id ∧
        candidate.id ∈
          (raw.blocks.take candidateIndex).map RawBlock.id)
      index block block.id ->
    Diagnostic.Valid alphabet raw
      { clause := .duplicateBlockId
        site := .block index
        payload := .block block.id })

#check (@Diagnostic.Valid.duplicateDecisionId :
  forall {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} {index : Nat} {block : RawBlock Ty}
      {decision : DecisionId},
    FirstFailureAt raw.blocks
      (fun candidateIndex candidate reported =>
        ∃ left right,
          candidate.term = .choose reported left right ∧
          reported ∈
            (raw.blocks.take candidateIndex).filterMap (fun prior =>
              match prior.term with
              | .choose priorDecision _ _ => some priorDecision
              | _ => none))
      index block decision ->
    Diagnostic.Valid alphabet raw
      { clause := .duplicateDecisionId
        site := .decision block.id
        payload := .decision decision })

#check (@Diagnostic.Valid.nonCanonicalBlockOrder :
  forall {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} {index : Nat} {block : RawBlock Ty},
    FirstFailureAt raw.blocks
      (fun candidateIndex candidate reported =>
        reported = candidate.id ∧ 0 < candidateIndex ∧
        ∃ previous,
          raw.blocks[candidateIndex - 1]? = some previous ∧
          Not (previous.id.value < candidate.id.value))
      index block block.id ->
    Diagnostic.Valid alphabet raw
      { clause := .nonCanonicalBlockOrder
        site := .block index
        payload := .block block.id })

#check (@Diagnostic.Valid.emptyRoots :
  forall {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty},
    raw.roots = [] ->
    Diagnostic.Valid alphabet raw
      { clause := .emptyRoots, site := .flow, payload := .none })

#check (@Diagnostic.Valid.duplicateRoot :
  forall {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} {index : Nat} {root : BlockId},
    FirstFailureAt raw.roots
      (fun candidateIndex candidate reported =>
        reported = candidate ∧
        candidate ∈ raw.roots.take candidateIndex)
      index root root ->
    Diagnostic.Valid alphabet raw
      { clause := .duplicateRoot
        site := .root index
        payload := .block root })

#check (@Diagnostic.Valid.nonCanonicalRootOrder :
  forall {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} {index : Nat} {root : BlockId},
    FirstFailureAt raw.roots
      (fun candidateIndex candidate reported =>
        reported = candidate ∧ 0 < candidateIndex ∧
        ∃ previous,
          raw.roots[candidateIndex - 1]? = some previous ∧
          Not (previous.value < candidate.value))
      index root root ->
    Diagnostic.Valid alphabet raw
      { clause := .nonCanonicalRootOrder
        site := .root index
        payload := .block root })

#check (@Diagnostic.Valid.entryNotRoot :
  forall {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty},
    raw.entry ∉ raw.roots ->
    Diagnostic.Valid alphabet raw
      { clause := .entryNotRoot
        site := .entry
        payload := .block raw.entry })

#check (@Diagnostic.Valid.danglingRoot :
  forall {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} {index : Nat} {root : BlockId},
    FirstFailureAt raw.roots
      (fun _ candidate reported =>
        reported = candidate ∧ lookupBlock raw candidate = none)
      index root root ->
    Diagnostic.Valid alphabet raw
      { clause := .danglingRoot
        site := .root index
        payload := .block root })

#check (@Diagnostic.Valid.danglingSuccessor :
  forall {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} {blockIndex successorIndex : Nat}
      {block : RawBlock Ty} {target : BlockId},
    FirstFailureAt raw.blocks
      (fun _ candidate witness =>
        FirstFailureAt candidate.term.successors
          (fun _ successor reported =>
            reported = successor ∧ lookupBlock raw successor = none)
          witness.1 witness.2 witness.2)
      blockIndex block (successorIndex, target) ->
    Diagnostic.Valid alphabet raw
      { clause := .danglingSuccessor
        site := .successor block.id successorIndex
        payload := .block target })

#check (@Diagnostic.Valid.unknownOperation :
  forall {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} {index : Nat} {block : RawBlock Ty}
      {operation : OperationId},
    FirstFailureAt raw.blocks
      (fun _ candidate reported =>
        ∃ target,
          candidate.term = .perform reported target ∧
          alphabet.lookup reported = none)
      index block operation ->
    Diagnostic.Valid alphabet raw
      { clause := .unknownOperation
        site := .operation block.id
        payload := .operation operation })

#check (@Diagnostic.Valid.entryMissing :
  forall {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty},
    lookupBlock raw raw.entry = none ->
    Diagnostic.Valid alphabet raw
      { clause := .entryTypeMismatch
        site := .entry
        payload := .block raw.entry })

#check (@Diagnostic.Valid.entryTypeMismatch :
  forall {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} {block : RawBlock Ty},
    lookupBlock raw raw.entry = some block ->
    block.inputTy ≠ raw.inputTy ->
    Diagnostic.Valid alphabet raw
      { clause := .entryTypeMismatch
        site := .entry
        payload := .typeMismatch raw.inputTy block.inputTy })

#check (@Diagnostic.Valid.termTypeMismatch :
  forall {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} {index : Nat} {block : RawBlock Ty}
      {payload : DiagnosticPayload Ty},
    FirstFailureAt raw.blocks
      (fun _ candidate failure =>
        TermFailureValid alphabet raw candidate failure)
      index block payload ->
    Diagnostic.Valid alphabet raw
      { clause := .termTypeMismatch
        site := .term block.id
        payload := payload })

/-! D3: precision propagates through the public admission observations. -/

#check (@diagnoseAt_some_valid :
  forall {Ty : Type uTy} [DecidableEq Ty]
      {alphabet : FlowAlphabet.{uTy, uOp} Ty} {raw : RawFlow Ty}
      {clause : AdmissionClause} {diagnostic : Diagnostic Ty},
    diagnoseAt alphabet raw clause = some diagnostic ->
    Diagnostic.Valid alphabet raw diagnostic)

#check (@FirstDiagnostic.valid :
  forall {Ty : Type uTy} [DecidableEq Ty]
      {alphabet : FlowAlphabet.{uTy, uOp} Ty} {raw : RawFlow Ty}
      {diagnostic : Diagnostic Ty},
    FirstDiagnostic alphabet raw diagnostic ->
    Diagnostic.Valid alphabet raw diagnostic)

#check (@admit_error_valid :
  forall {Ty : Type uTy} [DecidableEq Ty]
      {alphabet : FlowAlphabet.{uTy, uOp} Ty} {raw : RawFlow Ty}
      {diagnostic : Diagnostic Ty},
    admit alphabet raw = .error diagnostic ->
    Diagnostic.Valid alphabet raw diagnostic)

end SurfaceSnapshot

/-! Representative exactness attacks. -/

inductive ExampleTy where
  | unit
  | bool
  | nat
deriving DecidableEq, Repr

inductive ExampleOp where
  | decide
deriving DecidableEq, Repr

def blockId (value : Nat) : BlockId := { value }
def operationId (value : Nat) : OperationId := { value }
def alphabetId (value : Nat) : AlphabetId := { value }
def decisionId (value : Nat) : DecisionId := { value }

def exampleLookup : OperationId -> Option ExampleOp
  | { value := 0 } => some .decide
  | _ => none

def ExampleAlphabet : FlowAlphabet ExampleTy where
  id := alphabetId 7
  Op := ExampleOp
  operationId
    | .decide => operationId 0
  lookup := exampleLookup
  requestTy
    | .decide => .unit
  answerTy
    | .decide => .bool
  lookup_operationId := by
    intro operation
    cases operation
    rfl
  operationId_of_lookup := by
    intro id operation found
    cases operation
    cases id with
    | mk value =>
      cases value with
      | zero => rfl
      | succ value => simp [exampleLookup] at found

def rawBlock (id : Nat) (inputTy : ExampleTy) (term : RawTerm) :
    RawBlock ExampleTy :=
  { id := blockId id, inputTy, term }

/-!
E4-FLOW-CE-016a: the first repeated decision is the second `choose`, so both
the decision block and decision payload are forced.
-/

def duplicateDecisionFlow : RawFlow ExampleTy where
  alphabet := ExampleAlphabet.id
  roots := [blockId 0]
  entry := blockId 0
  inputTy := .unit
  resultTy := .unit
  blocks := [
    rawBlock 0 .unit (.choose (decisionId 5) (blockId 2) (blockId 2)),
    rawBlock 1 .unit (.choose (decisionId 5) (blockId 2) (blockId 2)),
    rawBlock 2 .unit .ret
  ]

#guard diagnoseAt ExampleAlphabet duplicateDecisionFlow
    .duplicateDecisionId =
  some {
    clause := .duplicateDecisionId
    site := .decision (blockId 1)
    payload := .decision (decisionId 5)
  }

/-!
E4-FLOW-CE-016b: block 0 is unreachable but is still the first source block.
Its `choose` has two bad successor input types, so the left mismatch must win
before the right mismatch and before the later `ret` mismatch in block 2.
-/

def nestedSourceOrderFlow : RawFlow ExampleTy where
  alphabet := ExampleAlphabet.id
  roots := [blockId 3]
  entry := blockId 3
  inputTy := .nat
  resultTy := .nat
  blocks := [
    rawBlock 0 .unit (.choose (decisionId 8) (blockId 1) (blockId 2)),
    rawBlock 1 .nat .ret,
    rawBlock 2 .bool .ret,
    rawBlock 3 .nat .ret
  ]

#guard diagnoseAt ExampleAlphabet nestedSourceOrderFlow .termTypeMismatch =
  some {
    clause := .termTypeMismatch
    site := .term (blockId 0)
    payload := .typeMismatch .unit .nat
  }

/-!
The unrelated-fallback mutation cannot satisfy the validity index. This test
mentions only the public relation, not any private implementation constant.
-/

example : Not (Diagnostic.Valid ExampleAlphabet duplicateDecisionFlow {
    clause := .duplicateDecisionId
    site := .flow
    payload := .none
  }) := by
  intro invalid
  cases invalid

end Effect4Test.Flow.DiagnosticPrecisionContract
