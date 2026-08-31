/-
Contract packet: `test/contracts/flow-admission.contract.md`

Breaker-owned red battery. The implementation phase must not edit this file.
It is red until the first-order Flow admission declarations exist.
-/

import Effect4.Flow.Admission
import Effect4.Flow.Block
import Effect4.Flow.Checked
import Effect4.Flow.Raw

namespace Effect4
end Effect4

namespace Effect4Test.Flow.AdmissionContract

open Effect4

universe uTy uOp

section SurfaceSnapshot

/-! D0: nominal identifiers. -/

#check (@BlockId : Type)
#check (@BlockId.mk : Nat -> BlockId)
#check (@BlockId.value : BlockId -> Nat)
#synth DecidableEq BlockId

#check (@OperationId : Type)
#check (@OperationId.mk : Nat -> OperationId)
#check (@OperationId.value : OperationId -> Nat)
#synth DecidableEq OperationId

#check (@AlphabetId : Type)
#check (@AlphabetId.mk : Nat -> AlphabetId)
#check (@AlphabetId.value : AlphabetId -> Nat)
#synth DecidableEq AlphabetId

#check (@DecisionId : Type)
#check (@DecisionId.mk : Nat -> DecisionId)
#check (@DecisionId.value : DecisionId -> Nat)
#synth DecidableEq DecisionId

/-! D1: one closed operation alphabet. -/

#check (@FlowAlphabet.id :
  forall {Ty : Type uTy}, FlowAlphabet.{uTy, uOp} Ty -> AlphabetId)

#check (@FlowAlphabet.Op :
  forall {Ty : Type uTy}, FlowAlphabet.{uTy, uOp} Ty -> Type uOp)

#check (@FlowAlphabet.operationId :
  forall {Ty : Type uTy} (alphabet : FlowAlphabet.{uTy, uOp} Ty),
    alphabet.Op -> OperationId)

#check (@FlowAlphabet.lookup :
  forall {Ty : Type uTy} (alphabet : FlowAlphabet.{uTy, uOp} Ty),
    OperationId -> Option alphabet.Op)

#check (@FlowAlphabet.requestTy :
  forall {Ty : Type uTy} (alphabet : FlowAlphabet.{uTy, uOp} Ty),
    alphabet.Op -> Ty)

#check (@FlowAlphabet.answerTy :
  forall {Ty : Type uTy} (alphabet : FlowAlphabet.{uTy, uOp} Ty),
    alphabet.Op -> Ty)

#check (@FlowAlphabet.lookup_operationId :
  forall {Ty : Type uTy} (alphabet : FlowAlphabet.{uTy, uOp} Ty)
      (operation : alphabet.Op),
    alphabet.lookup (alphabet.operationId operation) = some operation)

#check (@FlowAlphabet.operationId_of_lookup :
  forall {Ty : Type uTy} (alphabet : FlowAlphabet.{uTy, uOp} Ty)
      {id : OperationId} {operation : alphabet.Op},
    alphabet.lookup id = some operation -> alphabet.operationId operation = id)

/-! D2: raw first-order terms, blocks, and documents. -/

#check (@RawTerm.ret : RawTerm)
#check (@RawTerm.jump : BlockId -> RawTerm)
#check (@RawTerm.perform : OperationId -> BlockId -> RawTerm)
#check (@RawTerm.choose : DecisionId -> BlockId -> BlockId -> RawTerm)
#check (@RawTerm.successors : RawTerm -> List BlockId)

#check (@RawBlock.mk :
  forall {Ty : Type uTy}, BlockId -> Ty -> RawTerm -> RawBlock Ty)
#check (@RawBlock.id : forall {Ty : Type uTy}, RawBlock Ty -> BlockId)
#check (@RawBlock.inputTy : forall {Ty : Type uTy}, RawBlock Ty -> Ty)
#check (@RawBlock.term : forall {Ty : Type uTy}, RawBlock Ty -> RawTerm)

#check (@RawFlow.mk :
  forall {Ty : Type uTy},
    AlphabetId -> List BlockId -> BlockId -> Ty -> Ty ->
      List (RawBlock Ty) -> RawFlow Ty)
#check (@RawFlow.alphabet : forall {Ty : Type uTy}, RawFlow Ty -> AlphabetId)
#check (@RawFlow.roots : forall {Ty : Type uTy}, RawFlow Ty -> List BlockId)
#check (@RawFlow.entry : forall {Ty : Type uTy}, RawFlow Ty -> BlockId)
#check (@RawFlow.inputTy : forall {Ty : Type uTy}, RawFlow Ty -> Ty)
#check (@RawFlow.resultTy : forall {Ty : Type uTy}, RawFlow Ty -> Ty)
#check (@RawFlow.blocks :
  forall {Ty : Type uTy}, RawFlow Ty -> List (RawBlock Ty))

/-! D3: resolution, reachability, and exactly seven WF fields. -/

#check (@lookupBlock :
  forall {Ty : Type uTy}, RawFlow Ty -> BlockId -> Option (RawBlock Ty))

#check (@Edge :
  forall {Ty : Type uTy}, RawFlow Ty -> BlockId -> BlockId -> Prop)

#check (@ReachableFrom :
  forall {Ty : Type uTy}, RawFlow Ty -> BlockId -> BlockId -> Prop)

#check (@Reachable :
  forall {Ty : Type uTy}, RawFlow Ty -> BlockId -> Prop)

#check (@EntryReachable :
  forall {Ty : Type uTy}, RawFlow Ty -> BlockId -> Prop)

#check (@AlphabetWF :
  forall {Ty : Type uTy},
    FlowAlphabet.{uTy, uOp} Ty -> RawFlow Ty -> Prop)

#check (@IdsWF :
  forall {Ty : Type uTy}, RawFlow Ty -> Prop)

#check (@RootsWF :
  forall {Ty : Type uTy}, RawFlow Ty -> Prop)

#check (@ReferencesWF :
  forall {Ty : Type uTy}, RawFlow Ty -> Prop)

#check (@OperationsWF :
  forall {Ty : Type uTy},
    FlowAlphabet.{uTy, uOp} Ty -> RawFlow Ty -> Prop)

#check (@EntryWF :
  forall {Ty : Type uTy}, RawFlow Ty -> Prop)

#check (@TermsWF :
  forall {Ty : Type uTy},
    FlowAlphabet.{uTy, uOp} Ty -> RawFlow Ty -> Prop)

#check (@FlowWF :
  forall {Ty : Type uTy},
    FlowAlphabet.{uTy, uOp} Ty -> RawFlow Ty -> Prop)

#check (@FlowWF.mk :
  forall {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty},
    AlphabetWF alphabet raw ->
    IdsWF raw ->
    RootsWF raw ->
    ReferencesWF raw ->
    OperationsWF alphabet raw ->
    EntryWF raw ->
    TermsWF alphabet raw ->
    FlowWF alphabet raw)

/-! D4: diagnostic order, payload, checked boundary, and theorem edges. -/

#check (@AdmissionClause.alphabetMismatch : AdmissionClause)
#check (@AdmissionClause.duplicateBlockId : AdmissionClause)
#check (@AdmissionClause.duplicateDecisionId : AdmissionClause)
#check (@AdmissionClause.nonCanonicalBlockOrder : AdmissionClause)
#check (@AdmissionClause.emptyRoots : AdmissionClause)
#check (@AdmissionClause.duplicateRoot : AdmissionClause)
#check (@AdmissionClause.nonCanonicalRootOrder : AdmissionClause)
#check (@AdmissionClause.entryNotRoot : AdmissionClause)
#check (@AdmissionClause.danglingRoot : AdmissionClause)
#check (@AdmissionClause.danglingSuccessor : AdmissionClause)
#check (@AdmissionClause.unknownOperation : AdmissionClause)
#check (@AdmissionClause.entryTypeMismatch : AdmissionClause)
#check (@AdmissionClause.termTypeMismatch : AdmissionClause)
#synth DecidableEq AdmissionClause

#check (@scan : List AdmissionClause)

#guard scan = [
  .alphabetMismatch,
  .duplicateBlockId,
  .duplicateDecisionId,
  .nonCanonicalBlockOrder,
  .emptyRoots,
  .duplicateRoot,
  .nonCanonicalRootOrder,
  .entryNotRoot,
  .danglingRoot,
  .danglingSuccessor,
  .unknownOperation,
  .entryTypeMismatch,
  .termTypeMismatch
]

#check (@CheckSite.flow : CheckSite)
#check (@CheckSite.block : Nat -> CheckSite)
#check (@CheckSite.decision : BlockId -> CheckSite)
#check (@CheckSite.root : Nat -> CheckSite)
#check (@CheckSite.successor : BlockId -> Nat -> CheckSite)
#check (@CheckSite.operation : BlockId -> CheckSite)
#check (@CheckSite.entry : CheckSite)
#check (@CheckSite.term : BlockId -> CheckSite)
#synth DecidableEq CheckSite

#check (@DiagnosticPayload.none : forall {Ty : Type uTy}, DiagnosticPayload Ty)
#check (@DiagnosticPayload.alphabet :
  forall {Ty : Type uTy}, AlphabetId -> AlphabetId -> DiagnosticPayload Ty)
#check (@DiagnosticPayload.block :
  forall {Ty : Type uTy}, BlockId -> DiagnosticPayload Ty)
#check (@DiagnosticPayload.decision :
  forall {Ty : Type uTy}, DecisionId -> DiagnosticPayload Ty)
#check (@DiagnosticPayload.operation :
  forall {Ty : Type uTy}, OperationId -> DiagnosticPayload Ty)
#check (@DiagnosticPayload.typeMismatch :
  forall {Ty : Type uTy}, Ty -> Ty -> DiagnosticPayload Ty)

#check (@Diagnostic.mk :
  forall {Ty : Type uTy},
    AdmissionClause -> CheckSite -> DiagnosticPayload Ty -> Diagnostic Ty)
#check (@Diagnostic.clause :
  forall {Ty : Type uTy}, Diagnostic Ty -> AdmissionClause)
#check (@Diagnostic.site : forall {Ty : Type uTy}, Diagnostic Ty -> CheckSite)
#check (@Diagnostic.payload :
  forall {Ty : Type uTy}, Diagnostic Ty -> DiagnosticPayload Ty)

#check (@diagnoseAt :
  forall {Ty : Type uTy} [DecidableEq Ty],
    FlowAlphabet.{uTy, uOp} Ty -> RawFlow Ty -> AdmissionClause ->
      Option (Diagnostic Ty))

#check (@FirstDiagnostic :
  forall {Ty : Type uTy} [DecidableEq Ty],
    FlowAlphabet.{uTy, uOp} Ty -> RawFlow Ty -> Diagnostic Ty -> Prop)

#check (@FirstDiagnostic.mk :
  forall {Ty : Type uTy} [DecidableEq Ty]
      {alphabet : FlowAlphabet.{uTy, uOp} Ty} {raw : RawFlow Ty}
      {diagnostic : Diagnostic Ty},
    diagnoseAt alphabet raw diagnostic.clause = some diagnostic ->
    (forall clause,
      clause ∈ scan.takeWhile
        (fun candidate => decide (candidate != diagnostic.clause)) ->
      diagnoseAt alphabet raw clause = none) ->
    FirstDiagnostic alphabet raw diagnostic)

#check (@FirstDiagnostic.condemns :
  forall {Ty : Type uTy} [DecidableEq Ty]
      {alphabet : FlowAlphabet.{uTy, uOp} Ty} {raw : RawFlow Ty}
      {diagnostic : Diagnostic Ty},
    FirstDiagnostic alphabet raw diagnostic ->
      diagnoseAt alphabet raw diagnostic.clause = some diagnostic)

#check (@CheckedFlow :
  forall {Ty : Type uTy}, FlowAlphabet.{uTy, uOp} Ty -> Type uTy)

#check (@CheckedFlow.raw :
  forall {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty},
    CheckedFlow alphabet -> RawFlow Ty)

#check (@CheckedFlow.wf :
  forall {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      (checked : CheckedFlow alphabet),
    FlowWF alphabet checked.raw)

#check (@CheckedFlow.erase :
  forall {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty},
    CheckedFlow alphabet -> RawFlow Ty)

#check (@admit :
  forall {Ty : Type uTy} [DecidableEq Ty]
      (alphabet : FlowAlphabet.{uTy, uOp} Ty) (raw : RawFlow Ty),
    Except (Diagnostic Ty) (CheckedFlow alphabet))

#check (@admit_sound :
  forall {Ty : Type uTy} [DecidableEq Ty]
      {alphabet : FlowAlphabet.{uTy, uOp} Ty} {raw : RawFlow Ty}
      {checked : CheckedFlow alphabet},
    admit alphabet raw = .ok checked -> FlowWF alphabet raw)

#check (@admit_complete :
  forall {Ty : Type uTy} [DecidableEq Ty]
      {alphabet : FlowAlphabet.{uTy, uOp} Ty} {raw : RawFlow Ty},
    FlowWF alphabet raw ->
      exists checked : CheckedFlow alphabet, admit alphabet raw = .ok checked)

#check (@error_iff_not_wf :
  forall {Ty : Type uTy} [DecidableEq Ty]
      {alphabet : FlowAlphabet.{uTy, uOp} Ty} {raw : RawFlow Ty},
    (exists diagnostic : Diagnostic Ty,
      admit alphabet raw = .error diagnostic) <->
    Not (FlowWF alphabet raw))

#check (@error_iff_firstDiagnostic :
  forall {Ty : Type uTy} [DecidableEq Ty]
      {alphabet : FlowAlphabet.{uTy, uOp} Ty} {raw : RawFlow Ty}
      {diagnostic : Diagnostic Ty},
    admit alphabet raw = .error diagnostic <->
      FirstDiagnostic alphabet raw diagnostic)

#check (@Diagnostic.clause_all_complete :
  forall {Ty : Type uTy} [DecidableEq Ty]
      {alphabet : FlowAlphabet.{uTy, uOp} Ty} {raw : RawFlow Ty},
    FlowWF alphabet raw <->
      forall clause, clause ∈ scan -> diagnoseAt alphabet raw clause = none)

#check (@erase_wf :
  forall {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      (checked : CheckedFlow alphabet),
    FlowWF alphabet checked.erase)

#check (@erase_admit :
  forall {Ty : Type uTy} [DecidableEq Ty]
      {alphabet : FlowAlphabet.{uTy, uOp} Ty} {raw : RawFlow Ty}
      {checked : CheckedFlow alphabet},
    admit alphabet raw = .ok checked -> checked.erase = raw)

#check (@admit_erase :
  forall {Ty : Type uTy} [DecidableEq Ty]
      {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      (checked : CheckedFlow alphabet),
    admit alphabet checked.erase = .ok checked)

#check (@FlowWF.reachable_declared :
  forall {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} (wf : FlowWF alphabet raw) {target : BlockId},
    Reachable raw target -> exists block, lookupBlock raw target = some block)

end SurfaceSnapshot

/-! Representative alphabet and raw documents used by the retained attacks. -/

inductive ExampleTy where
  | unit
  | bool
  | nat
deriving DecidableEq, Repr

inductive ExampleOp where
  | decide
deriving DecidableEq, Repr

def blockId (value : Nat) : BlockId := ⟨value⟩
def operationId (value : Nat) : OperationId := ⟨value⟩
def alphabetId (value : Nat) : AlphabetId := ⟨value⟩
def decisionId (value : Nat) : DecisionId := ⟨value⟩

def exampleLookup : OperationId -> Option ExampleOp
  | ⟨0⟩ => some .decide
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
  ⟨blockId id, inputTy, term⟩

def rawFlow (roots : List BlockId) (entry : BlockId)
    (inputTy resultTy : ExampleTy) (blocks : List (RawBlock ExampleTy))
    (alphabet : AlphabetId := alphabetId 7) : RawFlow ExampleTy :=
  ⟨alphabet, roots, entry, inputTy, resultTy, blocks⟩

def rejectedBy (clause : AdmissionClause) (raw : RawFlow ExampleTy) : Bool :=
  match admit ExampleAlphabet raw with
  | .error diagnostic => decide (diagnostic.clause = clause)
  | .ok _ => false

def isAdmitted (raw : RawFlow ExampleTy) : Bool :=
  match admit ExampleAlphabet raw with
  | .error _ => false
  | .ok _ => true

/-! E4-FLOW-CE-001: duplicate identity is rejected before ordering. -/

def duplicateBlockFlow : RawFlow ExampleTy :=
  rawFlow [blockId 0] (blockId 0) .unit .unit [
    rawBlock 0 .unit .ret,
    rawBlock 0 .unit .ret
  ]

#guard rejectedBy .duplicateBlockId duplicateBlockFlow

/-! Every diagnostic clause is represented by an executable negative. -/

def duplicateDecisionFlow : RawFlow ExampleTy :=
  rawFlow [blockId 0] (blockId 0) .unit .unit [
    rawBlock 0 .unit (.choose (decisionId 0) (blockId 1) (blockId 2)),
    rawBlock 1 .unit (.choose (decisionId 0) (blockId 2) (blockId 2)),
    rawBlock 2 .unit .ret
  ]

#guard rejectedBy .duplicateDecisionId duplicateDecisionFlow

def nonCanonicalBlockFlow : RawFlow ExampleTy :=
  rawFlow [blockId 0] (blockId 0) .unit .unit [
    rawBlock 1 .unit .ret,
    rawBlock 0 .unit .ret
  ]

#guard rejectedBy .nonCanonicalBlockOrder nonCanonicalBlockFlow

def emptyRootsFlow : RawFlow ExampleTy :=
  rawFlow [] (blockId 0) .unit .unit [rawBlock 0 .unit .ret]

#guard rejectedBy .emptyRoots emptyRootsFlow

def duplicateRootFlow : RawFlow ExampleTy :=
  rawFlow [blockId 0, blockId 0] (blockId 0) .unit .unit [
    rawBlock 0 .unit .ret
  ]

#guard rejectedBy .duplicateRoot duplicateRootFlow

def nonCanonicalRootFlow : RawFlow ExampleTy :=
  rawFlow [blockId 1, blockId 0] (blockId 1) .unit .unit [
    rawBlock 0 .unit .ret,
    rawBlock 1 .unit .ret
  ]

#guard rejectedBy .nonCanonicalRootOrder nonCanonicalRootFlow

def entryNotRootFlow : RawFlow ExampleTy :=
  rawFlow [blockId 0] (blockId 1) .unit .unit [
    rawBlock 0 .unit .ret,
    rawBlock 1 .unit .ret
  ]

#guard rejectedBy .entryNotRoot entryNotRootFlow

/-! E4-FLOW-CE-002: root and successor failures preserve exact sites. -/

def danglingRootFlow : RawFlow ExampleTy :=
  rawFlow [blockId 0, blockId 9] (blockId 0) .unit .unit [
    rawBlock 0 .unit .ret
  ]

#guard
  match admit ExampleAlphabet danglingRootFlow with
  | .error diagnostic =>
      decide (
        diagnostic.clause = .danglingRoot /\
        diagnostic.site = .root 1 /\
        diagnostic.payload = .block (blockId 9))
  | .ok _ => false

def danglingSuccessorFlow : RawFlow ExampleTy :=
  rawFlow [blockId 0] (blockId 0) .unit .unit [
    rawBlock 0 .unit (.jump (blockId 9))
  ]

#guard
  match admit ExampleAlphabet danglingSuccessorFlow with
  | .error diagnostic =>
      decide (
        diagnostic.clause = .danglingSuccessor /\
        diagnostic.site = .successor (blockId 0) 0 /\
        diagnostic.payload = .block (blockId 9))
  | .ok _ => false

/-! E4-FLOW-CE-003: operation closure is independent of edge closure. -/

def unknownOperationFlow : RawFlow ExampleTy :=
  rawFlow [blockId 0] (blockId 0) .unit .bool [
    rawBlock 0 .unit (.perform (operationId 9) (blockId 1)),
    rawBlock 1 .bool .ret
  ]

#guard
  match admit ExampleAlphabet unknownOperationFlow with
  | .error diagnostic =>
      decide (
        diagnostic.clause = .unknownOperation /\
        diagnostic.site = .operation (blockId 0) /\
        diagnostic.payload = .operation (operationId 9))
  | .ok _ => false

/-! E4-FLOW-CE-004: the operation answer must match its target input. -/

def answerTargetMismatchFlow : RawFlow ExampleTy :=
  rawFlow [blockId 0] (blockId 0) .unit .nat [
    rawBlock 0 .unit (.perform (operationId 0) (blockId 1)),
    rawBlock 1 .nat .ret
  ]

#guard
  match admit ExampleAlphabet answerTargetMismatchFlow with
  | .error diagnostic =>
      decide (
        diagnostic.clause = .termTypeMismatch /\
        diagnostic.site = .term (blockId 0) /\
        diagnostic.payload = .typeMismatch .bool .nat)
  | .ok _ => false

def entryTypeMismatchFlow : RawFlow ExampleTy :=
  rawFlow [blockId 0] (blockId 0) .unit .bool [
    rawBlock 0 .bool .ret
  ]

#guard rejectedBy .entryTypeMismatch entryTypeMismatchFlow

def returnTypeMismatchFlow : RawFlow ExampleTy :=
  rawFlow [blockId 0] (blockId 0) .bool .nat [
    rawBlock 0 .bool .ret
  ]

#guard rejectedBy .termTypeMismatch returnTypeMismatchFlow

/-! E4-FLOW-CE-005: admission is not an acyclicity checker. -/

def selfCycleFlow : RawFlow ExampleTy :=
  rawFlow [blockId 0] (blockId 0) .unit .unit [
    rawBlock 0 .unit (.jump (blockId 0))
  ]

#guard isAdmitted selfCycleFlow

/-! E4-FLOW-CE-007: the packet-owned order selects the first defect. -/

def firstDiagnosticFlow : RawFlow ExampleTy :=
  rawFlow [blockId 0] (blockId 0) .unit .unit [
    rawBlock 0 .unit .ret,
    rawBlock 0 .unit .ret
  ] (alphabet := alphabetId 99)

#guard rejectedBy .alphabetMismatch firstDiagnosticFlow

/-!
E4-FLOW-CE-013: canonical terms contain block IDs, not Lean continuations.
-/

/--
error: Application type mismatch
-/
#guard_msgs(error, substring := true) in
#check (RawTerm.choose (decisionId 0)
  (fun _ : Bool => blockId 1) (blockId 2))

/-!
E4-FLOW-CE-014: closure is whole-document, while reachability coverage and
acyclicity are not admission clauses.
-/

def unreachableClosedCycleFlow : RawFlow ExampleTy :=
  rawFlow [blockId 0] (blockId 0) .unit .unit [
    rawBlock 0 .unit .ret,
    rawBlock 1 .bool (.jump (blockId 1))
  ]

#guard isAdmitted unreachableClosedCycleFlow

def unreachableDanglingFlow : RawFlow ExampleTy :=
  rawFlow [blockId 0] (blockId 0) .unit .unit [
    rawBlock 0 .unit .ret,
    rawBlock 1 .bool (.jump (blockId 9))
  ]

#guard rejectedBy .danglingSuccessor unreachableDanglingFlow

end Effect4Test.Flow.AdmissionContract
