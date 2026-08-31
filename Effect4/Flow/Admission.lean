import Effect4.Flow.Raw

/-!
# Checked flow admission

This module owns the closed admission boundary. Diagnostics are produced from
one clause-indexed checker, and the checked carrier is co-located here so its
constructor can remain genuinely private while `admit` can still construct it.
-/

namespace Effect4

/-- The fixed, public order of independently checkable admission clauses. -/
inductive AdmissionClause where
  | alphabetMismatch
  | duplicateBlockId
  | duplicateDecisionId
  | nonCanonicalBlockOrder
  | emptyRoots
  | duplicateRoot
  | nonCanonicalRootOrder
  | entryNotRoot
  | danglingRoot
  | danglingSuccessor
  | unknownOperation
  | entryTypeMismatch
  | termTypeMismatch
deriving DecidableEq, Repr

/-- Packet-owned locations for precise admission diagnostics. -/
inductive CheckSite where
  | flow
  | block (index : Nat)
  | decision (block : BlockId)
  | root (index : Nat)
  | successor (block : BlockId) (index : Nat)
  | operation (block : BlockId)
  | entry
  | term (block : BlockId)
deriving DecidableEq, Repr

/-- Typed evidence carried by a diagnostic. -/
inductive DiagnosticPayload (Ty : Type uTy) where
  | none
  | alphabet (expected actual : AlphabetId)
  | block (id : BlockId)
  | decision (id : DecisionId)
  | operation (id : OperationId)
  | typeMismatch (expected actual : Ty)
deriving DecidableEq, Repr

/-- One failed admission clause, its source location, and its typed payload. -/
structure Diagnostic (Ty : Type uTy) where
  clause : AdmissionClause
  site : CheckSite
  payload : DiagnosticPayload Ty
deriving DecidableEq, Repr

/-- The exhaustive first-error scan order. -/
def scan : List AdmissionClause := [
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

private def localDecisionIds (raw : RawFlow Ty) : List DecisionId :=
  raw.blocks.filterMap fun block =>
    match block.term with
    | .choose decision _ _ => some decision
    | _ => none

private def localTermWF
    (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty)
    (block : RawBlock Ty) : Prop :=
  match block.term with
  | .ret => block.inputTy = raw.resultTy
  | .jump target =>
      match lookupBlock raw target with
      | none => False
      | some targetBlock => targetBlock.inputTy = block.inputTy
  | .perform operation target =>
      match alphabet.lookup operation, lookupBlock raw target with
      | some operation, some targetBlock =>
          block.inputTy = alphabet.requestTy operation ∧
          targetBlock.inputTy = alphabet.answerTy operation
      | _, _ => False
  | .choose _ left right =>
      match lookupBlock raw left, lookupBlock raw right with
      | some leftBlock, some rightBlock =>
          leftBlock.inputTy = block.inputTy ∧
          rightBlock.inputTy = block.inputTy
      | _, _ => False

private def localOperationWF
    (alphabet : FlowAlphabet Ty) (block : RawBlock Ty) : Prop :=
  match block.term with
  | .perform operation _ => (alphabet.lookup operation).isSome = true
  | _ => True

private def localTermWFDecidable [DecidableEq Ty]
    (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty)
    (block : RawBlock Ty) : Decidable (localTermWF alphabet raw block) := by
  cases termEq : block.term with
  | ret =>
      simp only [localTermWF, termEq]
      infer_instance
  | jump target =>
      cases lookupEq : lookupBlock raw target <;>
        simp only [localTermWF, termEq, lookupEq] <;>
        infer_instance
  | perform operation target =>
      cases operationEq : alphabet.lookup operation <;>
        cases targetEq : lookupBlock raw target <;>
        simp only [localTermWF, termEq, operationEq, targetEq] <;>
        infer_instance
  | choose decision left right =>
      cases leftEq : lookupBlock raw left <;>
        cases rightEq : lookupBlock raw right <;>
        simp only [localTermWF, termEq, leftEq, rightEq] <;>
        infer_instance

private def localOperationWFDecidable
    (alphabet : FlowAlphabet Ty) (block : RawBlock Ty) :
    Decidable (localOperationWF alphabet block) := by
  unfold localOperationWF
  split <;> infer_instance

private def localEntryWFDecidable [DecidableEq Ty]
    (raw : RawFlow Ty) : Decidable (EntryWF raw) := by
  unfold EntryWF
  split <;> infer_instance

private theorem idsWF_view (raw : RawFlow Ty) :
    IdsWF raw ↔
      (raw.blocks.map RawBlock.id).Nodup ∧
      raw.blocks.Pairwise
        (fun left right => left.id.value < right.id.value) ∧
      (localDecisionIds raw).Nodup := by
  rfl

private theorem termsWF_view (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty) :
    TermsWF alphabet raw ↔
      ∀ block, block ∈ raw.blocks → localTermWF alphabet raw block := by
  rfl

private theorem operationsWF_view
    (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty) :
    OperationsWF alphabet raw ↔
      ∀ block, block ∈ raw.blocks → localOperationWF alphabet block := by
  rfl

/-- The proposition checked by one diagnostic clause. -/
private def ClauseHolds
    (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty) :
    AdmissionClause → Prop
  | .alphabetMismatch => AlphabetWF alphabet raw
  | .duplicateBlockId => (raw.blocks.map RawBlock.id).Nodup
  | .duplicateDecisionId => (localDecisionIds raw).Nodup
  | .nonCanonicalBlockOrder =>
      raw.blocks.Pairwise
        (fun left right => left.id.value < right.id.value)
  | .emptyRoots => raw.roots ≠ []
  | .duplicateRoot => raw.roots.Nodup
  | .nonCanonicalRootOrder =>
      raw.roots.Pairwise (fun left right => left.value < right.value)
  | .entryNotRoot => raw.entry ∈ raw.roots
  | .danglingRoot =>
      ∀ root, root ∈ raw.roots → (lookupBlock raw root).isSome = true
  | .danglingSuccessor => ReferencesWF raw
  | .unknownOperation =>
      ∀ block, block ∈ raw.blocks → localOperationWF alphabet block
  | .entryTypeMismatch => EntryWF raw
  | .termTypeMismatch =>
      ∀ block, block ∈ raw.blocks → localTermWF alphabet raw block

private def clauseHoldsDecidable [DecidableEq Ty]
    (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty)
    (clause : AdmissionClause) : Decidable (ClauseHolds alphabet raw clause) := by
  cases clause with
  | alphabetMismatch | duplicateBlockId | duplicateDecisionId |
    nonCanonicalBlockOrder | emptyRoots | duplicateRoot |
    nonCanonicalRootOrder | entryNotRoot | danglingRoot |
    danglingSuccessor =>
      unfold ClauseHolds AlphabetWF ReferencesWF
      infer_instance
  | unknownOperation =>
      unfold ClauseHolds
      letI : DecidablePred (localOperationWF alphabet) :=
        localOperationWFDecidable alphabet
      infer_instance
  | entryTypeMismatch =>
      unfold ClauseHolds
      exact localEntryWFDecidable raw
  | termTypeMismatch =>
      unfold ClauseHolds
      letI : DecidablePred (localTermWF alphabet raw) :=
        localTermWFDecidable alphabet raw
      infer_instance

private def firstDuplicate? [DecidableEq α] :
    Nat → List α → List α → Option (Nat × α)
  | _, _, [] => none
  | index, seen, item :: rest =>
      if item ∈ seen then
        some (index, item)
      else
        firstDuplicate? (index + 1) (item :: seen) rest

private def firstOrderViolation? (value : α → Nat) :
    Nat → List α → Option (Nat × α)
  | _, [] => none
  | _, [_] => none
  | index, left :: right :: rest =>
      if value left < value right then
        firstOrderViolation? value (index + 1) (right :: rest)
      else
        some (index + 1, right)

private def firstDuplicateDecision? :
    List DecisionId → List (RawBlock Ty) → Option (BlockId × DecisionId)
  | _, [] => none
  | seen, block :: rest =>
      match block.term with
      | .choose decision _ _ =>
          if decision ∈ seen then
            some (block.id, decision)
          else
            firstDuplicateDecision? (decision :: seen) rest
      | _ => firstDuplicateDecision? seen rest

private def firstDanglingRoot? (raw : RawFlow Ty) :
    Nat → List BlockId → Option (Nat × BlockId)
  | _, [] => none
  | index, root :: rest =>
      match lookupBlock raw root with
      | none => some (index, root)
      | some _ => firstDanglingRoot? raw (index + 1) rest

private def firstDanglingSuccessorIn? (raw : RawFlow Ty)
    (block : RawBlock Ty) : Nat → List BlockId → Option (CheckSite × DiagnosticPayload Ty)
  | _, [] => none
  | index, target :: rest =>
      match lookupBlock raw target with
      | none => some (.successor block.id index, .block target)
      | some _ => firstDanglingSuccessorIn? raw block (index + 1) rest

private def firstDanglingSuccessor? (raw : RawFlow Ty) :
    List (RawBlock Ty) → Option (CheckSite × DiagnosticPayload Ty)
  | [] => none
  | block :: rest =>
      match firstDanglingSuccessorIn? raw block 0 block.term.successors with
      | some failure => some failure
      | none => firstDanglingSuccessor? raw rest

private def firstUnknownOperation? (alphabet : FlowAlphabet Ty) :
    List (RawBlock Ty) → Option (BlockId × OperationId)
  | [] => none
  | block :: rest =>
      match block.term with
      | .perform operation _ =>
          match alphabet.lookup operation with
          | none => some (block.id, operation)
          | some _ => firstUnknownOperation? alphabet rest
      | _ => firstUnknownOperation? alphabet rest

private def termFailure? [DecidableEq Ty]
    (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty)
    (block : RawBlock Ty) : Option (DiagnosticPayload Ty) :=
  match block.term with
  | .ret =>
      if block.inputTy = raw.resultTy then none
      else some (.typeMismatch raw.resultTy block.inputTy)
  | .jump target =>
      match lookupBlock raw target with
      | none => some (.block target)
      | some targetBlock =>
          if targetBlock.inputTy = block.inputTy then none
          else some (.typeMismatch block.inputTy targetBlock.inputTy)
  | .perform operationId target =>
      match alphabet.lookup operationId, lookupBlock raw target with
      | none, _ => some (.operation operationId)
      | _, none => some (.block target)
      | some operation, some targetBlock =>
          if block.inputTy = alphabet.requestTy operation then
            if targetBlock.inputTy = alphabet.answerTy operation then none
            else some (.typeMismatch
              (alphabet.answerTy operation) targetBlock.inputTy)
          else
            some (.typeMismatch
              (alphabet.requestTy operation) block.inputTy)
  | .choose _ left right =>
      match lookupBlock raw left, lookupBlock raw right with
      | none, _ => some (.block left)
      | _, none => some (.block right)
      | some leftBlock, some rightBlock =>
          if leftBlock.inputTy = block.inputTy then
            if rightBlock.inputTy = block.inputTy then none
            else some (.typeMismatch block.inputTy rightBlock.inputTy)
          else
            some (.typeMismatch block.inputTy leftBlock.inputTy)

private def firstTermFailure? [DecidableEq Ty]
    (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty) :
    List (RawBlock Ty) → Option (BlockId × DiagnosticPayload Ty)
  | [] => none
  | block :: rest =>
      match termFailure? alphabet raw block with
      | some payload => some (block.id, payload)
      | none => firstTermFailure? alphabet raw rest

private def failureWitness [DecidableEq Ty]
    (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty) :
    AdmissionClause → CheckSite × DiagnosticPayload Ty
  | .alphabetMismatch =>
      (.flow, .alphabet alphabet.id raw.alphabet)
  | .duplicateBlockId =>
      match firstDuplicate? 0 [] (raw.blocks.map RawBlock.id) with
      | some (index, id) => (.block index, .block id)
      | none => (.flow, .none)
  | .duplicateDecisionId =>
      match firstDuplicateDecision? [] raw.blocks with
      | some (block, decision) => (.decision block, .decision decision)
      | none => (.flow, .none)
  | .nonCanonicalBlockOrder =>
      match firstOrderViolation? (fun block : RawBlock Ty => block.id.value)
          0 raw.blocks with
      | some (index, block) => (.block index, .block block.id)
      | none => (.flow, .none)
  | .emptyRoots => (.flow, .none)
  | .duplicateRoot =>
      match firstDuplicate? 0 [] raw.roots with
      | some (index, root) => (.root index, .block root)
      | none => (.flow, .none)
  | .nonCanonicalRootOrder =>
      match firstOrderViolation? BlockId.value 0 raw.roots with
      | some (index, root) => (.root index, .block root)
      | none => (.flow, .none)
  | .entryNotRoot => (.entry, .block raw.entry)
  | .danglingRoot =>
      match firstDanglingRoot? raw 0 raw.roots with
      | some (index, root) => (.root index, .block root)
      | none => (.flow, .none)
  | .danglingSuccessor =>
      match firstDanglingSuccessor? raw raw.blocks with
      | some failure => failure
      | none => (.flow, .none)
  | .unknownOperation =>
      match firstUnknownOperation? alphabet raw.blocks with
      | some (block, operation) => (.operation block, .operation operation)
      | none => (.flow, .none)
  | .entryTypeMismatch =>
      match lookupBlock raw raw.entry with
      | some block =>
          (.entry, .typeMismatch raw.inputTy block.inputTy)
      | none => (.entry, .block raw.entry)
  | .termTypeMismatch =>
      match firstTermFailure? alphabet raw raw.blocks with
      | some (block, payload) => (.term block, payload)
      | none => (.flow, .none)

/-- A clause-indexed result makes an unrelated diagnostic unrepresentable. -/
private inductive ClauseResult (Ty : Type uTy)
    (clause : AdmissionClause) (holds : Prop) where
  | pass (proof : holds)
  | fail (site : CheckSite) (payload : DiagnosticPayload Ty)
      (refute : ¬ holds)

private def ClauseResult.diagnostic? :
    ClauseResult Ty clause holds → Option (Diagnostic Ty)
  | .pass _ => none
  | .fail site payload _ => some ⟨clause, site, payload⟩

private def checkClause [DecidableEq Ty]
    (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty)
    (clause : AdmissionClause) :
    ClauseResult Ty clause (ClauseHolds alphabet raw clause) :=
  letI := clauseHoldsDecidable alphabet raw clause
  if holds : ClauseHolds alphabet raw clause then
    .pass holds
  else
    let failure := failureWitness alphabet raw clause
    .fail failure.1 failure.2 holds

/-- Diagnose exactly one clause, independently of the global scan order. -/
def diagnoseAt [DecidableEq Ty]
    (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty)
    (clause : AdmissionClause) : Option (Diagnostic Ty) :=
  (checkClause alphabet raw clause).diagnostic?

private theorem diagnoseAt_eq_none_iff [DecidableEq Ty]
    {alphabet : FlowAlphabet Ty} {raw : RawFlow Ty}
    {clause : AdmissionClause} :
    diagnoseAt alphabet raw clause = none ↔
      ClauseHolds alphabet raw clause := by
  unfold diagnoseAt checkClause
  split <;> simp_all [ClauseResult.diagnostic?]

private theorem diagnoseAt_clause [DecidableEq Ty]
    {alphabet : FlowAlphabet Ty} {raw : RawFlow Ty}
    {clause : AdmissionClause} {diagnostic : Diagnostic Ty}
    (found : diagnoseAt alphabet raw clause = some diagnostic) :
    diagnostic.clause = clause := by
  unfold diagnoseAt at found
  generalize resultEq : checkClause alphabet raw clause = result at found
  cases result with
  | pass proof => simp [ClauseResult.diagnostic?] at found
  | fail site payload refute =>
      simp [ClauseResult.diagnostic?] at found
      cases found
      rfl

private theorem flowWF_iff_clauses [DecidableEq Ty]
    (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty) :
    FlowWF alphabet raw ↔
      ∀ clause, clause ∈ scan → ClauseHolds alphabet raw clause := by
  constructor
  · intro wf clause _
    rcases idsWF_view raw |>.mp wf.ids with ⟨blockIds, blockOrder, decisions⟩
    rcases wf.roots with
      ⟨rootsNonempty, rootIds, rootOrder, entryRoot, rootsResolve⟩
    cases clause with
    | alphabetMismatch => exact wf.alphabet
    | duplicateBlockId => exact blockIds
    | duplicateDecisionId => exact decisions
    | nonCanonicalBlockOrder => exact blockOrder
    | emptyRoots => exact rootsNonempty
    | duplicateRoot => exact rootIds
    | nonCanonicalRootOrder => exact rootOrder
    | entryNotRoot => exact entryRoot
    | danglingRoot => exact rootsResolve
    | danglingSuccessor => exact wf.references
    | unknownOperation =>
        exact (operationsWF_view alphabet raw).mp wf.operations
    | entryTypeMismatch => exact wf.entry
    | termTypeMismatch => exact (termsWF_view alphabet raw |>.mp wf.terms)
  · intro clauses
    have holds (clause : AdmissionClause) : ClauseHolds alphabet raw clause :=
      clauses clause (by cases clause <;> simp [scan])
    refine {
      alphabet := holds .alphabetMismatch
      ids := idsWF_view raw |>.mpr ⟨
        holds .duplicateBlockId,
        holds .nonCanonicalBlockOrder,
        holds .duplicateDecisionId⟩
      roots := ⟨
        holds .emptyRoots,
        holds .duplicateRoot,
        holds .nonCanonicalRootOrder,
        holds .entryNotRoot,
        holds .danglingRoot⟩
      references := holds .danglingSuccessor
      operations := (operationsWF_view alphabet raw).mpr
        (holds .unknownOperation)
      entry := holds .entryTypeMismatch
      terms := termsWF_view alphabet raw |>.mpr (holds .termTypeMismatch)
    }

/-- A diagnostic is first exactly when its clause fails and every prior clause passes. -/
structure FirstDiagnostic [DecidableEq Ty]
    (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty)
    (diagnostic : Diagnostic Ty) : Prop where
  condemns : diagnoseAt alphabet raw diagnostic.clause = some diagnostic
  prior : ∀ clause,
    clause ∈ scan.takeWhile
      (fun candidate => decide (candidate != diagnostic.clause)) →
    diagnoseAt alphabet raw clause = none

namespace Diagnostic

/-- All thirteen independent checks pass exactly when the seven WF fields hold. -/
theorem clause_all_complete [DecidableEq Ty]
    {alphabet : FlowAlphabet Ty} {raw : RawFlow Ty} :
    FlowWF alphabet raw ↔
      ∀ clause, clause ∈ scan → diagnoseAt alphabet raw clause = none := by
  constructor
  · intro wf clause member
    exact diagnoseAt_eq_none_iff.mpr
      ((flowWF_iff_clauses alphabet raw).mp wf clause member)
  · intro clear
    apply (flowWF_iff_clauses alphabet raw).mpr
    intro clause member
    exact diagnoseAt_eq_none_iff.mp (clear clause member)

end Diagnostic

private theorem scan_nodup : scan.Nodup := by decide

private def clausesBefore : AdmissionClause → List AdmissionClause
  | .alphabetMismatch => []
  | .duplicateBlockId => [.alphabetMismatch]
  | .duplicateDecisionId => [.alphabetMismatch, .duplicateBlockId]
  | .nonCanonicalBlockOrder =>
      [.alphabetMismatch, .duplicateBlockId, .duplicateDecisionId]
  | .emptyRoots =>
      [.alphabetMismatch, .duplicateBlockId, .duplicateDecisionId,
       .nonCanonicalBlockOrder]
  | .duplicateRoot =>
      [.alphabetMismatch, .duplicateBlockId, .duplicateDecisionId,
       .nonCanonicalBlockOrder, .emptyRoots]
  | .nonCanonicalRootOrder =>
      [.alphabetMismatch, .duplicateBlockId, .duplicateDecisionId,
       .nonCanonicalBlockOrder, .emptyRoots, .duplicateRoot]
  | .entryNotRoot =>
      [.alphabetMismatch, .duplicateBlockId, .duplicateDecisionId,
       .nonCanonicalBlockOrder, .emptyRoots, .duplicateRoot,
       .nonCanonicalRootOrder]
  | .danglingRoot =>
      [.alphabetMismatch, .duplicateBlockId, .duplicateDecisionId,
       .nonCanonicalBlockOrder, .emptyRoots, .duplicateRoot,
       .nonCanonicalRootOrder, .entryNotRoot]
  | .danglingSuccessor =>
      [.alphabetMismatch, .duplicateBlockId, .duplicateDecisionId,
       .nonCanonicalBlockOrder, .emptyRoots, .duplicateRoot,
       .nonCanonicalRootOrder, .entryNotRoot, .danglingRoot]
  | .unknownOperation =>
      [.alphabetMismatch, .duplicateBlockId, .duplicateDecisionId,
       .nonCanonicalBlockOrder, .emptyRoots, .duplicateRoot,
       .nonCanonicalRootOrder, .entryNotRoot, .danglingRoot,
       .danglingSuccessor]
  | .entryTypeMismatch =>
      [.alphabetMismatch, .duplicateBlockId, .duplicateDecisionId,
       .nonCanonicalBlockOrder, .emptyRoots, .duplicateRoot,
       .nonCanonicalRootOrder, .entryNotRoot, .danglingRoot,
       .danglingSuccessor, .unknownOperation]
  | .termTypeMismatch =>
      [.alphabetMismatch, .duplicateBlockId, .duplicateDecisionId,
       .nonCanonicalBlockOrder, .emptyRoots, .duplicateRoot,
       .nonCanonicalRootOrder, .entryNotRoot, .danglingRoot,
       .danglingSuccessor, .unknownOperation, .entryTypeMismatch]

private def clausesAfter (clause : AdmissionClause) : List AdmissionClause :=
  scan.drop ((clausesBefore clause).length + 1)

private theorem clause_split (clause : AdmissionClause) :
    scan = clausesBefore clause ++ clause :: clausesAfter clause := by
  cases clause <;> rfl

private theorem takeWhile_before
    (clause : AdmissionClause) {before after : List AdmissionClause}
    (split : scan = before ++ clause :: after) :
    scan.takeWhile (fun candidate => decide (candidate != clause)) = before := by
  have noDuplicates : (before ++ clause :: after).Nodup :=
    split ▸ scan_nodup
  have clauseNotInBefore : clause ∉ before := by
    rw [List.nodup_append] at noDuplicates
    intro clauseInBefore
    exact (noDuplicates.2.2 clause clauseInBefore clause (by simp)) rfl
  rw [split, List.takeWhile_append_of_pos]
  · simp
  · intro candidate candidateInBefore
    simp only [decide_eq_true_eq]
    apply bne_iff_ne.mpr
    intro candidateEqClause
    subst candidate
    exact clauseNotInBefore candidateInBefore

private def firstDiagnostic? [DecidableEq Ty]
    (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty) :
    Option (Diagnostic Ty) :=
  scan.findSome? (diagnoseAt alphabet raw)

private theorem firstDiagnostic?_eq_none_iff [DecidableEq Ty]
    {alphabet : FlowAlphabet Ty} {raw : RawFlow Ty} :
    firstDiagnostic? alphabet raw = none ↔
      ∀ clause, clause ∈ scan → diagnoseAt alphabet raw clause = none := by
  simp [firstDiagnostic?]

private theorem firstDiagnostic?_eq_some_iff [DecidableEq Ty]
    {alphabet : FlowAlphabet Ty} {raw : RawFlow Ty}
    {diagnostic : Diagnostic Ty} :
    firstDiagnostic? alphabet raw = some diagnostic ↔
      FirstDiagnostic alphabet raw diagnostic := by
  unfold firstDiagnostic?
  constructor
  · intro found
    obtain ⟨before, clause, after, split, condemns, prior⟩ :=
      List.findSome?_eq_some_iff.mp found
    have clauseEq : diagnostic.clause = clause :=
      diagnoseAt_clause condemns
    subst clause
    refine ⟨condemns, ?_⟩
    intro candidate candidateInPrior
    rw [takeWhile_before diagnostic.clause split] at candidateInPrior
    exact prior candidate candidateInPrior
  · intro first
    let before := clausesBefore diagnostic.clause
    let after := clausesAfter diagnostic.clause
    have split : scan = before ++ diagnostic.clause :: after :=
      clause_split diagnostic.clause
    apply List.findSome?_eq_some_iff.mpr
    refine ⟨before, diagnostic.clause, after, split, first.condemns, ?_⟩
    intro candidate candidateInBefore
    apply first.prior candidate
    rw [takeWhile_before diagnostic.clause split]
    exact candidateInBefore

/-- The proof-carrying result of successful admission. -/
structure CheckedFlow.{uTy, uOp} {Ty : Type uTy}
    (alphabet : FlowAlphabet.{uTy, uOp} Ty) : Type uTy where
  private mk ::
  raw : RawFlow Ty
  wf : FlowWF alphabet raw

namespace CheckedFlow

/-- Forget the proof while retaining the complete first-order document. -/
def erase {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
    (checked : CheckedFlow alphabet) : RawFlow Ty :=
  checked.raw

@[simp] theorem erase_eq_raw
    {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
    (checked : CheckedFlow alphabet) :
    checked.erase = checked.raw := rfl

@[ext] theorem ext
    {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
    {left right : CheckedFlow alphabet}
    (raw : left.raw = right.raw) : left = right := by
  cases left
  cases right
  cases raw
  rfl

end CheckedFlow

private def defaultDiagnostic : Diagnostic Ty :=
  ⟨.alphabetMismatch, .flow, .none⟩

/-- Check every clause in the fixed order and seal the raw graph on success. -/
def admit [DecidableEq Ty]
    (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty) :
    Except (Diagnostic Ty) (CheckedFlow alphabet) :=
  if clear : firstDiagnostic? alphabet raw = none then
    .ok <| CheckedFlow.mk raw <|
      Diagnostic.clause_all_complete.mpr <|
        firstDiagnostic?_eq_none_iff.mp clear
  else
    .error <| (firstDiagnostic? alphabet raw).getD defaultDiagnostic

/-- Successful admission proves all seven WF fields for the original raw graph. -/
theorem admit_sound [DecidableEq Ty]
    {alphabet : FlowAlphabet Ty} {raw : RawFlow Ty}
    {checked : CheckedFlow alphabet}
    (accepted : admit alphabet raw = .ok checked) :
    FlowWF alphabet raw := by
  unfold admit at accepted
  split at accepted
  · rename_i found
    exact Diagnostic.clause_all_complete.mpr
      (firstDiagnostic?_eq_none_iff.mp found)
  · contradiction

/-- Every graph satisfying the frozen seven clauses is admitted. -/
theorem admit_complete [DecidableEq Ty]
    {alphabet : FlowAlphabet Ty} {raw : RawFlow Ty}
    (wf : FlowWF alphabet raw) :
    ∃ checked : CheckedFlow alphabet, admit alphabet raw = .ok checked := by
  have clear := Diagnostic.clause_all_complete.mp wf
  have found : firstDiagnostic? alphabet raw = none :=
    firstDiagnostic?_eq_none_iff.mpr clear
  refine ⟨CheckedFlow.mk raw wf, ?_⟩
  simp only [admit, found]
  congr 2

/-- Admission reports some error exactly when the raw graph is not well formed. -/
theorem error_iff_not_wf [DecidableEq Ty]
    {alphabet : FlowAlphabet Ty} {raw : RawFlow Ty} :
    (∃ diagnostic : Diagnostic Ty,
      admit alphabet raw = .error diagnostic) ↔
    ¬ FlowWF alphabet raw := by
  constructor
  · rintro ⟨diagnostic, errored⟩ wf
    obtain ⟨checked, accepted⟩ := admit_complete wf
    rw [errored] at accepted
    contradiction
  · intro notWf
    cases resultEq : admit alphabet raw with
    | error diagnostic => exact ⟨diagnostic, rfl⟩
    | ok checked => exact (notWf (admit_sound resultEq)).elim

/-- A particular error is returned exactly when it is the first failing clause. -/
theorem error_iff_firstDiagnostic [DecidableEq Ty]
    {alphabet : FlowAlphabet Ty} {raw : RawFlow Ty}
    {diagnostic : Diagnostic Ty} :
    admit alphabet raw = .error diagnostic ↔
      FirstDiagnostic alphabet raw diagnostic := by
  rw [← firstDiagnostic?_eq_some_iff]
  unfold admit
  split
  · rename_i clear
    constructor
    · intro impossible
      contradiction
    · intro found
      rw [clear] at found
      contradiction
  · rename_i notClear
    cases found : firstDiagnostic? alphabet raw with
    | none => exact (notClear found).elim
    | some first => simp

/-- Erasing any checked flow retains its WF evidence. -/
theorem erase_wf (checked : CheckedFlow alphabet) :
    FlowWF alphabet checked.erase :=
  by simpa using checked.wf

/-- A successful admission result erases to the exact input raw graph. -/
theorem erase_admit [DecidableEq Ty]
    {alphabet : FlowAlphabet Ty} {raw : RawFlow Ty}
    {checked : CheckedFlow alphabet}
    (accepted : admit alphabet raw = .ok checked) :
    checked.erase = raw := by
  unfold admit at accepted
  split at accepted
  · cases accepted
    simp
  · contradiction

/-- Re-admitting a checked erasure returns the same proof-carrying value. -/
theorem admit_erase [DecidableEq Ty]
    {alphabet : FlowAlphabet Ty} (checked : CheckedFlow alphabet) :
    admit alphabet checked.erase = .ok checked := by
  have clear := Diagnostic.clause_all_complete.mp checked.wf
  have found : firstDiagnostic? alphabet checked.erase = none :=
    firstDiagnostic?_eq_none_iff.mpr (by simpa using clear)
  simp only [admit, found]
  congr 2

end Effect4
