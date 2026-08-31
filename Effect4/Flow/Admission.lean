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

/--
`failure` is the first witness of `FailureAt` in the authored source order.
The relation is generic so nested scans use the same ordering law.
-/
structure FirstFailureAt
    (source : List α)
    (FailureAt : Nat → α → β → Prop)
    (index : Nat) (item : α) (failure : β) : Prop where
  source_at : source[index]? = some item
  fails_at : FailureAt index item failure
  prior_clear : ∀ priorIndex priorItem,
    priorIndex < index →
    source[priorIndex]? = some priorItem →
    ∀ priorFailure, ¬ FailureAt priorIndex priorItem priorFailure

/-- The exact, ordered local typing failure carried by a term diagnostic. -/
inductive TermFailureValid
    (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty)
    (block : RawBlock Ty) : DiagnosticPayload Ty → Prop where
  | retTypeMismatch
      (term : block.term = .ret)
      (mismatch : block.inputTy ≠ raw.resultTy) :
      TermFailureValid alphabet raw block
        (.typeMismatch raw.resultTy block.inputTy)
  | jumpMissing {target : BlockId}
      (term : block.term = .jump target)
      (missing : lookupBlock raw target = none) :
      TermFailureValid alphabet raw block (.block target)
  | jumpTypeMismatch {target : BlockId} {targetBlock : RawBlock Ty}
      (term : block.term = .jump target)
      (found : lookupBlock raw target = some targetBlock)
      (mismatch : targetBlock.inputTy ≠ block.inputTy) :
      TermFailureValid alphabet raw block
        (.typeMismatch block.inputTy targetBlock.inputTy)
  | performUnknownOperation {operation : OperationId} {target : BlockId}
      (term : block.term = .perform operation target)
      (unknown : alphabet.lookup operation = none) :
      TermFailureValid alphabet raw block (.operation operation)
  | performMissingTarget {operation : OperationId} {target : BlockId}
      {operationDef : alphabet.Op}
      (term : block.term = .perform operation target)
      (known : alphabet.lookup operation = some operationDef)
      (missing : lookupBlock raw target = none) :
      TermFailureValid alphabet raw block (.block target)
  | performRequestTypeMismatch {operation : OperationId} {target : BlockId}
      {operationDef : alphabet.Op} {targetBlock : RawBlock Ty}
      (term : block.term = .perform operation target)
      (known : alphabet.lookup operation = some operationDef)
      (found : lookupBlock raw target = some targetBlock)
      (mismatch : block.inputTy ≠ alphabet.requestTy operationDef) :
      TermFailureValid alphabet raw block
        (.typeMismatch (alphabet.requestTy operationDef) block.inputTy)
  | performAnswerTypeMismatch {operation : OperationId} {target : BlockId}
      {operationDef : alphabet.Op} {targetBlock : RawBlock Ty}
      (term : block.term = .perform operation target)
      (known : alphabet.lookup operation = some operationDef)
      (found : lookupBlock raw target = some targetBlock)
      (request : block.inputTy = alphabet.requestTy operationDef)
      (mismatch : targetBlock.inputTy ≠ alphabet.answerTy operationDef) :
      TermFailureValid alphabet raw block
        (.typeMismatch (alphabet.answerTy operationDef) targetBlock.inputTy)
  | chooseMissingLeft {decision : DecisionId} {left right : BlockId}
      (term : block.term = .choose decision left right)
      (missing : lookupBlock raw left = none) :
      TermFailureValid alphabet raw block (.block left)
  | chooseMissingRight {decision : DecisionId} {left right : BlockId}
      {leftBlock : RawBlock Ty}
      (term : block.term = .choose decision left right)
      (leftFound : lookupBlock raw left = some leftBlock)
      (missing : lookupBlock raw right = none) :
      TermFailureValid alphabet raw block (.block right)
  | chooseLeftTypeMismatch {decision : DecisionId} {left right : BlockId}
      {leftBlock rightBlock : RawBlock Ty}
      (term : block.term = .choose decision left right)
      (leftFound : lookupBlock raw left = some leftBlock)
      (rightFound : lookupBlock raw right = some rightBlock)
      (mismatch : leftBlock.inputTy ≠ block.inputTy) :
      TermFailureValid alphabet raw block
        (.typeMismatch block.inputTy leftBlock.inputTy)
  | chooseRightTypeMismatch {decision : DecisionId} {left right : BlockId}
      {leftBlock rightBlock : RawBlock Ty}
      (term : block.term = .choose decision left right)
      (leftFound : lookupBlock raw left = some leftBlock)
      (rightFound : lookupBlock raw right = some rightBlock)
      (leftTyped : leftBlock.inputTy = block.inputTy)
      (mismatch : rightBlock.inputTy ≠ block.inputTy) :
      TermFailureValid alphabet raw block
        (.typeMismatch block.inputTy rightBlock.inputTy)

namespace Diagnostic

/-- A diagnostic points to the exact first source witness for its clause. -/
inductive Valid (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty) :
    Diagnostic Ty → Prop where
  | alphabetMismatch
      (mismatch : raw.alphabet ≠ alphabet.id) :
      Valid alphabet raw
        ⟨.alphabetMismatch, .flow, .alphabet alphabet.id raw.alphabet⟩
  | duplicateBlockId {index : Nat} {block : RawBlock Ty}
      (first : FirstFailureAt raw.blocks
        (fun candidateIndex candidate reported =>
          reported = candidate.id ∧
          candidate.id ∈ (raw.blocks.take candidateIndex).map RawBlock.id)
        index block block.id) :
      Valid alphabet raw ⟨.duplicateBlockId, .block index, .block block.id⟩
  | duplicateDecisionId {index : Nat} {block : RawBlock Ty}
      {decision : DecisionId}
      (first : FirstFailureAt raw.blocks
        (fun candidateIndex candidate reported =>
          ∃ left right,
            candidate.term = .choose reported left right ∧
            reported ∈
              (raw.blocks.take candidateIndex).filterMap (fun prior =>
                match prior.term with
                | .choose priorDecision _ _ => some priorDecision
                | _ => none))
        index block decision) :
      Valid alphabet raw
        ⟨.duplicateDecisionId, .decision block.id, .decision decision⟩
  | nonCanonicalBlockOrder {index : Nat} {block : RawBlock Ty}
      (first : FirstFailureAt raw.blocks
        (fun candidateIndex candidate reported =>
          reported = candidate.id ∧ 0 < candidateIndex ∧
          ∃ previous,
            raw.blocks[candidateIndex - 1]? = some previous ∧
            ¬ previous.id.value < candidate.id.value)
        index block block.id) :
      Valid alphabet raw
        ⟨.nonCanonicalBlockOrder, .block index, .block block.id⟩
  | emptyRoots (empty : raw.roots = []) :
      Valid alphabet raw ⟨.emptyRoots, .flow, .none⟩
  | duplicateRoot {index : Nat} {root : BlockId}
      (first : FirstFailureAt raw.roots
        (fun candidateIndex candidate reported =>
          reported = candidate ∧ candidate ∈ raw.roots.take candidateIndex)
        index root root) :
      Valid alphabet raw ⟨.duplicateRoot, .root index, .block root⟩
  | nonCanonicalRootOrder {index : Nat} {root : BlockId}
      (first : FirstFailureAt raw.roots
        (fun candidateIndex candidate reported =>
          reported = candidate ∧ 0 < candidateIndex ∧
          ∃ previous,
            raw.roots[candidateIndex - 1]? = some previous ∧
            ¬ previous.value < candidate.value)
        index root root) :
      Valid alphabet raw
        ⟨.nonCanonicalRootOrder, .root index, .block root⟩
  | entryNotRoot (missing : raw.entry ∉ raw.roots) :
      Valid alphabet raw ⟨.entryNotRoot, .entry, .block raw.entry⟩
  | danglingRoot {index : Nat} {root : BlockId}
      (first : FirstFailureAt raw.roots
        (fun _ candidate reported =>
          reported = candidate ∧ lookupBlock raw candidate = none)
        index root root) :
      Valid alphabet raw ⟨.danglingRoot, .root index, .block root⟩
  | danglingSuccessor {blockIndex successorIndex : Nat}
      {block : RawBlock Ty} {target : BlockId}
      (first : FirstFailureAt raw.blocks
        (fun _ candidate witness =>
          FirstFailureAt candidate.term.successors
            (fun _ successor reported =>
              reported = successor ∧ lookupBlock raw successor = none)
            witness.1 witness.2 witness.2)
        blockIndex block (successorIndex, target)) :
      Valid alphabet raw
        ⟨.danglingSuccessor, .successor block.id successorIndex, .block target⟩
  | unknownOperation {index : Nat} {block : RawBlock Ty}
      {operation : OperationId}
      (first : FirstFailureAt raw.blocks
        (fun _ candidate reported =>
          ∃ target,
            candidate.term = .perform reported target ∧
            alphabet.lookup reported = none)
        index block operation) :
      Valid alphabet raw
        ⟨.unknownOperation, .operation block.id, .operation operation⟩
  | entryMissing (missing : lookupBlock raw raw.entry = none) :
      Valid alphabet raw ⟨.entryTypeMismatch, .entry, .block raw.entry⟩
  | entryTypeMismatch {block : RawBlock Ty}
      (found : lookupBlock raw raw.entry = some block)
      (mismatch : block.inputTy ≠ raw.inputTy) :
      Valid alphabet raw
        ⟨.entryTypeMismatch, .entry,
          .typeMismatch raw.inputTy block.inputTy⟩
  | termTypeMismatch {index : Nat} {block : RawBlock Ty}
      {payload : DiagnosticPayload Ty}
      (first : FirstFailureAt raw.blocks
        (fun _ candidate failure =>
          TermFailureValid alphabet raw candidate failure)
        index block payload) :
      Valid alphabet raw ⟨.termTypeMismatch, .term block.id, payload⟩

end Diagnostic

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

/-- Run one indexed source-order scan and retain the exact source item. -/
private def firstFailure?
    (source : List α) (check : Nat → α → Option β) :
    Option (Nat × α × β) :=
  source.zipIdx.findSome? fun (item, index) =>
    (check index item).map fun failure => (index, item, failure)

private theorem firstFailure?_eq_none_iff
    {source : List α} {check : Nat → α → Option β} :
    firstFailure? source check = none ↔
      ∀ index item, source[index]? = some item → check index item = none := by
  simp only [firstFailure?, List.findSome?_eq_none_iff]
  constructor
  · intro clear index item sourceAt
    have member : (item, index) ∈ source.zipIdx :=
      List.mk_mem_zipIdx_iff_getElem?.mpr sourceAt
    have mapped := clear (item, index) member
    simpa using mapped
  · intro clear pair member
    rcases pair with ⟨item, index⟩
    have sourceAt : source[index]? = some item :=
      List.mk_mem_zipIdx_iff_getElem?.mp member
    have checked := clear index item sourceAt
    simp [checked]

private theorem firstFailure?_eq_some_valid
    {source : List α} {check : Nat → α → Option β}
    {FailureAt : Nat → α → β → Prop}
    (precise : ∀ index item failure,
      check index item = some failure ↔ FailureAt index item failure)
    {index : Nat} {item : α} {failure : β}
    (found : firstFailure? source check = some (index, item, failure)) :
    FirstFailureAt source FailureAt index item failure := by
  simp only [firstFailure?] at found
  obtain ⟨before, pair, after, split, atPair, prior⟩ :=
    List.findSome?_eq_some_iff.mp found
  rcases pair with ⟨foundItem, foundIndex⟩
  simp only [Option.map_eq_some_iff] at atPair
  obtain ⟨foundFailure, checkFound, tripleEq⟩ := atPair
  cases tripleEq
  have pairMember : (item, index) ∈ source.zipIdx := by
    rw [split]
    simp
  have sourceAt : source[index]? = some item :=
    List.mk_mem_zipIdx_iff_getElem?.mp pairMember
  refine {
    source_at := sourceAt
    fails_at := (precise index item failure).mp checkFound
    prior_clear := ?_
  }
  intro priorIndex priorItem priorLt priorAt priorFailure priorFails
  have currentAtPosition :
      (source.zipIdx)[before.length]? = some (item, index) := by
    rw [split]
    simp
  rw [List.getElem?_zipIdx] at currentAtPosition
  cases sourceEq : source[before.length]? with
  | none => simp [sourceEq] at currentAtPosition
  | some currentItem =>
    simp [sourceEq] at currentAtPosition
    have indexEq : index = before.length := currentAtPosition.2.symm
    have priorPairAt :
        (source.zipIdx)[priorIndex]? = some (priorItem, priorIndex) := by
      simp [List.getElem?_zipIdx, priorAt]
    have priorBeforeAt : before[priorIndex]? = some (priorItem, priorIndex) := by
      rw [split] at priorPairAt
      rw [List.getElem?_append_left (by omega)] at priorPairAt
      exact priorPairAt
    have priorMember : (priorItem, priorIndex) ∈ before :=
      List.mem_iff_getElem?.mpr ⟨priorIndex, priorBeforeAt⟩
    have clearMapped := prior (priorItem, priorIndex) priorMember
    have clear : check priorIndex priorItem = none := by
      simpa using clearMapped
    have failedCheck : check priorIndex priorItem = some priorFailure :=
      (precise priorIndex priorItem priorFailure).mpr priorFails
    rw [clear] at failedCheck
    contradiction

private theorem firstFailure?_eq_some_iff
    {source : List α} {check : Nat → α → Option β}
    {FailureAt : Nat → α → β → Prop}
    (precise : ∀ index item failure,
      check index item = some failure ↔ FailureAt index item failure)
    {index : Nat} {item : α} {failure : β} :
    firstFailure? source check = some (index, item, failure) ↔
      FirstFailureAt source FailureAt index item failure := by
  constructor
  · exact firstFailure?_eq_some_valid precise
  · intro expected
    cases resultEq : firstFailure? source check with
    | none =>
        have clear := firstFailure?_eq_none_iff.mp resultEq
        have checkedClear := clear index item expected.source_at
        have checkedFailure :=
          (precise index item failure).mpr expected.fails_at
        rw [checkedClear] at checkedFailure
        contradiction
    | some result =>
        rcases result with ⟨foundIndex, foundItem, foundFailure⟩
        have found := firstFailure?_eq_some_valid precise resultEq
        have indexEq : foundIndex = index := by
          rcases Nat.lt_trichotomy foundIndex index with earlier | equalOrLater
          · exact (expected.prior_clear foundIndex foundItem earlier
              found.source_at foundFailure found.fails_at).elim
          · rcases equalOrLater with equal | later
            · exact equal
            · exact (found.prior_clear index item later expected.source_at
                failure expected.fails_at).elim
        subst foundIndex
        have itemEq : foundItem = item := by
          have expectedAt := expected.source_at
          rw [found.source_at] at expectedAt
          exact Option.some.inj expectedAt
        subst foundItem
        have foundCheck : check index item = some foundFailure :=
          (precise index item foundFailure).mpr found.fails_at
        have expectedCheck : check index item = some failure :=
          (precise index item failure).mpr expected.fails_at
        have failureEq : foundFailure = failure :=
          Option.some.inj (foundCheck.symm.trans expectedCheck)
        subst foundFailure
        rfl

private theorem nodup_of_no_prefix_duplicate [DecidableEq α]
    (source : List α)
    (clear : ∀ index item,
      source[index]? = some item → item ∉ source.take index) :
    source.Nodup := by
  induction source with
  | nil => simp
  | cons head tail ih =>
      rw [List.nodup_cons]
      constructor
      · intro headMem
        obtain ⟨index, headAt⟩ := List.mem_iff_getElem?.mp headMem
        have noDuplicate := clear (index + 1) head (by simp [headAt])
        exact noDuplicate (by simp)
      · apply ih
        intro index item itemAt itemMem
        have noDuplicate := clear (index + 1) item (by simp [itemAt])
        exact noDuplicate (by simp [itemMem])

private theorem map_nodup_of_no_prefix_duplicate [DecidableEq β]
    (source : List α) (key : α → β)
    (clear : ∀ index item,
      source[index]? = some item →
      key item ∉ (source.take index).map key) :
    (source.map key).Nodup := by
  apply nodup_of_no_prefix_duplicate
  intro index item mappedAt mappedMem
  rw [List.getElem?_map] at mappedAt
  cases sourceAt : source[index]? with
  | none => simp [sourceAt] at mappedAt
  | some sourceItem =>
      simp [sourceAt] at mappedAt
      subst item
      exact clear index sourceItem sourceAt (by simpa using mappedMem)

private theorem filterMap_nodup_of_no_prefix_duplicate [DecidableEq β]
    (source : List α) (pick : α → Option β)
    (clear : ∀ index item,
      source[index]? = some item →
      ∀ value, pick item = some value →
        value ∉ (source.take index).filterMap pick) :
    (source.filterMap pick).Nodup := by
  induction source with
  | nil => simp
  | cons head tail ih =>
      cases headEq : pick head with
      | none =>
          simp only [List.filterMap_cons, headEq]
          apply ih
          intro index item itemAt value picked valueMem
          have noDuplicate := clear (index + 1) item (by simp [itemAt])
            value picked
          exact noDuplicate (by simp [headEq, valueMem])
      | some headValue =>
          simp only [List.filterMap_cons, headEq, List.nodup_cons]
          constructor
          · intro headValueMem
            simp only [List.mem_filterMap] at headValueMem
            obtain ⟨item, itemMem, picked⟩ := headValueMem
            obtain ⟨index, itemAt⟩ := List.mem_iff_getElem?.mp itemMem
            have noDuplicate := clear (index + 1) item (by simp [itemAt])
              headValue picked
            exact noDuplicate (by simp [headEq])
          · apply ih
            intro index item itemAt value picked valueMem
            have noDuplicate := clear (index + 1) item (by simp [itemAt])
              value picked
            exact noDuplicate (by simp [headEq, valueMem])

private theorem pairwise_nat_of_adjacent
    (source : List α) (value : α → Nat)
    (adjacent : ∀ index item previous,
      0 < index →
      source[index]? = some item →
      source[index - 1]? = some previous →
      value previous < value item) :
    source.Pairwise (fun left right => value left < value right) := by
  induction source with
  | nil => simp
  | cons head tail ih =>
      have tailAdjacent : ∀ index item previous,
          0 < index →
          tail[index]? = some item →
          tail[index - 1]? = some previous →
          value previous < value item := by
        intro index item previous positive itemAt previousAt
        cases index with
        | zero => omega
        | succ prior =>
            exact adjacent (prior + 2) item previous (by omega)
              (by simp [itemAt]) (by simpa using previousAt)
      have tailPairwise := ih tailAdjacent
      rw [List.pairwise_cons]
      refine ⟨?_, tailPairwise⟩
      intro item itemMem
      cases tail with
      | nil => contradiction
      | cons first rest =>
          have headFirst : value head < value first :=
            adjacent 1 first head (by omega) (by simp) (by simp)
          simp only [List.mem_cons] at itemMem
          rcases itemMem with rfl | itemMem
          · exact headFirst
          · exact Nat.lt_trans headFirst
              (List.rel_of_pairwise_cons tailPairwise itemMem)

private def duplicateBlockFailure? (raw : RawFlow Ty)
    (index : Nat) (block : RawBlock Ty) : Option BlockId :=
  if block.id ∈ (raw.blocks.take index).map RawBlock.id then
    some block.id
  else
    none

private theorem duplicateBlockFailure?_eq_some_iff
    (raw : RawFlow Ty) (index : Nat) (block : RawBlock Ty)
    (reported : BlockId) :
    duplicateBlockFailure? raw index block = some reported ↔
      reported = block.id ∧
      block.id ∈ (raw.blocks.take index).map RawBlock.id := by
  simp [duplicateBlockFailure?, and_comm, eq_comm]

private def duplicateDecisionFailure? (raw : RawFlow Ty)
    (index : Nat) (block : RawBlock Ty) : Option DecisionId :=
  match block.term with
  | .choose decision _ _ =>
      if decision ∈
          (raw.blocks.take index).filterMap (fun prior =>
            match prior.term with
            | .choose priorDecision _ _ => some priorDecision
            | _ => none) then
        some decision
      else
        none
  | _ => none

private theorem duplicateDecisionFailure?_eq_some_iff
    (raw : RawFlow Ty) (index : Nat) (block : RawBlock Ty)
    (reported : DecisionId) :
    duplicateDecisionFailure? raw index block = some reported ↔
      ∃ left right,
        block.term = .choose reported left right ∧
        reported ∈
          (raw.blocks.take index).filterMap (fun prior =>
            match prior.term with
            | .choose priorDecision _ _ => some priorDecision
            | _ => none) := by
  cases termEq : block.term with
  | ret | jump | perform => simp [duplicateDecisionFailure?, termEq]
  | choose decision left right =>
      by_cases member : decision ∈
          (raw.blocks.take index).filterMap (fun prior =>
            match prior.term with
            | .choose priorDecision _ _ => some priorDecision
            | _ => none)
      · simp [duplicateDecisionFailure?, termEq, member, eq_comm]
        intro reportedEq
        subst reported
        simpa only [List.mem_filterMap, eq_comm] using member
      · simp [duplicateDecisionFailure?, termEq, member]
        intro reportedEq
        subst reported
        simp only [List.mem_filterMap] at member
        intro prior priorMem priorDecision
        exact member ⟨prior, priorMem, priorDecision⟩

private def orderFailure? (source : List α) (value : α → Nat)
    (index : Nat) (item : α) : Option α :=
  match index with
  | 0 => none
  | prior + 1 =>
      match source[prior]? with
      | none => none
      | some previous =>
          if value previous < value item then none else some item

private theorem orderFailure?_eq_some_iff
    (source : List α) (value : α → Nat)
    (index : Nat) (item reported : α) :
    orderFailure? source value index item = some reported ↔
      reported = item ∧ 0 < index ∧
      ∃ previous,
        source[index - 1]? = some previous ∧
        ¬ value previous < value item := by
  cases index with
  | zero => simp [orderFailure?]
  | succ prior =>
      cases previousEq : source[prior]? with
      | none => simp [orderFailure?, previousEq]
      | some previous =>
          by_cases ordered : value previous < value item
          · simp [orderFailure?, previousEq, ordered]
          · simp [orderFailure?, previousEq, ordered, eq_comm, Nat.not_lt]
            omega

private def duplicateRootFailure? (raw : RawFlow Ty)
    (index : Nat) (root : BlockId) : Option BlockId :=
  if root ∈ raw.roots.take index then some root else none

private theorem duplicateRootFailure?_eq_some_iff
    (raw : RawFlow Ty) (index : Nat) (root reported : BlockId) :
    duplicateRootFailure? raw index root = some reported ↔
      reported = root ∧ root ∈ raw.roots.take index := by
  simp [duplicateRootFailure?, and_comm, eq_comm]

private def danglingRootFailure? (raw : RawFlow Ty)
    (_ : Nat) (root : BlockId) : Option BlockId :=
  match lookupBlock raw root with
  | none => some root
  | some _ => none

private theorem danglingRootFailure?_eq_some_iff
    (raw : RawFlow Ty) (index : Nat) (root reported : BlockId) :
    danglingRootFailure? raw index root = some reported ↔
      reported = root ∧ lookupBlock raw root = none := by
  cases found : lookupBlock raw root <;>
    simp [danglingRootFailure?, found, eq_comm]

private def danglingSuccessorFailure? (raw : RawFlow Ty)
    (_ : Nat) (target : BlockId) : Option BlockId :=
  match lookupBlock raw target with
  | none => some target
  | some _ => none

private theorem danglingSuccessorFailure?_eq_some_iff
    (raw : RawFlow Ty) (index : Nat) (target reported : BlockId) :
    danglingSuccessorFailure? raw index target = some reported ↔
      reported = target ∧ lookupBlock raw target = none := by
  cases found : lookupBlock raw target <;>
    simp [danglingSuccessorFailure?, found, eq_comm]

private def firstPreciseDanglingSuccessorIn? (raw : RawFlow Ty)
    (block : RawBlock Ty) : Option (Nat × BlockId × BlockId) :=
  firstFailure? block.term.successors (danglingSuccessorFailure? raw)

private theorem firstPreciseDanglingSuccessorIn?_eq_some_valid
    {raw : RawFlow Ty} {block : RawBlock Ty}
    {index : Nat} {target reported : BlockId}
    (found : firstPreciseDanglingSuccessorIn? raw block =
      some (index, target, reported)) :
    FirstFailureAt block.term.successors
      (fun _ successor witness =>
        witness = successor ∧ lookupBlock raw successor = none)
      index target reported := by
  exact firstFailure?_eq_some_valid
    (danglingSuccessorFailure?_eq_some_iff raw) found

private def danglingBlockFailure? (raw : RawFlow Ty)
    (_ : Nat) (block : RawBlock Ty) : Option (Nat × BlockId) :=
  match firstPreciseDanglingSuccessorIn? raw block with
  | none => none
  | some (index, target, _) => some (index, target)

private theorem danglingBlockFailure?_eq_some_iff
    (raw : RawFlow Ty) (index : Nat) (block : RawBlock Ty)
    (witness : Nat × BlockId) :
    danglingBlockFailure? raw index block = some witness ↔
      FirstFailureAt block.term.successors
        (fun _ successor reported =>
          reported = successor ∧ lookupBlock raw successor = none)
        witness.1 witness.2 witness.2 := by
  constructor
  · intro found
    unfold danglingBlockFailure? at found
    cases innerEq : firstPreciseDanglingSuccessorIn? raw block with
    | none => simp [innerEq] at found
    | some result =>
        rcases result with ⟨successorIndex, target, reported⟩
        simp [innerEq] at found
        obtain ⟨rfl, rfl⟩ := found
        have valid := firstPreciseDanglingSuccessorIn?_eq_some_valid innerEq
        have reportedEq : reported = target := valid.fails_at.1
        subst reported
        exact valid
  · intro valid
    unfold danglingBlockFailure?
    have innerEq : firstPreciseDanglingSuccessorIn? raw block =
        some (witness.1, witness.2, witness.2) :=
      firstFailure?_eq_some_iff
        (danglingSuccessorFailure?_eq_some_iff raw) |>.mpr valid
    simp [innerEq]

private def unknownOperationFailure? (alphabet : FlowAlphabet Ty)
    (_ : Nat) (block : RawBlock Ty) : Option OperationId :=
  match block.term with
  | .perform operation _ =>
      match alphabet.lookup operation with
      | none => some operation
      | some _ => none
  | _ => none

private theorem unknownOperationFailure?_eq_some_iff
    (alphabet : FlowAlphabet Ty) (index : Nat) (block : RawBlock Ty)
    (reported : OperationId) :
    unknownOperationFailure? alphabet index block = some reported ↔
      ∃ target,
        block.term = .perform reported target ∧
        alphabet.lookup reported = none := by
  cases termEq : block.term with
  | ret | jump | choose => simp [unknownOperationFailure?, termEq]
  | perform operation target =>
      cases found : alphabet.lookup operation with
      | none =>
          constructor
          · intro failure
            simp [unknownOperationFailure?, termEq, found] at failure
            subst reported
            exact ⟨target, by simp [termEq], found⟩
          · rintro ⟨otherTarget, sameTerm, unknown⟩
            have same : reported = operation := by
              injection sameTerm with operationEq targetEq
              exact operationEq.symm
            subst reported
            simp [unknownOperationFailure?, termEq, found]
      | some operationDef =>
          constructor
          · intro failure
            simp [unknownOperationFailure?, termEq, found] at failure
          · rintro ⟨otherTarget, sameTerm, unknown⟩
            have same : reported = operation := by
              injection sameTerm with operationEq targetEq
              exact operationEq.symm
            subst reported
            rw [found] at unknown
            contradiction

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

private theorem termFailure?_eq_some_iff [DecidableEq Ty]
    (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty)
    (block : RawBlock Ty) (payload : DiagnosticPayload Ty) :
    termFailure? alphabet raw block = some payload ↔
      TermFailureValid alphabet raw block payload := by
  constructor
  · intro failure
    cases termEq : block.term with
    | ret =>
        by_cases typed : block.inputTy = raw.resultTy
        · simp [termFailure?, termEq, typed] at failure
        · simp [termFailure?, termEq, typed] at failure
          subst payload
          exact .retTypeMismatch termEq typed
    | jump target =>
        cases targetEq : lookupBlock raw target with
        | none =>
            simp [termFailure?, termEq, targetEq] at failure
            subst payload
            exact .jumpMissing termEq targetEq
        | some targetBlock =>
            by_cases typed : targetBlock.inputTy = block.inputTy
            · simp [termFailure?, termEq, targetEq, typed] at failure
            · simp [termFailure?, termEq, targetEq, typed] at failure
              subst payload
              exact .jumpTypeMismatch termEq targetEq typed
    | perform operation target =>
        cases operationEq : alphabet.lookup operation with
        | none =>
            simp [termFailure?, termEq, operationEq] at failure
            subst payload
            exact .performUnknownOperation termEq operationEq
        | some operationDef =>
            cases targetEq : lookupBlock raw target with
            | none =>
                simp [termFailure?, termEq, operationEq, targetEq] at failure
                subst payload
                exact .performMissingTarget termEq operationEq targetEq
            | some targetBlock =>
                by_cases requestTyped :
                    block.inputTy = alphabet.requestTy operationDef
                · by_cases answerTyped :
                      targetBlock.inputTy = alphabet.answerTy operationDef
                  · simp [termFailure?, termEq, operationEq, targetEq,
                      requestTyped, answerTyped] at failure
                  · simp [termFailure?, termEq, operationEq, targetEq,
                      requestTyped, answerTyped] at failure
                    subst payload
                    exact .performAnswerTypeMismatch termEq operationEq
                      targetEq requestTyped answerTyped
                · simp [termFailure?, termEq, operationEq, targetEq,
                    requestTyped] at failure
                  subst payload
                  exact .performRequestTypeMismatch termEq operationEq
                    targetEq requestTyped
    | choose decision left right =>
        cases leftEq : lookupBlock raw left with
        | none =>
            simp [termFailure?, termEq, leftEq] at failure
            subst payload
            exact .chooseMissingLeft termEq leftEq
        | some leftBlock =>
            cases rightEq : lookupBlock raw right with
            | none =>
                simp [termFailure?, termEq, leftEq, rightEq] at failure
                subst payload
                exact .chooseMissingRight termEq leftEq rightEq
            | some rightBlock =>
                by_cases leftTyped : leftBlock.inputTy = block.inputTy
                · by_cases rightTyped : rightBlock.inputTy = block.inputTy
                  · simp [termFailure?, termEq, leftEq, rightEq,
                      leftTyped, rightTyped] at failure
                  · simp [termFailure?, termEq, leftEq, rightEq,
                      leftTyped, rightTyped] at failure
                    subst payload
                    exact .chooseRightTypeMismatch termEq leftEq rightEq
                      leftTyped rightTyped
                · simp [termFailure?, termEq, leftEq, rightEq,
                    leftTyped] at failure
                  subst payload
                  exact .chooseLeftTypeMismatch termEq leftEq rightEq leftTyped
  · intro valid
    cases valid with
    | retTypeMismatch term mismatch =>
        simp [termFailure?, term, mismatch]
    | jumpMissing term missing =>
        simp [termFailure?, term, missing]
    | jumpTypeMismatch term found mismatch =>
        simp [termFailure?, term, found, mismatch]
    | performUnknownOperation term unknown =>
        simp [termFailure?, term, unknown]
    | performMissingTarget term known missing =>
        simp [termFailure?, term, known, missing]
    | performRequestTypeMismatch term known found mismatch =>
        simp [termFailure?, term, known, found, mismatch]
    | performAnswerTypeMismatch term known found request mismatch =>
        simp [termFailure?, term, known, found, request, mismatch]
    | chooseMissingLeft term missing =>
        simp [termFailure?, term, missing]
    | chooseMissingRight term leftFound missing =>
        simp [termFailure?, term, leftFound, missing]
    | chooseLeftTypeMismatch term leftFound rightFound mismatch =>
        simp [termFailure?, term, leftFound, rightFound, mismatch]
    | chooseRightTypeMismatch term leftFound rightFound leftTyped mismatch =>
        simp [termFailure?, term, leftFound, rightFound, leftTyped, mismatch]

private theorem termFailure?_eq_none_iff [DecidableEq Ty]
    (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty)
    (block : RawBlock Ty) :
    termFailure? alphabet raw block = none ↔
      localTermWF alphabet raw block := by
  cases termEq : block.term with
  | ret => simp [termFailure?, localTermWF, termEq]
  | jump target =>
      cases targetEq : lookupBlock raw target <;>
        simp [termFailure?, localTermWF, termEq, targetEq]
  | perform operation target =>
      cases operationEq : alphabet.lookup operation with
      | none =>
          cases targetEq : lookupBlock raw target <;>
            simp [termFailure?, localTermWF, termEq, operationEq, targetEq]
      | some operationDef =>
          cases targetEq : lookupBlock raw target with
          | none =>
              simp [termFailure?, localTermWF, termEq, operationEq, targetEq]
          | some targetBlock =>
              by_cases requestTyped :
                  block.inputTy = alphabet.requestTy operationDef
              <;> by_cases answerTyped :
                  targetBlock.inputTy = alphabet.answerTy operationDef
              <;> simp [termFailure?, localTermWF, termEq, operationEq,
                targetEq, requestTyped, answerTyped]
  | choose decision left right =>
      cases leftEq : lookupBlock raw left with
      | none =>
          cases rightEq : lookupBlock raw right <;>
            simp [termFailure?, localTermWF, termEq, leftEq, rightEq]
      | some leftBlock =>
          cases rightEq : lookupBlock raw right with
          | none =>
              simp [termFailure?, localTermWF, termEq, leftEq, rightEq]
          | some rightBlock =>
              by_cases leftTyped : leftBlock.inputTy = block.inputTy
              <;> by_cases rightTyped : rightBlock.inputTy = block.inputTy
              <;> simp [termFailure?, localTermWF, termEq, leftEq, rightEq,
                leftTyped, rightTyped]

private structure PreciseFailure (alphabet : FlowAlphabet Ty)
    (raw : RawFlow Ty) (clause : AdmissionClause) where
  site : CheckSite
  payload : DiagnosticPayload Ty
  valid : Diagnostic.Valid alphabet raw ⟨clause, site, payload⟩

private def preciseFailure [DecidableEq Ty]
    (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty)
    (clause : AdmissionClause)
    (refute : ¬ ClauseHolds alphabet raw clause) :
    PreciseFailure alphabet raw clause := by
  cases clause with
  | alphabetMismatch =>
      refine ⟨.flow, .alphabet alphabet.id raw.alphabet,
        .alphabetMismatch ?_⟩
      exact refute
  | duplicateBlockId =>
      cases found : firstFailure? raw.blocks (duplicateBlockFailure? raw) with
      | none =>
          have clear := firstFailure?_eq_none_iff.mp found
          have noDuplicates : (raw.blocks.map RawBlock.id).Nodup := by
            apply map_nodup_of_no_prefix_duplicate raw.blocks RawBlock.id
            intro index block blockAt
            have checked := clear index block blockAt
            intro duplicate
            have mappedDuplicate :
                block.id ∈ (raw.blocks.map RawBlock.id).take index := by
              simpa using duplicate
            simp [duplicateBlockFailure?, mappedDuplicate] at checked
          exact (refute noDuplicates).elim
      | some result =>
          rcases result with ⟨index, block, reported⟩
          have first := firstFailure?_eq_some_valid
            (duplicateBlockFailure?_eq_some_iff raw) found
          have reportedEq : reported = block.id := first.fails_at.1
          subst reported
          exact ⟨.block index, .block block.id, .duplicateBlockId first⟩
  | duplicateDecisionId =>
      cases found : firstFailure? raw.blocks (duplicateDecisionFailure? raw) with
      | none =>
          have clear := firstFailure?_eq_none_iff.mp found
          have noDuplicates : (localDecisionIds raw).Nodup := by
            unfold localDecisionIds
            apply filterMap_nodup_of_no_prefix_duplicate
            intro index block blockAt decision selected duplicate
            have checked := clear index block blockAt
            cases termEq : block.term with
            | ret | jump | perform => simp [termEq] at selected
            | choose actual left right =>
                simp [termEq] at selected
                subst decision
                simp [duplicateDecisionFailure?, termEq, duplicate] at checked
          exact (refute noDuplicates).elim
      | some result =>
          rcases result with ⟨index, block, decision⟩
          have first := firstFailure?_eq_some_valid
            (duplicateDecisionFailure?_eq_some_iff raw) found
          exact ⟨.decision block.id, .decision decision,
            .duplicateDecisionId first⟩
  | nonCanonicalBlockOrder =>
      cases found : firstFailure? raw.blocks
          (orderFailure? raw.blocks
            (fun block : RawBlock Ty => block.id.value)) with
      | none =>
          have clear := firstFailure?_eq_none_iff.mp found
          have ordered : raw.blocks.Pairwise
              (fun left right => left.id.value < right.id.value) := by
            apply pairwise_nat_of_adjacent raw.blocks
              (fun block : RawBlock Ty => block.id.value)
            intro index block previous positive blockAt previousAt
            have checked := clear index block blockAt
            by_cases ordered : previous.id.value < block.id.value
            · exact ordered
            · have failed := (orderFailure?_eq_some_iff raw.blocks
                (fun candidate : RawBlock Ty => candidate.id.value)
                index block block).mpr
                  ⟨rfl, positive, ⟨previous, previousAt, ordered⟩⟩
              rw [checked] at failed
              contradiction
          exact (refute ordered).elim
      | some result =>
          rcases result with ⟨index, block, reported⟩
          have first := firstFailure?_eq_some_valid
            (orderFailure?_eq_some_iff raw.blocks
              (fun candidate : RawBlock Ty => candidate.id.value)) found
          have reportedEq : reported = block := first.fails_at.1
          subst reported
          have converted : FirstFailureAt raw.blocks
              (fun candidateIndex candidate (reported : BlockId) =>
                reported = candidate.id ∧
                0 < candidateIndex ∧
                ∃ previous,
                  raw.blocks[candidateIndex - 1]? = some previous ∧
                  ¬ previous.id.value < candidate.id.value)
              index block block.id := by
            refine ⟨first.source_at, ?_, ?_⟩
            · exact ⟨rfl, first.fails_at.2⟩
            · intro priorIndex priorBlock priorLt priorAt priorFailure failed
              exact first.prior_clear priorIndex priorBlock priorLt priorAt
                priorBlock ⟨rfl, failed.2⟩
          exact ⟨.block index, .block block.id,
            .nonCanonicalBlockOrder converted⟩
  | emptyRoots =>
      by_cases empty : raw.roots = []
      · exact ⟨.flow, .none, .emptyRoots empty⟩
      · exact (refute empty).elim
  | duplicateRoot =>
      cases found : firstFailure? raw.roots (duplicateRootFailure? raw) with
      | none =>
          have clear := firstFailure?_eq_none_iff.mp found
          have noDuplicates : raw.roots.Nodup := by
            apply nodup_of_no_prefix_duplicate raw.roots
            intro index root rootAt duplicate
            have checked := clear index root rootAt
            simp [duplicateRootFailure?, duplicate] at checked
          exact (refute noDuplicates).elim
      | some result =>
          rcases result with ⟨index, root, reported⟩
          have first := firstFailure?_eq_some_valid
            (duplicateRootFailure?_eq_some_iff raw) found
          have reportedEq : reported = root := first.fails_at.1
          subst reported
          exact ⟨.root index, .block root, .duplicateRoot first⟩
  | nonCanonicalRootOrder =>
      cases found : firstFailure? raw.roots
          (orderFailure? raw.roots BlockId.value) with
      | none =>
          have clear := firstFailure?_eq_none_iff.mp found
          have ordered : raw.roots.Pairwise
              (fun left right => left.value < right.value) := by
            apply pairwise_nat_of_adjacent raw.roots BlockId.value
            intro index root previous positive rootAt previousAt
            have checked := clear index root rootAt
            by_cases ordered : previous.value < root.value
            · exact ordered
            · have failed := (orderFailure?_eq_some_iff raw.roots
                BlockId.value index root root).mpr
                  ⟨rfl, positive, ⟨previous, previousAt, ordered⟩⟩
              rw [checked] at failed
              contradiction
          exact (refute ordered).elim
      | some result =>
          rcases result with ⟨index, root, reported⟩
          have first := firstFailure?_eq_some_valid
            (orderFailure?_eq_some_iff raw.roots BlockId.value) found
          have reportedEq : reported = root := first.fails_at.1
          subst reported
          exact ⟨.root index, .block root,
            .nonCanonicalRootOrder first⟩
  | entryNotRoot =>
      exact ⟨.entry, .block raw.entry, .entryNotRoot refute⟩
  | danglingRoot =>
      cases found : firstFailure? raw.roots (danglingRootFailure? raw) with
      | none =>
          have clear := firstFailure?_eq_none_iff.mp found
          have allResolve : ∀ root, root ∈ raw.roots →
              (lookupBlock raw root).isSome = true := by
            intro root rootMem
            obtain ⟨index, rootAt⟩ := List.mem_iff_getElem?.mp rootMem
            have checked := clear index root rootAt
            cases lookupEq : lookupBlock raw root with
            | none => simp [danglingRootFailure?, lookupEq] at checked
            | some block => rfl
          exact (refute allResolve).elim
      | some result =>
          rcases result with ⟨index, root, reported⟩
          have first := firstFailure?_eq_some_valid
            (danglingRootFailure?_eq_some_iff raw) found
          have reportedEq : reported = root := first.fails_at.1
          subst reported
          exact ⟨.root index, .block root, .danglingRoot first⟩
  | danglingSuccessor =>
      cases found : firstFailure? raw.blocks (danglingBlockFailure? raw) with
      | none =>
          have clear := firstFailure?_eq_none_iff.mp found
          have allResolve : ReferencesWF raw := by
            intro block blockMem target targetMem
            obtain ⟨blockIndex, blockAt⟩ :=
              List.mem_iff_getElem?.mp blockMem
            have blockClear := clear blockIndex block blockAt
            unfold danglingBlockFailure? at blockClear
            cases innerEq : firstPreciseDanglingSuccessorIn? raw block with
            | some result => simp [innerEq] at blockClear
            | none =>
                have innerClear := firstFailure?_eq_none_iff.mp innerEq
                obtain ⟨targetIndex, targetAt⟩ :=
                  List.mem_iff_getElem?.mp targetMem
                have targetClear := innerClear targetIndex target targetAt
                cases lookupEq : lookupBlock raw target with
                | none =>
                    simp [danglingSuccessorFailure?, lookupEq] at targetClear
                | some targetBlock => rfl
          exact (refute allResolve).elim
      | some result =>
          rcases result with ⟨blockIndex, block, witness⟩
          have first := firstFailure?_eq_some_valid
            (danglingBlockFailure?_eq_some_iff raw) found
          exact ⟨.successor block.id witness.1, .block witness.2,
            .danglingSuccessor first⟩
  | unknownOperation =>
      cases found : firstFailure? raw.blocks
          (unknownOperationFailure? alphabet) with
      | none =>
          have clear := firstFailure?_eq_none_iff.mp found
          have allKnown : ∀ block, block ∈ raw.blocks →
              localOperationWF alphabet block := by
            intro block blockMem
            obtain ⟨index, blockAt⟩ := List.mem_iff_getElem?.mp blockMem
            have checked := clear index block blockAt
            cases termEq : block.term with
            | ret | jump | choose => simp [localOperationWF, termEq]
            | perform operation target =>
                cases operationEq : alphabet.lookup operation with
                | none =>
                    simp [unknownOperationFailure?, termEq, operationEq]
                      at checked
                | some operationDef =>
                    simp [localOperationWF, termEq, operationEq]
          exact (refute allKnown).elim
      | some result =>
          rcases result with ⟨index, block, operation⟩
          have first := firstFailure?_eq_some_valid
            (unknownOperationFailure?_eq_some_iff alphabet) found
          exact ⟨.operation block.id, .operation operation,
            .unknownOperation first⟩
  | entryTypeMismatch =>
      cases entryEq : lookupBlock raw raw.entry with
      | none =>
          exact ⟨.entry, .block raw.entry, .entryMissing entryEq⟩
      | some block =>
          have mismatch : block.inputTy ≠ raw.inputTy := by
            intro typed
            apply refute
            simp [ClauseHolds, EntryWF, entryEq, typed]
          exact ⟨.entry, .typeMismatch raw.inputTy block.inputTy,
            .entryTypeMismatch entryEq mismatch⟩
  | termTypeMismatch =>
      cases found : firstFailure? raw.blocks
          (fun _ block => termFailure? alphabet raw block) with
      | none =>
          have clear := firstFailure?_eq_none_iff.mp found
          have allTyped : ∀ block, block ∈ raw.blocks →
              localTermWF alphabet raw block := by
            intro block blockMem
            obtain ⟨index, blockAt⟩ := List.mem_iff_getElem?.mp blockMem
            exact (termFailure?_eq_none_iff alphabet raw block).mp
              (clear index block blockAt)
          exact (refute allTyped).elim
      | some result =>
          rcases result with ⟨index, block, payload⟩
          have first := firstFailure?_eq_some_valid
            (fun _ candidate failure =>
              termFailure?_eq_some_iff alphabet raw candidate failure) found
          exact ⟨.term block.id, payload, .termTypeMismatch first⟩

/-- A clause-indexed result makes an unrelated diagnostic unrepresentable. -/
private inductive ClauseResult (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty)
    (clause : AdmissionClause) (holds : Prop) where
  | pass (proof : holds)
  | fail (site : CheckSite) (payload : DiagnosticPayload Ty)
      (valid : Diagnostic.Valid alphabet raw ⟨clause, site, payload⟩)
      (refute : ¬ holds)

private def ClauseResult.diagnostic?
    {Ty : Type uTy} {alphabet : FlowAlphabet Ty} {raw : RawFlow Ty}
    {clause : AdmissionClause} {holds : Prop} :
    ClauseResult alphabet raw clause holds → Option (Diagnostic Ty)
  | .pass _ => none
  | .fail site payload _ _ => some ⟨clause, site, payload⟩

private def checkClause [DecidableEq Ty]
    (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty)
    (clause : AdmissionClause) :
    ClauseResult alphabet raw clause (ClauseHolds alphabet raw clause) :=
  letI := clauseHoldsDecidable alphabet raw clause
  if holds : ClauseHolds alphabet raw clause then
    .pass holds
  else
    let failure := preciseFailure alphabet raw clause holds
    .fail failure.site failure.payload failure.valid holds

/-- Diagnose exactly one clause, independently of the global scan order. -/
def diagnoseAt [DecidableEq Ty]
    (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty)
    (clause : AdmissionClause) : Option (Diagnostic Ty) :=
  (checkClause alphabet raw clause).diagnostic?

/-- Every reported clause-local diagnostic carries its exact source witness. -/
theorem diagnoseAt_some_valid [DecidableEq Ty]
    {alphabet : FlowAlphabet Ty} {raw : RawFlow Ty}
    {clause : AdmissionClause} {diagnostic : Diagnostic Ty}
    (found : diagnoseAt alphabet raw clause = some diagnostic) :
    Diagnostic.Valid alphabet raw diagnostic := by
  unfold diagnoseAt at found
  generalize resultEq : checkClause alphabet raw clause = result at found
  cases result with
  | pass proof => simp [ClauseResult.diagnostic?] at found
  | fail site payload valid refute =>
      simp [ClauseResult.diagnostic?] at found
      cases found
      exact valid

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
  | fail site payload valid refute =>
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

namespace FirstDiagnostic

/-- A globally first diagnostic retains the exact witness from its clause. -/
theorem valid [DecidableEq Ty]
    {alphabet : FlowAlphabet Ty} {raw : RawFlow Ty}
    {diagnostic : Diagnostic Ty}
    (first : FirstDiagnostic alphabet raw diagnostic) :
    Diagnostic.Valid alphabet raw diagnostic :=
  diagnoseAt_some_valid first.condemns

end FirstDiagnostic

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

/-- Check every clause in the fixed order and seal the raw graph on success. -/
def admit [DecidableEq Ty]
    (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty) :
    Except (Diagnostic Ty) (CheckedFlow alphabet) :=
  match found : firstDiagnostic? alphabet raw with
  | none =>
      .ok <| CheckedFlow.mk raw <|
        Diagnostic.clause_all_complete.mpr <|
          firstDiagnostic?_eq_none_iff.mp found
  | some diagnostic => .error diagnostic

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
  unfold admit
  split
  · congr 2
  · rename_i diagnostic impossible
    rw [found] at impossible
    contradiction

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
    simp [notClear]

/-- Every observable admission error carries its exact first source witness. -/
theorem admit_error_valid [DecidableEq Ty]
    {alphabet : FlowAlphabet Ty} {raw : RawFlow Ty}
    {diagnostic : Diagnostic Ty}
    (errored : admit alphabet raw = .error diagnostic) :
    Diagnostic.Valid alphabet raw diagnostic :=
  (error_iff_firstDiagnostic.mp errored).valid

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
  unfold admit
  split
  · congr 2
  · rename_i diagnostic impossible
    rw [found] at impossible
    contradiction

end Effect4
