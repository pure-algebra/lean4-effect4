import Effect4.Flow.Block

/-!
# Raw first-order flows

Raw flows retain graph identity, sharing, cycles, and unreachable declarations.
The seven well-formedness clauses below check the entire declared document;
none adds acyclicity or reachability coverage.
-/

namespace Effect4

/-- Unchecked, canonicalizable first-order effect-flow input. -/
structure RawFlow (Ty : Type uTy) where
  alphabet : AlphabetId
  roots : List BlockId
  entry : BlockId
  inputTy : Ty
  resultTy : Ty
  blocks : List (RawBlock Ty)
deriving DecidableEq, Repr

/-- Resolve the first declared block with the requested nominal identity. -/
def lookupBlock (raw : RawFlow Ty) (id : BlockId) : Option (RawBlock Ty) :=
  raw.blocks.find? fun block => block.id = id

/-- A declared block directly names `target` as one of its successors. -/
def Edge (raw : RawFlow Ty) (source target : BlockId) : Prop :=
  ∃ block, block ∈ raw.blocks ∧ block.id = source ∧
    target ∈ block.term.successors

/-- Reflexive-transitive reachability through declared successor edges. -/
inductive ReachableFrom (raw : RawFlow Ty) : BlockId → BlockId → Prop where
  | refl (source : BlockId) : ReachableFrom raw source source
  | step {source middle target : BlockId} :
      ReachableFrom raw source middle →
      Edge raw middle target →
      ReachableFrom raw source target

/-- Reachability from any declared root. -/
def Reachable (raw : RawFlow Ty) (target : BlockId) : Prop :=
  ∃ root, root ∈ raw.roots ∧ ReachableFrom raw root target

/-- Reachability from the distinguished entry block. -/
def EntryReachable (raw : RawFlow Ty) (target : BlockId) : Prop :=
  ReachableFrom raw raw.entry target

/-- The raw document names the supplied closed alphabet. -/
def AlphabetWF (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty) : Prop :=
  raw.alphabet = alphabet.id

private def decisionIds (raw : RawFlow Ty) : List DecisionId :=
  raw.blocks.filterMap fun block =>
    match block.term with
    | .choose decision _ _ => some decision
    | _ => none

/--
Block identities are unique and strictly ascending, and decision identities
are globally unique across all declared blocks, reachable or otherwise.
-/
def IdsWF (raw : RawFlow Ty) : Prop :=
  (raw.blocks.map RawBlock.id).Nodup ∧
  raw.blocks.Pairwise
    (fun left right => left.id.value < right.id.value) ∧
  (decisionIds raw).Nodup

/--
Roots form a nonempty, unique, strictly ascending table containing the entry,
and every root resolves in the declared block table.
-/
def RootsWF (raw : RawFlow Ty) : Prop :=
  raw.roots ≠ [] ∧
  raw.roots.Nodup ∧
  raw.roots.Pairwise (fun left right => left.value < right.value) ∧
  raw.entry ∈ raw.roots ∧
  ∀ root, root ∈ raw.roots → (lookupBlock raw root).isSome = true

/-- Every successor in every declared block resolves, including unreachable blocks. -/
def ReferencesWF (raw : RawFlow Ty) : Prop :=
  ∀ block, block ∈ raw.blocks →
    ∀ target, target ∈ block.term.successors →
      (lookupBlock raw target).isSome = true

/-- Every performed operation in every declared block belongs to the alphabet. -/
def OperationsWF (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty) : Prop :=
  ∀ block, block ∈ raw.blocks →
    match block.term with
    | .perform operation _ => (alphabet.lookup operation).isSome = true
    | _ => True

/-- The distinguished entry resolves and accepts the document input type. -/
def EntryWF (raw : RawFlow Ty) : Prop :=
  match lookupBlock raw raw.entry with
  | none => False
  | some block => block.inputTy = raw.inputTy

private def TermWF
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

/-- Every declared block satisfies its local ANF input/output type equations. -/
def TermsWF (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty) : Prop :=
  ∀ block, block ∈ raw.blocks → TermWF alphabet raw block

/-- Exactly the seven independent admission clauses for a raw flow. -/
structure FlowWF (alphabetDef : FlowAlphabet Ty) (raw : RawFlow Ty) : Prop where
  alphabet : AlphabetWF alphabetDef raw
  ids : IdsWF raw
  roots : RootsWF raw
  references : ReferencesWF raw
  operations : OperationsWF alphabetDef raw
  entry : EntryWF raw
  terms : TermsWF alphabetDef raw

private theorem exists_eq_some_of_isSome
    {value : Option α} (isSome : value.isSome = true) :
    ∃ item, value = some item := by
  cases value with
  | none => cases isSome
  | some item => exact ⟨item, rfl⟩

namespace FlowWF

/-- Every block reachable from a root resolves in the declared block table. -/
theorem reachable_declared
    {alphabet : FlowAlphabet Ty} {raw : RawFlow Ty}
    (wf : FlowWF alphabet raw) {target : BlockId} :
    Reachable raw target → ∃ block, lookupBlock raw target = some block := by
  rintro ⟨root, rootMem, path⟩
  have rootIsSome : (lookupBlock raw root).isSome = true :=
    wf.roots.2.2.2.2 root rootMem
  have rootDeclared : ∃ block, lookupBlock raw root = some block :=
    exists_eq_some_of_isSome rootIsSome
  induction path with
  | refl => exact rootDeclared
  | step _ edge _ =>
      rcases edge with ⟨block, blockMem, _, targetMem⟩
      exact exists_eq_some_of_isSome
        (wf.references block blockMem _ targetMem)

end FlowWF

end Effect4
