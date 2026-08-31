import Std

/-!
# Effect Core v1 representation workshop

This ignored, pre-grade file exercises only the first representation slice of
the frozen effect-core-v1 packet.  It is intentionally self-contained and is
not a public declaration freeze.
-/

namespace EffectCoreProbe

/-! ## Closed identifiers and type/row carriers -/

structure BlockId where
  value : Nat
  deriving DecidableEq, BEq, Repr

structure OpId where
  value : Nat
  deriving DecidableEq, BEq, Repr

structure ErrorId where
  value : Nat
  deriving DecidableEq, BEq, Repr

structure ServiceId where
  value : Nat
  deriving DecidableEq, BEq, Repr

inductive ValueTy where
  | unit
  | bool
  | nat
  | text
  | product (left right : ValueTy)
  | sum (left right : ValueTy)
  deriving DecidableEq, BEq, Repr

def Value : ValueTy → Type
  | .unit => PUnit
  | .bool => Bool
  | .nat => Nat
  | .text => String
  | .product left right => Value left × Value right
  | .sum left right => Sum (Value left) (Value right)

structure ErrorAlternative where
  tag : ErrorId
  payload : ValueTy
  deriving DecidableEq, BEq, Repr

structure Requirement where
  service : ServiceId
  deriving DecidableEq, BEq, Repr

abbrev ErrorRow := List ErrorAlternative
abbrev RequirementRow := List Requirement

structure AER where
  result : ValueTy
  errors : ErrorRow
  requirements : RequirementRow
  deriving DecidableEq, BEq, Repr

structure OpDesc where
  id : OpId
  request : ValueTy
  answer : ValueTy
  errors : ErrorRow
  requirements : RequirementRow
  deriving DecidableEq, BEq, Repr

/-- Identity of the independently generated public-surface ledger.  It is not
the authored operation alphabet and cannot be substituted for that table. -/
structure PublicSurfaceId where
  packageName : String
  packageVersion : String
  mappingSchemaVersion : Nat
  ledgerDigest : String
  deriving DecidableEq, BEq, Repr

/-! ## Pure expressions are not effect terms -/

inductive PureExpr : ValueTy → Type where
  | unit : PureExpr .unit
  | bool (value : Bool) : PureExpr .bool
  | nat (value : Nat) : PureExpr .nat
  | text (value : String) : PureExpr .text
  | pair (left : PureExpr a) (right : PureExpr b) :
      PureExpr (.product a b)
  | first (pair : PureExpr (.product a b)) : PureExpr a
  | second (pair : PureExpr (.product a b)) : PureExpr b
  | ifThenElse (guard : PureExpr .bool)
      (ifTrue ifFalse : PureExpr ty) : PureExpr ty

def PureExpr.eval : PureExpr ty → Value ty
  | .unit => PUnit.unit
  | .bool value => value
  | .nat value => value
  | .text value => value
  | .pair left right => (left.eval, right.eval)
  | .first value => value.eval.1
  | .second value => value.eval.2
  | .ifThenElse guard ifTrue ifFalse =>
      match guard.eval with
      | true => ifTrue.eval
      | false => ifFalse.eval

/-! ## Raw graph, decidable admission, and checked carrier -/

inductive RawTerm where
  | close {ty : ValueTy} (result : PureExpr ty)
  | jump (target : BlockId)
  | perform (op : OpId) (onAnswer : BlockId)
  | choose (guard : PureExpr .bool) (ifTrue ifFalse : BlockId)

def RawTerm.successors : RawTerm → List BlockId
  | .close _ => []
  | .jump target => [target]
  | .perform _ onAnswer => [onAnswer]
  | .choose _ ifTrue ifFalse => [ifTrue, ifFalse]

def RawTerm.operation : RawTerm → Option OpId
  | .perform op _ => some op
  | _ => none

def RawTerm.closedType : RawTerm → Option ValueTy
  | .close (ty := ty) _ => some ty
  | _ => none

structure RawBlock where
  id : BlockId
  term : RawTerm

structure RawProgram where
  publicSurface : PublicSurfaceId
  declaredAER : AER
  alphabet : List OpDesc
  blocks : List RawBlock
  entry : BlockId

def RawProgram.blockIds (raw : RawProgram) : List BlockId :=
  raw.blocks.map (·.id)

def RawProgram.opIds (raw : RawProgram) : List OpId :=
  raw.alphabet.map (·.id)

def RawProgram.idsOK (raw : RawProgram) : Bool :=
  decide (raw.blockIds.Nodup ∧ raw.opIds.Nodup)

def RawProgram.entryOK (raw : RawProgram) : Bool :=
  raw.blockIds.contains raw.entry

def RawProgram.edgesOK (raw : RawProgram) : Bool :=
  raw.blocks.all fun block =>
    block.term.successors.all fun successor => raw.blockIds.contains successor

def RawProgram.operationsOK (raw : RawProgram) : Bool :=
  raw.blocks.all fun block =>
    match block.term.operation with
    | none => true
    | some op => raw.opIds.contains op

def RawProgram.typesOK (raw : RawProgram) : Bool :=
  raw.blocks.all fun block =>
    match block.term.closedType with
    | none => true
    | some ty => ty == raw.declaredAER.result

def RawProgram.rowsOK (raw : RawProgram) : Bool :=
  decide (
    (raw.declaredAER.errors.map (·.tag)).Nodup ∧
    (raw.declaredAER.requirements.map (·.service)).Nodup ∧
    ∀ op ∈ raw.alphabet,
      (op.errors.map (·.tag)).Nodup ∧
      (op.requirements.map (·.service)).Nodup)

def RawProgram.wfBool (raw : RawProgram) : Bool :=
  raw.idsOK && raw.entryOK && raw.edgesOK && raw.operationsOK &&
    raw.typesOK && raw.rowsOK

def ProgramWF (raw : RawProgram) : Prop := raw.wfBool = true

instance (raw : RawProgram) : Decidable (ProgramWF raw) := by
  unfold ProgramWF
  infer_instance

inductive Diagnostic where
  | duplicateId
  | danglingEntry
  | danglingSuccessor
  | danglingOperation
  | closeTypeMismatch
  | nonCanonicalRow
  deriving DecidableEq, Repr

structure Diagnostics where
  head : Diagnostic
  tail : List Diagnostic
  deriving Repr

def RawProgram.firstDiagnostic (raw : RawProgram) : Diagnostic :=
  if !raw.idsOK then .duplicateId
  else if !raw.entryOK then .danglingEntry
  else if !raw.edgesOK then .danglingSuccessor
  else if !raw.operationsOK then .danglingOperation
  else if !raw.typesOK then .closeTypeMismatch
  else .nonCanonicalRow

structure CheckedProgram (aer : AER) where
  raw : RawProgram
  aer_eq : raw.declaredAER = aer
  wf : ProgramWF raw

abbrev SomeChecked := Sigma CheckedProgram

def check (raw : RawProgram) : Except Diagnostics SomeChecked :=
  if h : ProgramWF raw then
    .ok ⟨raw.declaredAER, ⟨raw, rfl, h⟩⟩
  else
    .error ⟨raw.firstDiagnostic, []⟩

theorem check_sound {raw : RawProgram} {checked : SomeChecked}
    (accepted : check raw = .ok checked) : ProgramWF raw := by
  unfold check at accepted
  split at accepted
  · assumption
  · cases accepted

/-! ## A small may/must footprint algebra -/

abbrev OpSet := OpId → Bool

namespace OpSet

def empty : OpSet := fun _ => false

def union (left right : OpSet) : OpSet := fun op => left op || right op

def intersection (left right : OpSet) : OpSet := fun op => left op && right op

theorem union_assoc (left middle right : OpSet) :
    union (union left middle) right = union left (union middle right) := by
  funext op
  simp only [union]
  cases left op <;> cases middle op <;> cases right op <;> rfl

end OpSet

structure FlowSummary where
  may : OpSet
  must : OpSet
  mustNormalExit : Bool

def FlowSummary.empty : FlowSummary where
  may := OpSet.empty
  must := OpSet.empty
  mustNormalExit := true

/-- The right must-set contributes only when the left must reach normal exit. -/
def FlowSummary.seq (left right : FlowSummary) : FlowSummary where
  may := OpSet.union left.may right.may
  must := if left.mustNormalExit then OpSet.union left.must right.must else left.must
  mustNormalExit := left.mustNormalExit && right.mustNormalExit

/-- An undecided branch may take either arm and must take only their overlap. -/
def FlowSummary.choice (ifTrue ifFalse : FlowSummary) : FlowSummary where
  may := OpSet.union ifTrue.may ifFalse.may
  must := OpSet.intersection ifTrue.must ifFalse.must
  mustNormalExit := ifTrue.mustNormalExit && ifFalse.mustNormalExit

def PureExpr.flowSummary (_ : PureExpr ty) : FlowSummary :=
  FlowSummary.empty

theorem pure_closure_empty_effect_footprint (expr : PureExpr ty) :
    expr.flowSummary.may = OpSet.empty ∧
      expr.flowSummary.must = OpSet.empty := by
  exact ⟨rfl, rfl⟩

theorem sequential_summary_associative (left middle right : FlowSummary) :
    FlowSummary.seq (FlowSummary.seq left middle) right =
      FlowSummary.seq left (FlowSummary.seq middle right) := by
  cases left with
  | mk leftMay leftMust leftNormal =>
    cases middle with
    | mk middleMay middleMust middleNormal =>
      cases right with
      | mk rightMay rightMust rightNormal =>
        cases leftNormal <;> cases middleNormal <;>
          simp [FlowSummary.seq, OpSet.union_assoc]

theorem choice_may_union_must_intersection (ifTrue ifFalse : FlowSummary) :
    (FlowSummary.choice ifTrue ifFalse).may =
        OpSet.union ifTrue.may ifFalse.may ∧
    (FlowSummary.choice ifTrue ifFalse).must =
        OpSet.intersection ifTrue.must ifFalse.must := by
  exact ⟨rfl, rfl⟩

/-! ## Total seven-way surface disposition -/

inductive Disposition where
  | reifiedPrimitive
  | derivedExpansion
  | separateSubcalculus
  | pureOrHostOnlyClosedOutsideProg
  | projectOwnedReplacementOrForeignOp
  | targetOnly
  | excludedInternal
  deriving DecidableEq, Repr

inductive SurfaceRole where
  | primitiveOperation
  | derivedCombinator
  | separateEffectLanguage
  | pureOrHostOnly
  | foreignBoundary
  | targetRunner
  | packageInternal
  deriving DecidableEq, Repr

def classifyDisposition : SurfaceRole → Disposition
  | .primitiveOperation => .reifiedPrimitive
  | .derivedCombinator => .derivedExpansion
  | .separateEffectLanguage => .separateSubcalculus
  | .pureOrHostOnly => .pureOrHostOnlyClosedOutsideProg
  | .foreignBoundary => .projectOwnedReplacementOrForeignOp
  | .targetRunner => .targetOnly
  | .packageInternal => .excludedInternal

theorem total_disposition_classification (role : SurfaceRole) :
    ∃ disposition,
      classifyDisposition role = disposition ∧
      ∀ other, classifyDisposition role = other → other = disposition := by
  exact ⟨classifyDisposition role, rfl, fun _ found => found.symm⟩

/-! ## Executable examples -/

def emptyAER : AER := ⟨.nat, [], []⟩

def readOp : OpDesc :=
  ⟨⟨0⟩, .unit, .nat, [], []⟩

def goodProgram : RawProgram where
  publicSurface := ⟨"effect", "4.0.0-rc.112", 1, "workshop-only"⟩
  declaredAER := emptyAER
  alphabet := [readOp]
  blocks := [
    ⟨⟨0⟩, .perform readOp.id ⟨1⟩⟩,
    ⟨⟨1⟩, .close (.nat 7)⟩
  ]
  entry := ⟨0⟩

def danglingProgram : RawProgram where
  publicSurface := ⟨"effect", "4.0.0-rc.112", 1, "workshop-only"⟩
  declaredAER := emptyAER
  alphabet := []
  blocks := [⟨⟨0⟩, .jump ⟨99⟩⟩]
  entry := ⟨0⟩

#guard goodProgram.wfBool
#guard !danglingProgram.wfBool

#print axioms check_sound
#print axioms pure_closure_empty_effect_footprint
#print axioms sequential_summary_associative
#print axioms choice_may_union_must_intersection
#print axioms total_disposition_classification

end EffectCoreProbe
