import Std

/-!
# Cause and Exit counterexamples

This file is a self-contained breaker model. It deliberately does not import
`Effect4.Semantics.Cause` or `Effect4.Semantics.Exit`: the witnesses must remain
executable while the production surface is still absent, and they must keep
proving the attack after the repaired declarations land.

Each theorem is finite and proves only the named attack. None of them is a
production law; the frozen laws live in
`test/contracts/cause-exit.contract.md`.
-/

set_option autoImplicit false

namespace Test.Counterexamples.Semantics.CauseExit

/-! ## The shared miniature alphabets -/

/-- A miniature annotation map: ordered key/value entries, no invariant. -/
structure MiniAnnotations where
  entries : List (String × Nat)
  deriving DecidableEq, Repr

/-- The three-tag reason alphabet, with payload and annotations. -/
inductive MiniReason
  | fail (error : Nat) (annotations : MiniAnnotations)
  | die (defect : Nat) (annotations : MiniAnnotations)
  | interrupt (interruptor : Option Nat) (annotations : MiniAnnotations)
  deriving DecidableEq, Repr

/-- The flat cause of the pinned runtime is exactly an ordered reason list. -/
abbrev MiniCause := List MiniReason

def noAnnotations : MiniAnnotations := { entries := [] }

def failOne : MiniReason := .fail 1 noAnnotations
def failTwo : MiniReason := .fail 2 noAnnotations
def dieOne : MiniReason := .die 1 noAnnotations
def interruptNone : MiniReason := .interrupt none noAnnotations

/-! ## E4-SEM-CE-001 — a tree-shaped cause invents structure -/

/-- A rejected richer carrier with sequential and parallel composition. -/
inductive MiniTree
  | empty
  | leaf (reason : MiniReason)
  | sequential (left right : MiniTree)
  | parallel (left right : MiniTree)
  deriving DecidableEq, Repr

/-- The only observation rc.112 exposes is the ordered reason list. -/
def MiniTree.flatten : MiniTree -> MiniCause
  | empty => []
  | leaf reason => [reason]
  | sequential left right => left.flatten ++ right.flatten
  | parallel left right => left.flatten ++ right.flatten

/-- E4-SEM-CE-001: a tree carrier distinguishes causes the pinned runtime
identifies, so the sequential/parallel node is unobservable structure. -/
theorem tree_invents_structure :
    exists left right : MiniTree,
      left ≠ right /\ left.flatten = right.flatten := by
  refine ⟨MiniTree.sequential (.leaf failOne) (.leaf failTwo),
    MiniTree.parallel (.leaf failOne) (.leaf failTwo), ?_, ?_⟩
  · decide
  · decide

/-- E4-SEM-CE-001: the tree carrier also has more than one spelling of the
empty cause, which the flat list does not. -/
theorem tree_empty_not_unique :
    exists left right : MiniTree,
      left ≠ right /\ left.flatten = [] /\ right.flatten = [] := by
  refine ⟨MiniTree.empty, MiniTree.sequential .empty .empty, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide

/-! ## E4-SEM-CE-002 — append is not `Arr.union` -/

/-- Membership test that reduces in the kernel. -/
def containsReason (list : MiniCause) (reason : MiniReason) : Bool :=
  list.any (fun other => decide (other = reason))

/-- The pinned `Arr.union` shape: `self`, then the new elements of `that`. -/
def unionReasons (self that : MiniCause) : MiniCause :=
  self ++ that.filter (fun reason => !containsReason self reason)

/-- The rejected combine: plain concatenation. -/
def appendReasons (self that : MiniCause) : MiniCause :=
  self ++ that

/-- E4-SEM-CE-002: concatenation duplicates a reason the union keeps once. -/
theorem append_duplicates_reasons :
    appendReasons [failOne] [failOne, failTwo] ≠
      unionReasons [failOne] [failOne, failTwo] := by
  decide

/-- E4-SEM-CE-002: concatenation also destroys the structural short circuit,
so `combine a a = a` fails for it. -/
theorem append_breaks_self_combine :
    appendReasons [failOne] [failOne] ≠ [failOne] /\
      unionReasons [failOne] [failOne] = [failOne] := by
  constructor
  · decide
  · decide

/-! ## E4-SEM-CE-003 — squash must prefer an earlier or later `Fail` -/

inductive MiniSquashed
  | error (error : Nat)
  | defect (defect : Nat)
  | interruptedWithoutError
  | emptyCause
  deriving DecidableEq, Repr

def errorOf : MiniReason -> Option Nat
  | .fail error _ => some error
  | _ => none

def defectOf : MiniReason -> Option Nat
  | .die defect _ => some defect
  | _ => none

/-- The pinned four-arm partition order: Fail, then Die, then Interrupt. -/
def squash (cause : MiniCause) : MiniSquashed :=
  match cause.filterMap errorOf with
  | error :: _ => .error error
  | [] =>
    match cause.filterMap defectOf with
    | defect :: _ => .defect defect
    | [] => match cause with
      | [] => .emptyCause
      | _ => .interruptedWithoutError

/-- The rejected squash: whichever reason comes first in the list wins. -/
def squashFirstReason (cause : MiniCause) : MiniSquashed :=
  match cause with
  | [] => .emptyCause
  | .fail error _ :: _ => .error error
  | .die defect _ :: _ => .defect defect
  | .interrupt _ _ :: _ => .interruptedWithoutError

/-- E4-SEM-CE-003: a positional squash reports the defect of an earlier `Die`
where rc.112 reports the error of the later `Fail`. -/
theorem squash_must_partition_before_choosing :
    squashFirstReason [dieOne, failOne] ≠ squash [dieOne, failOne] /\
      squash [dieOne, failOne] = MiniSquashed.error 1 := by
  constructor
  · decide
  · decide

/-- E4-SEM-CE-003: the same failure appears with interruption before a defect. -/
theorem squash_interrupt_does_not_shadow_defect :
    squashFirstReason [interruptNone, dieOne] ≠ squash [interruptNone, dieOne] /\
      squash [interruptNone, dieOne] = MiniSquashed.defect 1 := by
  constructor
  · decide
  · decide

/-- E4-SEM-CE-003: the fourth arm is not the third one. An empty cause and an
interrupt-only cause squash to different values. -/
theorem squash_empty_is_a_fourth_arm :
    squash [] = MiniSquashed.emptyCause /\
      squash [interruptNone] = MiniSquashed.interruptedWithoutError /\
      squash [] ≠ squash [interruptNone] := by
  refine ⟨by decide, by decide, by decide⟩

/-! ## E4-SEM-CE-004 — `annotate` must not overwrite silently -/

def lookupKey (annotations : MiniAnnotations) (key : String) : Option Nat :=
  (annotations.entries.find? (fun entry => decide (entry.fst = key))).map Prod.snd

def containsKey (annotations : MiniAnnotations) (key : String) : Bool :=
  annotations.entries.any (fun entry => decide (entry.fst = key))

/-- The pinned merge: existing keys keep their value unless `overwrite`. -/
def annotate (self extra : MiniAnnotations) (overwrite : Bool) :
    MiniAnnotations :=
  { entries :=
      self.entries.map (fun entry =>
        if overwrite = true then
          match lookupKey extra entry.fst with
          | some value => (entry.fst, value)
          | none => entry
        else entry) ++
      extra.entries.filter (fun entry => !containsKey self entry.fst) }

/-- The rejected merge: the incoming map always wins. -/
def annotateOverwriting (self extra : MiniAnnotations) : MiniAnnotations :=
  { entries :=
      self.entries.filter (fun entry => !containsKey extra entry.fst) ++
        extra.entries }

def stackTrace : String := "effect/Cause/StackTrace"

def keptAnnotations : MiniAnnotations := { entries := [(stackTrace, 1)] }
def incomingAnnotations : MiniAnnotations := { entries := [(stackTrace, 2)] }

/-- E4-SEM-CE-004: a silently overwriting merge loses the first annotation
recorded for a key, which the pinned default keeps. -/
theorem annotate_must_not_overwrite_by_default :
    lookupKey (annotate keptAnnotations incomingAnnotations false) stackTrace =
        some 1 /\
      lookupKey (annotateOverwriting keptAnnotations incomingAnnotations)
        stackTrace = some 2 /\
      annotate keptAnnotations incomingAnnotations false ≠
        annotateOverwriting keptAnnotations incomingAnnotations := by
  refine ⟨by decide, by decide, by decide⟩

/-- E4-SEM-CE-004: with `overwrite := true` the two merges still differ,
because the pinned merge replaces the value in place while the rejected one
moves the key to the end. -/
theorem annotate_overwrite_keeps_position :
    (annotate { entries := [(stackTrace, 1), ("a", 1)] } incomingAnnotations
        true).entries = [(stackTrace, 2), ("a", 1)] /\
      (annotateOverwriting { entries := [(stackTrace, 1), ("a", 1)] }
        incomingAnnotations).entries = [("a", 1), (stackTrace, 2)] := by
  refine ⟨by decide, by decide⟩

/-- E4-SEM-CE-004: annotating with the empty map is the identity, so the
`size === 0` guard in the pinned source is observable. -/
theorem annotate_empty_is_identity :
    annotate keptAnnotations { entries := [] } true = keptAnnotations := by
  decide

/-! ## E4-SEM-CE-005 — a finalizer failure under a successful exit -/

inductive MiniExit
  | success
  | failure (cause : MiniCause)
  deriving DecidableEq, Repr

/-- The pinned `combineFinalizerCause` at internal/effect.ts:3800-3804. -/
def mergeFinalizer : MiniExit -> MiniExit -> MiniExit
  | .success, finalizer => finalizer
  | .failure _, .success => .success
  | .failure cause, .failure finalizerCause =>
      .failure (unionReasons cause finalizerCause)

/-- The rejected merge: the original exit always wins. -/
def mergeFinalizerExitWins : MiniExit -> MiniExit -> MiniExit
  | .success, _ => .success
  | .failure cause, _ => .failure cause

/-- E4-SEM-CE-005: keeping the successful exit discards the finalizer failure
that rc.112 lets stand alone. -/
theorem finalizer_failure_stands_alone :
    mergeFinalizer .success (.failure [failTwo]) = .failure [failTwo] /\
      mergeFinalizerExitWins .success (.failure [failTwo]) = .success /\
      mergeFinalizer .success (.failure [failTwo]) ≠
        mergeFinalizerExitWins .success (.failure [failTwo]) := by
  refine ⟨by decide, by decide, by decide⟩

/-- E4-SEM-CE-005: a successful finalizer under a failed exit does not
re-raise the exit cause inside this combinator; the caller restores it. -/
theorem successful_finalizer_under_failed_exit :
    mergeFinalizer (.failure [failOne]) .success = MiniExit.success /\
      mergeFinalizerExitWins (.failure [failOne]) .success =
        MiniExit.failure [failOne] := by
  refine ⟨by decide, by decide⟩

/-! ## E4-SEM-CE-006 — a failed exit with an empty cause joins to success -/

def causeReasons : MiniExit -> MiniCause
  | .success => []
  | .failure cause => cause

/-- The pinned `exitAsVoidAll` at internal/effect.ts:2024-2038. -/
def asVoidAll (exits : List MiniExit) : MiniExit :=
  let reasons := exits.flatMap causeReasons
  if reasons.isEmpty then .success else .failure reasons

/-- The rejected join: any failed exit makes the join fail. -/
def asVoidAllAnyFailure (exits : List MiniExit) : MiniExit :=
  if exits.any (fun exit => decide (exit ≠ MiniExit.success)) then
    .failure (exits.flatMap causeReasons)
  else
    .success

/-- E4-SEM-CE-006: a `Failure` exit carrying an empty cause contributes no
reason, so the pinned join succeeds while the naive join fails. -/
theorem empty_cause_failure_joins_to_success :
    asVoidAll [.failure []] = MiniExit.success /\
      asVoidAllAnyFailure [.failure []] = MiniExit.failure [] /\
      asVoidAll [.failure []] ≠ asVoidAllAnyFailure [.failure []] := by
  refine ⟨by decide, by decide, by decide⟩

/-- E4-SEM-CE-006: the join concatenates and does not deduplicate, so it is
not `causeCombine` applied pairwise. -/
theorem join_is_not_combine :
    asVoidAll [.failure [failOne], .failure [failOne]] =
        MiniExit.failure [failOne, failOne] /\
      unionReasons [failOne] [failOne] = [failOne] := by
  refine ⟨by decide, by decide⟩

/-! ## E4-SEM-CE-007 — a set carrier erases reason order -/

/-- The rejected carrier: an order-insensitive membership view of a cause. -/
def memberEquivalent (left right : MiniCause) : Bool :=
  left.all (fun reason => containsReason right reason) &&
    right.all (fun reason => containsReason left reason)

/-- E4-SEM-CE-007: `causeCombine` is not commutative, so a canonical finite
set (`Effect4.Data.Row`) cannot carry a cause. -/
theorem union_is_not_commutative :
    unionReasons [failOne] [failTwo] ≠ unionReasons [failTwo] [failOne] /\
      memberEquivalent (unionReasons [failOne] [failTwo])
        (unionReasons [failTwo] [failOne]) = true := by
  refine ⟨by decide, by decide⟩

/-- E4-SEM-CE-007: the two orders also squash differently, so order is not a
presentation detail. -/
theorem order_changes_squash :
    squash [failOne, failTwo] = MiniSquashed.error 1 /\
      squash [failTwo, failOne] = MiniSquashed.error 2 := by
  refine ⟨by decide, by decide⟩

/-! ## Kernel dependency receipts

Every attack witness above is finite and decidable. The accepted ceiling is
no dependency, `propext`, or `propext` with `Quot.sound`.
-/

#print axioms Test.Counterexamples.Semantics.CauseExit.tree_invents_structure
#print axioms Test.Counterexamples.Semantics.CauseExit.tree_empty_not_unique
#print axioms Test.Counterexamples.Semantics.CauseExit.append_duplicates_reasons
#print axioms Test.Counterexamples.Semantics.CauseExit.append_breaks_self_combine
#print axioms Test.Counterexamples.Semantics.CauseExit.squash_must_partition_before_choosing
#print axioms Test.Counterexamples.Semantics.CauseExit.squash_interrupt_does_not_shadow_defect
#print axioms Test.Counterexamples.Semantics.CauseExit.squash_empty_is_a_fourth_arm
#print axioms Test.Counterexamples.Semantics.CauseExit.annotate_must_not_overwrite_by_default
#print axioms Test.Counterexamples.Semantics.CauseExit.annotate_overwrite_keeps_position
#print axioms Test.Counterexamples.Semantics.CauseExit.annotate_empty_is_identity
#print axioms Test.Counterexamples.Semantics.CauseExit.finalizer_failure_stands_alone
#print axioms Test.Counterexamples.Semantics.CauseExit.successful_finalizer_under_failed_exit
#print axioms Test.Counterexamples.Semantics.CauseExit.empty_cause_failure_joins_to_success
#print axioms Test.Counterexamples.Semantics.CauseExit.join_is_not_combine
#print axioms Test.Counterexamples.Semantics.CauseExit.union_is_not_commutative
#print axioms Test.Counterexamples.Semantics.CauseExit.order_changes_squash

end Test.Counterexamples.Semantics.CauseExit
