import Effect4.Laws.Program.Eliminators
import Effect4.Program.Checker
import Effect4.Program.Native
import Effect4.Program.Sketch

/-!
# Controls of the five widened classifiers

The raw-first classifiers use `UnionRule.extendAll`; option uses the normalized full lift.
These controls apply laws to the real classifier rules and evaluate concrete checker programs.
The legacy `liftOne` controls retain the boundary of that guarded helper.
Proper homogeneous unions now answer. A retained member outside a classifier's family still refuses.
Raw constructor answers and option normalization remain unchanged.
-/

set_option autoImplicit false

namespace Effect4.Test.Eliminators

open Effect4 Effect4.Program Effect4.Program.UnionRule
open Effect4.Machine.Env (Requirement)

/-! ## The guard, at the member rule of the fiber rule -/

/-- Two fiber types with no order between them: a proper union. -/
def twoFibers : Ty := .union (.fiberOf .nat .never) (.fiberOf .string .bool)

/-- One fiber type under a raw union with `never`: its normal form is the fiber type. -/
def fiberOrNever : Ty := .union (.fiberOf .nat .string) .never

/-- Two fiber types with one below the other: the normal form keeps the larger. -/
def literalOrString : Ty := .union (.fiberOf (.lit "a") .never) (.fiberOf .string .never)

-- Green: the guarded rule at `never`, at one union member, and at one union member in the
-- normal form.
#guard liftOne Member.fiber .never = some (.never, .never)
#guard liftOne Member.fiber (.fiberOf .nat .string) = some (.nat, .string)
#guard liftOne Member.fiber fiberOrNever = some (.nat, .string)
#guard liftOne Member.fiber literalOrString = some (.string, .never)

-- Red: the member rule reads one union member. It refuses `never` and each raw union.
#guard Member.fiber .never = none
#guard Member.fiber fiberOrNever = none
#guard Member.fiber literalOrString = none

-- Red: the guard refuses a proper union, and the lifted rule answers there. The refusal is the
-- guard's own.
#guard twoFibers.normalize.members.length = 2
#guard liftOne Member.fiber twoFibers = none
#guard lift Member.fiber twoFibers = some (.union .nat .string, .bool)

-- Red for another reason: a member that is no fiber type. The lifted rule refuses it too.
#guard liftOne Member.fiber (.union (.fiberOf .nat .never) .nat) = none
#guard lift Member.fiber (.union (.fiberOf .nat .never) .nat) = none
#guard liftOne Member.fiber .nat = none

/-- **What the guarded rule alone answers at a raw fiber type**: the normal forms of the two
columns. It reads the normal form (`liftOne_congr`), and at one normal union member it is the
member rule (`liftOne_member`). The fiber rule answers the raw columns there instead
(`fiberTy_fiberOf`). -/
theorem liftOne_fiberOf (value error : Ty) :
    liftOne Member.fiber (.fiberOf value error) = some (value.normalize, error.normalize) := by
  have normal : Ty.Normal (.fiberOf value.normalize error.normalize) :=
    .fiberOf (Ty.normal_normalize value) (Ty.normal_normalize error)
  rw [liftOne_congr Member.fiber (s := .fiberOf value error)
    (t := .fiberOf value.normalize error.normalize) normal.fixed.symm,
    liftOne_member Member.fiber normal rfl]
  show some (Ty.join .never value.normalize, Ty.join .never error.normalize) = _
  rw [Ty.join_never, Ty.join_never, Ty.normalize_idem, Ty.normalize_idem]

/-! ## The fiber rule: the extended rule of its member rule -/

-- The fiber rule is the extended rule of `Member.fiber`, by definition.
example : fiberTy = extendAll Member.fiber := rfl

/-- A fiber type whose value column is not its own normal form: normalization distributes the
product over the union. -/
def rawFiber : Ty := .fiberOf (.prod (.union .nat .string) .unit) .never

-- Green: at a raw fiber type the rule answers the columns as they are spelled, as the by-shape
-- rule did.
example (value error : Ty) : fiberTy (.fiberOf value error) = some (value, error) := rfl
#guard fiberTy rawFiber = some (.prod (.union .nat .string) .unit, .never)
#guard fiberTy rawFiber = Member.fiber rawFiber

-- Red: the guarded rule alone answers the normal form of the value column there.
#guard liftOne Member.fiber rawFiber =
  some (.union (.prod .nat .unit) (.prod .string .unit), .never)

-- Red: two spellings of one type have two spellings of one answer. The extended rule keeps the
-- raw answer, so it does not read the normal form. Each answer is below the other.
#guard (Ty.union rawFiber .never).normalize = rawFiber.normalize
#guard fiberTy (.union rawFiber .never) =
  some (.union (.prod .nat .unit) (.prod .string .unit), .never)
#guard fiberTy (.union rawFiber .never) != fiberTy rawFiber
#guard Ty.subN (.prod (.union .nat .string) .unit) (.union (.prod .nat .unit) (.prod .string .unit))
#guard Ty.subN (.union (.prod .nat .unit) (.prod .string .unit)) (.prod (.union .nat .string) .unit)

-- Green: `never`, one fiber type under a raw union with `never`, and two fiber types with one
-- below the other.
example : fiberTy .never = some (.never, .never) := extendAll_never rfl
#guard fiberTy .never = some (.never, .never)
#guard fiberTy fiberOrNever = some (.nat, .string)
#guard fiberTy literalOrString = some (.string, .never)

-- Green: two fiber types with no order join. Other heads still refuse.
#guard fiberTy twoFibers = some (.union .nat .string, .bool)
#guard fiberTy .nat = none
#guard fiberTy (.union (.fiberOf .nat .never) .nat) = none

/-! ## The checker: the sites that ask the fiber rule -/

-- Green: a join and an await of a handle at `never`. The rule answers `never` twice.
#guard Checker.check nativeSignature [.never] [] (.awaitFiber (.var 0) .joinEffect) =
  .ok ⟨.never, .never, Requirement.empty⟩
#guard Checker.check nativeSignature [.never] [] (.awaitFiber (.var 0) .awaitValue) =
  .ok (EffTy.pure (.exitOf .never .never))

-- Green: the three actions on one handle, at `never`.
#guard Checker.check nativeSignature [.never, Ty.scope] [] (.withFiber (.runIn (.var 0) (.var 1))) =
  .ok (EffTy.pure .unit)
#guard Checker.check nativeSignature [.never] [] (.withFiber (.interrupt (.var 0))) =
  .ok (EffTy.pure .unit)
#guard Checker.check nativeSignature [.never] [] (.withFiber (.interruptScoped (.var 0))) =
  .ok (EffTy.pure .unit)

/-- The empty list, as a term: its type is `list never`. -/
def noFibers : Term := .app "nil" .nil

-- Green: the three actions on a list of handles, at the empty list. Each is a closed program
-- that the by-shape rule refused, as no fiber at `never`.
#guard Checker.check nativeSignature [] [] (.withFiber (.interruptAll noFibers none)) =
  .ok (EffTy.pure .unit)
#guard Checker.check nativeSignature [] [] (.withFiber (.awaitAll noFibers)) =
  .ok (EffTy.pure (.list (.exitOf .never .never)))
#guard Checker.check nativeSignature [] [] (.withFiber (.awaitAllFailFast noFibers)) =
  .ok (EffTy.pure (.list (.exitOf .never .never)))

-- Green: one fiber type under a raw union with `never`.
#guard Checker.check nativeSignature [fiberOrNever] [] (.awaitFiber (.var 0) .joinEffect) =
  .ok ⟨.nat, .string, Requirement.empty⟩

-- Green: the checker joins two fiber types with no order.
#guard Checker.check nativeSignature [twoFibers] [] (.awaitFiber (.var 0) .joinEffect) =
  .ok ⟨.union .nat .string, .bool, Requirement.empty⟩
-- Red: a type that is no fiber type is refused, as before the conversion.
#guard explain nativeSignature [.nat] (.awaitFiber (.var 0) .joinEffect) =
  some ⟨[], .notFiber .nat⟩

/-! ## A sketch: a hole at `never` under the fiber rule

A hole with no stated type is declared at `never` (decisions row 288, point 5). The fiber rule
answers at `never`, so a sketch that joins such a handle is admitted modulo its holes. -/

/-- A sketch whose hole 0 stands for a handle, and that joins it. -/
def joinsHole (handle : Ty) : Sketch :=
  { program := .bind (Sketch.hole {} 0) (.awaitFiber (.var 0) .joinEffect)
    holes := [Row.hole "handle" handle] }

-- Green: the hole is declared at `never`, and the sketch is admitted at `never`.
#guard (joinsHole .never).check = .ok ⟨.never, .never, Requirement.empty⟩
-- Green: the hole is declared at a fiber type, and the sketch has that type's columns.
#guard (joinsHole (.fiberOf .nat .string)).check = .ok ⟨.nat, .string, Requirement.empty⟩
-- Red: the hole is declared at a type that is no fiber type. The join is refused, at the join.
#guard Checker.refusal (joinsHole .nat).check = some ⟨[1], .notFiber .nat⟩

/-! ## The closed program of the design note: one type at both spellings

The body builds a list of pairs whose second part is a union. `cons` joins the pair with the
element type of the empty list, so the body's answer is the normal form: a list of a union of
pairs. `mapFromEntries` reads a union member by member (the match by bounds, decisions row 303).
So the last line has one type at the written type and at its normal form, and the guarded rule
alone would type this program too.

Decisions row 294, point 4, gave an atom's refusal of the normal form as the reason for the raw
answer of the extended rule. That refusal is gone. One rule still reads the raw form: the interim
guard at a binder term (`Test/Program/BoundsControls.lean`). -/

/-- `true ? 1 : "s"`, as a program: its answer is `nat | string`. -/
def numberOrText : NativeEff :=
  .select (.lit (.bool true)) .bool (.succeed (.lit (.nat 1))) (.succeed (.lit (.str "s")))

/-- The forked body: one entry `["k", x]` in a list, with `x` at `nat | string`. -/
def body : NativeEff :=
  .bind numberOrText
    (.succeed (.app "cons" (.cons
      (.app "pair" (.cons (.lit (.str "k")) (.cons (.var 0) .nil)))
      (.cons (.app "nil" .nil) .nil))))

/-- The last line: a map from the joined entries. The handle is variable 0, and the joined
value is variable 1. -/
def useEntries : NativeEff := .succeed (.app "mapFromEntries" (.cons (.var 1) .nil))

/-- The closed program: fork the body, join the fiber, build a map from the joined entries. -/
def joinsEntries : NativeEff :=
  .bind (.withFiber (.fork body ⟨true, false, .inherit⟩))
    (.bind (.awaitFiber (.var 0) .joinEffect) useEntries)

/-- The type of the body's list as it is written: a product over a union, and no normal form. -/
def rawEntries : Ty := .list (.prod (.lit "k") (.union .nat .string))

/-- The same type's normal form: a union of two products. -/
def normalEntries : Ty := .list (.union (.prod (.lit "k") .nat) (.prod (.lit "k") .string))

-- tested: the body's answer is the normal form of the written type
#guard Checker.check nativeSignature [] [] body = .ok ⟨normalEntries, .never, Requirement.empty⟩
#guard rawEntries.normalize = normalEntries
#guard rawEntries != normalEntries

-- Green: the checker admits the program.
#guard fiberTy (.fiberOf rawEntries .never) = some (rawEntries, .never)
#guard Checker.check nativeSignature [] [] joinsEntries =
  .ok ⟨.map .string (.union .nat .string), .never, Requirement.empty⟩

-- Green: the guarded rule alone answers the normal form of the value column, and the last line
-- has one type at the written type and at the normal form.
#guard liftOne Member.fiber (.fiberOf rawEntries .never) = some (normalEntries, .never)
#guard Checker.check nativeSignature [.fiberOf rawEntries .never, rawEntries] [] useEntries =
  .ok ⟨.map .string (.union .nat .string), .never, Requirement.empty⟩
#guard explain nativeSignature [.fiberOf rawEntries .never, normalEntries] useEntries = none
#guard NativeAtom.typeOf .mapFromEntries [rawEntries] = some (.map .string (.union .nat .string))
#guard NativeAtom.typeOf .mapFromEntries [normalEntries] = some (.map .string (.union .nat .string))

/-! ## The contract at the fiber rule, by projection -/

/-- **The contract of the fiber rule**: `Eliminator.extendAll_laws` at `Member.fiber_eliminator`,
with the order of a pair spelled by column. The rule agrees with its member rule. Where the
member rule refuses, it is the full lift. It answers a least pair at `never`. Its answer is
the least pair of columns with the handle type below their fiber type. It admits a proper union whose retained members answer. -/
theorem fiberTy_contract :
    (∀ {t : Ty} {a : Ty × Ty}, Member.fiber t = some a → fiberTy t = some a) ∧
    (∀ {t : Ty}, Member.fiber t = none → fiberTy t = lift Member.fiber t) ∧
    (∃ a : Ty × Ty, fiberTy .never = some a ∧
      ∀ b : Ty × Ty, Ty.subN a.1 b.1 = true ∧ Ty.subN a.2 b.2 = true) ∧
    (∀ {t : Ty} {a : Ty × Ty}, fiberTy t = some a →
      Ty.subN t (.fiberOf a.1 a.2) = true ∧
      ∀ b : Ty × Ty, (Ty.subN a.1 b.1 = true ∧ Ty.subN a.2 b.2 = true) ↔
        Ty.subN t (.fiberOf b.1 b.2) = true) ∧
    (∀ {t : Ty} {a : Ty × Ty}, extend Member.fiber t = some a → fiberTy t = some a) :=
  Member.fiber_eliminator.extendAll_laws

/-- The fiber rule answers exactly at a raw fiber type, or at a type that is below a fiber type. -/
theorem fiberTy_isSome_iff (t : Ty) :
    (fiberTy t).isSome = true ↔
      ∃ b : Ty × Ty, Ty.subN t (.fiberOf b.1 b.2) = true :=
  Member.fiber_eliminator.extendAll_isSome_iff t

/-- **The raw answer of the fiber rule is a matter of spelling.** Where the fiber rule answers,
the full lift answers too, and each answer is below the other by column. So the removal
of the raw answer changes no verdict of the fiber rule (decisions row 294). It can change the spelling that a later rule reads. The raw answer remains in place. -/
theorem fiberTy_lift {t : Ty} {a : Ty × Ty} (typed : fiberTy t = some a) :
    ∃ a' : Ty × Ty, lift Member.fiber t = some a' ∧
      (Ty.subN a.1 a'.1 = true ∧ Ty.subN a.2 a'.2 = true) ∧
      (Ty.subN a'.1 a.1 = true ∧ Ty.subN a'.2 a.2 = true) :=
  Member.fiber_eliminator.extendAll_lift typed

/-- What the fiber rule keeps of the monotone law: every smaller handle type. -/
theorem fiberTy_mono {s t : Ty} (smaller : Ty.subN s t = true)
    {b : Ty × Ty} (typed : fiberTy t = some b) :
    ∃ a : Ty × Ty, fiberTy s = some a ∧ Ty.subN a.1 b.1 = true ∧ Ty.subN a.2 b.2 = true :=
  Member.fiber_eliminator.extendAll_mono smaller typed

-- Green: monotonicity now includes a proper union below a fiber type.
#guard Ty.subN twoFibers (.fiberOf (.union .nat .string) .bool)
#guard fiberTy (.fiberOf (.union .nat .string) .bool) = some (.union .nat .string, .bool)
#guard fiberTy twoFibers = some (.union .nat .string, .bool)

/-! ## The member rule at one union member: which constructors have the premise

`Member.fiber_one` bounds the historical guarded connector: the member rule answers only
where the normal form has at most one union member. The normal form of a fiber type is a fiber
type. The constructors of the next conversions have the same form. A product does not: its
normal form distributes over a union. -/

-- Green: the normal form of each of these constructors is the constructor again.
example (a e : Ty) : (Ty.fiberOf a e).normalize = .fiberOf a.normalize e.normalize := rfl
example (a : Ty) : (Ty.list a).normalize = .list a.normalize := rfl
example (a e : Ty) : (Ty.exitOf a e).normalize = .exitOf a.normalize e.normalize := rfl
example (a : Ty) : (Ty.option a).normalize = .option a.normalize := rfl
example (e : Ty) : (Ty.causeOf e).normalize = .causeOf e.normalize := rfl

/-- A member rule that reads a product: the two columns of one product type. -/
def pairOf : Ty → Option (Ty × Ty)
  | .prod first second => some (first, second)
  | _ => none

/-- A product over a union: its normal form is a union of two products. -/
def rawProduct : Ty := .prod (.union .nat .string) .unit

-- Red: the member rule answers at the raw product, and the normal form there is a proper union.
-- So the guarded rule alone refuses, and the extended rule answers by its raw answer only.
#guard pairOf rawProduct = some (.union .nat .string, .unit)
#guard rawProduct.normalize.members.length = 2
#guard liftOne pairOf rawProduct = none
#guard extend pairOf rawProduct = some (.union .nat .string, .unit)
#guard lift pairOf rawProduct = some (.union .nat .string, .unit)

/-! ## The list rule, the exit rule, the cause rule and the option rule (decisions row 304)

The list rule, the exit rule and the cause rule read the raw head of their target, so each is the
extended rule of its member rule, as the fiber rule is. The option rule of `Decision.arms` read
the normal form of its target, so it is the normalized full lift, with no raw answer. -/

example : Checker.listOf? = extendAll Member.list := rfl
example : Checker.exitOf? = extendAll Member.exit := rfl
example : causeInputError? = extendAll Member.cause := rfl
example : optionTy = lift Member.option := rfl

-- green (tested): each rule at a raw type of its constructor answers as it did
#guard Checker.listOf? (.list rawProduct) = some rawProduct
#guard Checker.exitOf? (.exitOf rawProduct .string) = some (rawProduct, .string)
#guard causeInputError? (.causeOf rawProduct) = some rawProduct
#guard causeInputError? (.exitOf .nat rawProduct) = some rawProduct
-- green (tested): the new answers. Each rule answers at `never`, and at one union member under a
-- raw union
#guard Checker.listOf? .never = some .never
#guard Checker.listOf? (.union (.list .nat) .never) = some .nat
#guard Checker.exitOf? .never = some (.never, .never)
#guard Checker.exitOf? (.union (.exitOf .nat .string) .never) = some (.nat, .string)
#guard causeInputError? .never = some .never
#guard causeInputError? (.union (.causeOf .string) .never) = some .string
#guard optionTy .never = some .never
-- Green: each full fallback joins its approved input families.
#guard Checker.listOf? (.union (.list .nat) (.list .string)) = some (.union .nat .string)
#guard Checker.exitOf? (.union (.exitOf .nat .never) (.exitOf .string .never)) = some (.union .nat .string, .never)
#guard causeInputError? (.union (.causeOf .nat) (.exitOf .unit .string)) = some (.union .nat .string)
#guard optionTy (.union (.option .nat) (.option .string)) = some (.union .nat .string)
#guard Checker.listOf? .nat = none
#guard Checker.exitOf? .nat = none
#guard causeInputError? .nat = none
#guard optionTy .nat = none

-- green (tested): the option rule answers the normal form of the element, as `Decision.arms`
-- did before its conversion
#guard optionTy (.option rawProduct) = some rawProduct.normalize
#guard optionTy (.option (.union .bool .never)) = some .bool
#guard Decision.arms .option (.option (.union .bool .never)) = some ([], [.bool])
#guard Decision.arms .option .never = some ([], [.never])
-- red (tested): the extended rule would answer the raw element there, and move a type
#guard extend Member.option (.option rawProduct) = some rawProduct
#guard extend Member.option (.option (.union .bool .never)) = some (.union .bool .never)
#guard rawProduct.normalize != rawProduct

/-- **`Decision.arms` at an option is the former rule at one normal member** (proved, by
`optionTy_eq_normal`): the element type at a normal form that is one option type, and a refusal
elsewhere. -/
theorem arms_option_eq_normal {t : Ty} (some_member : t.normalize ≠ .never)
    (one : t.normalize.members.length ≤ 1) :
    Decision.arms .option t = (match t.normalize with
      | .option a => some ([], [a])
      | _ => none) := by
  show (optionTy t).map (fun a => (([] : List Ty), [a])) = _
  rw [optionTy_eq_normal some_member one]
  cases t.normalize <;> rfl

/-- **The raw answer of the list rule is a matter of spelling** (proved, by
`Eliminator.extendAll_lift` at `Member.list_eliminator`): where the list rule answers, the full lift
alone answers, and each answer is below the other. -/
theorem listOf_lift {t : Ty} {a : Ty} (typed : Checker.listOf? t = some a) :
    ∃ a' : Ty, lift Member.list t = some a' ∧ Ty.subN a a' = true ∧ Ty.subN a' a = true :=
  Member.list_eliminator.extendAll_lift typed

/-- The same at the exit rule, by column (proved, at `Member.exit_eliminator`). -/
theorem exitOf_lift {t : Ty} {a : Ty × Ty} (typed : Checker.exitOf? t = some a) :
    ∃ a' : Ty × Ty, lift Member.exit t = some a' ∧
      (Ty.subN a.1 a'.1 = true ∧ Ty.subN a.2 a'.2 = true) ∧
      (Ty.subN a'.1 a.1 = true ∧ Ty.subN a'.2 a.2 = true) :=
  Member.exit_eliminator.extendAll_lift typed

/-- **The option rule answers exactly** at a type below an option type
(proved, by `Eliminator.adjoint`). -/
theorem optionTy_isSome_iff (t : Ty) :
    (optionTy t).isSome = true ↔
      ∃ b : Ty, Ty.subN t (.option b) = true :=
  (Member.option_eliminator.adjoint t).1

/-! ## Closed types -/

/-- **A closed handle type has a closed value type and a closed error type.** It is
`extendAll_closed_pair` at the member fact of the fiber rule: the member fact at the raw answer,
and `lift_closed_pair` at the full lift's answer. -/
theorem fiberTy_closed {t : Ty} {a : Ty × Ty} (typed : fiberTy t = some a)
    (closed : t.closed = true) : a.1.closed = true ∧ a.2.closed = true :=
  extendAll_closed_pair Member.fiber_closed typed closed


/-! ## Proper unions at each production consumer -/

/-- Two distinct list types. -/
def twoLists : Ty := .union (.list .nat) (.list .string)

/-- Two distinct exit types. -/
def twoExits : Ty := .union (.exitOf .nat .never) (.exitOf .string .never)

/-- The two cause-query input families with distinct error types. -/
def twoCauses : Ty := .union (.causeOf .nat) (.exitOf .unit .string)

/-- Two distinct option types. -/
def twoOptions : Ty := .union (.option .nat) (.option .string)

/-- A list union whose items are distinct fiber types. -/
def twoFiberLists : Ty := .union (.list (.fiberOf .nat .never)) (.list (.fiberOf .string .bool))

-- Each retained member must belong to the classifier's input family.
#guard Checker.listOf? (.union twoLists .nat) = none
#guard Checker.exitOf? (.union twoExits .nat) = none
#guard causeInputError? (.union twoCauses .nat) = none
#guard optionTy (.union twoOptions .nat) = none

-- Both fiber result modes use the joined columns.
#guard Checker.check nativeSignature [twoFibers] [] (.awaitFiber (.var 0) .awaitValue) =
  .ok (EffTy.pure (.exitOf (.union .nat .string) .bool))
#guard Checker.check nativeSignature [twoFibers, .scope] []
    (.withFiber (.runIn (.var 0) (.var 1))) = .ok (EffTy.pure .unit)
#guard Checker.check nativeSignature [twoFibers] [] (.withFiber (.interrupt (.var 0))) =
  .ok (EffTy.pure .unit)
#guard Checker.check nativeSignature [twoFibers] [] (.withFiber (.interruptScoped (.var 0))) =
  .ok (EffTy.pure .unit)

-- List actions require both list and fiber classifiers. Target profile refusals stay separate.
#guard Checker.check nativeSignature [twoFiberLists] [] (.withFiber (.interruptAll (.var 0) none)) =
  .ok (EffTy.pure .unit)
#guard Checker.check nativeSignature [twoFiberLists] [] (.withFiber (.awaitAll (.var 0))) =
  .ok (EffTy.pure (.list (.exitOf (.union .nat .string) .bool)))
#guard Checker.check nativeSignature [twoFiberLists] [] (.withFiber (.awaitAllFailFast (.var 0))) =
  .ok (EffTy.pure (.list (.exitOf (.union .nat .string) .bool)))
#guard (Checker.check nativeSignature [.union twoFiberLists (.list .nat)] []
    (.withFiber (.awaitAll (.var 0)))).toOption = none

-- The scope and interruptor premises remain in force.
#guard (Checker.check nativeSignature [twoFibers, .nat] []
    (.withFiber (.runIn (.var 0) (.var 1)))).toOption = none
#guard (Checker.check nativeSignature [twoFiberLists, .string] []
    (.withFiber (.interruptAll (.var 0) (some (.var 1))))).toOption = none
#guard Checker.check nativeSignature [.scope, twoExits] []
    (.withFiber (.closeScope (.var 0) (.var 1))) = .ok (EffTy.pure .unit)
#guard (Checker.check nativeSignature [.nat, twoExits] []
    (.withFiber (.closeScope (.var 0) (.var 1)))).toOption = none
#guard (Checker.check nativeSignature [.scope, .union twoExits .nat] []
    (.withFiber (.closeScope (.var 0) (.var 1)))).toOption = none

-- An option branch receives the joined element. The invalid-member companion refuses.
#guard Checker.check nativeSignature [twoOptions] []
    (.select (.var 0) .option (.succeed (.lit .unit)) (.succeed (.var 1))) =
  .ok ⟨Ty.join .unit (.union .nat .string), .never, Requirement.empty⟩
#guard (Checker.check nativeSignature [.union twoOptions .nat] []
    (.select (.var 0) .option (.succeed (.lit .unit)) (.succeed (.var 1)))).toOption = none

-- Fold binds its joined item after its accumulator. Both accumulator bounds remain required.
#guard termTy nativeSignature [twoLists]
    (.fold (some .unknown) (.var 0) (.lit (.nat 0)) (.var 2)) = some .unknown
#guard termTy nativeSignature [twoLists]
    (.fold (some .nat) (.var 0) (.lit (.nat 0)) (.var 2)) = none
#guard termTy nativeSignature [twoLists]
    (.fold (some .nat) (.var 0) (.lit (.str "bad")) (.var 1)) = none
#guard termTy nativeSignature [.union twoLists .nat]
    (.fold (some .unknown) (.var 0) (.lit (.nat 0)) (.var 2)) = none

#guard explain nativeSignature [twoLists]
    (.succeed (.fold (some .unknown) (.var 0) (.lit (.nat 0)) (.var 2))) = none
#guard (explain nativeSignature [twoLists]
    (.succeed (.fold (some .nat) (.var 0) (.lit (.nat 0)) (.var 2)))).isSome

-- Every cause query uses the same joined input classifier.
#guard NativeAtom.typeOf .causeIsFail [twoCauses] = some .bool
#guard NativeAtom.typeOf .causeIsDie [twoCauses] = some .bool
#guard NativeAtom.typeOf .causeIsInterrupt [twoCauses] = some .bool
#guard NativeAtom.typeOf .causeError [twoCauses] = some (.option (.union .nat .string))
#guard NativeAtom.typeOf .causeIsFail [.union twoCauses .nat] = none
#guard NativeAtom.typeOf .causeIsDie [.union twoCauses .nat] = none
#guard NativeAtom.typeOf .causeIsInterrupt [.union twoCauses .nat] = none
#guard NativeAtom.typeOf .causeError [.union twoCauses .nat] = none
#guard termTy nativeSignature [twoCauses] (.app "causeError" (.cons (.var 0) .nil)) =
  some (.option (.union .nat .string))

end Effect4.Test.Eliminators
