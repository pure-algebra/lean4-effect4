import Effect4.Laws.Program.Eliminators
import Effect4.Program.Checker
import Effect4.Program.Native
import Effect4.Program.Sketch

/-!
# Controls of the converted eliminators of the checker

A rule of the checker that reads a type by one constructor is converted to the extended rule of
its member rule (`UnionRule.extend`, `src/Effect4/Program/UnionRule.lean`; candidate N,
decisions rows 285 and 292 to 294). The laws are in `src/Effect4/Laws/Program/UnionRule.lean`,
and each converted rule has a section of `src/Effect4/Laws/Program/Eliminators.lean`. The fiber
rule, `fiberTy`, is the first. Each control below is finite: a guard on closed types, or a law
at one instance. A guard is a finite check and no theorem.

Green controls:

- the guarded rule at `never`, at one union member and at a raw union with one union member in
  its normal form;
- the fiber rule at a raw fiber type: the columns as they are spelled, as before the
  conversion;
- the checker at `never`, at each of its sites that ask the fiber rule;
- a sketch that joins a handle that its hole declares at `never`;
- the closed program of the design note: admitted, at the type it had before the conversion;
- the contract at the fiber rule, by projection of `Eliminator.extend_laws`;
- a closed handle type has closed columns, through both alternatives of the extended rule.

Red controls, each red for its stated reason:

- the member rule at `never` and at a raw union: it reads one union member;
- the fiber rule at two fiber types with no order: the guard refuses, and the lifted rule
  answers;
- the fiber rule at a union with a member that is no fiber type: the member rule refuses the
  member;
- the guarded rule alone at the closed program: it answers the normal form of the value column,
  and an atom's scheme refuses that type. It is the reason for the raw answer;
- two spellings of one type at the fiber rule: the answers differ in spelling, because the
  extended rule keeps the raw answer;
- the monotone law at a proper union below a fiber type: the premise on the smaller target is
  needed;
- a member rule that reads a product: it answers where the normal form is a proper union, so
  the guarded rule alone refuses there.
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
example : fiberTy = extend Member.fiber := rfl

/-- A fiber type whose value column is not its own normal form: normalization distributes the
product over the union. -/
def rawFiber : Ty := .fiberOf (.prod (.union .nat .string) .unit) .never

-- Green: at a raw fiber type the rule answers the columns as they are spelled, as the by-shape
-- rule did.
example (value error : Ty) : fiberTy (.fiberOf value error) = some (value, error) :=
  fiberTy_fiberOf value error
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
example : fiberTy .never = some (.never, .never) := extend_never rfl
#guard fiberTy .never = some (.never, .never)
#guard fiberTy fiberOrNever = some (.nat, .string)
#guard fiberTy literalOrString = some (.string, .never)

-- Red: two fiber types with no order, and a type that is no fiber type.
#guard fiberTy twoFibers = none
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

-- Red: two fiber types with no order are refused, as no fiber (decisions row 292). The guard
-- refuses: the lifted rule answers at that type (above).
#guard explain nativeSignature [twoFibers] (.awaitFiber (.var 0) .joinEffect) =
  some ⟨[], .notFiber twoFibers⟩
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

/-! ## The closed program of the design note: admitted, at the type it had

An atom's scheme infers on the raw type of its argument. So the checker admits a type and can
refuse that type's normal form (decisions row 294, point 4). The guarded rule alone answers a
normal form, and it would refuse this program. The extended rule keeps the member rule's raw
answer, so the program keeps its type. -/

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

/-- The body's answer, as the checker spells it: a product over a union, and no normal form. -/
def rawEntries : Ty := .list (.prod (.lit "k") (.union .nat .string))

/-- The same type's normal form: a union of two products. -/
def normalEntries : Ty := .list (.union (.prod (.lit "k") .nat) (.prod (.lit "k") .string))

#guard Checker.check nativeSignature [] [] body = .ok ⟨rawEntries, .never, Requirement.empty⟩
#guard rawEntries.normalize = normalEntries
#guard rawEntries != normalEntries

-- Green: the checker admits the program, at the type it had before the conversion.
#guard fiberTy (.fiberOf rawEntries .never) = some (rawEntries, .never)
#guard Checker.check nativeSignature [] [] joinsEntries =
  .ok ⟨.map .string (.union .nat .string), .never, Requirement.empty⟩

-- Red: the guarded rule alone answers the normal form of the value column. The last line is
-- admitted at the raw type and refused at its normal form: the scheme of `mapFromEntries` binds
-- its parameter at the first union member, `nat`.
#guard liftOne Member.fiber (.fiberOf rawEntries .never) = some (normalEntries, .never)
#guard Checker.check nativeSignature [.fiberOf rawEntries .never, rawEntries] [] useEntries =
  .ok ⟨.map .string (.union .nat .string), .never, Requirement.empty⟩
#guard explain nativeSignature [.fiberOf rawEntries .never, normalEntries] useEntries =
  some ⟨[], .term (.app "mapFromEntries" (.cons (.var 1) .nil))⟩
#guard NativeAtom.typeOf .mapFromEntries [rawEntries] = some (.map .string (.union .nat .string))
#guard NativeAtom.typeOf .mapFromEntries [normalEntries] = none

/-! ## The contract at the fiber rule, by projection -/

/-- **The contract of the fiber rule**: `Eliminator.extend_laws` at `Member.fiber_eliminator`,
with the order of a pair spelled by column. The rule agrees with its member rule. Where the
member rule refuses, it is the guarded rule. It answers a least pair at `never`. Its answer is
the least pair of columns with the handle type below their fiber type. It refuses a proper union
that the member rule refuses. -/
theorem fiberTy_contract :
    (∀ {t : Ty} {a : Ty × Ty}, Member.fiber t = some a → fiberTy t = some a) ∧
    (∀ {t : Ty}, Member.fiber t = none → fiberTy t = liftOne Member.fiber t) ∧
    (∃ a : Ty × Ty, fiberTy .never = some a ∧
      ∀ b : Ty × Ty, Ty.subN a.1 b.1 = true ∧ Ty.subN a.2 b.2 = true) ∧
    (∀ {t : Ty} {a : Ty × Ty}, fiberTy t = some a →
      Ty.subN t (.fiberOf a.1 a.2) = true ∧
      ∀ b : Ty × Ty, (Ty.subN a.1 b.1 = true ∧ Ty.subN a.2 b.2 = true) ↔
        Ty.subN t (.fiberOf b.1 b.2) = true) ∧
    (∀ {t : Ty}, Member.fiber t = none → 1 < t.normalize.members.length → fiberTy t = none) :=
  Member.fiber_eliminator.extend_laws

/-- The fiber rule answers exactly at a raw fiber type, or at a type with at most one union
member in its normal form that is below a fiber type. -/
theorem fiberTy_isSome_iff (t : Ty) :
    (fiberTy t).isSome = true ↔
      (Member.fiber t).isSome = true ∨
        (t.normalize.members.length ≤ 1 ∧ ∃ b : Ty × Ty, Ty.subN t (.fiberOf b.1 b.2) = true) :=
  Member.fiber_eliminator.extend_isSome_iff t

/-- **The raw answer of the fiber rule is a matter of spelling.** Where the fiber rule answers,
the guarded rule alone answers too, and each answer is below the other by column. So the removal
of the raw answer changes no verdict of the fiber rule (decisions row 294). It changes what a
later rule reads: the closed program above. -/
theorem fiberTy_liftOne {t : Ty} {a : Ty × Ty} (typed : fiberTy t = some a) :
    ∃ a' : Ty × Ty, liftOne Member.fiber t = some a' ∧
      (Ty.subN a.1 a'.1 = true ∧ Ty.subN a.2 a'.2 = true) ∧
      (Ty.subN a'.1 a.1 = true ∧ Ty.subN a'.2 a.2 = true) :=
  (Member.fiber_eliminator.extend_liftOne (fun answered => Member.fiber_one answered)).1 typed

/-- What the fiber rule keeps of the monotone law: a smaller handle type with at most one union
member in its normal form. -/
theorem fiberTy_mono {s t : Ty} (smaller : Ty.subN s t = true)
    (one : s.normalize.members.length ≤ 1) {b : Ty × Ty} (typed : fiberTy t = some b) :
    ∃ a : Ty × Ty, fiberTy s = some a ∧ Ty.subN a.1 b.1 = true ∧ Ty.subN a.2 b.2 = true :=
  Member.fiber_eliminator.extend_mono smaller one typed

-- Red: without the premise the monotone law fails. A proper union is below a fiber type, the
-- rule answers at the fiber type, and it refuses the union.
#guard Ty.subN twoFibers (.fiberOf (.union .nat .string) .bool)
#guard fiberTy (.fiberOf (.union .nat .string) .bool) = some (.union .nat .string, .bool)
#guard fiberTy twoFibers = none

/-! ## The member rule at one union member: which constructors have the premise

`Member.fiber_one` is the premise of `Eliminator.extend_liftOne`: the member rule answers only
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

/-! ## Closed types -/

/-- A fiber type that is closed has closed columns: the member fact. -/
theorem fiber_closed {m : Ty} {a : Ty × Ty} (closed : m.closed = true)
    (answered : Member.fiber m = some a) : a.1.closed = true ∧ a.2.closed = true := by
  cases m with
  | fiberOf value error =>
    cases answered
    exact Bool.and_eq_true_iff.mp closed
  | _ => exact nomatch answered

/-- **A closed handle type has a closed value type and a closed error type.** The proof reads
the fiber rule by its two alternatives (`extend_eq_some_iff`): the member fact at the raw
answer, and `lift_closed_pair` at the guarded rule's answer. -/
theorem fiberTy_closed {t : Ty} {a : Ty × Ty} (typed : fiberTy t = some a)
    (closed : t.closed = true) : a.1.closed = true ∧ a.2.closed = true := by
  rcases (extend_eq_some_iff Member.fiber).mp typed with answered | ⟨-, lifted⟩
  · exact fiber_closed closed answered
  · exact lift_closed_pair (fun _ _ closed answered => fiber_closed closed answered)
      (liftOne_some lifted) closed

end Effect4.Test.Eliminators
