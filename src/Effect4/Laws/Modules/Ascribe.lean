import Effect4.Program.Authoring.Ascribe
import Effect4.Laws.Modules.Checking
import Effect4.Laws.Auto.Semantics

/-!
# A term at a declared type: what an ascription types at, and what it reads

`ascribe T e` (`src/Effect4/Program/Authoring/Ascribe.lean`) is a record with one field
declared at `T` that holds `e`, and a read of that field. This file gives the form its two
builder rules, beside the rules of a construction and of a field's read
(`src/Effect4/Laws/Modules/Checking.lean`, `src/Effect4/Laws/Modules/Reading.lean`). It names
no module.

- **`types_ascribe`**: the form has its declared type under each literal flag, where the type
  of `e` is below it. The premise on `e` is at the record's own flag, the flag of a
  const-generic position. So a string literal is a term for this rule: its type there is its
  literal type, and its ascription at `string` has one type under each flag.
- **`ascribe_untyped`**: the form has no type where the type of `e` is not below the declared
  type. With the rule above, the record's check decides the form: it is no cast.
- **`reads_ascribe`**: the form reads what `e` reads.

Placement.

| Statement | Concept; requirement | Reach | It does not establish | Consumer |
| --- | --- | --- | --- | --- |
| `types_ascribe`, `ascribe_untyped` | `store-typing`; R4: helpers of a module's typing statements | the checker's `argTy` at every scope and every signature, for a declared type in normal form whose one-field declaration is formed | program admission, a run, a target's type, `Ref.make<A>` | a cell made at a declared type: the scenarios' logs (`Test/Dogfood/Scenario/`), and the public `make` of a later module |
| `reads_ascribe` | `translation-simulation`; R10: a helper of a module expansion's reading | one evaluation of the form's tree, at every scope | typing, a store step, a model's step | the attempt law of a caller that makes its cell at a declared type |

The finite controls are in `Test/Program/Ascribe.lean`.
-/

set_option autoImplicit false

namespace Effect4.Modules

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring

variable {Op : Type} {sig : Signature Op} {env : Env} {path : List Nat} {types : List Ty}

/-! ## The record's check at one declared field -/

/-- The one-field declaration at a type in normal form is its own normal form. -/
theorem ascribeFields_normal {T : Ty} (canonical : T.normalize = T) :
    Ty.normalize (.record (ascribeFields T)) = .record (ascribeFields T) := by
  rw [Ty.normalize_record]
  show Ty.record [("v", false, Ty.normalize T)] = _
  rw [canonical]
  rfl

/-- **The record's check at one declared field is the checker's order**: the supplied type,
normalized, is below the declared type, normalized. The check answers the declaration's normal
form there, and it refuses everywhere else. -/
theorem ascribe_check (S T : Ty) :
    Record.check (ascribeFields T) ["v"] [S] =
      if Ty.subN S T = true then some (Ty.normalize (.record (ascribeFields T))) else none := by
  have fit : Record.argumentsFit (ascribeFields T) [("v", S)] = Ty.subN S T := by
    show ((Field.firstOf "v" (ascribeFields T)).isSome && true &&
      ((match Field.firstOf "v" [("v", S)] with
        | none => false
        | some actual => Ty.sub actual.normalize T.normalize) && true)) = Ty.subN S T
    have declared : Field.firstOf "v" (ascribeFields T) = some (false, T) := rfl
    have supplied : Field.firstOf "v" [("v", S)] = some S := rfl
    rw [declared, supplied]
    show (true && true && (Ty.sub S.normalize T.normalize && true)) = Ty.subN S T
    rw [Bool.and_true, Bool.and_true, Bool.true_and]
    rfl
  have distinct : (["v"] : List String).Nodup := by decide
  show (if ((ascribeFields T).map Prod.fst).Nodup ∧ (["v"] : List String).Nodup ∧
      Record.argumentsFit (ascribeFields T) [("v", S)] = true then
    some (Ty.normalize (.record (ascribeFields T))) else none) = _
  rw [fit]
  by_cases below : Ty.subN S T = true
  · rw [if_pos below]
    exact if_pos ⟨distinct, distinct, below⟩
  · rw [if_neg below]
    exact if_neg fun accepted => below accepted.2.2

/-! ## The typing rule -/

/-- **An ascription has its declared type.** At a scope, let `e` have the type `S` inside a
const-generic position: a record's value is typed there. Let the declared type `T` be its own
normal form, with a formed one-field declaration, and let `S` be below `T` in the checker's
order: the record's check. Then `ascribe T e` has the type `T` under each literal flag.

Reach: the checker's `argTy` at every scope and every signature. The premise on `e` is at one
flag, so a string literal is a term for this rule. It does not establish program admission, a
run or a target's type, and it is no rule of `Ref.make<A>`. -/
@[semantics "store-typing" (requirement := R4)]
theorem types_ascribe {e : TermSrc} {S T : Ty} (canonical : T.normalize = T)
    (formed : Formation.check (Formation.sites false [] (.record (ascribeFields T))) = none)
    (he : Types sig e env path types true S) (below : Ty.subN S T = true) :
    TypesEach sig (ascribe T e) env path types T := by
  intro const
  have normal := ascribeFields_normal canonical
  have checked : Record.check (ascribeFields T) ["v"] [S] =
      some (Ty.normalize (.record (ascribeFields T))) := by
    rw [ascribe_check, if_pos below]
  have built : Types sig (record (ascribeFields T) [("v", e)]) env path types false
      (.record (ascribeFields T)) :=
    (types_record (present := [("v", e)]) formed
      (show TypesAll sig [e] env path types true [S] from .cons he .nil) checked).to normal
  exact types_field built (Record.fieldType_normal normal rfl)

/-- **An ascription is no cast.** Where the type of `e` is not below the declared type, the
checker has no type for `ascribe T e`, under either literal flag. With `types_ascribe`, the
record's check decides the form.

Reach: the checker's `argTy` at every scope and every signature, for a term `e` that has a type
inside a const-generic position. It says nothing of a term that has no type there. -/
@[semantics "store-typing" (requirement := R4)]
theorem ascribe_untyped {e : TermSrc} {S T : Ty} (he : Types sig e env path types true S)
    (above : Ty.subN S T = false) (const : Bool) (U : Ty) :
    ¬ Types sig (ascribe T e) env path types const U := by
  obtain ⟨t, tree, typed⟩ := he
  rintro ⟨whole, elaborated, answered⟩
  have shape : ascribe T e env path =
      .ok (.field .required (.record (ascribeFields T) ["v"] (termsOfList [t])) "v") := by
    show ((([("v", e)] : List (String × TermSrc)).mapM (fun entry => entry.2 env path) >>=
        fun values => Except.ok (Term.record (ascribeFields T) ["v"] (termsOfList values))) >>=
      fun value => Except.ok (Term.field .required value "v")) = _
    rw [mapM_ok _ [("v", e)] [t] (.cons tree .nil)]
    rfl
  rw [shape] at elaborated
  cases elaborated
  have values : argsTy sig types true (termsOfList [t]) = some [S] :=
    argsTy_ok sig types true [t] [S] (.cons typed .nil)
  have refused : argTy sig types false (.record (ascribeFields T) ["v"] (termsOfList [t])) =
      none := by
    show (match Formation.check (Formation.sites false [] (.record (ascribeFields T))) with
      | some _ => none
      | none => (argsTy sig types true (termsOfList [t])).bind
          (Record.check (ascribeFields T) ["v"])) = none
    split
    · rfl
    · rw [values, Option.bind_some, ascribe_check, above]
      rfl
  have none : argTy sig types const
      (.field .required (.record (ascribeFields T) ["v"] (termsOfList [t])) "v") = none := by
    show (argTy sig types false (.record (ascribeFields T) ["v"] (termsOfList [t]))).bind
      (fun type => Record.fieldType (decide (FieldReadMode.required = .optional)) type "v") = none
    rw [refused]
    rfl
  rw [none] at answered
  cases answered

/-! ## The reading rule -/

/-- **An ascription reads what its term reads.** The record's construction builds the frame of
one field, and the field's read answers the value that the field holds: the declared type takes
no part in the evaluation.

Reach: one evaluation of the form's tree, at every scope and every environment of values. It
does not establish typing, a store step or a model's step. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem reads_ascribe (T : Ty) {e : TermSrc} {vals : List Val} {v : Val}
    (he : Reads e env path vals v) : Reads (ascribe T e) env path vals v :=
  reads_field
    (reads_record (fields := ascribeFields T) (present := [("v", e)]) (.cons he .nil)
      (show Machine.Record.build ["v"] [v] = some (Machine.Record.frame [("v", v)]) from rfl))
    (show Machine.Record.read false (Machine.Record.frame [("v", v)]) "v" = some v from rfl)

end Effect4.Modules
