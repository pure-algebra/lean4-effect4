import Effect4.Program.Native
import Effect4.Laws.Program.TypeAlgebra
import Effect4.Laws.Program.TyView

/-!
# Laws.Program.Typing.TermIntro — the term checker's rules in their introduction form

The term checker is `argTy` and `argsTy` (`src/Effect4/Program/Typing/Rules.lean`), and `termTy`
is its projection outside a const-generic atom. The laws beside it are inversions: each reads a
successful check (`termTy_record_inv`, `termTy_fold_inv`,
`src/Effect4/Laws/Program/Typed.lean`). This file gives the other direction: from the parts'
types to the whole's type. Each rule is stated once, and it names no module.

- **Normal forms.** The types that a rule compares after `Ty.normalize`, written as their own
  normal forms: a list, an option, a product, a tuple and a record's fields.
- **Templates.** `Ty.matchTemplate` at a parameter's first and second occurrence.
- **Native calls.** `nativeAtomTy` at a symbolic list, option, pair or tuple type, for the
  atoms that a step term uses. `ite` has two rules: its second arm above the first, and below
  it.
- **Nodes.** One rule for each node of `argTy`: an application, a field's read, an overwrite, a
  construction and a fold. Each keeps the literal flag of the checker.
- **Records.** `Record.fieldType`, `Record.setType` and `Record.check` at a record type in
  normal form. The field list is a parameter, and each side condition is decidable or a named
  premise, so a new cell's instance is one application.

Placement. Concept `store-typing`, requirement R4. Every rule here is a helper of the five
typing statements of the Queue's steps (`src/Effect4/Laws/Modules/Queue/Typing.lean`), and each
docstring names a step that uses it. Their consumers are the judgment `Types` and its builder
lemmas (`src/Effect4/Laws/Modules/Queue/Checking.lean`). A second composed module takes the
same rules.

Reach. Each rule is an equation of the checker. `Ty.sub` and `Ty.normalize` are well-founded,
so a rule rewrites with their lemmas and never by evaluation at a symbolic type. The rules
establish nothing of evaluation, of a value's membership or of a target. The checker's typing
of a term is not program admission.
-/

set_option autoImplicit false

namespace Effect4.Program

/-! ## Types in normal form -/

namespace Ty

/-- A type that is its own normal form has the construction invariant. Used by the take step's
reply, a tuple of three. -/
theorem normal_of_canonical {t : Ty} (canonical : t.normalize = t) : Normal t := by
  rw [← canonical]
  exact normal_normalize t

/-- A list of a type in normal form is its own normal form. Used by every step: the cell's
buffer. -/
theorem normalize_list_canonical {t : Ty} (canonical : t.normalize = t) :
    normalize (.list t) = .list t := by
  show Ty.list (normalize t) = _
  rw [canonical]

/-- An option of a type in normal form is its own normal form. Used by the poll step's reply. -/
theorem normalize_option_canonical {t : Ty} (canonical : t.normalize = t) :
    normalize (.option t) = .option t := by
  show Ty.option (normalize t) = _
  rw [canonical]

/-- A product of two types in normal form, neither a union, is its own normal form. Used by
every step: the pair of a reply and the cell's value. -/
theorem normalize_prod_canonical {a b : Ty} (ha : a.normalize = a) (hb : b.normalize = b)
    (fa : isFactor a = true) (fb : isFactor b = true) : normalize (.prod a b) = .prod a b :=
  (Normal.prod (normal_of_canonical ha) (normal_of_canonical hb) fa fb).fixed

/-- A tuple of two normalizes to the product. Used by the poll step's and the offer step's
reply. -/
theorem normalize_pair_canonical {a b : Ty} (ha : a.normalize = a) (hb : b.normalize = b)
    (fa : isFactor a = true) (fb : isFactor b = true) : normalize (.tuple [a, b]) = .prod a b := by
  rw [normalize_tuple_pair]
  exact normalize_prod_canonical ha hb fa fb

/-- A tuple of types in normal form, of any arity but two, is its own normal form. Used by the
take step's reply. -/
theorem normalize_tuple_canonical {ts : List Ty} (items : ∀ t ∈ ts, t.normalize = t)
    (arity : ts.length ≠ 2) : normalize (.tuple ts) = .tuple ts := by
  rw [normalize_tuple_of_ne ts arity, normalizeItems_eq_map]
  exact congrArg Ty.tuple ((List.map_congr_left items).trans (List.map_id ts))

/-- A tuple of three types in normal form is its own normal form: the instance that the take
step's reply reads. -/
theorem normalize_triple_canonical {a b c : Ty} (ha : a.normalize = a) (hb : b.normalize = b)
    (hc : c.normalize = c) : normalize (.tuple [a, b, c]) = .tuple [a, b, c] := by
  refine normalize_tuple_canonical (fun t member => ?_) (show (3 : Nat) ≠ 2 by decide)
  rcases List.mem_cons.mp member with rfl | member
  · exact ha
  rcases List.mem_cons.mp member with rfl | member
  · exact hb
  rcases List.mem_cons.mp member with rfl | member
  · exact hc
  · exact absurd member List.not_mem_nil

/-- **A record type in normal form**: its fields are in the canonical order, and each field's
type is its own normal form. Used by every record rule below. -/
theorem record_normal_fields {fields : List (String × Bool × Ty)}
    (normal : normalize (.record fields) = .record fields) :
    Field.Ascending Field.bytesKey fields ∧ ∀ p ∈ fields, p.2.2.normalize = p.2.2 := by
  have mapped : (canon fields).map (fun q => (q.1, normPayload q.2)) = fields := by
    have unfolded := normal
    rw [normalize_record] at unfolded
    exact Ty.record.inj unfolded
  constructor
  · rw [← mapped]
    exact Field.ascending_map normPayload (Field.canonBy_ascending fields)
  · intro p member
    rw [← mapped] at member
    obtain ⟨q, -, rfl⟩ := List.mem_map.mp member
    exact normalize_idem q.2.2

/-- Two types in normal form, each below the other, are one type. Used by `ite` at an arm
below. -/
theorem eq_of_sub_of_sub {a b : Ty} (ha : a.normalize = a) (hb : b.normalize = b)
    (hab : sub a b = true) (hba : sub b a = true) : a = b :=
  congrArg Subtype.val (sub_antisymm_canonical ⟨a, ha⟩ ⟨b, hb⟩ hab hba)

/-- Among the types in normal form, nothing but the empty union is below it. Used by `cons` on
the empty list. -/
theorem eq_never_of_sub_never {t : Ty} (canonical : t.normalize = t)
    (below : sub t .never = true) : t = .never :=
  eq_of_sub_of_sub canonical rfl below (OrderProof.sub_never t)

/-- The order under a list head. -/
theorem sub_list (a b : Ty) : sub (.list a) (.list b) = sub a b := by
  rw [sub_args_list]
  show (sub a b && true) = sub a b
  rw [Bool.and_true]

/-- The order under an option head. -/
theorem sub_option (a b : Ty) : sub (.option a) (.option b) = sub a b := by
  rw [sub_args_option]
  show (sub a b && true) = sub a b
  rw [Bool.and_true]

/-- The order under a product head. -/
theorem sub_prod (a1 a2 b1 b2 : Ty) :
    sub (.prod a1 a2) (.prod b1 b2) = (sub a1 b1 && sub a2 b2) := by
  rw [sub_args_prod]
  show (sub a1 b1 && (sub a2 b2 && true)) = (sub a1 b1 && sub a2 b2)
  rw [Bool.and_true]

/-- A tuple is below a tuple of its arity whose items are above its own, one by one. Used by
the take step: the reply of the arm that waits is below the reply of the arm that consumes. -/
theorem sub_tuple_of_items {xs ys : List Ty} (arity : xs.length = ys.length)
    (items : ∀ p ∈ xs.zip ys, sub p.1 p.2 = true) : sub (.tuple xs) (.tuple ys) = true := by
  rw [sub_args_tuple xs ys (by simp only [sameHead, arity, decide_true])]
  unfold argsBelow
  simp only [args]
  rw [List.zip_map, List.all_map, List.all_eq_true]
  intro p member
  exact items p member

/-! ## Templates: a parameter's first and second occurrence -/

/-- A match answers the bindings that inference reads, where the instance is the request. -/
theorem matchTemplate_exact {σ σ' : Subst} {template request : Ty} {join : Bool}
    (inferred : infer σ template request join = σ')
    (same : instantiate σ' template = request) :
    matchTemplate σ template request join = some σ' := by
  subst inferred
  show (if sub request.normalize
      (instantiate (infer σ template request join) template).normalize = true
    then some (infer σ template request join) else none) = _
  exact if_pos (by rw [same]; exact sub_refl _)

/-- A match answers the bindings that inference reads, where the request is below the instance
in the checker's order. -/
theorem matchTemplate_below {σ σ' : Subst} {template request : Ty} {join : Bool}
    (inferred : infer σ template request join = σ')
    (below : sub request.normalize (instantiate σ' template).normalize = true) :
    matchTemplate σ template request join = some σ' := by
  subst inferred
  show (if sub request.normalize
      (instantiate (infer σ template request join) template).normalize = true
    then some (infer σ template request join) else none) = _
  exact if_pos below

/-- A parameter that no binding names binds to the request. -/
theorem infer_var_fresh {σ : Subst} {i : Nat} (request : Ty) (join : Bool)
    (fresh : σ.lookup i = none) : infer σ (.var i) request join = σ ++ [(i, request)] := by
  have unfolded := infer.eq_1 σ request join i
  rw [fresh] at unfolded
  exact unfolded

/-- A bound parameter, met again: under the join rule the binding moves to a request above
it, and it stays otherwise. -/
theorem infer_var_bound {σ : Subst} {i : Nat} {bound : Ty} (request : Ty) (join : Bool)
    (held : σ.lookup i = some bound) :
    infer σ (.var i) request join =
      if (join && sub bound request) = true then (i, request) :: σ else σ := by
  have unfolded := infer.eq_1 σ request join i
  rw [held] at unfolded
  exact unfolded

/-- A bound parameter, met again under the join rule at a request above its binding: the
binding moves up. -/
theorem infer_var_join_above {σ : Subst} {i : Nat} {bound request : Ty}
    (held : σ.lookup i = some bound) (above : sub bound request = true) :
    infer σ (.var i) request true = (i, request) :: σ := by
  have unfolded := infer_var_bound request true held
  rw [above] at unfolded
  exact unfolded

/-- A bound parameter, met again under the join rule at a request not above its binding: the
binding stays. -/
theorem infer_var_join_below {σ : Subst} {i : Nat} {bound request : Ty}
    (held : σ.lookup i = some bound) (notAbove : sub bound request = false) :
    infer σ (.var i) request true = σ := by
  have unfolded := infer_var_bound request true held
  rw [notAbove] at unfolded
  exact unfolded

/-- The first occurrence of the parameter `0` binds it to the request. -/
theorem matchTemplate_var_first (X : Ty) (join : Bool) :
    matchTemplate [] (.var 0) X join = some [(0, X)] := by
  refine matchTemplate_exact ?_ rfl
  exact infer_var_fresh X join rfl

/-- The first occurrence of the parameter `0` under a list head binds it to the element's
type. -/
theorem matchTemplate_list_first (X : Ty) (join : Bool) :
    matchTemplate [] (.list (.var 0)) (.list X) join = some [(0, X)] := by
  refine matchTemplate_exact ?_ rfl
  show infer [] (.var 0) X join = [(0, X)]
  exact infer_var_fresh X join rfl

/-- A number parameter at a number binds nothing. -/
theorem matchTemplate_nat (σ : Subst) (join : Bool) :
    matchTemplate σ .nat .nat join = some σ :=
  matchTemplate_exact rfl rfl

/-- A Boolean parameter at a Boolean binds nothing. -/
theorem matchTemplate_bool (σ : Subst) (join : Bool) :
    matchTemplate σ .bool .bool join = some σ :=
  matchTemplate_exact rfl rfl

end Ty

/-! ## Native calls at a symbolic type

One rule for each atom that a step term of the Queue uses. A template atom is read through
`Ty.matchTemplateArgs`, a fixed signature through `NativeAtom.monoApply`. -/

/-- A fixed signature answers at its own parameters. Used by `isZero`, `not`, `and`, `or`, `lt`
and `sub` in every step. -/
theorem NativeAtom.monoApply_self (params : List Ty) (answer : Ty) :
    NativeAtom.monoApply params answer params = some answer := by
  unfold NativeAtom.monoApply
  refine if_pos ⟨rfl, List.all_eq_true.mpr fun pair member => ?_⟩
  obtain ⟨a, e⟩ := pair
  have same : a = e := Ty.mem_zip_self member
  subst same
  exact Ty.sub_refl a

theorem nativeAtomTy_nil : nativeAtomTy "nil" [] = some (.list .never) := rfl

theorem nativeAtomTy_none : nativeAtomTy "none" [] = some (.option .never) := rfl

theorem nativeAtomTy_isZero : nativeAtomTy "isZero" [.nat] = some .bool :=
  NativeAtom.monoApply_self [.nat] .bool

theorem nativeAtomTy_not : nativeAtomTy "not" [.bool] = some .bool :=
  NativeAtom.monoApply_self [.bool] .bool

theorem nativeAtomTy_and : nativeAtomTy "and" [.bool, .bool] = some .bool :=
  NativeAtom.monoApply_self [.bool, .bool] .bool

theorem nativeAtomTy_or : nativeAtomTy "or" [.bool, .bool] = some .bool :=
  NativeAtom.monoApply_self [.bool, .bool] .bool

theorem nativeAtomTy_lt : nativeAtomTy "lt" [.nat, .nat] = some .bool :=
  NativeAtom.monoApply_self [.nat, .nat] .bool

theorem nativeAtomTy_sub : nativeAtomTy "sub" [.nat, .nat] = some .nat :=
  NativeAtom.monoApply_self [.nat, .nat] .nat

/-- A list of any element type has a length. Used by the size step and by `isEmpty`. -/
theorem nativeAtomTy_length (T : Ty) : nativeAtomTy "length" [.list T] = some .nat := by
  show NativeAtom.monoApply [.list .unknown] .nat [.list T] = some .nat
  unfold NativeAtom.monoApply
  refine if_pos ⟨rfl, ?_⟩
  show (Ty.sub (.list T) (.list .unknown) && true) = true
  rw [Ty.sub_list, Ty.sub_unknown]
  rfl

/-- Two `Deferred` handles are compared, whatever each holds. Used by every pass that tests a
request's identity. -/
theorem nativeAtomTy_sameHandle_deferred (a e b f : Ty) :
    nativeAtomTy "sameHandle" [.deferredOf a e, .deferredOf b f] = some .bool := rfl

/-- Two `Ref` handles are compared, whatever each holds. -/
theorem nativeAtomTy_sameHandle_ref (a b : Ty) :
    nativeAtomTy "sameHandle" [.refOf a, .refOf b] = some .bool := rfl

/-- A tuple answers the normal form of the tuple type of its items. Used by every reply of two
or three parts. -/
theorem nativeAtomTy_tuple (types : List Ty) :
    nativeAtomTy "tuple" types = some (Ty.normalize (.tuple types)) := rfl

/-- `some` wraps its argument's type. Used by the offer step's decided answer. -/
theorem nativeAtomTy_some (X : Ty) : nativeAtomTy "some" [X] = some (.option X) := by
  show ((Ty.matchTemplate [] (.var 0) X false).bind fun σ => some σ).map
    (fun σ => Ty.instantiate σ (.option (.var 0))) = some (.option X)
  rw [Ty.matchTemplate_var_first]
  rfl

/-- A pair has the product of its two arguments' types. Used by every step of a `Ref.modify`:
the reply and the cell's next value. -/
theorem nativeAtomTy_pair (X Y : Ty) : nativeAtomTy "pair" [X, Y] = some (.prod X Y) := by
  have second : Ty.matchTemplate [(0, X)] (.var 1) Y false = some [(0, X), (1, Y)] := by
    refine Ty.matchTemplate_exact ?_ rfl
    exact Ty.infer_var_fresh Y false rfl
  show ((Ty.matchTemplate [] (.var 0) X false).bind fun σ =>
    (Ty.matchTemplate σ (.var 1) Y false).bind fun σ' => some σ').map
      (fun σ => Ty.instantiate σ (.prod (.var 0) (.var 1))) = some (.prod X Y)
  rw [Ty.matchTemplate_var_first, Option.bind_some, second]
  rfl

/-- `take` keeps a list's type. Used by `noneOf`, `wake` and `entering`. -/
theorem nativeAtomTy_take (X : Ty) : nativeAtomTy "take" [.list X, .nat] = some (.list X) := by
  show ((Ty.matchTemplate [] (.list (.var 0)) (.list X) false).bind fun σ =>
    (Ty.matchTemplate σ .nat .nat false).bind fun σ' => some σ').map
      (fun σ => Ty.instantiate σ (.list (.var 0))) = some (.list X)
  rw [Ty.matchTemplate_list_first, Option.bind_some, Ty.matchTemplate_nat]
  rfl

/-- `drop` keeps a list's type. Used by `staying` and by the buffer after a consumed message. -/
theorem nativeAtomTy_drop (X : Ty) : nativeAtomTy "drop" [.list X, .nat] = some (.list X) := by
  show ((Ty.matchTemplate [] (.list (.var 0)) (.list X) false).bind fun σ =>
    (Ty.matchTemplate σ .nat .nat false).bind fun σ' => some σ').map
      (fun σ => Ty.instantiate σ (.list (.var 0))) = some (.list X)
  rw [Ty.matchTemplate_list_first, Option.bind_some, Ty.matchTemplate_nat]
  rfl

/-- `get` answers an option of a list's element type. Used by the take step's and the poll
step's message. -/
theorem nativeAtomTy_get (X : Ty) : nativeAtomTy "get" [.list X, .nat] = some (.option X) := by
  show ((Ty.matchTemplate [] (.list (.var 0)) (.list X) false).bind fun σ =>
    (Ty.matchTemplate σ .nat .nat false).bind fun σ' => some σ').map
      (fun σ => Ty.instantiate σ (.option (.var 0))) = some (.option X)
  rw [Ty.matchTemplate_list_first, Option.bind_some, Ty.matchTemplate_nat]
  rfl

/-- Two lists of one element type append to a list of that type. Used by `snoc` and
`gained`. -/
theorem nativeAtomTy_append (X : Ty) :
    nativeAtomTy "append" [.list X, .list X] = some (.list X) := by
  have second : Ty.matchTemplate [(0, X)] (.list (.var 0)) (.list X) true =
      some [(0, X), (0, X)] := by
    refine Ty.matchTemplate_exact ?_ rfl
    show Ty.infer [(0, X)] (.var 0) X true = [(0, X), (0, X)]
    exact Ty.infer_var_join_above rfl (Ty.sub_refl X)
  show ((Ty.matchTemplate [] (.list (.var 0)) (.list X) true).bind fun σ =>
    (Ty.matchTemplate σ (.list (.var 0)) (.list X) true).bind fun σ' => some σ').map
      (fun σ => Ty.instantiate σ (.list (.var 0))) = some (.list X)
  rw [Ty.matchTemplate_list_first, Option.bind_some, second]
  rfl

/-- **`cons` onto the empty list** answers a list of the element's type, where that type is its
own normal form. The tail's element type is the empty union: it replaces the element's binding
only where the element's type is below it, and then both are the empty union. Used by `snoc`. -/
theorem nativeAtomTy_cons_nil {X : Ty} (canonical : X.normalize = X) :
    nativeAtomTy "cons" [X, .list .never] = some (.list X) := by
  show ((Ty.matchTemplate [] (.var 0) X true).bind fun σ =>
    (Ty.matchTemplate σ (.list (.var 0)) (.list .never) true).bind fun σ' => some σ').map
      (fun σ => Ty.instantiate σ (.list (.var 0))) = some (.list X)
  rw [Ty.matchTemplate_var_first, Option.bind_some]
  cases empty : Ty.sub X .never with
  | true =>
    have isNever : X = .never := Ty.eq_never_of_sub_never canonical empty
    subst isNever
    have second : Ty.matchTemplate [(0, .never)] (.list (.var 0)) (.list .never) true =
        some [(0, .never), (0, .never)] := by
      refine Ty.matchTemplate_exact ?_ rfl
      show Ty.infer [(0, .never)] (.var 0) .never true = [(0, .never), (0, .never)]
      exact Ty.infer_var_join_above rfl (Ty.sub_refl .never)
    rw [second]
    rfl
  | false =>
    have second : Ty.matchTemplate [(0, X)] (.list (.var 0)) (.list .never) true =
        some [(0, X)] := by
      refine Ty.matchTemplate_below ?_ ?_
      · show Ty.infer [(0, X)] (.var 0) .never true = [(0, X)]
        exact Ty.infer_var_join_below rfl empty
      · show Ty.sub (.list .never) (.list X.normalize) = true
        rw [Ty.sub_list]
        exact Ty.OrderProof.sub_never _
    rw [second]
    rfl

/-- **`ite` at an arm above**: where the first arm's type is below the second's, the answer is
the second arm's type. Used by the offer step's outer selection, and at two equal arms by
`wake`. -/
theorem nativeAtomTy_ite_above {X Y : Ty} (above : Ty.sub X Y = true) :
    nativeAtomTy "ite" [.bool, X, Y] = some Y := by
  have third : Ty.matchTemplate [(0, X)] (.var 0) Y true = some [(0, Y), (0, X)] := by
    refine Ty.matchTemplate_exact ?_ rfl
    exact Ty.infer_var_join_above rfl above
  show ((Ty.matchTemplate [] .bool .bool true).bind fun σ =>
    (Ty.matchTemplate σ (.var 0) X true).bind fun σ' =>
      (Ty.matchTemplate σ' (.var 0) Y true).bind fun σ'' => some σ'').map
        (fun σ => Ty.instantiate σ (.var 0)) = some Y
  rw [Ty.matchTemplate_bool, Option.bind_some, Ty.matchTemplate_var_first, Option.bind_some,
    third]
  rfl

/-- `ite` at two arms of one type answers that type. -/
theorem nativeAtomTy_ite_self (X : Ty) : nativeAtomTy "ite" [.bool, X, X] = some X :=
  nativeAtomTy_ite_above (Ty.sub_refl X)

/-- **`ite` at an arm below**: where the second arm's type is below the first's, and both are
their own normal forms, the answer is the first arm's type. Used by the take step and the poll
step: the arm that waits answers no message. -/
theorem nativeAtomTy_ite_below {X Y : Ty} (hX : X.normalize = X) (hY : Y.normalize = Y)
    (below : Ty.sub Y X = true) : nativeAtomTy "ite" [.bool, X, Y] = some X := by
  cases above : Ty.sub X Y with
  | true =>
    have same : X = Y := Ty.eq_of_sub_of_sub hX hY above below
    subst same
    exact nativeAtomTy_ite_self X
  | false =>
    have third : Ty.matchTemplate [(0, X)] (.var 0) Y true = some [(0, X)] := by
      refine Ty.matchTemplate_below ?_ ?_
      · exact Ty.infer_var_join_below rfl above
      · show Ty.sub Y.normalize X.normalize = true
        rw [hX, hY]
        exact below
    show ((Ty.matchTemplate [] .bool .bool true).bind fun σ =>
      (Ty.matchTemplate σ (.var 0) X true).bind fun σ' =>
        (Ty.matchTemplate σ' (.var 0) Y true).bind fun σ'' => some σ'').map
          (fun σ => Ty.instantiate σ (.var 0)) = some X
    rw [Ty.matchTemplate_bool, Option.bind_some, Ty.matchTemplate_var_first, Option.bind_some,
      third]
    rfl

/-! ## The checker's nodes

One rule for each node of `argTy` that a step term uses. The conclusion holds under each
literal flag, because the flag reaches a literal and no other node. Each premise stands at the
flag that the node gives its part: the atom's own flag for an application's arguments, `true`
for a construction's values and an overwrite's value, and `false` elsewhere. -/

section Nodes

variable {Op : Type} {sig : Signature Op} {env : TyEnv}

/-- **An application**: its arguments under the atom's own flag, then the atom's answer. -/
theorem argTy_app_intro (const : Bool) {atom : String} {args : Terms} {types : List Ty}
    {answer : Ty} (hargs : argsTy sig env (sig.constAtom atom) args = some types)
    (hatom : sig.atomOf atom types = some answer) :
    argTy sig env const (.app atom args) = some answer := by
  show (argsTy sig env (sig.constAtom atom) args).bind (sig.atomOf atom) = some answer
  rw [hargs]
  exact hatom

/-- The arguments' types, a head and a tail. -/
theorem argsTy_cons_intro {const : Bool} {head : Term} {tail : Terms} {type : Ty}
    {rest : List Ty} (hhead : argTy sig env const head = some type)
    (htail : argsTy sig env const tail = some rest) :
    argsTy sig env const (.cons head tail) = some (type :: rest) := by
  rw [argsTy_cons, hhead, Option.bind_some, htail, Option.bind_some]

/-- **A field's read**: the target outside a const-generic position, then the record rule. -/
theorem argTy_field_intro (const : Bool) {mode : FieldReadMode} {target : Term} {name : String}
    {record answer : Ty} (htarget : argTy sig env false target = some record)
    (hfield : Record.fieldType (decide (mode = .optional)) record name = some answer) :
    argTy sig env const (.field mode target name) = some answer := by
  show (argTy sig env false target).bind
    (fun type => Record.fieldType (decide (mode = .optional)) type name) = some answer
  rw [htarget]
  exact hfield

/-- **An overwrite**: the target outside a const-generic position, the value inside one, then
the record rule. -/
theorem argTy_recordSet_intro (const : Bool) {target value : Term} {name : String}
    {record replacement answer : Ty} (htarget : argTy sig env false target = some record)
    (hvalue : argTy sig env true value = some replacement)
    (hset : Record.setType record name replacement = some answer) :
    argTy sig env const (.recordSet target name value) = some answer := by
  show (argTy sig env false target).bind (fun targetType =>
    (argTy sig env true value).bind fun valueType =>
      Record.setType targetType name valueType) = some answer
  rw [htarget, Option.bind_some, hvalue]
  exact hset

/-- **A construction**: the raw declaration is formed, the values are typed inside a
const-generic position, and the record rule answers. -/
theorem argTy_record_intro (const : Bool) {fields : List (String × Bool × Ty)}
    {names : List String} {values : Terms} {types : List Ty} {answer : Ty}
    (formed : Formation.check (Formation.sites false [] (.record fields)) = none)
    (hvalues : argsTy sig env true values = some types)
    (hcheck : Record.check fields names types = some answer) :
    argTy sig env const (.record fields names values) = some answer := by
  show (match Formation.check (Formation.sites false [] (.record fields)) with
    | some _ => none
    | none => (argsTy sig env true values).bind (Record.check fields names)) = some answer
  rw [formed, hvalues]
  exact hcheck

/-- **A fold** (the introduction form of `termTy_fold_inv`). The list has a list type. The
accumulator's type is the stated one, or the initial value's. The initial value's type is below
it in the checker's order. Under the accumulator at the fold's level and the element one above
it, the body's type is below it too. The fold has the accumulator's type. -/
theorem argTy_fold_intro (const : Bool) {accTy : Option Ty} {list init body : Term}
    {item initial bodyType : Ty} (hlist : argTy sig env false list = some (.list item))
    (hinit : argTy sig env false init = some initial)
    (start : Ty.subN initial (accTy.getD initial) = true)
    (hbody : argTy sig (env ++ [accTy.getD initial, item]) false body = some bodyType)
    (step : Ty.subN bodyType (accTy.getD initial) = true) :
    argTy sig env const (.fold accTy list init body) = some (accTy.getD initial) := by
  have start' : Ty.sub initial.normalize (accTy.getD initial).normalize = true := start
  have step' : Ty.sub bodyType.normalize (accTy.getD initial).normalize = true := step
  show (argTy sig env false list).bind (fun listType =>
    (Checker.listOf? listType).bind fun item =>
      (argTy sig env false init).bind fun initType =>
        if Ty.sub initType.normalize (accTy.getD initType).normalize = true then
          (argTy sig (env ++ [accTy.getD initType, item]) false body).bind fun bodyType =>
            if Ty.sub bodyType.normalize (accTy.getD initType).normalize = true then
              some (accTy.getD initType)
            else none
        else none) = some (accTy.getD initial)
  rw [hlist]
  show (argTy sig env false init).bind (fun initType =>
    if Ty.sub initType.normalize (accTy.getD initType).normalize = true then
      (argTy sig (env ++ [accTy.getD initType, item]) false body).bind fun bodyType =>
        if Ty.sub bodyType.normalize (accTy.getD initType).normalize = true then
          some (accTy.getD initType)
        else none
    else none) = some (accTy.getD initial)
  rw [hinit]
  show (if Ty.sub initial.normalize (accTy.getD initial).normalize = true then
    (argTy sig (env ++ [accTy.getD initial, item]) false body).bind fun bodyType =>
      if Ty.sub bodyType.normalize (accTy.getD initial).normalize = true then
        some (accTy.getD initial)
      else none
    else none) = some (accTy.getD initial)
  rw [if_pos start', hbody]
  show (if Ty.sub bodyType.normalize (accTy.getD initial).normalize = true then
    some (accTy.getD initial) else none) = some (accTy.getD initial)
  exact if_pos step'

end Nodes

/-! ## Records at a record type in normal form

The field list is a parameter. A cell's instance is one application: the normal form of the
cell's type, and a lookup that `rfl` decides. -/

namespace Record

/-- One alternative's answers are that alternative's answer. -/
private theorem mapM_singleton {α β : Type} (f : α → Option β) (x : α) :
    [x].mapM f = (f x).map fun y => [y] := by
  show (f x >>= fun b => List.mapM.loop f [] [b]) = _
  cases f x <;> rfl

/-- A map that fixes every element fixes the list. -/
private theorem map_fixed {α : Type} {f : α → α} :
    ∀ {l : List α}, (∀ a ∈ l, f a = a) → l.map f = l
  | [], _ => rfl
  | x :: xs, fixed => by
    rw [List.map_cons, fixed x List.mem_cons_self,
      map_fixed fun a member => fixed a (List.mem_cons_of_mem x member)]

/-- **A required field's read** at a record type in normal form answers the field's declared
type. Used by every step: the cell's four fields, and a stored request's identity. -/
theorem fieldType_normal {fields : Fields} {name : String} {type : Ty}
    (normal : Ty.normalize (.record fields) = .record fields)
    (declared : Field.firstOf name fields = some (false, type)) :
    fieldType false (.record fields) name = some type := by
  have typeNormal : type.normalize = type :=
    (Ty.record_normal_fields normal).2 (name, false, type) (Field.firstOf_mem declared)
  have read : fieldOf false name (.record fields) = some type := by
    show (Field.firstOf name fields >>= fun entry =>
      match entry with
      | (mayBeAbsent, declaredType) =>
        if false = true then some (Ty.option declaredType)
        else if mayBeAbsent = true then none else some declaredType) = some type
    rw [declared]
    rfl
  unfold fieldType
  rw [normal]
  show (([Ty.record fields].mapM (fieldOf false name)).map joinResults) = some type
  rw [mapM_singleton, read]
  show some (Ty.join .never type) = some type
  rw [Ty.join_never, typeNormal]

/-- An overwrite at a record type in normal form writes the replacement first, required at its
own type, and takes the normal form. -/
theorem setType_normal {fields : Fields} (name : String) (valueType : Ty)
    (normal : Ty.normalize (.record fields) = .record fields) :
    setType (.record fields) name valueType =
      some (Ty.normalize (.record ((name, false, valueType) ::
        fields.filter (fun field => decide (field.1 ≠ name))))) := by
  unfold setType
  rw [normal]
  show (([Ty.record fields].mapM (setOf name valueType)).map joinResults) = _
  rw [mapM_singleton]
  show some (Ty.join .never (Ty.normalize (.record ((name, false, valueType) ::
    fields.filter (fun field => decide (field.1 ≠ name)))))) = _
  rw [Ty.join_never, Ty.normalize_idem]

/-- The canonical order of the fields that a same-field overwrite writes is the declaration. -/
private theorem canon_overwrite {fields : Fields} {name : String} {type : Ty}
    (ascending : Field.Ascending Field.bytesKey fields)
    (declared : Field.firstOf name fields = some (false, type)) :
    Field.canonBy Field.bytesKey
      ((name, false, type) :: fields.filter (fun field => decide (field.1 ≠ name))) = fields := by
  have distinct : (fields.map Prod.fst).Nodup := Field.names_nodup_of_ascending ascending
  have member : (name, false, type) ∈ fields := Field.firstOf_mem declared
  have othersNames :
      ((fields.filter (fun field => decide (field.1 ≠ name))).map Prod.fst).Nodup :=
    (List.filter_sublist.map Prod.fst).nodup distinct
  have fresh : name ∉ (fields.filter (fun field => decide (field.1 ≠ name))).map Prod.fst := by
    intro found
    obtain ⟨p, inside, named⟩ := List.mem_map.mp found
    exact of_decide_eq_true (List.mem_filter.mp inside).2 named
  have writtenNames : (((name, false, type) ::
      fields.filter (fun field => decide (field.1 ≠ name))).map Prod.fst).Nodup := by
    rw [List.map_cons, List.nodup_cons]
    exact ⟨fresh, othersNames⟩
  refine Field.ascending_ext (Field.canonBy_ascending _) ascending fun x => ?_
  rw [Field.mem_canonBy_iff Field.bytesKey_injective writtenNames, List.mem_cons,
    List.mem_filter]
  constructor
  · intro written
    rcases written with same | ⟨inside, -⟩
    · rw [same]
      exact member
    · exact inside
  · intro inside
    by_cases isName : x.1 = name
    · obtain ⟨n, payload⟩ := x
      have named : n = name := isName
      have first : Field.firstOf n fields = some payload :=
        Field.firstOf_of_nodup distinct inside
      rw [named, declared] at first
      have same : (false, type) = payload := Option.some.inj first
      rw [named, ← same]
      exact Or.inl rfl
    · exact Or.inr ⟨inside, decide_eq_true isName⟩

/-- **A same-field overwrite keeps a record type in normal form**, where the replacement's type
has the field's declared type as its normal form. Used by every step of a `Ref.modify`: the
cell's next value is the cell with one field replaced. -/
theorem setType_same {fields : Fields} {name : String} {type valueType : Ty}
    (normal : Ty.normalize (.record fields) = .record fields)
    (declared : Field.firstOf name fields = some (false, type))
    (same : valueType.normalize = type) :
    setType (.record fields) name valueType = some (.record fields) := by
  obtain ⟨ascending, typesNormal⟩ := Ty.record_normal_fields normal
  have fixed : ∀ p ∈ fields.filter (fun field => decide (field.1 ≠ name)),
      (fun q : String × Bool × Ty => (q.1, Ty.normPayload q.2)) p = p := by
    intro p inside
    obtain ⟨n, o, t⟩ := p
    have typeNormal : Ty.normalize t = t := typesNormal (n, o, t) (List.mem_filter.mp inside).1
    show (n, o, Ty.normalize t) = (n, o, t)
    rw [typeNormal]
  rw [setType_normal name valueType normal]
  show some (Ty.record (Field.canonBy Field.bytesKey (Ty.normalizeFields
    ((name, false, valueType) :: fields.filter (fun field => decide (field.1 ≠ name)))))) =
      some (Ty.record fields)
  rw [Ty.normalizeFields_eq_map, List.map_cons, map_fixed fixed]
  show some (Ty.record (Field.canonBy Field.bytesKey
    ((name, false, Ty.normalize valueType) ::
      fields.filter (fun field => decide (field.1 ≠ name))))) = some (Ty.record fields)
  rw [same, canon_overwrite ascending declared]

/-- The supplied names of a full construction are the declared names. -/
private theorem names_declared : ∀ (fields : Fields),
    (fields.map fun field => (field.1, field.2.2)).map Prod.fst = fields.map Prod.fst
  | [] => rfl
  | field :: rest => congrArg (List.cons field.1) (names_declared rest)

/-- The supplied columns of a full construction pair each name with its declared type. -/
private theorem zipNames_declared : ∀ (fields : Fields),
    Machine.Record.zipNames (fields.map Prod.fst) (fields.map fun field => field.2.2) =
      some (fields.map fun field => (field.1, field.2.2))
  | [] => rfl
  | field :: rest => by
    show (Machine.Record.zipNames (rest.map Prod.fst) (rest.map fun field => field.2.2)).map
      ((field.1, field.2.2) :: ·) = _
    rw [zipNames_declared rest]
    rfl

/-- **A full construction at the declared types**: every declared field supplied once, in the
declaration's order, each at its own type. The answer is the declaration's normal form. Used by
a waiting taker's record and a pending offer's. -/
theorem check_declared {fields : Fields} (distinct : (fields.map Prod.fst).Nodup) :
    check fields (fields.map Prod.fst) (fields.map fun field => field.2.2) =
      some (Ty.normalize (.record fields)) := by
  have fit : argumentsFit fields (fields.map fun field => (field.1, field.2.2)) = true := by
    unfold argumentsFit
    rw [Bool.and_eq_true]
    constructor
    · refine List.all_eq_true.mpr fun argument member => ?_
      obtain ⟨field, inside, rfl⟩ := List.mem_map.mp member
      show (Field.firstOf field.1 fields).isSome = true
      cases found : Field.firstOf field.1 fields with
      | none => exact absurd found (Field.firstOf_ne_none_of_mem inside rfl)
      | some payload => rfl
    · refine List.all_eq_true.mpr fun field inside => ?_
      have supplied : Field.firstOf field.1 (fields.map fun field => (field.1, field.2.2)) =
          some field.2.2 :=
        Field.firstOf_of_nodup (by rw [names_declared]; exact distinct)
          (List.mem_map.mpr ⟨field, inside, rfl⟩)
      show (match Field.firstOf field.1 (fields.map fun field => (field.1, field.2.2)) with
        | none => field.2.1
        | some actual => Ty.sub actual.normalize field.2.2.normalize) = true
      rw [supplied]
      exact Ty.sub_refl _
  unfold check
  rw [zipNames_declared fields]
  exact if_pos ⟨distinct, distinct, fit⟩

end Record

end Effect4.Program
