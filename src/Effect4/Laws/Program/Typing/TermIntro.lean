import Effect4.Program.Native
import Effect4.Laws.Program.TypeAlgebra
import Effect4.Laws.Program.TyView
import Effect4.Laws.Program.UnionRule
import Effect4.Laws.Program.Bounds

/-!
# Laws.Program.Typing.TermIntro — the term checker's rules in their introduction form

The term checker is `argTy` and `argsTy` (`src/Effect4/Program/Typing/Rules.lean`), and `termTy`
is its projection outside a const-generic atom. The laws beside it are inversions: each reads a
successful check (`termTy_record_inv`, `termTy_fold_inv`,
`src/Effect4/Laws/Program/Typed.lean`). This file gives the other direction: from the parts'
types to the whole's type. Each rule is stated once, and it names no module.

- **Normal forms.** The types that a rule compares after `Ty.normalize`, written as their own
  normal forms: a list, an option, a product, a tuple and a record's fields.
- **Templates.** The match by bounds at an atom's parameter list (`Bounds.matchArgsB`): the
  symbolic matches stand in `src/Effect4/Laws/Program/Bounds.lean`.
- **Native calls.** `nativeAtomTy` at a symbolic list, option, pair or tuple type, for the
  atoms that a step term uses. `ite` has two rules: its second arm above the first, and below
  it.
- **Nodes.** One rule for each node of `argTy`: an application, a field's read, an overwrite, a
  positional read, a construction and a fold. Each keeps the literal flag of the checker.
- **Records.** `Record.fieldType`, `Record.setType` and `Record.check` at a record type in
  normal form. The field list is a parameter, and each side condition is decidable or a named
  premise, so a new cell's instance is one application.
- **Tuples.** `Tuple.typeAt` at a tuple type in normal form, for a reply that is read by
  position.

Placement. Concept `store-typing`, requirement R4. Every rule here is a helper of the typing
statements of a composed module's steps: the Queue's
(`src/Effect4/Laws/Modules/Queue/Typing.lean`), where each docstring names a step that uses
it, and Semaphore's (`src/Effect4/Laws/Modules/Semaphore/Typing.lean`). The two rules of a
positional read are the exception: their consumer is the wrapper's law, which reads a step's
reply by position. The rules reach the statements through the judgment `Types` and its builder
lemmas (`src/Effect4/Laws/Modules/Checking.lean`).

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

-- A parameter's first occurrence binds by bounds (`matchArgsB_one_var`), and two distinct
-- parameters bind positionally (`matchArgsB_two_vars`).

end Ty

open Ty

/-! ## Native calls at a symbolic type

One rule for each atom that a step term of the Queue uses. A template atom is read through
`Bounds.matchArgsB`, a fixed signature through `NativeAtom.monoApply`. -/

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

/-- `add` on two numbers. A fixed signature at its own parameters. -/
theorem nativeAtomTy_add : nativeAtomTy "add" [.nat, .nat] = some .nat :=
  NativeAtom.monoApply_self [.nat, .nat] .nat

theorem nativeAtomTy_not : nativeAtomTy "not" [.bool] = some .bool :=
  NativeAtom.monoApply_self [.bool] .bool

theorem nativeAtomTy_and : nativeAtomTy "and" [.bool, .bool] = some .bool :=
  NativeAtom.monoApply_self [.bool, .bool] .bool

theorem nativeAtomTy_or : nativeAtomTy "or" [.bool, .bool] = some .bool :=
  NativeAtom.monoApply_self [.bool, .bool] .bool

theorem nativeAtomTy_lt : nativeAtomTy "lt" [.nat, .nat] = some .bool :=
  NativeAtom.monoApply_self [.nat, .nat] .bool

/-- `eq` on two numbers: the first of the atom's two fixed signatures, at its own parameters.
Used by a step that compares two stamps. -/
theorem nativeAtomTy_eq : nativeAtomTy "eq" [.nat, .nat] = some .bool := by
  show ([([Ty.nat, Ty.nat], Ty.bool), ([Ty.string, Ty.string], Ty.bool)].findSome? fun c =>
    NativeAtom.monoApply c.1 c.2 [.nat, .nat]) = some .bool
  rw [List.findSome?_cons, NativeAtom.monoApply_self]

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

/-- A tuple answers the normal form of the tuple type of its items. Used by every reply of two
or three parts. -/
theorem nativeAtomTy_tuple (types : List Ty) :
    nativeAtomTy "tuple" types = some (Ty.normalize (.tuple types)) := rfl

/-- `some` wraps its argument's type. Used by the offer step's decided answer. -/
theorem nativeAtomTy_some (X : Ty) : nativeAtomTy "some" [X] = some (.option X) := by
  change (Bounds.matchArgsB [.var 0] [X]).map (fun σ => Ty.instantiate σ (.option (.var 0))) = some (.option X)
  rw [Bounds.matchArgsB_one_var]
  rfl

/-- A pair has the product of its two arguments' types. Used by every step of a `Ref.modify`:
the reply and the cell's next value. -/
theorem nativeAtomTy_pair (X Y : Ty) : nativeAtomTy "pair" [X, Y] = some (.prod X Y) := by
  change (Bounds.matchArgsB [.var 0, .var 1] [X, Y]).map (fun σ => Ty.instantiate σ (.prod (.var 0) (.var 1))) = some (.prod X Y)
  rw [Bounds.matchArgsB_two_vars]
  rfl

/-- `take` keeps a list's type. Used by `noneOf`, `wake` and `entering`. -/
theorem nativeAtomTy_take (X : Ty) : nativeAtomTy "take" [.list X, .nat] = some (.list X) := by
  change (Bounds.matchArgsB [.list (.var 0), .nat] [.list X, .nat]).map (fun σ => Ty.instantiate σ (.list (.var 0))) = some (.list X)
  rw [Bounds.matchArgsB_list_var_nat]
  rfl

/-- `drop` keeps a list's type. Used by `staying` and by the buffer after a consumed message. -/
theorem nativeAtomTy_drop (X : Ty) : nativeAtomTy "drop" [.list X, .nat] = some (.list X) := by
  change (Bounds.matchArgsB [.list (.var 0), .nat] [.list X, .nat]).map (fun σ => Ty.instantiate σ (.list (.var 0))) = some (.list X)
  rw [Bounds.matchArgsB_list_var_nat]
  rfl

/-- `get` answers an option of a list's element type. Used by the take step's and the poll
step's message. -/
theorem nativeAtomTy_get (X : Ty) : nativeAtomTy "get" [.list X, .nat] = some (.option X) := by
  change (Bounds.matchArgsB [.list (.var 0), .nat] [.list X, .nat]).map (fun σ => Ty.instantiate σ (.option (.var 0))) = some (.option X)
  rw [Bounds.matchArgsB_list_var_nat]
  rfl

/-- Two lists of one element type append to a list of that type. Used by `snoc` and
`gained`. -/
theorem nativeAtomTy_append (X : Ty) (canonical : X.normalize = X) :
    nativeAtomTy "append" [.list X, .list X] = some (.list X) := by
  change (Bounds.matchArgsB [.list (.var 0), .list (.var 0)] [.list X, .list X]).map
    (fun σ => Ty.instantiate σ (.list (.var 0))) = some (.list X)
  rw [Bounds.matchArgsB_append X canonical]
  dsimp only [Option.map, Ty.instantiate, List.lookup, BEq.beq, Nat.beq]
  have hj : Ty.join X X = X := by rw [Ty.join_self, canonical]
  rw [hj]
  rfl

/-- **`cons` onto the empty list** answers a list of the element's type, where that type is its
own normal form. The tail's element type is the empty union: it replaces the element's binding
only where the element's type is below it, and then both are the empty union. Used by `snoc`. -/
theorem nativeAtomTy_cons_nil {X : Ty} (canonical : X.normalize = X) :
    nativeAtomTy "cons" [X, .list .never] = some (.list X) := by
  change (Bounds.matchArgsB [.var 0, .list (.var 0)] [X, .list .never]).map
    (fun σ => Ty.instantiate σ (.list (.var 0))) = some (.list X)
  rw [Bounds.matchArgsB_cons_nil canonical]
  dsimp only [Option.map, Ty.instantiate, List.lookup, BEq.beq, Nat.beq]
  have hj : Ty.join X .never = X := by rw [Ty.join_never_right, canonical]
  rw [hj]
  rfl

/-- **`ite`** types at the join of the two arm types unconditionally. -/
theorem nativeAtomTy_ite (X Y : Ty) : nativeAtomTy "ite" [.bool, X, Y] = some (Ty.join X Y) := by
  change (Bounds.matchArgsB [.bool, .var 0, .var 0] [.bool, X, Y]).map
    (fun σ => Ty.instantiate σ (.var 0)) = some (Ty.join X Y)
  rw [Bounds.matchArgsB_ite]
  rfl

/-- **`ite` at an arm above**: where the first arm's type is below the second's, the answer is
the second arm's type. It is a corollary of `nativeAtomTy_ite`. Used by the offer step's outer
selection, and at two equal arms by `wake`. -/
theorem nativeAtomTy_ite_above {X Y : Ty} (above : Ty.sub X Y = true)
    (canonical : Y.normalize = Y) : nativeAtomTy "ite" [.bool, X, Y] = some Y := by
  rw [nativeAtomTy_ite]
  have hNorm : Normal Y := canonical ▸ normal_normalize Y
  rw [Bounds.join_eq_right_of_subN (OrderProof.sub_normalize_of_sub sub_trans X Y above) hNorm]

/-- **`ite` at an arm below**: where the second arm's type is below the first's, and the first
is its own normal form, the answer is the first arm's type. It is a corollary of `nativeAtomTy_ite`.
Used by the take step and the poll step: the arm that waits answers no message. -/
theorem nativeAtomTy_ite_below {X Y : Ty} (hX : X.normalize = X)
    (below : Ty.sub Y X = true) : nativeAtomTy "ite" [.bool, X, Y] = some X := by
  rw [nativeAtomTy_ite]
  have hNorm : Normal X := hX ▸ normal_normalize X
  rw [Bounds.join_eq_left_of_subN (OrderProof.sub_normalize_of_sub sub_trans Y X below) hNorm]

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

/-- **A positional read**: the target outside a const-generic position, then the tuple rule.
Its consumer is the wrapper's law, which reads a step's reply by position. -/
theorem argTy_tupleAt_intro (const : Bool) {target : Term} {index : Nat} {tuple answer : Ty}
    (htarget : argTy sig env false target = some tuple)
    (hitem : Tuple.typeAt tuple index = some answer) :
    argTy sig env const (.tupleAt target index) = some answer := by
  show (argTy sig env false target).bind
    (fun targetType => Tuple.typeAt targetType index) = some answer
  rw [htarget]
  exact hitem

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

/-- A map that fixes every element fixes the list. -/
private theorem map_fixed {α : Type} {f : α → α} :
    ∀ {l : List α}, (∀ a ∈ l, f a = a) → l.map f = l
  | [], _ => rfl
  | x :: xs, fixed => by
    rw [List.map_cons, fixed x List.mem_cons_self,
      map_fixed fun a member => fixed a (List.mem_cons_of_mem x member)]

/-- **A required field's read** at a record type in normal form answers the field's declared
type. Used by every step: the cell's four fields, and a stored request's identity. A record
type is one union member, so the lifted rule is the record rule there (`UnionRule.lift_member`,
`src/Effect4/Laws/Program/UnionRule.lean`). -/
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
  show UnionRule.lift (fieldOf false name) (.record fields) = some type
  rw [UnionRule.lift_member _ (Ty.normal_of_canonical normal) rfl, read]
  show some (Ty.join .never type) = some type
  rw [Ty.join_never, typeNormal]

/-- An overwrite at a record type in normal form writes the replacement first, required at its
own type, and takes the normal form. The lifted rule is the record rule at one union member
(`UnionRule.lift_member`). -/
theorem setType_normal {fields : Fields} (name : String) (valueType : Ty)
    (normal : Ty.normalize (.record fields) = .record fields) :
    setType (.record fields) name valueType =
      some (Ty.normalize (.record ((name, false, valueType) ::
        fields.filter (fun field => decide (field.1 ≠ name))))) := by
  show UnionRule.lift (setOf name valueType) (.record fields) = _
  rw [UnionRule.lift_member _ (Ty.normal_of_canonical normal) rfl]
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

/-! ## A positional read at a tuple type in normal form -/

/-- **A positional read at a tuple type in normal form** answers the item at the position: a
tuple's item, or one of a product's two. The position is a lookup that `rfl` decides. Its
consumer is the wrapper's law: a take's reply is a tuple of three, and an offer's and a poll's
are products. -/
theorem Tuple.typeAt_normal {target : Ty} {index : Nat} {answer : Ty}
    (normal : target.normalize = target) (item : Tuple.project index target = some answer) :
    Tuple.typeAt target index = some answer := by
  unfold Tuple.typeAt
  rw [normal]
  exact item

end Effect4.Program
