import Effect4.Program.Typing
import Effect4.Program.Native
import Effect4.Laws.Program.TypeAlgebra
import Effect4.Laws.Program.TyView
import Effect4.Laws.Modules.Reading
import Effect4.Laws.Program.Typing.TermIntro

/-!
# Checking a step term: the types of the authoring builders and of the words (row 257)

A typing statement of a composed module's step says that the checker types the step's tree.
This file holds the judgment that the statements are proved through, beside `Reads`
(`src/Effect4/Laws/Modules/Reading.lean`), and what each builder of a step types at, from what
its arguments type at. It names no module. The order is that of `Reading.lean`: a literal, an
application, a field's read, an overwrite, a construction, a fold with minted binders, and the
words of a step term. A positional read is here for a wrapper, which reads a step's reply by
position.

- **`Types`** ties a source term to its elaboration and to the checker's `argTy`, under one
  literal flag. A string literal has two types: its literal type inside a const-generic
  position, and `string` outside one. So the flag is part of the judgment.
- **`TypesEach`** is `Types` under each flag. Every term but a string literal has it, and a
  step uses one argument under several flags: a request's identity stands in an atom's call and
  in a record's construction.
- **`CapturedTy`** is the typed twin of `Captured`: a caller's term keeps its type under the
  two binders that a fold mints. An author's variable has it (`capturedTy_var`), and so has a
  minted name that differs from the fold's two names (`capturedTy_minted`). Weakening is not
  substitution, so capture stays a premise.
- **The removal by identity** is typed once (`types_removeById`), at every entry type that
  holds a `Deferred` identity.
- **`typeAt`** is the checker's answer for a source term at a scope of names, and
  `typeAt_of_types` and `typeAt_tree` join it to `Types` and to the tree's `termTy` equation.

Each builder lemma takes each premise at the flag that the builder's node gives its part, and
its conclusion holds under each flag. The rules of the nodes are the checker's, in their
introduction form (`src/Effect4/Laws/Program/Typing/TermIntro.lean`).

Placement. Concept `store-typing`, requirement R4. Every lemma here is a helper of a module's
typing statements: the Queue's (`src/Effect4/Laws/Modules/Queue/Typing.lean`) and Semaphore's
(`src/Effect4/Laws/Modules/Semaphore/Typing.lean`). A wrapper's law types its own terms with
the same lemmas. They establish nothing of evaluation, of a model or of a target.
-/

set_option autoImplicit false

namespace Effect4.Modules

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring

variable {Op : Type}

/-! ## The judgment -/

/-- **A source term types at a scope**: it elaborates under the scope's names, and the checker
types its tree at the scope's types, under the literal flag `const`. The flag is `true` inside a
const-generic position: a record's value, an overwrite's value and a const-generic atom's
argument. -/
def Types (sig : Signature Op) (src : TermSrc) (env : Env) (path : List Nat) (types : List Ty)
    (const : Bool) (T : Ty) : Prop :=
  ∃ t, src env path = .ok t ∧ argTy sig types const t = some T

/-- **A source term types at a scope under each literal flag.** Every term but a string literal
does: the flag reaches a literal and no other node. -/
def TypesEach (sig : Signature Op) (src : TermSrc) (env : Env) (path : List Nat)
    (types : List Ty) (T : Ty) : Prop :=
  ∀ const : Bool, Types sig src env path types const T

/-- **A caller's term under a step's folds, typed.** It has one type at the scope. It has the
same type under the two binders that a fold of that scope mints, whatever their types. The
typed twin of `Captured`. -/
structure CapturedTy (sig : Signature Op) (src : TermSrc) (env : Env) (path : List Nat)
    (types : List Ty) (T : Ty) : Prop where
  atScope : TypesEach sig src env path types T
  underFold : ∀ acc item : Ty,
    TypesEach sig src (env.push [env.mint "acc", env.mint "item"]) path (types ++ [acc, item]) T

section Builders

variable {sig : Signature Op} {env : Env} {path : List Nat} {types : List Ty}

/-! ## Typing: the base facts -/

/-- A typing at another type that is the same type. -/
theorem Types.to {src : TermSrc} {const : Bool} {T U : Ty}
    (h : Types sig src env path types const T) (same : T = U) :
    Types sig src env path types const U := same ▸ h

/-- A source's tree is one tree: the checker types it at what the source types at. -/
theorem Types.tree {src : TermSrc} {const : Bool} {T : Ty}
    (h : Types sig src env path types const T) {t : Term} (tree : src env path = .ok t) :
    argTy sig types const t = some T := by
  obtain ⟨t', tree', typed⟩ := h
  rw [tree] at tree'
  cases tree'
  exact typed

/-- **A literal** has the literal rule's type under the flag: a string literal keeps its
literal type inside a const-generic position. -/
theorem types_lit (value : Lit) (const : Bool) :
    Types sig (lit value) env path types const (litArgTy const value) :=
  ⟨.lit value, rfl, rfl⟩

theorem types_nat (n : Nat) : TypesEach sig (nat n) env path types .nat :=
  fun const => types_lit (.nat n) const

theorem types_bool (b : Bool) : TypesEach sig (bool b) env path types .bool :=
  fun const => types_lit (.bool b) const

/-- The literal of nothing. -/
theorem types_unit : TypesEach sig unit env path types .unit :=
  fun const => types_lit .unit const

/-- The sources have the types, one by one, under one literal flag. -/
abbrev TypesAll (sig : Signature Op) (srcs : List TermSrc) (env : Env) (path : List Nat)
    (types : List Ty) (const : Bool) (Ts : List Ty) : Prop :=
  Pointwise (fun src T => Types sig src env path types const T) srcs Ts

theorem argsTy_ok (sig : Signature Op) (types : List Ty) (const : Bool) :
    ∀ (ts : List Term) (Ts : List Ty),
      Pointwise (fun t T => argTy sig types const t = some T) ts Ts →
        argsTy sig types const (termsOfList ts) = some Ts
  | [], _, h => by cases h; rfl
  | t :: ts, _, h => by
    cases h with
    | cons ht rest =>
      rename_i T Ts
      exact argsTy_cons_intro ht (argsTy_ok sig types const ts Ts rest)

/-- The trees of sources that type, with the types of the trees. -/
theorem TypesAll.trees {srcs : List TermSrc} {const : Bool} {Ts : List Ty}
    (h : TypesAll sig srcs env path types const Ts) :
    ∃ ts, Pointwise (fun (src : TermSrc) t => src env path = .ok t) srcs ts ∧
      Pointwise (fun t T => argTy sig types const t = some T) ts Ts := by
  induction h with
  | nil => exact ⟨[], .nil, .nil⟩
  | cons head _ ih =>
    obtain ⟨t, tree, typed⟩ := head
    obtain ⟨ts, trees, typeds⟩ := ih
    exact ⟨t :: ts, .cons tree trees, .cons typed typeds⟩

/-- **An application types at its atom's answer** on the types of its arguments, each under the
atom's own flag. -/
theorem types_app {atom : String} {args : List TermSrc} {Ts : List Ty} {T : Ty} {const : Bool}
    (hargs : TypesAll sig args env path types (sig.constAtom atom) Ts)
    (answer : sig.atomOf atom Ts = some T) :
    Types sig (app atom args) env path types const T := by
  obtain ⟨ts, trees, typeds⟩ := hargs.trees
  refine ⟨.app atom (termsOfList ts), ?_,
    argTy_app_intro const (argsTy_ok sig types (sig.constAtom atom) ts Ts typeds) answer⟩
  show (args.mapM (fun src => src env path) >>= fun xs =>
    Except.ok (Term.app atom (termsOfList xs))) = _
  rw [mapM_ok _ args ts trees]
  rfl

/-- A required field types at what the record rule answers under the name. -/
theorem types_field {target : TermSrc} {name : String} {R T : Ty} {const : Bool}
    (htarget : Types sig target env path types false R)
    (declared : Record.fieldType false R name = some T) :
    Types sig (field target name) env path types const T := by
  obtain ⟨t, tree, typed⟩ := htarget
  refine ⟨.field .required t name, ?_, argTy_field_intro const typed declared⟩
  show (target env path >>= fun x => Except.ok (Term.field .required x name)) = _
  rw [tree]
  rfl

/-- An overwrite types at what the record rule answers: the target outside a const-generic
position, the replacement inside one. -/
theorem types_recordSet {target replacement : TermSrc} {name : String} {R V T : Ty}
    {const : Bool} (htarget : Types sig target env path types false R)
    (hreplacement : Types sig replacement env path types true V)
    (written : Record.setType R name V = some T) :
    Types sig (recordSet target name replacement) env path types const T := by
  obtain ⟨t, tree, typed⟩ := htarget
  obtain ⟨r, tree', typed'⟩ := hreplacement
  refine ⟨.recordSet t name r, ?_, argTy_recordSet_intro const typed typed' written⟩
  show (target env path >>= fun x => replacement env path >>= fun y =>
    Except.ok (Term.recordSet x name y)) = _
  rw [tree, tree']
  rfl

/-- A positional read types at what the tuple rule answers at the position. Its consumer is the
wrapper's law, which reads a step's reply by position. -/
theorem types_tupleAt {target : TermSrc} {index : Nat} {R T : Ty} {const : Bool}
    (htarget : Types sig target env path types false R)
    (item : Tuple.typeAt R index = some T) :
    Types sig (tupleAt target index) env path types const T := by
  obtain ⟨t, tree, typed⟩ := htarget
  refine ⟨.tupleAt t index, ?_, argTy_tupleAt_intro const typed item⟩
  show (target env path >>= fun x => Except.ok (Term.tupleAt x index)) = _
  rw [tree]
  rfl

/-- A construction types at what the record rule answers: the raw declaration is formed, and
each present value is typed inside a const-generic position. -/
theorem types_record {fields : List (String × Bool × Ty)} {present : List (String × TermSrc)}
    {Ts : List Ty} {T : Ty} {const : Bool}
    (formed : Formation.check (Formation.sites false [] (.record fields)) = none)
    (hvalues : TypesAll sig (present.map Prod.snd) env path types true Ts)
    (checked : Record.check fields (present.map Prod.fst) Ts = some T) :
    Types sig (record fields present) env path types const T := by
  obtain ⟨ts, trees, typeds⟩ := hvalues.trees
  have elaborated : present.mapM (fun entry => entry.2 env path) = .ok ts :=
    mapM_ok _ present ts (Pointwise.of_map trees)
  refine ⟨.record fields (present.map Prod.fst) (termsOfList ts), ?_,
    argTy_record_intro const formed (argsTy_ok sig types true ts Ts typeds) checked⟩
  show (present.mapM (fun entry => entry.2 env path) >>= fun xs =>
    Except.ok (Term.record fields (present.map Prod.fst) (termsOfList xs))) = _
  rw [elaborated]
  rfl

/-! ## Typing under a fold's two binders -/

/-- Under a fold's two binders, the accumulator's name has the accumulator's type. -/
theorem types_minted_acc (depth : types.length = env.names.length) (path : List Nat)
    (acc item : Ty) :
    TypesEach sig (minted (env.mint "acc")) (env.push [env.mint "acc", env.mint "item"]) path
      (types ++ [acc, item]) acc := by
  intro const
  refine ⟨.var env.names.length, minted_acc_tree env path, ?_⟩
  show (types ++ [acc, item])[env.names.length]? = some acc
  rw [← depth, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

/-- Under a fold's two binders, the element's name has the element's type. -/
theorem types_minted_item (depth : types.length = env.names.length) (path : List Nat)
    (acc item : Ty) :
    TypesEach sig (minted (env.mint "item")) (env.push [env.mint "acc", env.mint "item"]) path
      (types ++ [acc, item]) item := by
  intro const
  refine ⟨.var (env.names.length + 1), minted_item_tree env path, ?_⟩
  show (types ++ [acc, item])[env.names.length + 1]? = some item
  rw [← depth, List.getElem?_append_right (Nat.le_succ _)]
  have one : types.length + 1 - types.length = 1 := by omega
  rw [one]
  rfl

/-- A variable that an author wrote has the type that the scope holds at its level. -/
theorem types_var {x : String} {i : Nat} {T : Ty} (written : Name.reserved x = false)
    (bound : env.names.resolve x = some i) (held : types[i]? = some T) :
    TypesEach sig (var x) env path types T :=
  fun _ => ⟨.var i, var_tree written bound path, held⟩

/-- A minted name has the type that the scope holds at its level. -/
theorem types_minted {name : String} {i : Nat} {T : Ty}
    (bound : env.names.resolve name = some i) (held : types[i]? = some T) :
    TypesEach sig (minted name) env path types T :=
  fun _ => ⟨.var i, minted_tree bound path, held⟩

/-- **A variable that an author wrote is a caller's term under a step's folds, typed**: it has
its type at the scope, and the same type under the two binders that a fold mints. The typed
twin of `captured_var`. -/
theorem capturedTy_var {x : String} {i : Nat} {T : Ty} (written : Name.reserved x = false)
    (bound : env.names.resolve x = some i) (held : types[i]? = some T) :
    CapturedTy sig (var x) env path types T := by
  refine ⟨types_var written bound held, fun acc item const => ⟨.var i, ?_, ?_⟩⟩
  · rw [var_push_minted_pair (mint_reserved env "acc") (mint_reserved env "item") written env
      path]
    exact var_tree written bound path
  · obtain ⟨inside, -⟩ := List.getElem?_eq_some_iff.mp held
    show (types ++ [acc, item])[i]? = some T
    rw [List.getElem?_append_left inside]
    exact held

/-- **A minted name is a caller's term under a step's folds, typed**, where it differs from the
two names that a fold of the scope mints. The typed twin of `captured_minted`. -/
theorem capturedTy_minted {name : String} {i : Nat} {T : Ty}
    (bound : env.names.resolve name = some i) (held : types[i]? = some T)
    (notAcc : env.mint "acc" ≠ name) (notItem : env.mint "item" ≠ name) :
    CapturedTy sig (minted name) env path types T := by
  have pushed : (env.push [env.mint "acc", env.mint "item"]).names.resolve name = some i :=
    resolve_under_pair bound notAcc notItem
  refine ⟨types_minted bound held,
    fun acc item const => ⟨.var i, minted_tree pushed path, ?_⟩⟩
  obtain ⟨inside, -⟩ := List.getElem?_eq_some_iff.mp held
  show (types ++ [acc, item])[i]? = some T
  rw [List.getElem?_append_left inside]
  exact held

/-- **The name that `bindWith` mints is a caller's term under a step's folds, typed**, at every
scope where it is bound: `outer` is the scope of the `bindWith`, and `env` the scope of the
step. The typed twin of `captured_answer`. -/
theorem capturedTy_answer {outer : Env} {i : Nat} {T : Ty}
    (bound : env.names.resolve (outer.mint "answer") = some i) (held : types[i]? = some T) :
    CapturedTy sig (minted (outer.mint "answer")) env path types T :=
  capturedTy_minted bound held (mint_acc_ne_answer env outer) (mint_item_ne_answer env outer)

/-- A field's read of a caller's term is a caller's term: the read stands under the binders
with its target. -/
theorem capturedTy_field {target : TermSrc} {name : String} {R T : Ty}
    (htarget : CapturedTy sig target env path types R)
    (declared : Record.fieldType false R name = some T) :
    CapturedTy sig (field target name) env path types T :=
  ⟨fun _ => types_field (htarget.atScope false) declared,
    fun acc item _ => types_field (htarget.underFold acc item false) declared⟩

/-- **A fold with minted binders types at its accumulator's type.** The list has a list type.
The accumulator's type is the stated one, or the initial value's. The initial value's type is
below it in the checker's order. The body, under the two binders at the accumulator's and the
element's types, has a type below it too. A caller's term in the body keeps its type there by
its own premise (`CapturedTy`). -/
theorem types_foldWith {list init : TermSrc} {body : TermSrc → TermSrc → TermSrc}
    {accTy : Option Ty} {item initial bodyType : Ty} {const : Bool}
    (hlist : Types sig list env path types false (.list item))
    (hinit : Types sig init env path types false initial)
    (start : Ty.subN initial (accTy.getD initial) = true)
    (hbody : Types sig (body (minted (env.mint "acc")) (minted (env.mint "item")))
      (env.push [env.mint "acc", env.mint "item"]) path
      (types ++ [accTy.getD initial, item]) false bodyType)
    (step : Ty.subN bodyType (accTy.getD initial) = true) :
    Types sig (foldWith list init body accTy) env path types const (accTy.getD initial) := by
  obtain ⟨l, listTree, listTyped⟩ := hlist
  obtain ⟨i, initTree, initTyped⟩ := hinit
  obtain ⟨b, bodyTree, bodyTyped⟩ := hbody
  refine ⟨.fold accTy l i b, ?_,
    argTy_fold_intro const listTyped initTyped start bodyTyped step⟩
  show (list env path >>= fun x => init env path >>= fun y =>
    body (minted (env.mint "acc")) (minted (env.mint "item"))
      (env.push [env.mint "acc", env.mint "item"]) path >>= fun z =>
        Except.ok (Term.fold accTy x y z)) = _
  rw [listTree, initTree, bodyTree]
  rfl

/-- A fold that states no accumulator type: the accumulator has the initial value's type. -/
theorem types_foldWith_same {list init : TermSrc} {body : TermSrc → TermSrc → TermSrc}
    {item initial bodyType : Ty} {const : Bool}
    (hlist : Types sig list env path types false (.list item))
    (hinit : Types sig init env path types false initial)
    (hbody : Types sig (body (minted (env.mint "acc")) (minted (env.mint "item")))
      (env.push [env.mint "acc", env.mint "item"]) path (types ++ [initial, item]) false
      bodyType)
    (step : Ty.subN bodyType initial = true) :
    Types sig (foldWith list init body) env path types const initial :=
  types_foldWith (accTy := none) hlist hinit (Ty.subN_refl initial) hbody step

/-! ## The words of a step term -/

/-- The signature's atoms are the native table's: an atom's answer there is its answer here. -/
theorem atomOf_native (atoms : sig.atomOf = nativeAtomTy) {name : String} {Ts : List Ty}
    {T : Ty} (native : nativeAtomTy name Ts = some T) : sig.atomOf name Ts = some T := by
  rw [atoms]
  exact native

variable (atoms : sig.atomOf = nativeAtomTy)
include atoms

theorem types_nilT : TypesEach sig nilT env path types (.list .never) :=
  fun _ => types_app .nil (atomOf_native atoms nativeAtomTy_nil)

theorem types_noneT : TypesEach sig noneT env path types (.option .never) :=
  fun _ => types_app .nil (atomOf_native atoms nativeAtomTy_none)

theorem types_some {a : TermSrc} {T : Ty} (ha : TypesEach sig a env path types T) :
    TypesEach sig (app "some" [a]) env path types (.option T) :=
  fun _ => types_app (.cons (ha _) .nil) (atomOf_native atoms (nativeAtomTy_some T))

theorem types_len {xs : TermSrc} {T : Ty} (hxs : TypesEach sig xs env path types (.list T)) :
    TypesEach sig (len xs) env path types .nat :=
  fun _ => types_app (.cons (hxs _) .nil) (atomOf_native atoms (nativeAtomTy_length T))

theorem types_isEmpty {xs : TermSrc} {T : Ty}
    (hxs : TypesEach sig xs env path types (.list T)) :
    TypesEach sig (isEmpty xs) env path types .bool :=
  fun _ => types_app (.cons (types_len atoms hxs _) .nil) (atomOf_native atoms nativeAtomTy_isZero)

theorem types_notT {b : TermSrc} (hb : TypesEach sig b env path types .bool) :
    TypesEach sig (notT b) env path types .bool :=
  fun _ => types_app (.cons (hb _) .nil) (atomOf_native atoms nativeAtomTy_not)

theorem types_andT {a b : TermSrc} (ha : TypesEach sig a env path types .bool)
    (hb : TypesEach sig b env path types .bool) :
    TypesEach sig (andT a b) env path types .bool :=
  fun _ => types_app (.cons (ha _) (.cons (hb _) .nil)) (atomOf_native atoms nativeAtomTy_and)

theorem types_orT {a b : TermSrc} (ha : TypesEach sig a env path types .bool)
    (hb : TypesEach sig b env path types .bool) :
    TypesEach sig (orT a b) env path types .bool :=
  fun _ => types_app (.cons (ha _) (.cons (hb _) .nil)) (atomOf_native atoms nativeAtomTy_or)

/-- A selection whose second arm's type is above the first's types at the second's. -/
theorem types_ifT_above {c t f : TermSrc} {X Y : Ty}
    (hc : TypesEach sig c env path types .bool) (ht : TypesEach sig t env path types X)
    (hf : TypesEach sig f env path types Y) (above : Ty.sub X Y = true) :
    TypesEach sig (ifT c t f) env path types Y :=
  fun _ => types_app (.cons (hc _) (.cons (ht _) (.cons (hf _) .nil)))
    (atomOf_native atoms (nativeAtomTy_ite_above above))

/-- A selection between two arms of one type. -/
theorem types_ifT {c t f : TermSrc} {X : Ty} (hc : TypesEach sig c env path types .bool)
    (ht : TypesEach sig t env path types X) (hf : TypesEach sig f env path types X) :
    TypesEach sig (ifT c t f) env path types X :=
  types_ifT_above atoms hc ht hf (Ty.sub_refl X)

/-- A selection whose second arm's type is below the first's, both in normal form, types at
the first's. -/
theorem types_ifT_below {c t f : TermSrc} {X Y : Ty}
    (hc : TypesEach sig c env path types .bool) (ht : TypesEach sig t env path types X)
    (hf : TypesEach sig f env path types Y) (hX : X.normalize = X) (hY : Y.normalize = Y)
    (below : Ty.sub Y X = true) : TypesEach sig (ifT c t f) env path types X :=
  fun _ => types_app (.cons (hc _) (.cons (ht _) (.cons (hf _) .nil)))
    (atomOf_native atoms (nativeAtomTy_ite_below hX hY below))

/-- The identity test on two `Deferred` handles, whatever each holds. -/
theorem types_same {a b : TermSrc} {A E B F : Ty}
    (ha : TypesEach sig a env path types (.deferredOf A E))
    (hb : TypesEach sig b env path types (.deferredOf B F)) :
    TypesEach sig (same a b) env path types .bool :=
  fun _ => types_app (.cons (ha _) (.cons (hb _) .nil))
    (atomOf_native atoms (nativeAtomTy_sameHandle_deferred A E B F))

theorem types_take {xs n : TermSrc} {T : Ty} (hxs : TypesEach sig xs env path types (.list T))
    (hn : TypesEach sig n env path types .nat) :
    TypesEach sig (app "take" [xs, n]) env path types (.list T) :=
  fun _ => types_app (.cons (hxs _) (.cons (hn _) .nil)) (atomOf_native atoms (nativeAtomTy_take T))

theorem types_drop {xs n : TermSrc} {T : Ty} (hxs : TypesEach sig xs env path types (.list T))
    (hn : TypesEach sig n env path types .nat) :
    TypesEach sig (app "drop" [xs, n]) env path types (.list T) :=
  fun _ => types_app (.cons (hxs _) (.cons (hn _) .nil)) (atomOf_native atoms (nativeAtomTy_drop T))

/-- The empty list at the type of a list. -/
theorem types_noneOf {xs : TermSrc} {T : Ty} (hxs : TypesEach sig xs env path types (.list T)) :
    TypesEach sig (noneOf xs) env path types (.list T) :=
  types_take atoms hxs (types_nat 0)

theorem types_append {xs ys : TermSrc} {T : Ty}
    (hxs : TypesEach sig xs env path types (.list T))
    (hys : TypesEach sig ys env path types (.list T)) :
    TypesEach sig (app "append" [xs, ys]) env path types (.list T) :=
  fun _ => types_app (.cons (hxs _) (.cons (hys _) .nil))
    (atomOf_native atoms (nativeAtomTy_append T))

/-- The list of one element, whose type is its own normal form. -/
theorem types_single {x : TermSrc} {T : Ty} (canonical : T.normalize = T)
    (hx : TypesEach sig x env path types T) :
    TypesEach sig (app "cons" [x, nilT]) env path types (.list T) :=
  fun _ => types_app (.cons (hx _) (.cons (types_nilT atoms _) .nil))
    (atomOf_native atoms (nativeAtomTy_cons_nil canonical))

/-- A list with one element behind it, at the element's type in normal form. -/
theorem types_snoc {xs x : TermSrc} {T : Ty} (canonical : T.normalize = T)
    (hxs : TypesEach sig xs env path types (.list T)) (hx : TypesEach sig x env path types T) :
    TypesEach sig (snoc xs x) env path types (.list T) :=
  types_append atoms hxs (types_single atoms canonical hx)

theorem types_lt {a b : TermSrc} (ha : TypesEach sig a env path types .nat)
    (hb : TypesEach sig b env path types .nat) :
    TypesEach sig (app "lt" [a, b]) env path types .bool :=
  fun _ => types_app (.cons (ha _) (.cons (hb _) .nil)) (atomOf_native atoms nativeAtomTy_lt)

/-- `eq` on two numbers is a Boolean. -/
theorem types_eq {a b : TermSrc} (ha : TypesEach sig a env path types .nat)
    (hb : TypesEach sig b env path types .nat) :
    TypesEach sig (app "eq" [a, b]) env path types .bool :=
  fun _ => types_app (.cons (ha _) (.cons (hb _) .nil)) (atomOf_native atoms nativeAtomTy_eq)

theorem types_sub {a b : TermSrc} (ha : TypesEach sig a env path types .nat)
    (hb : TypesEach sig b env path types .nat) :
    TypesEach sig (app "sub" [a, b]) env path types .nat :=
  fun _ => types_app (.cons (ha _) (.cons (hb _) .nil)) (atomOf_native atoms nativeAtomTy_sub)

theorem types_add {a b : TermSrc} (ha : TypesEach sig a env path types .nat)
    (hb : TypesEach sig b env path types .nat) :
    TypesEach sig (app "add" [a, b]) env path types .nat :=
  fun _ => types_app (.cons (ha _) (.cons (hb _) .nil)) (atomOf_native atoms nativeAtomTy_add)

theorem types_isZero {n : TermSrc} (hn : TypesEach sig n env path types .nat) :
    TypesEach sig (app "isZero" [n]) env path types .bool :=
  fun _ => types_app (.cons (hn _) .nil) (atomOf_native atoms nativeAtomTy_isZero)

theorem types_minT {a b : TermSrc} (ha : TypesEach sig a env path types .nat)
    (hb : TypesEach sig b env path types .nat) :
    TypesEach sig (minT a b) env path types .nat :=
  types_ifT atoms (types_lt atoms ha hb) ha hb

/-- The first element of a list, as an option. -/
theorem types_head {xs : TermSrc} {T : Ty} (hxs : TypesEach sig xs env path types (.list T)) :
    TypesEach sig (app "get" [xs, nat 0]) env path types (.option T) :=
  fun _ => types_app (.cons (hxs _) (.cons (types_nat 0 _) .nil))
    (atomOf_native atoms (nativeAtomTy_get T))

theorem types_pair {a b : TermSrc} {X Y : Ty} (ha : TypesEach sig a env path types X)
    (hb : TypesEach sig b env path types Y) :
    TypesEach sig (app "pair" [a, b]) env path types (.prod X Y) :=
  fun _ => types_app (.cons (ha _) (.cons (hb _) .nil))
    (atomOf_native atoms (nativeAtomTy_pair X Y))

/-- A tuple of two types at the product, where both types are their own normal forms and
neither is a union. -/
theorem types_tuple2 {a b : TermSrc} {X Y : Ty} (ha : TypesEach sig a env path types X)
    (hb : TypesEach sig b env path types Y) (hX : X.normalize = X) (hY : Y.normalize = Y)
    (fX : X.isFactor = true) (fY : Y.isFactor = true) :
    TypesEach sig (tuple [a, b]) env path types (.prod X Y) :=
  fun _ => (types_app (.cons (ha _) (.cons (hb _) .nil))
    (atomOf_native atoms (nativeAtomTy_tuple [X, Y]))).to
      (Ty.normalize_pair_canonical hX hY fX fY)

/-- A tuple of three types at the tuple type, where each type is its own normal form. -/
theorem types_tuple3 {a b c : TermSrc} {X Y Z : Ty} (ha : TypesEach sig a env path types X)
    (hb : TypesEach sig b env path types Y) (hc : TypesEach sig c env path types Z)
    (hX : X.normalize = X) (hY : Y.normalize = Y) (hZ : Z.normalize = Z) :
    TypesEach sig (tuple [a, b, c]) env path types (.tuple [X, Y, Z]) :=
  fun _ => (types_app (.cons (ha _) (.cons (hb _) (.cons (hc _) .nil)))
    (atomOf_native atoms (nativeAtomTy_tuple [X, Y, Z]))).to
      (Ty.normalize_triple_canonical hX hY hZ)

/-! ## The removal by identity

The pass `removeById` (`src/Effect4/Modules/Words.lean`) is typed once, at an entry type that
holds a `Deferred` identity. Its consumers are a module's own removals: the Queue's
`removeTaker` and `removeOffer`, and Semaphore's `removeWaiter`. -/

/-- The identity of a folded record against the request's, under the fold's binders: the
record's `id` field and the request's identity are two `Deferred` handles. -/
theorem types_sameItem {id : TermSrc} {E accT a e b f : Ty}
    (depth : types.length = env.names.length)
    (idField : Record.fieldType false E "id" = some (.deferredOf a e))
    (hid : CapturedTy sig id env path types (.deferredOf b f)) :
    TypesEach sig (same (field (minted (env.mint "item")) "id") id)
      (env.push [env.mint "acc", env.mint "item"]) path (types ++ [accT, E]) .bool :=
  types_same atoms (fun _ => types_field (types_minted_item depth path accT E false) idField)
    (hid.underFold accT E)

/-- The fold that drops the entries of one identity types at the list's own type, where the
entries' type is its own normal form and holds a `Deferred` identity. The fold is the body of
the pass `removeById` (`src/Effect4/Modules/Words.lean`). -/
theorem types_removeById {entries id : TermSrc} {E a e b f : Ty}
    (depth : types.length = env.names.length) (canonical : E.normalize = E)
    (idField : Record.fieldType false E "id" = some (.deferredOf a e))
    (hentries : TypesEach sig entries env path types (.list E))
    (hid : CapturedTy sig id env path types (.deferredOf b f)) :
    TypesEach sig
      (foldWith entries (noneOf entries) fun kept entry =>
        ifT (same (field entry "id") id) kept (snoc kept entry))
      env path types (.list E) :=
  fun _ => types_foldWith_same (hentries false) (types_noneOf atoms hentries false)
    (types_ifT atoms (types_sameItem atoms depth idField hid)
      (types_minted_acc depth path (.list E) E)
      (types_snoc atoms canonical (types_minted_acc depth path (.list E) E)
        (types_minted_item depth path (.list E) E)) false)
    (Ty.subN_refl (.list E))

end Builders

/-! ## The checker's answer at a scope of names

`typeAt` is what the checker answers for a source term at a scope of names. A module states
each step's typing at the step's own names with it, and a battery reads it by `decide`. -/

/-- The checker's type of a source term, at a scope of names and their types. `none` where the
source refuses or its tree has no type. -/
def typeAt (sig : Signature NativeOp) (names : List String) (types : List Ty) (src : TermSrc) :
    Option Ty :=
  (src { names := names } []).toOption.bind (termTy sig types)

/-- A source term that types at a scope of names, outside a const-generic position, has the
checker's answer there. Each typing statement at a step's own scope is read so from the step's
typing at every scope. -/
theorem typeAt_of_types {sig : Signature NativeOp} {names : List String} {types : List Ty}
    {src : TermSrc} {T : Ty} (typed : Types sig src { names := names } [] types false T) :
    typeAt sig names types src = some T := by
  obtain ⟨t, tree, checked⟩ := typed
  show ((src { names := names } []).toOption.bind (termTy sig types)) = some T
  rw [tree]
  exact checked

/-- **From a `typeAt` answer to the tree's typing.** The source elaborates at the scope of
names, and the checker types its tree: the elaborated tree, its elaboration equation and its
`termTy` equation. Placement: concept `store-typing`, requirement R4, a helper of the wrapper's
law. Its consumer is the typing premise of `step_keeps_cell`
(`src/Effect4/Laws/Modules/Store.lean`). It reads `typeAt`'s definition, and it establishes
nothing of a wrapper. -/
theorem typeAt_tree {sig : Signature NativeOp} {names : List String} {types : List Ty}
    {src : TermSrc} {T : Ty} (typed : typeAt sig names types src = some T) :
    ∃ t, src { names := names } [] = .ok t ∧ termTy sig types t = some T := by
  unfold typeAt at typed
  cases tree : src { names := names } [] with
  | error refusal =>
    rw [tree] at typed
    exact absurd typed (Option.some_ne_none T).symm
  | ok t =>
    rw [tree] at typed
    exact ⟨t, rfl, typed⟩

/-! ## The order at a list -/

/-- The empty list is below every list type. -/
theorem sub_nil_list (T : Ty) : Ty.sub (.list .never) (.list T) = true := by
  rw [Ty.sub_args_list]
  show (Ty.sub .never T && true) = true
  rw [Ty.OrderProof.sub_never]
  rfl

/-! ## Lists that a term writes out

The words `front` and `listOf` of `src/Effect4/Modules/Words.lean`. `single` has its rule
above: `types_single`. Their first consumer is Pool (`src/Effect4/Laws/Modules/Pool/`): a
returned item at the front of the idle items, and the items of the initial value. -/

section Lists

variable {sig : Signature Op} {env : Env} {path : List Nat} {types : List Ty}
variable (atoms : sig.atomOf = nativeAtomTy)
include atoms

/-- A list with one element in front of it, at the element's type in normal form. -/
theorem types_front {x xs : TermSrc} {T : Ty} (canonical : T.normalize = T)
    (hx : TypesEach sig x env path types T) (hxs : TypesEach sig xs env path types (.list T)) :
    TypesEach sig (front x xs) env path types (.list T) :=
  types_append atoms (types_single atoms canonical hx) hxs

/-- The list of the given terms, each at one type in normal form, where at least one term is
given. -/
theorem types_listOf {T : Ty} (canonical : T.normalize = T) :
    ∀ {xs : List TermSrc}, xs ≠ [] → (∀ x ∈ xs, TypesEach sig x env path types T) →
      TypesEach sig (listOf xs) env path types (.list T)
  | [], nonempty, _ => absurd rfl nonempty
  | [x], _, each => types_single atoms canonical (each x List.mem_cons_self)
  | x :: y :: rest, _, each =>
    types_front atoms canonical (each x List.mem_cons_self)
      (types_listOf canonical (List.cons_ne_nil y rest) fun z member =>
        each z (List.mem_cons_of_mem x member))

end Lists

end Effect4.Modules
