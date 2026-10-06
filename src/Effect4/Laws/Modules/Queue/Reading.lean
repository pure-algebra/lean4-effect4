import Effect4.Laws.Modules.Queue.Relation
import Effect4.Laws.Program.Authoring.Folds
import Effect4.Laws.Program.Typed.ListFold

/-!
# Reading the Queue's step terms: the values of the authoring builders (decisions row 255)

A step goal says that a step's source term reads a value (`Reads`,
`src/Effect4/Laws/Modules/Queue/Relation.lean`). This file gives what each builder of a step
reads, from what its arguments read: an application, a record's read, overwrite and
construction, a fold with minted binders, the words of a step term, and each pass of
`src/Effect4/Modules/Queue/Steps.lean` on the encoding of a model's lists.

Placement. Concept `translation-simulation`, requirement R10. Every lemma here is a helper of
the six step goals (`src/Effect4/Laws/Modules/Queue/Steps.lean`), parts of the proposed claim
`queue-expansion-agrees`. Its consumer is the proof of a step goal. The lemmas establish
nothing of a model's step by themselves.

The rules of a fold's two binders are the scope reader's. The two names that `foldWith` mints
at a scope are two names (`mint_acc_ne_item`), so under the binders the accumulator's name
reads the accumulator and the element's name the element (`reads_minted_acc`,
`reads_minted_item`). A caller's term keeps its value there by its own premise (`Captured`).
The base lemmas are about the authoring surface and name no Queue. They stay here until a
second module reads a builder so.
-/

set_option autoImplicit false

namespace Effect4.Queue.Model

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Modules

/-! ## Reading: the base facts -/

/-- A reading at another value that is the same value. -/
theorem Reads.to {src : TermSrc} {env : Env} {path : List Nat} {vals : List Val} {v w : Val}
    (h : Reads src env path vals v) (same : v = w) : Reads src env path vals w := same ▸ h

/-- A source's tree is one tree: what it reads, its tree evaluates to. -/
theorem Reads.eval {src : TermSrc} {env : Env} {path : List Nat} {vals : List Val} {v : Val}
    (h : Reads src env path vals v) {t : Term} (tree : src env path = .ok t) :
    evalTerm vals t = some v := by
  obtain ⟨t', tree', value⟩ := h
  rw [tree] at tree'
  cases tree'
  exact value

theorem reads_lit (value : Lit) (env : Env) (path : List Nat) (vals : List Val) {v : Val}
    (h : value.toVal = some v) : Reads (lit value) env path vals v := ⟨.lit value, rfl, h⟩

theorem reads_nat (n : Nat) (env : Env) (path : List Nat) (vals : List Val) :
    Reads (nat n) env path vals (Val.nat n) := reads_lit _ env path vals rfl

theorem reads_bool (b : Bool) (env : Env) (path : List Nat) (vals : List Val) :
    Reads (bool b) env path vals (Val.bool b) := reads_lit _ env path vals rfl

/-- Two lists related entry by entry. -/
inductive Pointwise {α β : Type} (r : α → β → Prop) : List α → List β → Prop
  | nil : Pointwise r [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} :
    r a b → Pointwise r as bs → Pointwise r (a :: as) (b :: bs)

/-- The sources read the values, one by one. -/
abbrev ReadsAll (srcs : List TermSrc) (env : Env) (path : List Nat) (vals : List Val)
    (vs : List Val) : Prop :=
  Pointwise (fun src v => Reads src env path vals v) srcs vs

theorem mapM_loop_ok {α β ε : Type} (f : α → Except ε β) :
    ∀ (xs : List α) (ys acc : List β), Pointwise (fun x y => f x = .ok y) xs ys →
      List.mapM.loop f xs acc = .ok (acc.reverse ++ ys)
  | [], _, acc, h => by
    cases h
    show Except.ok acc.reverse = _
    rw [List.append_nil]
  | x :: xs, _, acc, h => by
    cases h with
    | cons hx rest =>
      rename_i y ys
      show (f x >>= fun b => List.mapM.loop f xs (b :: acc)) = _
      rw [hx]
      show List.mapM.loop f xs (y :: acc) = _
      rw [mapM_loop_ok f xs ys (y :: acc) rest, List.reverse_cons, List.append_assoc]
      rfl

theorem mapM_ok {α β ε : Type} (f : α → Except ε β) (xs : List α) (ys : List β)
    (h : Pointwise (fun x y => f x = .ok y) xs ys) : xs.mapM f = .ok ys :=
  mapM_loop_ok f xs ys [] h

theorem evalTerms_ok (vals : List Val) :
    ∀ (ts : List Term) (vs : List Val), Pointwise (fun t v => evalTerm vals t = some v) ts vs →
      evalTerms vals (termsOfList ts) = some vs
  | [], _, h => by cases h; rfl
  | t :: ts, _, h => by
    cases h with
    | cons ht rest =>
      rename_i v vs
      show (evalTerm vals t).bind (fun v => (evalTerms vals (termsOfList ts)).bind
        fun rest => some (v :: rest)) = _
      rw [ht, Option.bind_some, evalTerms_ok vals ts vs rest, Option.bind_some]

/-- The trees of sources that read values, with the values of the trees. -/
theorem ReadsAll.trees {srcs : List TermSrc} {env : Env} {path : List Nat} {vals vs : List Val}
    (h : ReadsAll srcs env path vals vs) :
    ∃ ts, Pointwise (fun (src : TermSrc) t => src env path = .ok t) srcs ts ∧
      Pointwise (fun t v => evalTerm vals t = some v) ts vs := by
  induction h with
  | nil => exact ⟨[], .nil, .nil⟩
  | cons head _ ih =>
    obtain ⟨t, tree, value⟩ := head
    obtain ⟨ts, trees, values⟩ := ih
    exact ⟨t :: ts, .cons tree trees, .cons value values⟩

/-- **An application reads its atom's answer** on the values that its arguments read. -/
theorem reads_app {atom : String} {args : List TermSrc} {env : Env} {path : List Nat}
    {vals vs : List Val} {v : Val} (hargs : ReadsAll args env path vals vs)
    (answer : nativeAtom atom vs = some v) : Reads (app atom args) env path vals v := by
  obtain ⟨ts, trees, values⟩ := hargs.trees
  refine ⟨.app atom (termsOfList ts), ?_, ?_⟩
  · show (args.mapM (fun src => src env path) >>= fun xs =>
      Except.ok (Term.app atom (termsOfList xs))) = _
    rw [mapM_ok _ args ts trees]
    rfl
  · show (evalTerms vals (termsOfList ts)).bind (nativeAtom atom) = _
    rw [evalTerms_ok vals ts vs values]
    exact answer


/-- A required field reads what the record holds under the name. -/
theorem reads_field {target : TermSrc} {env : Env} {path : List Nat} {vals : List Val}
    {record v : Val} {name : String} (htarget : Reads target env path vals record)
    (held : Machine.Record.read false record name = some v) :
    Reads (field target name) env path vals v := by
  obtain ⟨t, tree, value⟩ := htarget
  refine ⟨.field .required t name, ?_, ?_⟩
  · show (target env path >>= fun x => Except.ok (Term.field .required x name)) = _
    rw [tree]
    rfl
  · show (evalTerm vals t).bind (fun x => Machine.Record.read false x name) = _
    rw [value]
    exact held

/-- An overwrite reads the record with the field replaced. -/
theorem reads_recordSet {target replacement : TermSrc} {env : Env} {path : List Nat}
    {vals : List Val} {record next written : Val} {name : String}
    (htarget : Reads target env path vals record)
    (hreplacement : Reads replacement env path vals next)
    (set : Machine.Record.set record name next = some written) :
    Reads (recordSet target name replacement) env path vals written := by
  obtain ⟨t, tree, value⟩ := htarget
  obtain ⟨r, tree', value'⟩ := hreplacement
  refine ⟨.recordSet t name r, ?_, ?_⟩
  · show (target env path >>= fun x => replacement env path >>= fun y =>
      Except.ok (Term.recordSet x name y)) = _
    rw [tree, tree']
    rfl
  · show (evalTerm vals t).bind (fun x => (evalTerm vals r).bind fun y =>
      Machine.Record.set x name y) = _
    rw [value, value']
    exact set

/-- A relation on the images of a map is the relation through the map. -/
theorem Pointwise.of_map {α β γ : Type} {r : β → γ → Prop} {f : α → β} :
    ∀ {xs : List α} {ys : List γ}, Pointwise r (xs.map f) ys →
      Pointwise (fun x y => r (f x) y) xs ys
  | [], _, h => by cases h; exact .nil
  | _ :: _, _, h => by
    cases h with
    | cons head tail => exact .cons head (Pointwise.of_map tail)

/-- A record construction reads the record that its present values build. -/
theorem reads_record {fields : List (String × Bool × Ty)} {present : List (String × TermSrc)}
    {env : Env} {path : List Nat} {vals vs : List Val} {built : Val}
    (hvalues : ReadsAll (present.map Prod.snd) env path vals vs)
    (build : Machine.Record.build (present.map Prod.fst) vs = some built) :
    Reads (record fields present) env path vals built := by
  obtain ⟨ts, trees, values⟩ := hvalues.trees
  have elaborated : present.mapM (fun entry => entry.2 env path) = .ok ts :=
    mapM_ok _ present ts (Pointwise.of_map trees)
  refine ⟨.record fields (present.map Prod.fst) (termsOfList ts), ?_, ?_⟩
  · show (present.mapM (fun entry => entry.2 env path) >>= fun xs =>
      Except.ok (Term.record fields (present.map Prod.fst) (termsOfList xs))) = _
    rw [elaborated]
    rfl
  · show (evalTerms vals (termsOfList ts)).bind
      (fun xs => Machine.Record.build (present.map Prod.fst) xs) = _
    rw [evalTerms_ok vals ts vs values]
    exact build

/-! ## Reading under a fold's two binders -/

theorem resolve_go_last (x : String) :
    ∀ (names : Names) (k : Nat) (acc : Option Nat),
      Names.resolve.go x (names ++ [x]) k acc = some (k + names.length)
  | [], k, acc => by
    show Names.resolve.go x [] (k + 1) (if x = x then some k else acc) = _
    rw [if_pos rfl]
    rfl
  | y :: ys, k, acc => by
    show Names.resolve.go x (ys ++ [x]) (k + 1) (if y = x then some k else acc) = _
    rw [resolve_go_last x ys (k + 1), List.length_cons]
    congr 1
    omega

/-- The last name of a scope resolves to the last level. -/
theorem resolve_last (names : Names) (x : String) :
    Names.resolve (names ++ [x]) x = some names.length := by
  unfold Names.resolve
  rw [resolve_go_last x names 0 none, Nat.zero_add]

/-- The two names that a fold mints at a scope are two names. -/
theorem mint_acc_ne_item (env : Env) : env.mint "acc" ≠ env.mint "item" := by
  intro same
  unfold Env.mint reservedPrefix at same
  have bytes := congrArg (fun s : String => s.toByteArray.data.toList) same
  simp only [String.toByteArray_append, ByteArray.data_append, Array.toList_append] at bytes
  have h1 : ("_%" : String).toByteArray.data.toList = [95, 37] := by decide
  have h2 : ("acc" : String).toByteArray.data.toList = [97, 99, 99] := by decide
  have h3 : ("item" : String).toByteArray.data.toList = [105, 116, 101, 109] := by decide
  rw [h1, h2, h3] at bytes
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at bytes
  exact absurd bytes.2.2.1 (by decide)

/-- A name that resolves at a scope is the variable at its level. A step of every lemma that
reads a name: a fold's binder, an author's variable and a minted name. -/
theorem minted_tree {name : String} {env : Env} {i : Nat}
    (bound : env.names.resolve name = some i) (path : List Nat) :
    minted name env path = .ok (.var i) := by
  show (match env.names.resolve name with
    | some i => Except.ok (Term.var i)
    | none => Except.error (Refusal.mk path (Reason.unbound name))) = _
  rw [bound]

/-- Under a fold's two binders, the accumulator's name is the variable at the scope's depth.
The tree that both the value and the type of the accumulator are read from. -/
theorem minted_acc_tree (env : Env) (path : List Nat) :
    minted (env.mint "acc") (env.push [env.mint "acc", env.mint "item"]) path =
      .ok (.var env.names.length) := by
  have resolved : Names.resolve (env.names ++ [env.mint "acc", env.mint "item"])
      (env.mint "acc") = some env.names.length := by
    have split : env.names ++ [env.mint "acc", env.mint "item"] =
        (env.names ++ [env.mint "acc"]) ++ [env.mint "item"] := by
      rw [List.append_assoc]
      rfl
    rw [split, Names.resolve_append_ne (fun same => mint_acc_ne_item env same.symm),
      resolve_last]
  exact minted_tree resolved path

/-- Under a fold's two binders, the element's name is the variable one above the scope's
depth. -/
theorem minted_item_tree (env : Env) (path : List Nat) :
    minted (env.mint "item") (env.push [env.mint "acc", env.mint "item"]) path =
      .ok (.var (env.names.length + 1)) := by
  have resolved : Names.resolve (env.names ++ [env.mint "acc", env.mint "item"])
      (env.mint "item") = some (env.names.length + 1) := by
    have split : env.names ++ [env.mint "acc", env.mint "item"] =
        (env.names ++ [env.mint "acc"]) ++ [env.mint "item"] := by
      rw [List.append_assoc]
      rfl
    rw [split, resolve_last, List.length_append]
    rfl
  exact minted_tree resolved path

/-- Under a fold's two binders, the accumulator's name reads the accumulator. -/
theorem reads_minted_acc {env : Env} {vals : List Val} (depth : vals.length = env.names.length)
    (path : List Nat) (acc item : Val) :
    Reads (minted (env.mint "acc")) (env.push [env.mint "acc", env.mint "item"]) path
      (vals ++ [acc, item]) acc := by
  refine ⟨.var env.names.length, minted_acc_tree env path, ?_⟩
  show (vals ++ [acc, item])[env.names.length]? = some acc
  rw [← depth, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

/-- Under a fold's two binders, the element's name reads the element. -/
theorem reads_minted_item {env : Env} {vals : List Val} (depth : vals.length = env.names.length)
    (path : List Nat) (acc item : Val) :
    Reads (minted (env.mint "item")) (env.push [env.mint "acc", env.mint "item"]) path
      (vals ++ [acc, item]) item := by
  refine ⟨.var (env.names.length + 1), minted_item_tree env path, ?_⟩
  show (vals ++ [acc, item])[env.names.length + 1]? = some item
  rw [← depth, List.getElem?_append_right (Nat.le_succ _)]
  have one : vals.length + 1 - vals.length = 1 := by omega
  rw [one]
  rfl

/-- A name that the surface mints is reserved: an author cannot write it. -/
theorem mint_reserved (env : Env) (stem : String) : Name.reserved (env.mint stem) = true := by
  have bytes : (env.mint stem).toUTF8.data.toList =
      95 :: 37 :: (stem.toByteArray.data.toList ++
        (toString env.names.length).toByteArray.data.toList) := by
    show ("_%" ++ stem ++ toString env.names.length : String).toByteArray.data.toList = _
    simp only [String.toByteArray_append, ByteArray.data_append, Array.toList_append]
    have prefixBytes : ("_%" : String).toByteArray.data.toList = [95, 37] := by decide
    rw [prefixBytes]
    rfl
  unfold Name.reserved
  rw [bytes]
  rfl

/-- A variable that an author wrote, bound at a scope, is the variable at its level. -/
theorem var_tree {x : String} {env : Env} {i : Nat} (written : Name.reserved x = false)
    (bound : env.names.resolve x = some i) (path : List Nat) :
    var x env path = .ok (.var i) := by
  show (if Name.reserved x = true then _ else minted x env path) = _
  rw [written, if_neg Bool.false_ne_true]
  exact minted_tree bound path

/-- **A variable that an author wrote is a caller's term under a step's folds**: it reads its
value at the scope, and the same value under the two binders that a fold mints. -/
theorem captured_var {x : String} {env : Env} {path : List Nat} {vals : List Val} {i : Nat}
    {v : Val} (written : Name.reserved x = false) (bound : env.names.resolve x = some i)
    (held : vals[i]? = some v) : Captured (var x) env path vals v := by
  have tree : var x env path = .ok (.var i) := var_tree written bound path
  refine ⟨⟨.var i, tree, held⟩, fun acc item => ⟨.var i, ?_, ?_⟩⟩
  · rw [var_push_minted_pair (mint_reserved env "acc") (mint_reserved env "item") written env
      path]
    exact tree
  · obtain ⟨inside, -⟩ := List.getElem?_eq_some_iff.mp held
    show (vals ++ [acc, item])[i]? = some v
    rw [List.getElem?_append_left inside]
    exact held

/-! ## A minted name under a fold's two binders

A wrapper binds a request's identity with `bindWith`, whose name is minted. `var` refuses a
minted name, so `captured_var` does not cover it. A minted name keeps its level under a fold's
two binders where it differs from both of the fold's names. The name that `bindWith` mints
differs from both at every pair of scopes: the stem `answer` is no prefix of `acc` or of
`item`, and neither is a prefix of it. One stem at two depths gives two names
(`mint_depth_inj`), and a name that an author wrote is no minted name (`written_ne_mint`). No
statement here says that two stems and two depths give two names in general: the stems `a` at
depth 12 and `a1` at depth 2 give one name.

Placement. Concept `translation-simulation`, requirement R10: a helper of the step statements'
use by the wrapper, the open part `queue-expansion-agrees`. Reach: one read under a fold's two
binders. It establishes no wrapper typing, no cleanup, no scheduling and no host law. Its
consumer is the wrapper's law: the `Captured` premises of `takeStep_agrees`,
`withdrawTake_agrees` and `withdrawOffer_agrees`
(`src/Effect4/Laws/Modules/Queue/Steps.lean`). -/

/-- Two binders of other names leave a name's level. -/
theorem resolve_under_pair {name first second : String} {names : Names} {i : Nat}
    (bound : Names.resolve names name = some i) (notFirst : first ≠ name)
    (notSecond : second ≠ name) : Names.resolve (names ++ [first, second]) name = some i := by
  have split : names ++ [first, second] = (names ++ [first]) ++ [second] := by
    rw [List.append_assoc]
    rfl
  rw [split, Names.resolve_append_ne notSecond, Names.resolve_append_ne notFirst]
  exact bound

/-- **A minted name is a caller's term under a step's folds**, where it differs from the two
names that a fold of the scope mints. It resolves to a level of the scope, and the values hold
`v` there. It reads `v` at the scope, and `v` under the fold's two binders. -/
theorem captured_minted {name : String} {env : Env} {path : List Nat} {vals : List Val}
    {i : Nat} {v : Val} (bound : env.names.resolve name = some i) (held : vals[i]? = some v)
    (notAcc : env.mint "acc" ≠ name) (notItem : env.mint "item" ≠ name) :
    Captured (minted name) env path vals v := by
  have pushed : (env.push [env.mint "acc", env.mint "item"]).names.resolve name = some i :=
    resolve_under_pair bound notAcc notItem
  refine ⟨⟨.var i, minted_tree bound path, held⟩,
    fun acc item => ⟨.var i, minted_tree pushed path, ?_⟩⟩
  obtain ⟨inside, -⟩ := List.getElem?_eq_some_iff.mp held
  show (vals ++ [acc, item])[i]? = some v
  rw [List.getElem?_append_left inside]
  exact held

/-- A fold's accumulator name is no name that `bindWith` mints, at any two scopes. -/
theorem mint_acc_ne_answer (env outer : Env) : env.mint "acc" ≠ outer.mint "answer" := by
  intro same
  unfold Env.mint reservedPrefix at same
  have bytes := congrArg (fun s : String => s.toByteArray.data.toList) same
  simp only [String.toByteArray_append, ByteArray.data_append, Array.toList_append] at bytes
  have h1 : ("_%" : String).toByteArray.data.toList = [95, 37] := by decide
  have h2 : ("acc" : String).toByteArray.data.toList = [97, 99, 99] := by decide
  have h3 : ("answer" : String).toByteArray.data.toList = [97, 110, 115, 119, 101, 114] := by
    decide
  rw [h1, h2, h3] at bytes
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at bytes
  exact absurd bytes.2.2.2.1 (by decide)

/-- A fold's element name is no name that `bindWith` mints, at any two scopes. -/
theorem mint_item_ne_answer (env outer : Env) : env.mint "item" ≠ outer.mint "answer" := by
  intro same
  unfold Env.mint reservedPrefix at same
  have bytes := congrArg (fun s : String => s.toByteArray.data.toList) same
  simp only [String.toByteArray_append, ByteArray.data_append, Array.toList_append] at bytes
  have h1 : ("_%" : String).toByteArray.data.toList = [95, 37] := by decide
  have h2 : ("item" : String).toByteArray.data.toList = [105, 116, 101, 109] := by decide
  have h3 : ("answer" : String).toByteArray.data.toList = [97, 110, 115, 119, 101, 114] := by
    decide
  rw [h1, h2, h3] at bytes
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at bytes
  exact absurd bytes.2.2.1 (by decide)

/-- A name that an author wrote is no minted name. A step of the resolution premise: a row's
binder that an author wrote leaves a minted name's level. -/
theorem written_ne_mint {x : String} (written : Name.reserved x = false) (env : Env)
    (stem : String) : x ≠ env.mint stem := by
  intro same
  rw [same, mint_reserved] at written
  exact Bool.noConfusion written

/-- **The names that one stem mints at two depths are two names**: a minted name ends in its
depth's decimal digits (`repr_inj`, `src/Effect4/Laws/Codegen/ReadLeaf.lean`). It relates no
two stems. A step of the resolution premise: a second `bindWith` leaves the level of the name
that a first one minted. -/
theorem mint_depth_inj {env outer : Env} {stem : String}
    (same : env.mint stem = outer.mint stem) : env.names.length = outer.names.length :=
  repr_inj (String.append_right_inj _ |>.mp same)

/-- **The name that `bindWith` mints is a caller's term under a step's folds**, at every scope
where it is bound: `outer` is the scope of the `bindWith`, and `env` the scope of the step. -/
theorem captured_answer {outer env : Env} {path : List Nat} {vals : List Val} {i : Nat}
    {v : Val} (bound : env.names.resolve (outer.mint "answer") = some i)
    (held : vals[i]? = some v) :
    Captured (minted (outer.mint "answer")) env path vals v :=
  captured_minted bound held (mint_acc_ne_answer env outer) (mint_item_ne_answer env outer)

/-- A literal is a caller's term under a step's folds. -/
theorem captured_lit (value : Lit) (env : Env) (path : List Nat) (vals : List Val) {v : Val}
    (h : value.toVal = some v) : Captured (lit value) env path vals v :=
  ⟨reads_lit value env path vals h, fun acc item => reads_lit value _ path (vals ++ [acc, item]) h⟩

/-- **A fold with minted binders reads its fold.** The list and the initial value read at the
scope. The body, under the two binders, has one tree, and the fold of its values over the
list's elements answers. -/
theorem reads_foldWith {list init : TermSrc} {body : TermSrc → TermSrc → TermSrc} {env : Env}
    {path : List Nat} {vals items : List Val} {start v : Val} {bodyTree : Term}
    (hlist : Reads list env path vals (Val.list items)) (hinit : Reads init env path vals start)
    (tree : body (minted (env.mint "acc")) (minted (env.mint "item"))
      (env.push [env.mint "acc", env.mint "item"]) path = .ok bodyTree)
    (folded : items.foldlM (fun acc item => evalTerm (vals ++ [acc, item]) bodyTree) start =
      some v) :
    Reads (foldWith list init body) env path vals v := by
  obtain ⟨l, listTree, listValue⟩ := hlist
  obtain ⟨i, initTree, initValue⟩ := hinit
  refine ⟨.fold none l i bodyTree, ?_, ?_⟩
  · show (list env path >>= fun x => init env path >>= fun y =>
      body (minted (env.mint "acc")) (minted (env.mint "item"))
        (env.push [env.mint "acc", env.mint "item"]) path >>= fun z =>
          Except.ok (Term.fold none x y z)) = _
    rw [listTree, initTree, tree]
    rfl
  · rw [evalTerm_fold, listValue, Option.bind_some]
    show (some items).bind (fun xs => (evalTerm vals i).bind fun s =>
      xs.foldlM (fun acc item => evalTerm (vals ++ [acc, item]) bodyTree) s) = _
    rw [Option.bind_some, initValue, Option.bind_some]
    exact folded


/-- A fold over the encoding of a model list, with a model of its accumulator: where the body
reads the model's step on every accumulator and element, the fold reads the model's fold. The
witness gives the body's tree where the list is empty. -/
theorem reads_foldWith_model {α β : Type} {list init : TermSrc}
    {body : TermSrc → TermSrc → TermSrc} {env : Env} {path : List Nat} {vals : List Val}
    (item : α → Val) (acc : β → Val) (f : β → α → β) (xs : List α) (b0 : β) (witness : α)
    (hlist : Reads list env path vals (Val.list (xs.map item)))
    (hinit : Reads init env path vals (acc b0))
    (hbody : ∀ (b : β) (x : α),
      Reads (body (minted (env.mint "acc")) (minted (env.mint "item")))
        (env.push [env.mint "acc", env.mint "item"]) path (vals ++ [acc b, item x])
        (acc (f b x))) :
    Reads (foldWith list init body) env path vals (acc (xs.foldl f b0)) := by
  obtain ⟨bodyTree, tree, -⟩ := hbody b0 witness
  refine reads_foldWith hlist hinit tree ?_
  clear hlist hinit
  induction xs generalizing b0 with
  | nil => rfl
  | cons x xs ih =>
    show (evalTerm (vals ++ [acc b0, item x]) bodyTree).bind
      (fun next => (xs.map item).foldlM
        (fun a i => evalTerm (vals ++ [a, i]) bodyTree) next) = _
    rw [(hbody b0 x).eval tree, Option.bind_some]
    exact ih (f b0 x)

/-! ## The atoms of a step, on the values a step reads -/

theorem atom_nil : nativeAtom "nil" [] = some (Val.list []) := rfl
theorem atom_none : nativeAtom "none" [] = some Store.Val.none := rfl
theorem atom_some (a : Val) : nativeAtom "some" [a] = some (Store.Val.some a) := rfl
theorem atom_length (xs : List Val) :
    nativeAtom "length" [Val.list xs] = some (Val.nat xs.length) := rfl
theorem atom_isZero (n : Nat) :
    nativeAtom "isZero" [Val.nat n] = some (Val.bool (decide (n = 0))) := rfl
theorem atom_not (b : Bool) : nativeAtom "not" [Val.bool b] = some (Val.bool (!b)) := rfl
theorem atom_and (a b : Bool) :
    nativeAtom "and" [Val.bool a, Val.bool b] = some (Val.bool (a && b)) := rfl
theorem atom_or (a b : Bool) :
    nativeAtom "or" [Val.bool a, Val.bool b] = some (Val.bool (a || b)) := rfl
theorem atom_ite (c : Bool) (a b : Val) :
    nativeAtom "ite" [Val.bool c, a, b] = some (if c then a else b) := rfl
theorem atom_take (xs : List Val) (n : Nat) :
    nativeAtom "take" [Val.list xs, Val.nat n] = some (Val.list (xs.take n)) := rfl
theorem atom_drop (xs : List Val) (n : Nat) :
    nativeAtom "drop" [Val.list xs, Val.nat n] = some (Val.list (xs.drop n)) := rfl
theorem atom_append (xs ys : List Val) :
    nativeAtom "append" [Val.list xs, Val.list ys] = some (Val.list (xs ++ ys)) := rfl
theorem atom_cons (x : Val) (xs : List Val) :
    nativeAtom "cons" [x, Val.list xs] = some (Val.list (x :: xs)) := rfl
theorem atom_lt (a b : Nat) :
    nativeAtom "lt" [Val.nat a, Val.nat b] = some (Val.bool (decide (a < b))) := rfl
theorem atom_sub (a b : Nat) :
    nativeAtom "sub" [Val.nat a, Val.nat b] = some (Val.nat (a - b)) := rfl
theorem atom_get (xs : List Val) (i : Nat) :
    nativeAtom "get" [Val.list xs, Val.nat i] =
      some (match xs[i]? with
        | some v => Store.Val.some v
        | none => Store.Val.none) := rfl
theorem atom_pair (a b : Val) : nativeAtom "pair" [a, b] = some (Val.list [a, b]) := rfl
theorem atom_tuple (vs : List Val) : nativeAtom "tuple" vs = some (Val.list vs) := rfl
theorem atom_sameHandle (k k' : DeferredKey) :
    nativeAtom "sameHandle" [Val.promise k, Val.promise k'] =
      some (Val.bool (decide (k = k'))) :=
  Effect4.Program.Typed.sameHandle_promises k k'


/-! ## The words of a step term -/

section Words

variable {env : Env} {path : List Nat} {vals : List Val}

theorem reads_nilT : Reads nilT env path vals (Val.list []) := reads_app .nil atom_nil

theorem reads_noneT : Reads noneT env path vals Store.Val.none := reads_app .nil atom_none

theorem reads_some {a : TermSrc} {v : Val} (ha : Reads a env path vals v) :
    Reads (app "some" [a]) env path vals (Store.Val.some v) :=
  reads_app (.cons ha .nil) (atom_some v)

theorem reads_len {xs : TermSrc} {items : List Val} (hxs : Reads xs env path vals (Val.list items)) :
    Reads (len xs) env path vals (Val.nat items.length) :=
  reads_app (.cons hxs .nil) (atom_length items)

theorem reads_isEmpty {xs : TermSrc} {items : List Val}
    (hxs : Reads xs env path vals (Val.list items)) :
    Reads (isEmpty xs) env path vals (Val.bool (decide (items.length = 0))) :=
  reads_app (.cons (reads_len hxs) .nil) (atom_isZero items.length)

theorem reads_notT {b : TermSrc} {value : Bool} (hb : Reads b env path vals (Val.bool value)) :
    Reads (notT b) env path vals (Val.bool (!value)) :=
  reads_app (.cons hb .nil) (atom_not value)

theorem reads_andT {a b : TermSrc} {x y : Bool} (ha : Reads a env path vals (Val.bool x))
    (hb : Reads b env path vals (Val.bool y)) :
    Reads (andT a b) env path vals (Val.bool (x && y)) :=
  reads_app (.cons ha (.cons hb .nil)) (atom_and x y)

theorem reads_orT {a b : TermSrc} {x y : Bool} (ha : Reads a env path vals (Val.bool x))
    (hb : Reads b env path vals (Val.bool y)) :
    Reads (orT a b) env path vals (Val.bool (x || y)) :=
  reads_app (.cons ha (.cons hb .nil)) (atom_or x y)

theorem reads_ifT {c t f : TermSrc} {test : Bool} {x y : Val}
    (hc : Reads c env path vals (Val.bool test)) (ht : Reads t env path vals x)
    (hf : Reads f env path vals y) :
    Reads (ifT c t f) env path vals (if test then x else y) :=
  reads_app (.cons hc (.cons ht (.cons hf .nil))) (atom_ite test x y)

theorem reads_same {a b : TermSrc} {k k' : DeferredKey}
    (ha : Reads a env path vals (Val.promise k)) (hb : Reads b env path vals (Val.promise k')) :
    Reads (same a b) env path vals (Val.bool (decide (k = k'))) :=
  reads_app (.cons ha (.cons hb .nil)) (atom_sameHandle k k')

theorem reads_take {xs n : TermSrc} {items : List Val} {count : Nat}
    (hxs : Reads xs env path vals (Val.list items)) (hn : Reads n env path vals (Val.nat count)) :
    Reads (app "take" [xs, n]) env path vals (Val.list (items.take count)) :=
  reads_app (.cons hxs (.cons hn .nil)) (atom_take items count)

theorem reads_drop {xs n : TermSrc} {items : List Val} {count : Nat}
    (hxs : Reads xs env path vals (Val.list items)) (hn : Reads n env path vals (Val.nat count)) :
    Reads (app "drop" [xs, n]) env path vals (Val.list (items.drop count)) :=
  reads_app (.cons hxs (.cons hn .nil)) (atom_drop items count)

theorem reads_noneOf {xs : TermSrc} {items : List Val}
    (hxs : Reads xs env path vals (Val.list items)) :
    Reads (noneOf xs) env path vals (Val.list []) :=
  reads_take hxs (reads_nat 0 env path vals)

theorem reads_append {xs ys : TermSrc} {front back : List Val}
    (hxs : Reads xs env path vals (Val.list front)) (hys : Reads ys env path vals (Val.list back)) :
    Reads (app "append" [xs, ys]) env path vals (Val.list (front ++ back)) :=
  reads_app (.cons hxs (.cons hys .nil)) (atom_append front back)

theorem reads_snoc {xs x : TermSrc} {items : List Val} {v : Val}
    (hxs : Reads xs env path vals (Val.list items)) (hx : Reads x env path vals v) :
    Reads (snoc xs x) env path vals (Val.list (items ++ [v])) :=
  reads_append hxs (reads_app (.cons hx (.cons reads_nilT .nil)) (atom_cons v []))

theorem reads_lt {a b : TermSrc} {x y : Nat} (ha : Reads a env path vals (Val.nat x))
    (hb : Reads b env path vals (Val.nat y)) :
    Reads (app "lt" [a, b]) env path vals (Val.bool (decide (x < y))) :=
  reads_app (.cons ha (.cons hb .nil)) (atom_lt x y)

theorem reads_sub {a b : TermSrc} {x y : Nat} (ha : Reads a env path vals (Val.nat x))
    (hb : Reads b env path vals (Val.nat y)) :
    Reads (app "sub" [a, b]) env path vals (Val.nat (x - y)) :=
  reads_app (.cons ha (.cons hb .nil)) (atom_sub x y)

theorem reads_minT {a b : TermSrc} {x y : Nat} (ha : Reads a env path vals (Val.nat x))
    (hb : Reads b env path vals (Val.nat y)) :
    Reads (minT a b) env path vals (Val.nat (Nat.min x y)) := by
  refine (reads_ifT (reads_lt ha hb) ha hb).to ?_
  by_cases less : x < y
  · rw [decide_eq_true less, if_pos rfl]
    show Val.nat x = Val.nat (if x ≤ y then x else y)
    rw [if_pos (Nat.le_of_lt less)]
  · have ge : y ≤ x := Nat.le_of_not_lt less
    rw [decide_eq_false less, if_neg Bool.false_ne_true]
    show Val.nat y = Val.nat (if x ≤ y then x else y)
    by_cases le : x ≤ y
    · rw [if_pos le, Nat.le_antisymm le ge]
    · rw [if_neg le]

theorem reads_head {xs : TermSrc} {items : List Val}
    (hxs : Reads xs env path vals (Val.list items)) :
    Reads (app "get" [xs, nat 0]) env path vals
      (match items[0]? with
        | some v => Store.Val.some v
        | none => Store.Val.none) :=
  reads_app (.cons hxs (.cons (reads_nat 0 env path vals) .nil)) (atom_get items 0)

theorem reads_pair {a b : TermSrc} {x y : Val} (ha : Reads a env path vals x)
    (hb : Reads b env path vals y) : Reads (app "pair" [a, b]) env path vals (Val.tuple [x, y]) :=
  reads_app (.cons ha (.cons hb .nil)) (atom_pair x y)

theorem reads_tuple2 {a b : TermSrc} {x y : Val} (ha : Reads a env path vals x)
    (hb : Reads b env path vals y) : Reads (tuple [a, b]) env path vals (Val.tuple [x, y]) :=
  reads_app (.cons ha (.cons hb .nil)) (atom_tuple [x, y])

theorem reads_tuple3 {a b c : TermSrc} {x y z : Val} (ha : Reads a env path vals x)
    (hb : Reads b env path vals y) (hc : Reads c env path vals z) :
    Reads (tuple [a, b, c]) env path vals (Val.tuple [x, y, z]) :=
  reads_app (.cons ha (.cons hb (.cons hc .nil))) (atom_tuple [x, y, z])

end Words

/-! ## The cell's records: what a read answers and what an overwrite stores -/

theorem cell_cap (c m o t : Val) :
    Machine.Record.read false (cellOf c m o t) "cap" = some c := rfl
theorem cell_msgs (c m o t : Val) :
    Machine.Record.read false (cellOf c m o t) "msgs" = some m := rfl
theorem cell_offers (c m o t : Val) :
    Machine.Record.read false (cellOf c m o t) "offers" = some o := rfl
theorem cell_takers (c m o t : Val) :
    Machine.Record.read false (cellOf c m o t) "takers" = some t := rfl
theorem cell_setMsgs (c m o t v : Val) :
    Machine.Record.set (cellOf c m o t) "msgs" v = some (cellOf c v o t) := rfl
theorem cell_setOffers (c m o t v : Val) :
    Machine.Record.set (cellOf c m o t) "offers" v = some (cellOf c m v t) := rfl
theorem cell_setTakers (c m o t v : Val) :
    Machine.Record.set (cellOf c m o t) "takers" v = some (cellOf c m o v) := rfl
theorem taker_id (h i : Val) : Machine.Record.read false (takerOf h i) "id" = some i := rfl
theorem offer_id (b h i r : Val) :
    Machine.Record.read false (offerOf b h i r) "id" = some i := rfl
theorem offer_rest (b h i r : Val) :
    Machine.Record.read false (offerOf b h i r) "rest" = some r := rfl
theorem taker_build (i h : Val) :
    Machine.Record.build ["id", "hint"] [i, h] = some (takerOf h i) := rfl
theorem offer_build (i h b r : Val) :
    Machine.Record.build ["id", "hint", "batch", "rest"] [i, h, b, r] = some (offerOf b h i r) :=
  rfl


/-! ## The passes, on the encoding of a model's lists -/

section Passes

variable {env : Env} {path : List Nat} {vals : List Val}

/-- On an injective table the identity test on two handles decides the two identities. -/
theorem Table.Injective.decides {tb : Table} (injective : tb.Injective) (a b : Nat) :
    decide (tb.handle a = tb.handle b) = decide (a = b) :=
  decide_eq_decide.mpr ⟨injective a b, fun same => congrArg tb.handle same⟩

/-- A fold that appends the elements it keeps is a filter. -/
theorem foldl_keep {α : Type} (p : α → Prop) [DecidablePred p] :
    ∀ (xs kept : List α),
      xs.foldl (fun kept x => if p x then kept else kept ++ [x]) kept =
        kept ++ xs.filter (fun x => !decide (p x))
  | [], kept => by rw [List.foldl_nil, List.filter_nil, List.append_nil]
  | x :: xs, kept => by
    rw [List.foldl_cons, foldl_keep p xs, List.filter_cons]
    by_cases holds : p x
    · rw [if_pos holds, decide_eq_true holds]
      rfl
    · rw [if_neg holds, decide_eq_false holds, List.append_assoc]
      rfl

/-- A waiting taker's record, built from an identity and a hint. -/
theorem reads_mkTaker {id hint : TermSrc} {i h : Val} (hid : Reads id env path vals i)
    (hhint : Reads hint env path vals h) :
    Reads (Queue.mkTaker id hint) env path vals (takerOf h i) :=
  reads_record (.cons hid (.cons hhint .nil)) (taker_build i h)

/-- A pending offer's record. -/
theorem reads_mkOffer (A : Ty) {id hint batch rest : TermSrc} {i h b r : Val}
    (hid : Reads id env path vals i) (hhint : Reads hint env path vals h)
    (hbatch : Reads batch env path vals b) (hrest : Reads rest env path vals r) :
    Reads (Queue.mkOffer A id hint batch rest) env path vals (offerOf b h i r) :=
  reads_record (.cons hid (.cons hhint (.cons hbatch (.cons hrest .nil)))) (offer_build i h b r)

/-- The wake's pass: the earliest stored taker, where a message is buffered. -/
theorem reads_wake {takers msgs : TermSrc} {ts ms : List Val}
    (htakers : Reads takers env path vals (Val.list ts))
    (hmsgs : Reads msgs env path vals (Val.list ms)) :
    Reads (Queue.wake takers msgs) env path vals
      (Val.list (if ms.length = 0 then [] else ts.take 1)) := by
  refine (reads_ifT (reads_isEmpty hmsgs) (reads_noneOf htakers)
    (reads_take htakers (reads_nat 1 env path vals))).to ?_
  by_cases empty : ms.length = 0
  · rw [decide_eq_true empty, if_pos rfl, if_pos empty]
  · rw [decide_eq_false empty, if_neg Bool.false_ne_true, if_neg empty]

/-- The identity of a folded taker against the request's, under the fold's binders. -/
theorem reads_sameTaker {id : TermSrc} (tb : Table) (injective : tb.Injective) (i : Nat)
    (depth : vals.length = env.names.length)
    (hid : Captured id env path vals (Val.promise (tb.handle i))) (acc : Val) (t : Taker) :
    Reads (same (field (minted (env.mint "item")) "id") id)
      (env.push [env.mint "acc", env.mint "item"]) path (vals ++ [acc, takerVal tb t])
      (Val.bool (decide (t.id = i))) :=
  (reads_same (reads_field (reads_minted_item depth path acc (takerVal tb t)) (taker_id _ _))
    (hid.underFold acc (takerVal tb t))).to (by rw [injective.decides])

/-- `enrolled`: whether the request waits among the takers. -/
theorem reads_enrolled {takers id : TermSrc} (tb : Table) (injective : tb.Injective)
    (ts : List Taker) (i : Nat) (depth : vals.length = env.names.length)
    (htakers : Reads takers env path vals (Val.list (ts.map (takerVal tb))))
    (hid : Captured id env path vals (Val.promise (tb.handle i))) :
    Reads (Queue.enrolled takers id) env path vals
      (Val.bool (ts.foldl (fun found t => found || decide (t.id = i)) false)) :=
  reads_foldWith_model (takerVal tb) Val.bool (fun found t => found || decide (t.id = i)) ts
    false ⟨0, 1, 1⟩ htakers (reads_bool false env path vals) fun found t =>
      reads_orT (reads_minted_acc depth path (Val.bool found) (takerVal tb t))
        (reads_sameTaker tb injective i depth hid (Val.bool found) t)

/-- `isHead`: whether the request is the earliest taker. -/
theorem reads_isHead {takers id : TermSrc} (tb : Table) (injective : tb.Injective)
    (ts : List Taker) (i : Nat) (depth : vals.length = env.names.length)
    (htakers : Reads takers env path vals (Val.list (ts.map (takerVal tb))))
    (hid : Captured id env path vals (Val.promise (tb.handle i))) :
    Reads (Queue.isHead takers id) env path vals
      (Val.bool ((ts.take 1).foldl (fun _ t => decide (t.id = i)) false)) :=
  reads_foldWith_model (takerVal tb) Val.bool (fun _ t => decide (t.id = i)) (ts.take 1) false
    ⟨0, 1, 1⟩ ((reads_take htakers (reads_nat 1 env path vals)).to (by rw [List.map_take]))
    (reads_bool false env path vals) fun found t =>
      reads_sameTaker tb injective i depth hid (Val.bool found) t

/-- `removeTaker`: the takers without the request. -/
theorem reads_removeTaker {takers id : TermSrc} (tb : Table) (injective : tb.Injective)
    (ts : List Taker) (i : Nat) (depth : vals.length = env.names.length)
    (htakers : Reads takers env path vals (Val.list (ts.map (takerVal tb))))
    (hid : Captured id env path vals (Val.promise (tb.handle i))) :
    Reads (Queue.removeTaker takers id) env path vals
      (Val.list ((ts.filter (fun t => t.id != i)).map (takerVal tb))) := by
  have folded : Reads (Queue.removeTaker takers id) env path vals
      (Val.list ((ts.foldl (fun kept t => if t.id = i then kept else kept ++ [t]) []).map
        (takerVal tb))) :=
    reads_foldWith_model (takerVal tb)
    (fun kept : List Taker => Val.list (kept.map (takerVal tb)))
    (fun kept t => if t.id = i then kept else kept ++ [t]) ts [] ⟨0, 1, 1⟩ htakers
    (reads_noneOf htakers) fun kept t => by
      refine (reads_ifT (reads_sameTaker tb injective i depth hid _ t)
        (reads_minted_acc depth path _ (takerVal tb t))
        (reads_snoc (reads_minted_acc depth path _ (takerVal tb t))
          (reads_minted_item depth path _ (takerVal tb t)))).to ?_
      by_cases same : t.id = i
      · rw [decide_eq_true same, if_pos rfl, if_pos same]
      · rw [decide_eq_false same, if_neg Bool.false_ne_true, if_neg same, List.map_append]
        rfl
  exact folded.to (by rw [foldl_keep, List.nil_append]; rfl)

/-- The identity of a folded offer against the request's, under the fold's binders. -/
theorem reads_sameOffer {id : TermSrc} (tb : Table) (msg : Nat → Val) (injective : tb.Injective)
    (i : Nat) (depth : vals.length = env.names.length)
    (hid : Captured id env path vals (Val.promise (tb.handle i))) (acc : Val) (o : Offer) :
    Reads (same (field (minted (env.mint "item")) "id") id)
      (env.push [env.mint "acc", env.mint "item"]) path (vals ++ [acc, offerVal tb msg o])
      (Val.bool (decide (o.id = i))) :=
  (reads_same
    (reads_field (reads_minted_item depth path acc (offerVal tb msg o)) (offer_id _ _ _ _))
    (hid.underFold acc (offerVal tb msg o))).to (by rw [injective.decides])

/-- `removeOffer`: the pending offers without the request. -/
theorem reads_removeOffer {offers id : TermSrc} (tb : Table) (msg : Nat → Val)
    (injective : tb.Injective) (os : List Offer) (i : Nat)
    (depth : vals.length = env.names.length)
    (hoffers : Reads offers env path vals (Val.list (os.map (offerVal tb msg))))
    (hid : Captured id env path vals (Val.promise (tb.handle i))) :
    Reads (Queue.removeOffer offers id) env path vals
      (Val.list ((os.filter (fun o => o.id != i)).map (offerVal tb msg))) := by
  have folded : Reads (Queue.removeOffer offers id) env path vals
      (Val.list ((os.foldl (fun kept o => if o.id = i then kept else kept ++ [o]) []).map
        (offerVal tb msg))) :=
    reads_foldWith_model (offerVal tb msg)
      (fun kept : List Offer => Val.list (kept.map (offerVal tb msg)))
      (fun kept o => if o.id = i then kept else kept ++ [o]) os [] ⟨0, false, []⟩ hoffers
      (reads_noneOf hoffers) fun kept o => by
        refine (reads_ifT (reads_sameOffer tb msg injective i depth hid _ o)
          (reads_minted_acc depth path _ (offerVal tb msg o))
          (reads_snoc (reads_minted_acc depth path _ (offerVal tb msg o))
            (reads_minted_item depth path _ (offerVal tb msg o)))).to ?_
        by_cases same : o.id = i
        · rw [decide_eq_true same, if_pos rfl, if_pos same]
        · rw [decide_eq_false same, if_neg Bool.false_ne_true, if_neg same, List.map_append]
          rfl
  exact folded.to (by rw [foldl_keep, List.nil_append]; rfl)

/-- A fold that appends what each element gives is the list with the elements' gifts. -/
theorem foldl_append_flatMap {α β : Type} (f : α → List β) :
    ∀ (xs : List α) (init : List β),
      xs.foldl (fun acc x => acc ++ f x) init = init ++ xs.flatMap f
  | [], init => by rw [List.foldl_nil, List.flatMap_nil, List.append_nil]
  | x :: xs, init => by
    rw [List.foldl_cons, foldl_append_flatMap f xs, List.flatMap_cons, List.append_assoc]

/-- `fitting`: how many pending offers enter the room. -/
theorem reads_fitting {room offers : TermSrc} {r : Nat} {os : List Val}
    (hroom : Reads room env path vals (Val.nat r))
    (hoffers : Reads offers env path vals (Val.list os)) :
    Reads (Queue.fitting room offers) env path vals (Val.nat (Nat.min r os.length)) :=
  reads_minT hroom (reads_len hoffers)

/-- `entering`: the offers that enter, on the encoding of the pending offers. -/
theorem reads_entering {room offers : TermSrc} (tb : Table) (msg : Nat → Val) (r : Nat)
    (os : List Offer) (hroom : Reads room env path vals (Val.nat r))
    (hoffers : Reads offers env path vals (Val.list (os.map (offerVal tb msg)))) :
    Reads (Queue.entering room offers) env path vals
      (Val.list ((os.take (Nat.min r os.length)).map (offerVal tb msg))) :=
  (reads_take hoffers (reads_fitting hroom hoffers)).to
    (by rw [List.length_map, List.map_take])

/-- `staying`: the offers that stay pending. -/
theorem reads_staying {room offers : TermSrc} (tb : Table) (msg : Nat → Val) (r : Nat)
    (os : List Offer) (hroom : Reads room env path vals (Val.nat r))
    (hoffers : Reads offers env path vals (Val.list (os.map (offerVal tb msg)))) :
    Reads (Queue.staying room offers) env path vals
      (Val.list ((os.drop (Nat.min r os.length)).map (offerVal tb msg))) :=
  (reads_drop hoffers (reads_fitting hroom hoffers)).to
    (by rw [List.length_map, List.map_drop])

/-- `gained`: the buffer with the messages of the offers that enter. -/
theorem reads_gained {room msgs offers : TermSrc} (tb : Table) (msg : Nat → Val) (r : Nat)
    (ms : List Nat) (os : List Offer) (depth : vals.length = env.names.length)
    (hroom : Reads room env path vals (Val.nat r))
    (hmsgs : Reads msgs env path vals (Val.list (ms.map msg)))
    (hoffers : Reads offers env path vals (Val.list (os.map (offerVal tb msg)))) :
    Reads (Queue.gained room msgs offers) env path vals
      (Val.list ((ms ++ (os.take (Nat.min r os.length)).flatMap (·.rest)).map msg)) := by
  have folded : Reads (Queue.gained room msgs offers) env path vals
      (Val.list (((os.take (Nat.min r os.length)).foldl (fun buffer o => buffer ++ o.rest)
        ms).map msg)) :=
    reads_foldWith_model (offerVal tb msg) (fun buffer : List Nat => Val.list (buffer.map msg))
      (fun buffer o => buffer ++ o.rest) (os.take (Nat.min r os.length)) ms ⟨0, false, []⟩
      (reads_entering tb msg r os hroom hoffers) hmsgs fun buffer o =>
        (reads_append (reads_minted_acc depth path _ (offerVal tb msg o))
          (reads_field (reads_minted_item depth path _ (offerVal tb msg o))
            (offer_rest _ _ _ _))).to (by rw [List.map_append])
  exact folded.to (by rw [foldl_append_flatMap])

end Passes

end Effect4.Queue.Model
