import Lean

/-!
# Program.FoldOf — a hand traversal becomes its algebra, with the proof

`fold_of f` reads a definition `f` that recurses structurally on a free object of the estate
(`Eff`'s family, `Ty`, `Term`, `CauseTerm`, `Representation`) and adds three kinds of
declaration:

- `f.alg`, the algebra: one field per constructor of every family member, the constructor's
  arm of `f` with each recursive call `f child` replaced by that child's result;
- `f.hom`, the homomorphism witness (`EffHom f.alg`, `TyHom f.alg`, …): the members of `f`'s
  mutual block as the functions, and the arm equations as the field proofs, each by `rfl`
  (structural recursion reduces on a constructor);
- `g.eq_cata : ∀ e, g e = cata_<fam> f.alg e` for every member `g` of the block, by the
  generated uniqueness theorem (`hom_eq_cata_<fam>`).

Five shapes, chosen by reading `f`:

- **catamorphism** — the arms use only the children's results;
- **paramorphism** — an arm uses a child's value as well; the carrier pairs the value in and
  the connector reads `g e = (cata alg e).2`;
- **accumulator** — arguments before or after the family value that a recursive call changes
  (`effTy sig env e`, `findInt pos t`, `hasTy v t allocated`, `build sem l ctx`); the carrier
  is the function type over them, the arm a lambda, and the connector
  `g fixed pre e post = cata alg e pre post`. The binders every recursive call passes through
  unchanged are the fixed prefix and stay parameters of the algebra;
- **list sibling** — a block member over `List M` (`renderList` beside `render`) is a
  `List.foldr` over the mapped results, its `nil` and `cons` read off its two arms, with
  `s.eq_foldr` by induction on the list and `s.eq_cata` against the generated positional fold;
- **container paramorphism** — an arm uses a child under a container or a wrapper as a value
  (`encodeList xs`; a node rebuilt with its children; a case analysis on the child list). The
  value is read back from the paired results through the position's functor map
  (`List.map Prod.fst`, `Option.map`, the generated `W.map`), and the equation transports along
  the two functor laws (`map_map`, `map_id`) — the reading of the mapped results is the
  argument itself.

Family members the block does not traverse get the carrier `Unit`. Nothing in `f`'s own module
changes: this is the second file beside it, and `eq_cata` is the connector its callers move
across before `f` is deleted. Refused by name: a recursive call on something other than an
immediate child.

The names it relies on are the generator's (`tools/Effect4Gen/Fold.lean`): for a block whose
first member is `X` in namespace `N`, `N.XFam` with one constructor per member in declaration
order, `N.XAlgebra (params…) (R : XFam → Type u)` with fields `<fam>_<ctor>` in
member-then-constructor order, `N.XHom alg` with fields `f_<fam>` then `h_<fam>_<ctor>` in the
same order, and `N.hom_eq_cata_<fam>`, `N.cata_<fam>`.
-/

open Lean Meta Elab Command

namespace Effect4.Program.FoldOf

/-- The generated fold vocabulary of one free object. -/
structure Family where
  /-- The inductive and everything mutual with it. -/
  members : Array Name
  /-- The `Fam` enumeration's constructors, one per member, in the same order. -/
  fams : Array Name
  algebra : Name
  hom : Name
  /-- `cata_<fam>` per member. -/
  catas : Array Name
  /-- `hom_eq_cata_<fam>` per member. -/
  uniques : Array Name
  /-- The parameters of the inductive as `f`'s domain applies them (`Eff NativeOp` ↦ `[NativeOp]`). -/
  params : Array Expr

/-- The family of the inductive a type is an application of, if it has a generated fold. -/
def familyOf? (domain : Expr) : MetaM (Option Family) := do
  let domain ← whnf domain
  let .const member _ := domain.getAppFn | return none
  let some (.inductInfo info) := (← getEnv).find? member | return none
  -- the generated names follow the block's first member (`EffFam` for `Stmts` too)
  let root := info.all.head!
  let ns := root.getPrefix
  let famType := ns ++ Name.mkSimple (root.getString! ++ "Fam")
  let some (.inductInfo famInfo) := (← getEnv).find? famType | return none
  unless famInfo.ctors.length == info.all.length do
    throwError "fold_of: {famType} has {famInfo.ctors.length} constructors but {root} has \
      {info.all.length} members"
  let fams := famInfo.ctors.toArray
  let stems := fams.map (·.getString!)
  let algebra := ns ++ Name.mkSimple (root.getString! ++ "Algebra")
  let hom := ns ++ Name.mkSimple (root.getString! ++ "Hom")
  let catas := stems.map fun s => ns ++ Name.mkSimple ("cata_" ++ s)
  let uniques := stems.map fun s => ns ++ Name.mkSimple ("hom_eq_cata_" ++ s)
  for n in #[algebra, hom] ++ catas ++ uniques do
    unless (← getEnv).contains n do throwError "fold_of: the generated {n} does not exist"
  return some
    { members := info.all.toArray, fams, algebra, hom, catas, uniques
      params := domain.getAppArgs.extract 0 info.numParams }

/-- One member of `f`'s mutual block: its type, which family member it takes (directly, or as
a `List` of it — the list sibling of a traversal, `renderList` beside `render`) and at which
binder. -/
structure Member where
  fn : Name
  type : Expr
  /-- Index into `Family.members`. -/
  member : Nat
  /-- The binder index of the family value. -/
  at_ : Nat
  /-- Binders in all. -/
  arity : Nat
  /-- The binder is `List M` rather than `M`: a positional sibling, folded by `List.foldr`. -/
  isList : Bool
  /-- For a sibling over a list of products holding the member (`renderFields : List (String ×
  Ty) → String` beside `renderRaw`): the element type. `none` for a sibling over `List M`. -/
  elem : Option Expr := none
deriving Inhabited

/-- Which family member a type is, directly or under `List`, with the inductive's parameters
as applied there. -/
def familyArgsOf (fam : Family) (t : Expr) : MetaM (Option (Nat × Array Expr × Bool)) := do
  let t ← whnf t
  let (t, isList) ← match t.getAppFn with
    | .const ``List _ => pure (← whnf t.appArg!, true)
    | _ => pure (t, false)
  let .const c _ := t.getAppFn | return none
  let some j := fam.members.idxOf? c | return none
  return some (j, t.getAppArgs.extract 0 fam.params.size, isList)

/-- The leaves of a product type, left to right (a non-product type is its own one leaf). -/
def prodLeaves : Nat → Expr → MetaM (Array Expr)
  | 0, t => throwError "fold_of: the product {t} is nested too deep"
  | fuel + 1, t => do
    let t ← whnfR t
    if t.isAppOfArity ``Prod 2 then
      return (← prodLeaves fuel t.appFn!.appArg!) ++ (← prodLeaves fuel t.appArg!)
    return #[t]

/-- `List E` with `E` a product holding exactly one family member among its leaves, the others
naming none (`List (String × Ty)`, `List (String × Ty × Bool)`): the member and the element type.
What a sibling over a field list reads (decisions row 171; probe Q, Q3). -/
def pairElemOf (fam : Family) (t : Expr) : MetaM (Option (Nat × Expr)) := do
  let t ← whnf t
  unless t.isAppOfArity ``List 1 do return none
  let e ← whnfR t.appArg!
  unless e.isAppOfArity ``Prod 2 do return none
  let mentions := fun (s : Expr) => fam.members.any fun mem => (s.find? (·.isConstOf mem)).isSome
  let mut found : Option Nat := none
  for leaf in ← prodLeaves 8 e do
    match ← familyArgsOf fam leaf with
    | some (j, _, false) =>
      if found.isSome then return none
      found := some j
    | _ => if mentions leaf then return none
  match found with
  | some j =>
    if e.hasFVar || e.hasMVar then
      throwError "fold_of: the element type {e} depends on a binder; a field-list sibling reads a closed one"
    return some (j, e)
  | none => return none

/-- Read `g`'s signature: the first binder whose type is a family member, or, when there is
none, the first whose type is a list of one (the list sibling), or a list of products holding one
(the field-list sibling). -/
def memberOf (fam : Family) (g : Name) : MetaM Member := do
  let info ← getConstInfoDefn g
  forallTelescope info.type fun xs _ => do
    for h : i in [:xs.size] do
      if let some (j, _, false) ← familyArgsOf fam (← inferType xs[i]) then
        return { fn := g, type := info.type, member := j, at_ := i, arity := xs.size, isList := false }
    for h : i in [:xs.size] do
      if let some (j, _, true) ← familyArgsOf fam (← inferType xs[i]) then
        return { fn := g, type := info.type, member := j, at_ := i, arity := xs.size, isList := true }
    for h : i in [:xs.size] do
      if let some (j, e) ← pairElemOf fam (← inferType xs[i]) then
        return { fn := g, type := info.type, member := j, at_ := i, arity := xs.size, isList := true,
                 elem := some e }
    throwError "fold_of: {g} takes no value of the family {fam.members}"

/-- `XFam.rec (motive := fun _ => Type u) T₁ … Tₙ`, as a function of the family. -/
def carrierOf (famType : Name) (level : Level) (carriers : Array Expr) : MetaM Expr :=
  withLocalDeclD `fam (mkConst famType) fun famVar => do
    let motive ← mkLambdaFVars #[famVar] (mkSort (mkLevelSucc level))
    let recFn := mkConst (famType ++ `rec) [mkLevelSucc (mkLevelSucc level)]
    mkLambdaFVars #[famVar] (mkAppN recFn (#[motive] ++ carriers ++ #[famVar]))

/-- The number of leading binders of a type. -/
def forallArity : Expr → Nat
  | .forallE _ _ b _ => forallArity b + 1
  | _ => 0

/-- Whether an application of a recursor has a constructor as its major premise. -/
def recMajorIsCtor (env : Environment) (e : Expr) : Bool :=
  match e.getAppFn with
  | .const n _ =>
    match env.find? n with
    | some (.recInfo rec) =>
      let args := e.getAppArgs
      rec.getMajorIdx < args.size &&
        (match args[rec.getMajorIdx]!.getAppFn with
          | .const c _ => (env.find? c matches some (.ctorInfo _))
          | _ => false)
    | _ => false
  | _ => false

/-- Unfold a `casesOn` (or one of the match compiler's helpers, `f._sparseCasesOn_1`) to the
recursor application under it, in at most three delta steps. -/
def recAppOf (e : Expr) : MetaM Expr := do
  let env ← getEnv
  let mut e := e
  for _ in [:3] do
    match e.getAppFn with
    | .const n _ =>
      if env.find? n matches some (.recInfo _) then return e
      if isAuxRecursor env n then
        let some e' ← reduceRecMatcher? e | return e
        e := e'
      else if n.components.any (fun c => "_sparseCasesOn".isPrefixOf c.toString) then
        let some e' ← delta? e | return e
        e := e'.headBeta
      else return e
    | .lam .. => e := e.headBeta
    | _ => return e
  return e

/-- Does a stuck matcher application split on a CONSTRUCTOR at one of its discriminants?

This is the whole test for whether unfolding it can make progress. A match on more than the
family value (`| .unit, .unit => …`, the two-discriminant arms of `Codec.encodeRaw`) has the
node as one discriminant and something opaque as another: `reduceMatcher?` is stuck on the
opaque one, and unfolding lets the node's own split reduce. A match whose discriminants are
ALL opaque is a different animal — it is `match v with`, the accumulator's value, written by
the source. Unfolding that one gains nothing and costs the arm its matcher, which is what
`split` needs to see a case analysis. So it stays. -/
def matchOnCtorDiscr (n : Name) (e : Expr) : MetaM Bool := do
  let some info ← getMatcherInfo? n | return false
  let args := e.getAppArgs
  let first := info.getFirstDiscrPos
  if args.size < first + info.numDiscrs then return false
  let env ← getEnv
  for i in [first : first + info.numDiscrs] do
    if let .const c _ := args[i]!.getAppFn then
      if env.find? c matches some (.ctorInfo _) then return true
  return false

/-- Reduce every case split — a matcher, a `casesOn`, or one of the match compiler's own
helpers — whose major premise is a constructor, at any depth, one step at a time; a split on a
variable stays as written (readable, compilable), and what is inside it is reduced.

A split on a variable stays *as the source wrote it*: the matcher, not the `casesOn` or the
`_sparseCasesOn` underneath it. That is the difference between an algebra whose arms a proof
can `split` and one whose arms it can only `cases` a value through — the arm of an emitted
algebra is read back by exactly the tactics that read the hand definition's arm. -/
def reduceCases (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun e₀ => do
    unless e₀.isApp do return .continue
    -- an unfolded definition applied to its arguments
    if e₀.getAppFn.isLambda then return .visit e₀.headBeta
    let .const n _ := e₀.getAppFn | return .continue
    let env ← getEnv
    if isMatcherCore env n then
      match ← reduceMatcher? e₀ with
      | .reduced e' => return .visit e'
      -- a match on more than the family value: unfold it, so the splits underneath can reduce
      | .stuck _ =>
        if ← matchOnCtorDiscr n e₀ then return .visit ((← delta? e₀).getD e₀).headBeta
        else return .continue
      | _ => return .continue
    if isAuxRecursor env n || n.components.any (fun c => "_sparseCasesOn".isPrefixOf c.toString) then
      let r ← recAppOf e₀
      if recMajorIsCtor env r then
        let some e' ← reduceRecMatcher? r | return .continue
        return .visit e'
      return .continue
    if env.find? n matches some (.recInfo _) then
      if recMajorIsCtor env e₀ then
        let some e' ← reduceRecMatcher? e₀ | return .continue
        return .visit e'
    return .continue)

/-- `g`'s arm at a constructor: its unfold equation's right-hand side at the binders around the
node (`g … node … = M`, as the proof `M`'s equation gives it), and `M` with every case split on
the node reduced — the arm as written, with the recursive calls visible. -/
def armOf (m : Member) (before : Array Expr) (node : Expr) (after : Array Expr) :
    MetaM (Expr × Expr) := do
  let some eqDef ← getUnfoldEqnFor? m.fn (nonRec := true)
    | throwError "fold_of: {m.fn} has no unfold equation"
  let eq ← instantiateForall (← getConstInfo eqDef).type (before ++ #[node] ++ after)
  let some (_, _, rhs) := eq.eq? | throwError "fold_of: {eqDef} is not an equation"
  return (rhs, ← reduceCases rhs)

/-- The unfold equation of `g` at the binders around the node: `g … node … = M`. -/
def unfoldEqAt (m : Member) (levels : List Level) (before : Array Expr) (node : Expr)
    (after : Array Expr) : MetaM Expr := do
  let some eqDef ← getUnfoldEqnFor? m.fn (nonRec := true)
    | throwError "fold_of: {m.fn} has no unfold equation"
  return mkAppN (mkConst eqDef levels) (before ++ #[node] ++ after)

/-- `optParam T d` and `autoParam T tac` are a binder's annotations, not its type. -/
def stripParamAnnotations (e : Expr) : Expr :=
  e.replace fun sub =>
    if sub.isOptParam || sub.isAutoParam then some sub.appFn!.appArg! else none

/-- Every application of a block member inside `e`, the spine's partial applications included. -/
def appsIn (block : Array Name) : Expr → Array Expr → Array Expr
  | e@(.app fn arg), acc =>
    let acc := match e.getAppFn with
      | .const g _ => if block.contains g then acc.push e else acc
      | _ => acc
    appsIn block arg (appsIn block fn acc)
  | .lam _ t b _, acc => appsIn block b (appsIn block t acc)
  | .forallE _ t b _, acc => appsIn block b (appsIn block t acc)
  | .letE _ t v b _, acc => appsIn block b (appsIn block v (appsIn block t acc))
  | .mdata _ e, acc => appsIn block e acc
  | .proj _ _ e, acc => appsIn block e acc
  | _, acc => acc

/-- Every maximal application of a block member inside `e` (a spine's partial applications
are prefixes of the call they belong to and are dropped). -/
def callsIn (block : Array Name) (e : Expr) (acc : Array Expr) : Array Expr :=
  let apps := appsIn block e acc
  apps.filter fun a => !apps.any fun c =>
    c != a && c.getAppFn == a.getAppFn && c.getAppNumArgs > a.getAppNumArgs &&
      c.getAppArgs.extract 0 a.getAppNumArgs == a.getAppArgs

/-- The constructors a member's arms split on: the family member's, or `List`'s for a sibling. -/
def ctorsOf (fam : Family) (m : Member) : MetaM (Array Name) := do
  if m.isList then return #[``List.nil, ``List.cons]
  return (← getConstInfoInduct fam.members[m.member]!).ctors.toArray

/-- A list sibling's element type: the member, or the product a field-list sibling reads. -/
def elemTypeOf (fam : Family) (m : Member) (params : Array Expr) : Expr :=
  m.elem.getD (mkAppN (mkConst fam.members[m.member]!) params)

/-- A constructor's type at the member's parameters (`List`'s at the element type). -/
def ctorTypeAt (fam : Family) (m : Member) (ctor : Name) (params : Array Expr) : MetaM Expr := do
  let ty := (← getConstInfoCtor ctor).type
  if m.isList then instantiateForall ty #[elemTypeOf fam m params]
  else instantiateForall ty params

/-- A constructor applied to the member's parameters and its arguments. -/
def nodeOf (fam : Family) (m : Member) (ctor : Name) (params : Array Expr) (args : Array Expr) : Expr :=
  if m.isList then mkAppN (mkAppN (mkConst ctor [Level.zero]) #[elemTypeOf fam m params]) args
  else mkAppN (mkAppN (mkConst ctor) params) args

/-- The fold generator's name for a position (`tools/Effect4Gen/Fold.lean`, `Pos.suffix` and
`leafHint`): a member by its family label, a product `prod_<a>_<b>`, a leaf by the last dotted
component of its printed type with the first letter lowered. A field-list sibling's `eq_cata`
reads the generated `cata_pos_list_<suffix>_eq` by this name. -/
def posSuffix (fam : Family) : Nat → Expr → MetaM String
  | 0, t => throwError "fold_of: the position {t} is nested too deep"
  | fuel + 1, t => do
    let t ← whnfR t
    if t.isAppOfArity ``Prod 2 then
      return "prod_" ++ (← posSuffix fam fuel t.appFn!.appArg!) ++ "_" ++ (← posSuffix fam fuel t.appArg!)
    if let some (j, _, false) ← familyArgsOf fam t then return fam.fams[j]!.getString!
    let text ← withOptions (fun o => (o.setBool `pp.fullNames true).setBool `pp.universes false) do
      return toString (← ppExpr t)
    let kept := text.foldl (fun acc c => if c.isAlphanum || c == '.' then acc.push c else acc) ""
    let last := ((kept.splitOn ".").reverse.head?).getD ""
    match last.toList with
    | [] => return "leaf"
    | c :: rest => return String.ofList (c.toLower :: rest)

/-- An element of a product type as a constructor tree over fresh locals, one per leaf, so that the
pair split of a field-list sibling's arm reduces (`(n, t) :: rest`, not `x :: rest`). -/
def withElemCtor {α : Type} : Nat → Expr → Array Expr → (Array Expr → Expr → MetaM α) → MetaM α
  | 0, t, _, _ => throwError "fold_of: the product {t} is nested too deep"
  | fuel + 1, t, acc, k => do
    let t ← whnfR t
    if t.isAppOfArity ``Prod 2 then
      withElemCtor fuel t.appFn!.appArg! acc fun acc1 ea =>
        withElemCtor fuel t.appArg! acc1 fun acc2 eb => do
          k acc2 (← mkAppM ``Prod.mk #[ea, eb])
    else withLocalDeclD (Name.mkSimple s!"e{acc.size}") t fun x => k (acc.push x) x

/-- The leaves of a value of a product type, by projection, left to right. -/
def elemProjs : Nat → Expr → Expr → MetaM (Array Expr)
  | 0, t, _ => throwError "fold_of: the product {t} is nested too deep"
  | fuel + 1, t, e => do
    let t ← whnfR t
    if t.isAppOfArity ``Prod 2 then
      return (← elemProjs fuel t.appFn!.appArg! (← mkAppM ``Prod.fst #[e])) ++
        (← elemProjs fuel t.appArg! (← mkAppM ``Prod.snd #[e]))
    return #[e]

/-- A proof of `motive x` for `x` of a product type, from one of `motive` at the constructor tree
over the leaves (`Prod.rec`, nested): what reduces a field-list sibling's arm in its `eq_foldr`. -/
def caseElem : Nat → Expr → Expr → (Expr → MetaM Expr) → MetaM Expr
  | 0, x, _, _ => throwError "fold_of: the product at {x} is nested too deep"
  | fuel + 1, x, motive, k => do
    let t ← whnfR (← inferType x)
    unless t.isAppOfArity ``Prod 2 do return ← k x
    let α := t.appFn!.appArg!
    let β := t.appArg!
    let mk ← withLocalDeclD `a α fun a => withLocalDeclD `b β fun b => do
      let motiveA ← withLocalDeclD `a' α fun a' => do
        mkLambdaFVars #[a'] (motive.beta #[← mkAppM ``Prod.mk #[a', b]])
      let pa ← caseElem fuel a motiveA fun aval => do
        let motiveB ← withLocalDeclD `b' β fun b' => do
          mkLambdaFVars #[b'] (motive.beta #[← mkAppM ``Prod.mk #[aval, b']])
        caseElem fuel b motiveB fun bval => do
          let v ← mkAppM ``Prod.mk #[aval, bval]
          mkExpectedTypeHint (← k v) (motive.beta #[v])
      mkLambdaFVars #[a, b] pa
    mkAppOptM ``Prod.rec #[some α, some β, some motive, some mk, some x]

/-- The arguments and the node of `m`'s arm at a constructor: the constructor's fields, or, for a
field-list sibling at `List.cons`, the element's leaves and the tail with the element built as a
constructor tree. -/
def withArmNode {α : Type} (fam : Family) (m : Member) (ctor : Name) (params : Array Expr)
    (k : Array Expr → Expr → MetaM α) : MetaM α := do
  match m.elem with
  | some e =>
    if ctor == ``List.cons then
      withElemCtor 8 e #[] fun leaves xval =>
        withLocalDeclD `rest (mkApp (mkConst ``List [Level.zero]) e) fun restV =>
          k (leaves.push restV) (mkAppN (mkConst ``List.cons [Level.zero]) #[e, xval, restV])
    else k #[] (mkApp (mkConst ``List.nil [Level.zero]) e)
  | none =>
    let ctorTy ← ctorTypeAt fam m ctor params
    forallTelescope ctorTy fun args _ => k args (nodeOf fam m ctor params args)

/-- The number of leading binders that every member has and that every recursive call in the
block passes through unchanged: the fixed prefix. -/
def fixedPrefix (block : Array Name) (members : Array Member) (fam : Family) : MetaM Nat := do
  let mut k := members.foldl (fun k m => min k m.at_) members[0]!.at_
  for m in members do
    k ← forallTelescope m.type fun xs _ => do
      -- the family's parameters as the member's binder applies them; a field-list sibling's
      -- binder is a list of products, so they are read off the element's member leaf
      let params ← match m.elem with
        | some e => do
          let mut found : Option (Array Expr) := none
          for leaf in ← prodLeaves 8 e do
            if let some (_, ps, false) ← familyArgsOf fam leaf then found := some ps
          let some ps := found
            | throwError "fold_of: {m.fn}: no leaf of the element {e} is a member of the family"
          pure ps
        | none => do
          let some (_, ps, _) ← familyArgsOf fam (← inferType xs[m.at_]!)
            | throwError "fold_of: {m.fn}: the family value's type could not be read"
          pure ps
      let mut k := k
      for ctor in ← ctorsOf fam m do
        k ← withArmNode fam m ctor params fun _ node => do
          let (_, arm) ← armOf m (xs.extract 0 m.at_) node (xs.extract (m.at_ + 1) xs.size)
          let mut k := k
          for call in callsIn block arm #[] do
            let cargs := call.getAppArgs
            k := min k cargs.size
            for j in [:k] do
              if cargs[j]! != xs[j]! then k := min k j
          pure k
      pure k
  return k

/-- A block member's signature under the fixed binders, opened: `k ys pre body` where `ys[pre]`
is the family value and the rest of `ys` are the varying binders. -/
def withShape {α : Type} (fixed : Array Expr) (fixedCount : Nat) (m : Member)
    (k : Array Expr → Nat → Expr → MetaM α) : MetaM α := do
  let ty ← instantiateForall m.type fixed
  forallTelescope ty fun ys body => k ys (m.at_ - fixedCount) body

/-- What reading a position needs of the block: the members at the family's parameters, the
first projection out of the paired carrier, and the hom's function at each member. -/
structure Positions where
  members : Array Name
  /-- The family's namespace: the fold generator's `prodMapSnd`/`prodMapFst`/`prodMapBoth`. -/
  ns : Name
  memberTy : Nat → Expr
  /-- `Prod.fst : M × R → M` at member `j`. -/
  fstFn : Nat → Expr
  /-- The hom's function at member `j`, `fun e => (e, f e)` under `para`. -/
  fv : Nat → Expr

/-- The functor map through a position's type with `atMember j` at the member: `List.map`,
`Option.map`, or the generated `W.map` of a one-parameter wrapper, composed down to the member.
A partial application, `T[M ↦ A] → T[M ↦ B]` for `atMember j : A → B`. -/
def mapThrough (P : Positions) (atMember : Nat → Expr) : Nat → Expr → MetaM Expr
  | 0, t => throwError "fold_of: the position {t} is nested too deep"
  | fuel + 1, t => do
    let t ← whnfR t
    if let some j := P.members.idxOf? (t.getAppFn.constName?.getD .anonymous) then
      unless t == P.memberTy j do
        throwError "fold_of: {t} is not the member at the family's parameters"
      return atMember j
    unless t.isApp do throwError "fold_of: no functor map through the position {t}"
    -- a product: the generated map of the side(s) naming a member, the other side's type given
    -- (core's `Prod.map` takes two functions and is not a one-parameter wrapper's map)
    if t.isAppOfArity ``Prod 2 then
      let a := t.appFn!.appArg!
      let b := t.appArg!
      let names := fun (s : Expr) => P.members.any fun mem => (s.find? (·.isConstOf mem)).isSome
      match names a, names b with
      | false, true =>
        return ← mkAppOptM (P.ns ++ `prodMapSnd) #[some a, none, none, some (← mapThrough P atMember fuel b)]
      | true, false =>
        return ← mkAppOptM (P.ns ++ `prodMapFst) #[none, some b, none, some (← mapThrough P atMember fuel a)]
      | true, true =>
        return ← mkAppM (P.ns ++ `prodMapBoth) #[← mapThrough P atMember fuel a, ← mapThrough P atMember fuel b]
      | false, false => throwError "fold_of: the product {t} names no member"
    let inner ← mapThrough P atMember fuel t.appArg!
    if t.isAppOfArity ``List 1 then return ← mkAppM ``List.map #[inner]
    if t.isAppOfArity ``Option 1 then return ← mkAppM ``Option.map #[inner]
    let .const w _ := t.getAppFn | throwError "fold_of: no functor map through the position {t}"
    unless (← getEnv).contains (w ++ `map) do
      throwError "fold_of: {w} has no functor map {w ++ `map}; the generator emits one for a \
        one-parameter record"
    mkAppM (w ++ `map) #[inner]

/-- `mapThrough t fst (mapThrough t fv x) = x`: the value at a position read back from its
paired results. `Eq.refl` at the member (`(x, f x).1` reduces), and at each container the
composition law, the pointwise identity under `funext`, and the identity law. -/
def identThrough (P : Positions) : Nat → Expr → Expr → MetaM Expr
  | 0, t, _ => throwError "fold_of: the position {t} is nested too deep"
  | fuel + 1, t, x => do
    let t ← whnfR t
    if let some j := P.members.idxOf? (t.getAppFn.constName?.getD .anonymous) then
      let lhs := mkApp (P.fstFn j) (mkApp (P.fv j) x)
      return ← mkExpectedTypeHint (← mkEqRefl x) (← mkEq lhs x)
    unless t.isApp do throwError "fold_of: no functor map through the position {t}"
    if t.isAppOfArity ``Prod 2 then
      let a := t.appFn!.appArg!
      let b := t.appArg!
      let names := fun (s : Expr) => P.members.any fun mem => (s.find? (·.isConstOf mem)).isSome
      let lhs := mkApp (← mapThrough P P.fstFn (fuel + 1) t) (mkApp (← mapThrough P P.fv (fuel + 1) t) x)
      let side := fun (proj : Name) (s : Expr) => do
        let xs ← mkAppM proj #[x]
        let goal ← mkEq (← mkAppM proj #[lhs]) xs
        if names s then mkExpectedTypeHint (← identThrough P fuel s xs) goal
        else mkExpectedTypeHint (← mkEqRefl xs) goal
      return ← mkAppM ``Prod.ext #[← side ``Prod.fst a, ← side ``Prod.snd b]
    let inner := t.appArg!
    let h ← mapThrough P P.fstFn fuel inner
    let g ← mapThrough P P.fv fuel inner
    let pointwise ← withLocalDeclD `a inner fun a => do
      mkLambdaFVars #[a] (← identThrough P fuel inner a)
    let ext ← mkFunExt pointwise
    let (mapMap, mapId, mapFn) ←
      if t.isAppOfArity ``List 1 then
        pure (← mkAppOptM ``List.map_map #[none, none, none, some h, some g, some x],
          ← mkAppM ``List.map_id' #[x], ``List.map)
      else if t.isAppOfArity ``Option 1 then
        pure (← mkAppM ``Option.map_map #[h, g, x],
          ← mkAppOptM ``Option.map_id' #[none, some x], ``Option.map)
      else
        let .const w _ := t.getAppFn | throwError "fold_of: no functor map through the position {t}"
        pure (← mkAppM (w ++ `map_map) #[h, g, x], ← mkAppM (w ++ `map_id) #[x], w ++ `map)
    let congr ← mkCongrArg (← withLocalDeclD `k (← mkArrow inner inner) fun k => do
        mkLambdaFVars #[k] (← mkAppM mapFn #[k, x])) ext
    mkEqTrans mapMap (← mkEqTrans congr mapId)

/-- The work of `fold_of`, in `MetaM`. -/
def convert (target : Name) : MetaM Unit := do
    let info ← getConstInfoDefn target
    let block := info.all.toArray
    -- the family, read from `target`'s own signature
    let familyIn := fun (xs : Array Expr) => do
      for x in xs do
        if let some fam ← familyOf? (← inferType x) then return some fam
      for x in xs do
        let t ← whnf (← inferType x)
        if t.isAppOf ``List then
          if let some fam ← familyOf? t.appArg! then return some fam
      pure (none : Option Family)
    let fam₀ ← forallTelescope info.type fun xs _ => do
      let some fam ← familyIn xs
        | throwError "fold_of: {target} takes no value of a free object with a generated fold"
      pure fam
    let members ← block.mapM fun g => (memberOf fam₀ g : MetaM Member)
    let fixedCount ← fixedPrefix block members fam₀
    let algCtor := (← getConstInfoInduct fam₀.algebra).ctors[0]!
    let homCtor := (← getConstInfoInduct fam₀.hom).ctors[0]!
    forallBoundedTelescope info.type fixedCount fun fixed rest => do
      -- the family again, under the fixed binders (its parameters may mention them)
      let fam ← forallTelescope rest fun xs _ => do
        let some fam ← familyIn xs
          | throwError "fold_of: {target} takes no value of a free object with a generated fold"
        pure fam
      let famType := fam.fams[0]!.getPrefix
      let ns := famType.getPrefix
      let levelParams := info.levelParams.map mkLevelParam
      let memberTy := fun (j : Nat) => mkAppN (mkConst fam.members[j]!) fam.params
      let listTy := fun (j : Nat) => mkApp (mkConst ``List [Level.zero]) (memberTy j)
      let memberFn := fun (m : Member) => mkAppN (mkConst m.fn levelParams) fixed
      -- the block member reading a family member directly, and the sibling reading its list
      let byMember := fun (i : Nat) => members.find? fun m => m.member == i && !m.isList
          let withShape := fun {α : Type} (m : Member) (k : Array Expr → Nat → Expr → MetaM α) =>
        FoldOf.withShape fixed fixedCount m k
      -- a member's carrier: its function type over its varying binders
      let carrierOfMember := fun (m : Member) => withShape m fun ys pre body => do
        let e := ys[pre]!
        let acc := ys.eraseIdx! pre
        for y in acc do
          if (← inferType y).containsFVar e.fvarId! then
            throwError "fold_of: {m.fn}: a binder's type depends on the family value"
        if body.containsFVar e.fvarId! then
          throwError "fold_of: {m.fn}: the result type depends on the family value"
        pure (stripParamAnnotations (← mkForallFVars acc body))
      -- the carrier per family member, or `Unit`
      let mut results : Array Expr := #[]
      let mut level : Level := Level.zero
      for i in [:fam.members.size] do
        match byMember i with
        | some m =>
          let carrier ← carrierOfMember m
          results := results.push carrier
          level ← decLevel (← getLevel carrier)
        | none => results := results.push (mkConst ``Unit)
      for m in members do
        if m.isList then
          if (byMember m.member).isNone then
            throwError "fold_of: {m.fn} reads a list of {fam.members[m.member]!} but no member of \
              the block reads {fam.members[m.member]!} itself"
          level ← pure (mkLevelMax level (← decLevel (← getLevel (← carrierOfMember m)))).normalize
      let preOf : Name → Nat := fun g =>
        match members.find? (·.fn == g) with
        | some m => m.at_ - fixedCount
        | none => 0
      -- the children of a constructor's arguments: (argument index, member index, kind), the
      -- kind 0 for the member itself, 1 for a list of it, 2 for any other position whose type
      -- mentions a member (`Option M`, `List (ElementOf M)`): the generated algebra types that
      -- argument with the carrier in the member's place, and so does the field's local
      let childrenOf := fun (args : Array Expr) => do
        let mut out : Array (Nat × Nat × Nat) := #[]
        for h : k in [:args.size] do
          let t ← inferType args[k]
          match ← familyArgsOf fam t with
          | some (j, _, false) => out := out.push (k, j, 0)
          | some (j, _, true) => out := out.push (k, j, 1)
          | none =>
            let mentions := fam.members.findIdx? fun mem => t.find? (fun sub =>
              match sub with | .const c _ => c == mem | _ => false) |>.isSome
            if let some j := mentions then out := out.push (k, j, 2)
        pure out
      let isList := fun (kind : Nat) => kind == 1
      -- a call `g fixed pre child post…` becomes `r pre post…` for the replacement `r` paired
      -- with `child` — for every block member when the pair names no callee, for that
      -- sibling alone when it does (two siblings may read the same list, `acceptsList` and
      -- `acceptsFields`); the call may stop short of the last binders (`vs.mapM (encodeRaw
      -- t)`): the carrier is curried the same way
      let abstractCalls := fun (children : Array (Expr × Option Name × Expr)) (e : Expr) =>
        e.replace fun sub =>
          match sub.getAppFn with
          | .const g _ =>
            if block.contains g && sub.getAppNumArgs > fixedCount + preOf g then
              let args := sub.getAppArgs
              let at_ := fixedCount + preOf g
              if (fixed.zip (args.extract 0 fixedCount)).all (fun (a, b) => a == b) then
                match children.find? (fun (c, callee, _) =>
                    c == args[at_]! && (callee.isNone || callee == some g)) with
                | some (_, _, r) =>
                  some (mkAppN r (args.extract fixedCount at_ ++ args.extract (at_ + 1) args.size))
                | none => none
              else none
            else none
          | _ => none
      let stillRecursive := fun (body : Expr) => body.find? (fun sub => match sub with
        | .const g _ => block.contains g | _ => false) |>.isSome
      -- pass 1: does any arm use a child's value (a paramorphism)?
      let mut needsPara := false
      for m in members do
        for ctor in ← ctorsOf fam m do
          -- a field-list sibling's cons arm is read at `(n, t) :: rest`, so its pair split reduces
          let usesChild ← withArmNode fam m ctor fam.params fun args node => withShape m fun ys pre _ => do
            let acc := ys.eraseIdx! pre
            let childFam ← childrenOf args
            let (_, arm) ← armOf m (fixed ++ acc.extract 0 pre) node (acc.extract pre acc.size)
            let marks := childFam.map fun (k, _, _) =>
              (args[k]!, (none : Option Name), mkConst (`fold_of_result ++ Name.mkNum .anonymous k))
            let body := abstractCalls marks arm
            if stillRecursive body then
              throwError "fold_of: {m.fn} at {ctor}: a recursive call that is not on an \
                immediate child at the fixed parameters:\n  {← ppExpr arm}"
            pure (childFam.any fun (k, _, _) => body.containsFVar args[k]!.fvarId!)
          if usesChild then needsPara := true
      let para := needsPara
      let carriers ← results.mapIdxM fun j r => do
        if para then pure (mkAppN (mkConst ``Prod [Level.zero, level]) #[memberTy j, r]) else pure r
      let R ← carrierOf famType level carriers
      let levelsFor := fun (n : Name) => do
        let c ← getConstInfo n
        pure (c.levelParams.map fun _ => level)
      let pair := fun (j : Nat) (v r : Expr) =>
        mkAppN (mkConst ``Prod.mk [Level.zero, level]) #[memberTy j, results[j]!, v, r]
      let fstOf := fun (j : Nat) (r : Expr) =>
        mkAppN (mkConst ``Prod.fst [Level.zero, level]) #[memberTy j, results[j]!, r]
      let sndOf := fun (j : Nat) (r : Expr) =>
        mkAppN (mkConst ``Prod.snd [Level.zero, level]) #[memberTy j, results[j]!, r]
      let rTy := fun (j : Nat) => mkApp R (mkConst fam.fams[j]!)
      -- a position's type with every member replaced by its carrier
      let carrierTyped := fun (t : Expr) => t.replace fun sub =>
        match fam.members.idxOf? (sub.getAppFn.constName?.getD .anonymous) with
        | some j => if sub == memberTy j then some (rTy j) else none
        | none => none
      -- the hom's function at a family member: the block member as a function of the value,
      -- then of its varying binders; `()` where the block has no member; paired under `para`
      let homFnOf := fun (i : Nat) => withLocalDeclD `e (memberTy i) fun e => do
        let r ← match byMember i with
          | some m => withShape m fun ys pre _ => do
            let acc := ys.eraseIdx! pre
            let call := mkAppN (memberFn m) (acc.extract 0 pre ++ #[e] ++ acc.extract pre acc.size)
            mkLambdaFVars acc call
          | none => pure (mkConst ``Unit.unit)
        let r := if para then pair i e r else r
        mkLambdaFVars #[e] r
      let mut fns : Array Expr := #[]
      for i in [:fam.members.size] do fns := fns.push (← homFnOf i)
      -- the positions: a container child's value is read back from its paired results through
      -- the position's functor map (a field-list sibling maps its elements with it too)
      let P : Positions :=
        { members := fam.members, ns, memberTy
          fstFn := fun j => mkAppN (mkConst ``Prod.fst [Level.zero, level]) #[memberTy j, results[j]!]
          fv := fun j => fns[j]! }
      -- a sibling's element type (the member, or a field-list sibling's product), its list, the
      -- element with the member replaced by the carrier, and the element map built from one at
      -- the member
      let sibElem := fun (m : Member) => elemTypeOf fam m fam.params
      let sibList := fun (m : Member) => mkApp (mkConst ``List [Level.zero]) (sibElem m)
      let sibElemR := fun (m : Member) => match m.elem with
        | some e => carrierTyped e
        | none => rTy m.member
      let sibMap := fun (m : Member) (f : Expr) => match m.elem with
        | some e => mapThrough P (fun _ => f) 8 e
        | none => pure f
      -- the list siblings, each as a `List.foldr` over the mapped results: its `nil` and
      -- `cons` read off its two arms, with `f … x …` the element's result and `s … rest …`
      -- the fold of the rest
      let mut siblingFolds : Array (Name × Expr × Expr × Expr) := #[]  -- (fn, carrier, nil, cons)
      for m in members do
        unless m.isList do continue
        let j := m.member
        let carrier ← carrierOfMember m
        let nilArm ← withShape m fun ys pre _ => do
          let acc := ys.eraseIdx! pre
          let node := nodeOf fam m ``List.nil fam.params #[]
          let (_, arm) ← armOf m (fixed ++ acc.extract 0 pre) node (acc.extract pre acc.size)
          if stillRecursive arm then
            throwError "fold_of: {m.fn} at []: a recursive call in the base arm:\n  {← ppExpr arm}"
          mkLambdaFVars acc arm
        let consArm ← if let some e := m.elem then
          -- a field-list sibling: the arm read at `(n, t) :: rest`, the member's call its result
          -- and the other leaves the mapped element's own components
          withLocalDeclD `x (sibElemR m) fun x =>
          withLocalDeclD `rrest carrier fun rrest => withShape m fun ys pre _ => do
            let acc := ys.eraseIdx! pre
            withArmNode fam m ``List.cons fam.params fun args node => do
              let leaves := args.pop
              let restV := args.back!
              let (_, arm) ← armOf m (fixed ++ acc.extract 0 pre) node (acc.extract pre acc.size)
              let projs ← elemProjs 8 e x
              let mut found : Option Nat := none
              for h : i in [:leaves.size] do
                if let some (_, _, false) ← familyArgsOf fam (← inferType leaves[i]) then found := some i
              let some mi := found
                | throwError "fold_of: {m.fn}: no leaf of the element {e} is a member of the family"
              let r := projs[mi]!
              let body := abstractCalls #[(leaves[mi]!, none, if para then sndOf j r else r),
                (restV, some m.fn, rrest)] arm
              if stillRecursive body then
                throwError "fold_of: {m.fn} at (…) :: rest: a recursive call that is not on the \
                  element's member or the tail:\n  {← ppExpr arm}"
              if body.containsFVar restV.fvarId! then
                throwError "fold_of: {m.fn} at (…) :: rest: the tail is used as a value; a fold of \
                  the list does not carry it:\n  {← ppExpr arm}"
              let mut body := body
              for h : i in [:leaves.size] do
                if i != mi then body := body.replaceFVar leaves[i] projs[i]!
              -- under `para` the member's value is its result's first component
              if para then body := body.replaceFVar leaves[mi]! (fstOf j r)
              if body.containsFVar leaves[mi]!.fvarId! then
                throwError "fold_of: {m.fn} at (…) :: rest: the member is used as a value but no \
                  arm of the block made this a paramorphism:\n  {← ppExpr arm}"
              mkLambdaFVars #[x, rrest] (← mkLambdaFVars acc body)
        else
          withLocalDeclD `x (memberTy j) fun x =>
          withLocalDeclD `rest (listTy j) fun restV =>
          withLocalDeclD `r (rTy j) fun r =>
          withLocalDeclD `rrest carrier fun rrest => withShape m fun ys pre _ => do
            let acc := ys.eraseIdx! pre
            let node := nodeOf fam m ``List.cons fam.params #[x, restV]
            let (_, arm) ← armOf m (fixed ++ acc.extract 0 pre) node (acc.extract pre acc.size)
            let body := abstractCalls #[(x, none, if para then sndOf j r else r), (restV, some m.fn, rrest)] arm
            if stillRecursive body then
              throwError "fold_of: {m.fn} at x :: rest: a recursive call that is not on the head \
                or the tail:\n  {← ppExpr arm}"
            if body.containsFVar restV.fvarId! then
              throwError "fold_of: {m.fn} at x :: rest: the tail is used as a value; a fold of \
                the list does not carry it:\n  {← ppExpr arm}"
            -- under `para` the head's value is its result's first component
            let body := if para then body.replaceFVar x (fstOf j r) else body
            if body.containsFVar x.fvarId! then
              throwError "fold_of: {m.fn} at x :: rest: the head is used as a value but no arm \
                of the block made this a paramorphism:\n  {← ppExpr arm}"
            mkLambdaFVars #[r, rrest] (← mkLambdaFVars acc body)
        siblingFolds := siblingFolds.push (m.fn, carrier, nilArm, consArm)
      let foldOfSibling := fun (s : Name) (rs : Expr) => do
        let some (_, carrier, nilArm, consArm) := siblingFolds.find? (·.1 == s)
          | throwError "fold_of: {s} is not a list sibling"
        let some m := members.find? (·.fn == s) | throwError "fold_of: {s} is not a member"
        -- `List.foldr : (α → β → β) → β → List α → β`
        let foldr := mkConst ``List.foldr [Level.zero, level]
        pure (mkAppN foldr #[sibElemR m, carrier, consArm, nilArm, rs])
      -- `s.eq_foldr : ∀ xs, (fun pre post => s fixed pre xs post) = List.foldr cons nil (xs.map f)`
      -- by induction on the list, the base and the step by the sibling's unfold equations
      let mut siblingLemmas : Array (Name × Name) := #[]
      for m in members do
        unless m.isList do continue
        let j := m.member
        let some (_, carrier, nilArm, consArm) := siblingFolds.find? (·.1 == m.fn) | continue
        let fv ← sibMap m fns[j]!
        let mapped := fun (xs : Expr) =>
          mkAppN (mkConst ``List.map [Level.zero, level]) #[sibElem m, sibElemR m, fv, xs]
        let foldOf := fun (xs : Expr) =>
          mkAppN (mkConst ``List.foldr [Level.zero, level]) #[sibElemR m, carrier, consArm, nilArm, mapped xs]
        let asFn := fun (xs : Expr) => withShape m fun ys pre _ => do
          let acc := ys.eraseIdx! pre
          mkLambdaFVars acc (mkAppN (memberFn m) (acc.extract 0 pre ++ #[xs] ++ acc.extract pre acc.size))
        -- the equation at a list, closed over the varying binders
        let eqAt := fun (xs : Expr) (proofAt : Array Expr → Nat → MetaM Expr) => withShape m fun ys pre _ => do
          let acc := ys.eraseIdx! pre
          let mut h ← proofAt acc pre
          for a in acc.reverse do
            h ← mkFunExt (← mkLambdaFVars #[a] h)
          pure h
        let motive ← withLocalDeclD `xs (sibList m) fun xs => do
          mkLambdaFVars #[xs] (← mkEq (← asFn xs) (foldOf xs))
        let base ← eqAt (nodeOf fam m ``List.nil fam.params #[]) fun acc pre =>
          unfoldEqAt m levelParams (fixed ++ acc.extract 0 pre) (nodeOf fam m ``List.nil fam.params #[]) (acc.extract pre acc.size)
        let step ← withLocalDeclD `x (sibElem m) fun x => withLocalDeclD `rest (sibList m) fun restV => do
          let ihTy ← mkEq (← asFn restV) (foldOf restV)
          withLocalDeclD `ih ihTy fun ih => do
            let proofAt := fun (xval : Expr) => do
              let node := nodeOf fam m ``List.cons fam.params #[xval, restV]
              eqAt node fun acc pre => do
                let before := fixed ++ acc.extract 0 pre
                let after := acc.extract pre acc.size
                let (_, arm) ← armOf m before node after
                let h₀ ← unfoldEqAt m levelParams before node after
                -- the arm with every `s fixed a rest b` as `F a b`, for the induction hypothesis
                let motive' ← withLocalDeclD `F carrier fun F => do
                  mkLambdaFVars #[F] (abstractCalls #[(restV, some m.fn, F)] arm)
                mkEqTrans h₀ (← mkCongrArg motive' ih)
            -- a field-list sibling's element is cased into its leaves first, so the arm's pair
            -- split reduces
            let h ← if m.elem.isSome then do
                let motiveX ← withLocalDeclD `x' (sibElem m) fun x' => do
                  let node := nodeOf fam m ``List.cons fam.params #[x', restV]
                  mkLambdaFVars #[x'] (← mkEq (← asFn node) (foldOf node))
                caseElem 8 x motiveX proofAt
              else proofAt x
            mkLambdaFVars #[x, restV, ih] h
        let lemmaName := m.fn ++ `eq_foldr
        let (thmTy, thmVal) ← withLocalDeclD `xs (sibList m) fun xs => do
          let ty ← mkForallFVars (fixed ++ #[xs]) (← mkEq (← asFn xs) (foldOf xs))
          let recApp := mkAppN (mkConst ``List.rec [Level.zero, Level.zero]) #[sibElem m, motive, base, step, xs]
          pure (ty, ← mkLambdaFVars (fixed ++ #[xs]) recApp)
        addDecl <| .thmDecl { name := lemmaName, levelParams := info.levelParams, type := thmTy, value := thmVal }
        siblingLemmas := siblingLemmas.push (m.fn, lemmaName)
      -- the algebra: one field per constructor, member order then constructor order, and the
      -- homomorphism equation of each: `g … node … = M` is the unfold equation and `M` reduces
      -- to the field at the recursive results (a matcher on a constructor; never through the
      -- recursion's `brecOn`); a list child's sibling call is rewritten by `s.eq_foldr`; closed
      -- by `funext` over the varying binders and `congrArg (node, ·)` under `para`
      let mut fields : Array Expr := #[]
      let mut homEqs : Array Expr := #[]
      for i in [:fam.members.size] do
        let ind ← getConstInfoInduct fam.members[i]!
        for ctor in ind.ctors do
          let ctorTy ← instantiateForall (← getConstInfoCtor ctor).type fam.params
          let (field, homEq) ← forallTelescope ctorTy fun args _ => do
            let node := mkAppN (mkAppN (mkConst ctor) fam.params) args
            let childFam ← childrenOf args
            let argTys ← args.mapM inferType
            let decls := childFam.map fun (k, j, kind) =>
              (Name.mkSimple s!"r{k}", fun (_ : Array Expr) =>
                pure (if kind == 1 then mkApp (mkConst ``List [level]) (rTy j)
                  else if kind == 2 then carrierTyped argTys[k]! else rTy j))
            -- the container children (a list of the member, or any other position mentioning
            -- one) and, under `para`, a value local for each: the field reads it back from the
            -- paired results, and the equation transports along that reading
            let containers := childFam.filter fun (_, _, kind) => kind != 0
            let valueDecls := if para then containers.map fun (k, _, _) =>
                (Name.mkSimple s!"v{k}", fun (_ : Array Expr) => pure argTys[k]!)
              else #[]
            withLocalDeclsD decls fun rs => withLocalDeclsD valueDecls fun vs => do
              let fieldArgs := args.mapIdx fun k a =>
                match childFam.findIdx? (·.1 == k) with
                | some c => rs[c]!
                | none => a
              let valueOf := fun (r : Expr) (j : Nat) => if para then fstOf j r else r
              let resultOf := fun (r : Expr) (j : Nat) => if para then sndOf j r else r
              -- a child's value: a direct child's is its result's first component, a container
              -- child's is its value local
              let childValue := fun (c : Nat) => do
                let (k, j, kind) := childFam[c]!
                if kind == 0 then pure (valueOf rs[c]! j)
                else
                  let some v := containers.findIdx? (·.1 == k)
                    | throwError "fold_of: {ctor}: no value local for argument {k}"
                  if para then pure vs[v]!
                  else throwError "fold_of: {ctor}: a child under a container or a wrapper is \
                    used as a value but no arm of the block made this a paramorphism"
              -- the node rebuilt from its children's values, paired in under `para`
              let rebuilt ← if para then do
                  let mut out : Array Expr := #[]
                  for h : k in [:args.size] do
                    match childFam.findIdx? (·.1 == k) with
                    | some c => out := out.push (← childValue c)
                    | none => out := out.push args[k]
                  pure (mkAppN (mkAppN (mkConst ctor) fam.params) out)
                else pure node
              let (result, proof) ← match byMember i with
                | some m => withShape m fun ys pre _ => do
                  let acc := ys.eraseIdx! pre
                  let before := fixed ++ acc.extract 0 pre
                  let after := acc.extract pre acc.size
                  let (_, arm) ← armOf m before node after
                  -- a direct child's call is its result; a list child's sibling call is the
                  -- sibling's fold over the results
                  let mut calls : Array (Expr × Option Name × Expr) := #[]
                  let mut listChildren : Array (Expr × Name) := #[]
                  for ((k, j, kind), r) in childFam.zip rs do
                    if kind == 2 then
                      -- a field-list child (`List (String × Ty)`): every sibling reading a list
                      -- of this element folds the mapped elements; another position is read back
                      -- as a value below
                      for s in members do
                        if let some e := s.elem then
                          if ← isDefEq argTys[k]! (mkApp (mkConst ``List [Level.zero]) e) then
                            calls := calls.push (args[k]!, some s.fn, ← foldOfSibling s.fn r)
                            listChildren := listChildren.push (args[k]!, s.fn)
                    else if kind == 1 then
                      -- every sibling reading a list of this member folds the same results; a
                      -- list child the arm never mentions (`| .list _ => Tag.list`) needs none,
                      -- and the value check below catches any other use
                      for s in members do
                        if s.isList && s.member == j then
                          calls := calls.push (args[k]!, some s.fn, ← foldOfSibling s.fn r)
                          listChildren := listChildren.push (args[k]!, s.fn)
                    else calls := calls.push (args[k]!, none, resultOf r j)
                  -- the map idiom: `xs.map f` over a list child, `f` the member at the fixed
                  -- parameters, is the result list itself (`f_val` is `f` up to eta)
                  let arm := if para then arm else arm.replace fun sub =>
                    if sub.isAppOfArity ``List.map 4 then
                      let xs := sub.getArg! 3
                      match childFam.findIdx? (fun (k, _, kind) => kind == 1 && xs == args[k]!) with
                      | some c =>
                        match byMember childFam[c]!.2.1 with
                        | some f => if sub.getArg! 2 == memberFn f then some rs[c]! else none
                        | none => none
                      | none => none
                    else none
                  -- what remains of a child in the arm is its value
                  let mut body := abstractCalls calls arm
                  for c in [:childFam.size] do
                    let (k, _, kind) := childFam[c]!
                    if body.containsFVar args[k]!.fvarId! then
                      if kind != 0 && !para then
                        throwError "fold_of: {m.fn} at {ctor}: a child under a container or a \
                          wrapper is used as a value but no arm of the block made this a \
                          paramorphism:\n  {← ppExpr arm}"
                      body := body.replaceFVar args[k]! (← childValue c)
                  let mut h ← unfoldEqAt m levelParams before node after
                  -- rewrite each list child's sibling call by the sibling's lemma
                  let mut cur := arm
                  for (xs, s) in listChildren do
                    let some (_, lemmaName) := siblingLemmas.find? (·.1 == s)
                      | throwError "fold_of: no lemma for {s}"
                    let some (_, carrier, _, _) := siblingFolds.find? (·.1 == s)
                      | throwError "fold_of: no fold for {s}"
                    let abstracted := abstractCalls #[(xs, some s, mkConst `fold_of_F)] cur
                    if abstracted == cur then continue
                    let motive' ← withLocalDeclD `F carrier fun F => do
                      mkLambdaFVars #[F] (abstractCalls #[(xs, some s, F)] cur)
                    let lem := mkAppN (mkConst lemmaName levelParams) (fixed ++ #[xs])
                    h ← mkEqTrans h (← mkCongrArg motive' lem)
                    cur := motive'.beta #[← (do
                      let some sm := members.find? (·.fn == s) | throwError "fold_of: {s}"
                      let j := sm.member
                      let some (_, carrier', nilArm, consArm) := siblingFolds.find? (·.1 == s) | throwError "fold_of: {s}"
                      let mapped := mkAppN (mkConst ``List.map [Level.zero, level])
                        #[sibElem sm, sibElemR sm, ← sibMap sm fns[j]!, xs]
                      pure (mkAppN (mkConst ``List.foldr [Level.zero, level]) #[sibElemR sm, carrier', consArm, nilArm, mapped]))]
                  for a in acc.reverse do
                    h ← mkFunExt (← mkLambdaFVars #[a] h)
                  let proof ← if para then
                      mkCongrArg (mkAppN (mkConst ``Prod.mk [Level.zero, level]) #[memberTy i, results[i]!, node]) h
                    else pure h
                  pure (← mkLambdaFVars acc body, proof)
                | none => pure (mkConst ``Unit.unit, ← mkEqRefl (if para then pair i node (mkConst ``Unit.unit) else mkConst ``Unit.unit))
              let template := if para then pair i rebuilt result else result
              -- the field: every value local read back from the paired results
              let readBack ← containers.mapM fun (k, _, _) => do
                let some c := childFam.findIdx? (·.1 == k) | throwError "fold_of: {ctor}: argument {k}"
                pure (mkApp (← mapThrough P P.fstFn 8 argTys[k]!) rs[c]!)
              let field ← mkLambdaFVars fieldArgs (template.replaceFVars vs readBack)
              -- the equation under `para` with container children: at the hom's arguments the
              -- results are `mapThrough fv a_k`, and each value local moves from `a_k` to its
              -- reading `mapThrough fst (mapThrough fv a_k)` by the functor laws, one child at
              -- a time with the others held at their current stage
              let proof ← if para && !containers.isEmpty then do
                  let mapped ← containers.mapM fun (k, _, _) => do
                    pure (mkApp (← mapThrough P P.fv 8 argTys[k]!) args[k]!)
                  let atArgs ← childFam.mapM fun (k, j, kind) => do
                    if kind == 0 then pure (mkApp fns[j]! args[k]!)
                    else
                      let some v := containers.findIdx? (·.1 == k) | throwError "fold_of: {ctor}: argument {k}"
                      pure mapped[v]!
                  let atHom := template.replaceFVars rs atArgs
                  let mut current := containers.map fun (k, _, _) => args[k]!
                  let mut proof := proof
                  for v in [:containers.size] do
                    let (k, _, _) := containers[v]!
                    let ident ← identThrough P 8 argTys[k]! args[k]!
                    let motive ← mkLambdaFVars #[vs[v]!]
                      (atHom.replaceFVars (vs.eraseIdx! v) (current.eraseIdx! v))
                    proof ← mkEqTrans proof (← mkCongrArg motive (← mkEqSymm ident))
                    current := current.set! v (mkApp (← mapThrough P P.fstFn 8 argTys[k]!) mapped[v]!)
                  pure proof
                else pure proof
              let homEq ← mkLambdaFVars args proof
              pure (field, homEq)
          fields := fields.push field
          homEqs := homEqs.push homEq
      -- `f.alg`
      let algVal := mkAppN (mkConst algCtor (← levelsFor algCtor)) (fam.params ++ #[R] ++ fields)
      let algTy := mkAppN (mkConst fam.algebra (← levelsFor fam.algebra)) (fam.params ++ #[R])
      let algName := target ++ `alg
      let algDecl := Declaration.defnDecl
        { name := algName, levelParams := info.levelParams
          type := ← mkForallFVars fixed algTy, value := ← mkLambdaFVars fixed algVal
          hints := .abbrev, safety := .safe }
      addDecl algDecl
      -- the algebra is executable when its arms are; a case split the code generator refuses
      -- (a bare recursor left by `reduceCases`) leaves it a specification until rewritten
      try compileDecl algDecl
      catch ex => logWarning m!"fold_of: {algName} is not compiled: {ex.toMessageData}"
      let alg := mkAppN (mkConst algName levelParams) fixed
      -- `f.hom`
      let homVal := mkAppN (mkConst homCtor (← levelsFor homCtor)) (fam.params ++ #[R, alg] ++ fns ++ homEqs)
      let homTy := mkAppN (mkConst fam.hom (← levelsFor fam.hom)) (fam.params ++ #[R, alg])
      let homName := target ++ `hom
      addDecl <| .defnDecl
        { name := homName, levelParams := info.levelParams
          type := ← mkForallFVars fixed homTy, value := ← mkLambdaFVars fixed homVal
          hints := .abbrev, safety := .safe }
      let hom := mkAppN (mkConst homName levelParams) fixed
      -- `g.eq_cata` per family member of the block: `g fixed pre e post = cata alg e pre post`,
      -- the fold's second component under `para`
      for m in members do
        if m.isList then continue
        let j := m.member
        let unique := mkConst fam.uniques[j]! (← levelsFor fam.uniques[j]!)
        let (thmTy, thmVal) ← withShape m fun ys pre _ => do
          let e := ys[pre]!
          let acc := ys.eraseIdx! pre
          let lhs := mkAppN (memberFn m) (acc.extract 0 pre ++ #[e] ++ acc.extract pre acc.size)
          let cata := mkAppN (mkConst fam.catas[j]! (← levelsFor fam.catas[j]!)) (fam.params ++ #[R, alg, e])
          let uniq := mkAppN unique (fam.params ++ #[R, alg, hom, e])
          let (fold, proof) ←
            if para then
              let snd := mkAppN (mkConst ``Prod.snd [Level.zero, level]) #[memberTy j, results[j]!]
              pure (sndOf j cata, ← mkCongrArg snd uniq)
            else pure (cata, uniq)
          let mut rhs := fold
          let mut proof := proof
          for a in acc do
            rhs := mkApp rhs a
            proof ← mkCongrFun proof a
          pure (← mkForallFVars (fixed ++ ys) (← mkEq lhs rhs), ← mkLambdaFVars (fixed ++ ys) proof)
        let thmName := m.fn ++ `eq_cata
        addDecl <| .thmDecl { name := thmName, levelParams := info.levelParams, type := thmTy, value := thmVal }
        logInfo m!"fold_of: {thmName} : {← ppExpr thmTy}"
      -- `s.eq_cata` per list sibling: `s fixed pre xs post = List.foldr cons nil
      -- (cata_pos_list alg xs) pre post`, through `s.eq_foldr`, `f.eq_cata` under the map and
      -- the generated `cata_pos_list_<fam>_eq`
      for m in members do
        unless m.isList do continue
        let j := m.member
        let some (_, lemmaName) := siblingLemmas.find? (·.1 == m.fn) | continue
        let some (_, carrier, nilArm, consArm) := siblingFolds.find? (·.1 == m.fn) | continue
        -- the list position's helper: `cata_pos_list_ty`, or for a field-list sibling the
        -- element's (`cata_pos_list_prod_string_ty`)
        let stem ← match m.elem with
          | some e => posSuffix fam 8 e
          | none => pure fam.fams[j]!.getString!
        let posEqName := ns ++ Name.mkSimple ("cata_pos_list_" ++ stem ++ "_eq")
        let posName := ns ++ Name.mkSimple ("cata_pos_list_" ++ stem)
        unless (← getEnv).contains posEqName do
          throwError "fold_of: the generated {posEqName} does not exist"
        let (thmTy, thmVal) ← withShape m fun ys pre _ => do
          let xs := ys[pre]!
          let acc := ys.eraseIdx! pre
          let lhs := mkAppN (memberFn m) (acc.extract 0 pre ++ #[xs] ++ acc.extract pre acc.size)
          let cataL := mkAppN (mkConst posName (← levelsFor posName)) (fam.params ++ #[R, alg, xs])
          let foldr := fun (l : Expr) =>
            mkAppN (mkConst ``List.foldr [Level.zero, level]) #[sibElemR m, carrier, consArm, nilArm, l]
          -- e₁ : (fun acc => s … xs …) = foldr (xs.map fv)
          let e₁ := mkAppN (mkConst lemmaName levelParams) (fixed ++ #[xs])
          -- e₂ : xs.map fv = xs.map (cata alg), pointwise by the uniqueness theorem
          -- (`hom.f_<fam> x = cata alg x`, `hom.f_<fam>` being `fv`, the value paired in under
          -- `para`) under funext and the map
          let unique := mkConst fam.uniques[j]! (← levelsFor fam.uniques[j]!)
          let pointwise ← withLocalDeclD `x (memberTy j) fun x =>
            mkLambdaFVars #[x] (mkAppN unique (fam.params ++ #[R, alg, hom, x]))
          let e₂ ← mkCongrArg (← withLocalDeclD `g (← mkArrow (memberTy j) (rTy j)) fun g => do
              mkLambdaFVars #[g] (mkAppN (mkConst ``List.map [Level.zero, level])
                #[sibElem m, sibElemR m, ← sibMap m g, xs]))
            (← mkFunExt pointwise)
          -- e₃ : cata_pos_list alg xs = xs.map (cata alg)
          let e₃ := mkAppN (mkConst posEqName (← levelsFor posEqName)) (fam.params ++ #[R, alg, xs])
          let foldrFn ← withLocalDeclD `l (mkApp (mkConst ``List [level]) (sibElemR m)) fun l => mkLambdaFVars #[l] (foldr l)
          -- e₄ : foldr (cata_pos_list alg xs) = foldr (xs.map fv)
          let e₄ ← mkCongrArg foldrFn (← mkEqTrans e₃ (← mkEqSymm e₂))
          let h ← mkEqTrans e₁ (← mkEqSymm e₄)
          let mut rhs := foldr cataL
          let mut proof := h
          for a in acc do
            rhs := mkApp rhs a
            proof ← mkCongrFun proof a
          pure (← mkForallFVars (fixed ++ ys) (← mkEq lhs rhs), ← mkLambdaFVars (fixed ++ ys) proof)
        let thmName := m.fn ++ `eq_cata
        addDecl <| .thmDecl { name := thmName, levelParams := info.levelParams, type := thmTy, value := thmVal }
        logInfo m!"fold_of: {thmName} : {← ppExpr thmTy}"
      logInfo m!"fold_of{if para then " (paramorphism: the carrier pairs the value)" else ""}: \
        {algName} : {← ppExpr (← mkForallFVars fixed algTy)}"

syntax (name := foldOf) "fold_of " ident : command

@[command_elab foldOf] def elabFoldOf : CommandElab := fun stx => do
  let target ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  liftTermElabM (convert target)

end Effect4.Program.FoldOf
