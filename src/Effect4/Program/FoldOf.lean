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

Three shapes, chosen by reading `f`:

- **catamorphism** — the arms use only the children's results;
- **paramorphism** — an arm uses a child's value as well; the carrier pairs the value in and
  the connector reads `g e = (cata alg e).2`;
- **accumulator** — arguments before or after the family value that a recursive call changes
  (`effTy sig env e`, `findInt pos t`, `hasTy v t allocated`, `build sem l ctx`); the carrier
  is the function type over them, the arm a lambda, and the connector
  `g fixed pre e post = cata alg e pre post`. The binders every recursive call passes through
  unchanged are the fixed prefix and stay parameters of the algebra.

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

/-- Read `g`'s signature: the first binder whose type is a family member, or, when there is
none, the first whose type is a list of one (the list sibling). -/
def memberOf (fam : Family) (g : Name) : MetaM Member := do
  let info ← getConstInfoDefn g
  forallTelescope info.type fun xs _ => do
    for h : i in [:xs.size] do
      if let some (j, _, false) ← familyArgsOf fam (← inferType xs[i]) then
        return { fn := g, type := info.type, member := j, at_ := i, arity := xs.size, isList := false }
    for h : i in [:xs.size] do
      if let some (j, _, true) ← familyArgsOf fam (← inferType xs[i]) then
        return { fn := g, type := info.type, member := j, at_ := i, arity := xs.size, isList := true }
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

/-- Reduce every case split — a matcher, a `casesOn`, or one of the match compiler's own
helpers — whose major premise is a constructor, at any depth, one step at a time; a split on a
variable stays as written (readable, compilable), and what is inside it is reduced. -/
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
      | .stuck _ => return .visit ((← delta? e₀).getD e₀).headBeta
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

/-- A constructor's type at the member's parameters (`List`'s at the element type). -/
def ctorTypeAt (fam : Family) (m : Member) (ctor : Name) (params : Array Expr) : MetaM Expr := do
  let ty := (← getConstInfoCtor ctor).type
  if m.isList then instantiateForall ty #[mkAppN (mkConst fam.members[m.member]!) params]
  else instantiateForall ty params

/-- A constructor applied to the member's parameters and its arguments. -/
def nodeOf (fam : Family) (m : Member) (ctor : Name) (params : Array Expr) (args : Array Expr) : Expr :=
  if m.isList then mkAppN (mkAppN (mkConst ctor [Level.zero]) #[mkAppN (mkConst fam.members[m.member]!) params]) args
  else mkAppN (mkAppN (mkConst ctor) params) args

/-- The number of leading binders that every member has and that every recursive call in the
block passes through unchanged: the fixed prefix. -/
def fixedPrefix (block : Array Name) (members : Array Member) (fam : Family) : MetaM Nat := do
  let mut k := members.foldl (fun k m => min k m.at_) members[0]!.at_
  for m in members do
    k ← forallTelescope m.type fun xs _ => do
      let some (_, params, _) ← familyArgsOf fam (← inferType xs[m.at_]!)
        | throwError "fold_of: {m.fn}: the family value's type could not be read"
      let mut k := k
      for ctor in ← ctorsOf fam m do
        let ctorTy ← ctorTypeAt fam m ctor params
        k ← forallTelescope ctorTy fun args _ => do
          let node := nodeOf fam m ctor params args
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
      -- the children of a constructor's arguments: (argument index, member index, is a list)
      let childrenOf := fun (args : Array Expr) => do
        let mut out : Array (Nat × Nat × Bool) := #[]
        for h : k in [:args.size] do
          if let some (j, _, isList) ← familyArgsOf fam (← inferType args[k]) then
            out := out.push (k, j, isList)
        pure out
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
      let mut hasListChild := false
      for m in members do
        for ctor in ← ctorsOf fam m do
          let ctorTy ← ctorTypeAt fam m ctor fam.params
          let usesChild ← forallTelescope ctorTy fun args _ => withShape m fun ys pre _ => do
            let acc := ys.eraseIdx! pre
            let node := nodeOf fam m ctor fam.params args
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
          if !m.isList then
            let ctorTy ← ctorTypeAt fam m ctor fam.params
            if ← forallTelescope ctorTy fun args _ => do
                pure ((← childrenOf args).any (·.2.2)) then hasListChild := true
      let para := needsPara
      if para && hasListChild then
        throwError "fold_of: {target}: an arm uses a child's value and a constructor has a list \
          of children; the paramorphism over a container is not handled yet"
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
        let consArm ← withLocalDeclD `x (memberTy j) fun x =>
          withLocalDeclD `rest (listTy j) fun restV =>
          withLocalDeclD `r (rTy j) fun r =>
          withLocalDeclD `rrest carrier fun rrest => withShape m fun ys pre _ => do
            let acc := ys.eraseIdx! pre
            let node := nodeOf fam m ``List.cons fam.params #[x, restV]
            let (_, arm) ← armOf m (fixed ++ acc.extract 0 pre) node (acc.extract pre acc.size)
            let body := abstractCalls #[(x, none, r), (restV, some m.fn, rrest)] arm
            if stillRecursive body then
              throwError "fold_of: {m.fn} at x :: rest: a recursive call that is not on the head \
                or the tail:\n  {← ppExpr arm}"
            if body.containsFVar x.fvarId! || body.containsFVar restV.fvarId! then
              throwError "fold_of: {m.fn} at x :: rest: the head or the tail is used as a value; \
                the paramorphism over a container is not handled yet:\n  {← ppExpr arm}"
            mkLambdaFVars #[r, rrest] (← mkLambdaFVars acc body)
        siblingFolds := siblingFolds.push (m.fn, carrier, nilArm, consArm)
      let foldOfSibling := fun (s : Name) (rs : Expr) => do
        let some (_, carrier, nilArm, consArm) := siblingFolds.find? (·.1 == s)
          | throwError "fold_of: {s} is not a list sibling"
        let some m := members.find? (·.fn == s) | throwError "fold_of: {s} is not a member"
        -- `List.foldr : (α → β → β) → β → List α → β`
        let foldr := mkConst ``List.foldr [Level.zero, level]
        pure (mkAppN foldr #[rTy m.member, carrier, consArm, nilArm, rs])
      -- `s.eq_foldr : ∀ xs, (fun pre post => s fixed pre xs post) = List.foldr cons nil (xs.map f)`
      -- by induction on the list, the base and the step by the sibling's unfold equations
      let mut siblingLemmas : Array (Name × Name) := #[]
      for m in members do
        unless m.isList do continue
        let j := m.member
        let some (_, carrier, nilArm, consArm) := siblingFolds.find? (·.1 == m.fn) | continue
        let fv := fns[j]!
        let mapped := fun (xs : Expr) =>
          mkAppN (mkConst ``List.map [Level.zero, level]) #[memberTy j, rTy j, fv, xs]
        let foldOf := fun (xs : Expr) =>
          mkAppN (mkConst ``List.foldr [Level.zero, level]) #[rTy j, carrier, consArm, nilArm, mapped xs]
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
        let motive ← withLocalDeclD `xs (listTy j) fun xs => do
          mkLambdaFVars #[xs] (← mkEq (← asFn xs) (foldOf xs))
        let base ← eqAt (nodeOf fam m ``List.nil fam.params #[]) fun acc pre =>
          unfoldEqAt m levelParams (fixed ++ acc.extract 0 pre) (nodeOf fam m ``List.nil fam.params #[]) (acc.extract pre acc.size)
        let step ← withLocalDeclD `x (memberTy j) fun x => withLocalDeclD `rest (listTy j) fun restV => do
          let ihTy ← mkEq (← asFn restV) (foldOf restV)
          withLocalDeclD `ih ihTy fun ih => do
            let node := nodeOf fam m ``List.cons fam.params #[x, restV]
            let h ← eqAt node fun acc pre => do
              let before := fixed ++ acc.extract 0 pre
              let after := acc.extract pre acc.size
              let (_, arm) ← armOf m before node after
              let h₀ ← unfoldEqAt m levelParams before node after
              -- the arm with every `s fixed a rest b` as `F a b`, for the induction hypothesis
              let motive' ← withLocalDeclD `F carrier fun F => do
                mkLambdaFVars #[F] (abstractCalls #[(restV, some m.fn, F)] arm)
              mkEqTrans h₀ (← mkCongrArg motive' ih)
            mkLambdaFVars #[x, restV, ih] h
        let lemmaName := m.fn ++ `eq_foldr
        let (thmTy, thmVal) ← withLocalDeclD `xs (listTy j) fun xs => do
          let ty ← mkForallFVars (fixed ++ #[xs]) (← mkEq (← asFn xs) (foldOf xs))
          let recApp := mkAppN (mkConst ``List.rec [Level.zero, Level.zero]) #[memberTy j, motive, base, step, xs]
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
            let decls := childFam.map fun (k, j, isList) =>
              (Name.mkSimple s!"r{k}", fun (_ : Array Expr) =>
                pure (if isList then mkApp (mkConst ``List [level]) (rTy j) else rTy j))
            withLocalDeclsD decls fun rs => do
              let fieldArgs := args.mapIdx fun k a =>
                match childFam.findIdx? (·.1 == k) with
                | some c => rs[c]!
                | none => a
              let valueOf := fun (r : Expr) (j : Nat) => if para then fstOf j r else r
              let resultOf := fun (r : Expr) (j : Nat) => if para then sndOf j r else r
              let rebuilt := mkAppN (mkAppN (mkConst ctor) fam.params) (args.mapIdx fun k a =>
                match childFam.findIdx? (·.1 == k) with
                | some c => valueOf rs[c]! childFam[c]!.2.1
                | none => a)
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
                  for ((k, j, isList), r) in childFam.zip rs do
                    if isList then
                      -- every sibling reading a list of this member folds the same results; a
                      -- list child the arm never mentions (`| .list _ => Tag.list`) needs none,
                      -- and the value check below catches any other use
                      for s in members do
                        if s.isList && s.member == j then
                          calls := calls.push (args[k]!, some s.fn, ← foldOfSibling s.fn r)
                          listChildren := listChildren.push (args[k]!, s.fn)
                    else calls := calls.push (args[k]!, none, resultOf r j)
                  let body := abstractCalls calls arm
                  let body := body.replace fun sub =>
                    match childFam.findIdx? (fun (k, _, _) => sub == args[k]!) with
                    | some c => if childFam[c]!.2.2 then none else some (valueOf rs[c]! childFam[c]!.2.1)
                    | none => none
                  for (k, _, isList) in childFam do
                    if isList && body.containsFVar args[k]!.fvarId! then
                      throwError "fold_of: {m.fn} at {ctor}: a list of children is used as a value; \
                        the paramorphism over a container is not handled yet:\n  {← ppExpr arm}"
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
                      let mapped := mkAppN (mkConst ``List.map [Level.zero, level]) #[memberTy j, rTy j, fns[j]!, xs]
                      pure (mkAppN (mkConst ``List.foldr [Level.zero, level]) #[rTy j, carrier', consArm, nilArm, mapped]))]
                  for a in acc.reverse do
                    h ← mkFunExt (← mkLambdaFVars #[a] h)
                  let proof ← if para then
                      mkCongrArg (mkAppN (mkConst ``Prod.mk [Level.zero, level]) #[memberTy i, results[i]!, node]) h
                    else pure h
                  pure (← mkLambdaFVars acc body, proof)
                | none => pure (mkConst ``Unit.unit, ← mkEqRefl (if para then pair i node (mkConst ``Unit.unit) else mkConst ``Unit.unit))
              let value := if para then pair i rebuilt result else result
              let field ← mkLambdaFVars fieldArgs value
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
        let some f := byMember j | continue
        let some (_, lemmaName) := siblingLemmas.find? (·.1 == m.fn) | continue
        let some (_, carrier, nilArm, consArm) := siblingFolds.find? (·.1 == m.fn) | continue
        let stem := fam.fams[j]!.getString!
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
            mkAppN (mkConst ``List.foldr [Level.zero, level]) #[rTy j, carrier, consArm, nilArm, l]
          -- e₁ : (fun acc => s … xs …) = foldr (xs.map fv)
          let e₁ := mkAppN (mkConst lemmaName levelParams) (fixed ++ #[xs])
          -- e₂ : xs.map fv = xs.map (cata alg), from f.eq_cata under funext and the map
          let cataFn := mkAppN (mkConst fam.catas[j]! (← levelsFor fam.catas[j]!)) (fam.params ++ #[R, alg])
          let pointwise ← withLocalDeclD `x (memberTy j) fun x => do
            let hx ← withShape f fun ys' pre' _ => do
              let acc' := ys'.eraseIdx! pre'
              let mut h := mkAppN (mkConst (f.fn ++ `eq_cata) levelParams) (fixed ++ acc'.extract 0 pre' ++ #[x] ++ acc'.extract pre' acc'.size)
              for a in acc'.reverse do
                h ← mkFunExt (← mkLambdaFVars #[a] h)
              pure h
            mkLambdaFVars #[x] hx
          let e₂ ← mkCongrArg (← withLocalDeclD `g (← mkArrow (memberTy j) (rTy j)) fun g =>
              mkLambdaFVars #[g] (mkAppN (mkConst ``List.map [Level.zero, level]) #[memberTy j, rTy j, g, xs]))
            (← mkFunExt pointwise)
          -- e₃ : cata_pos_list alg xs = xs.map (cata alg)
          let e₃ := mkAppN (mkConst posEqName (← levelsFor posEqName)) (fam.params ++ #[R, alg, xs])
          let foldrFn ← withLocalDeclD `l (mkApp (mkConst ``List [level]) (rTy j)) fun l => mkLambdaFVars #[l] (foldr l)
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
