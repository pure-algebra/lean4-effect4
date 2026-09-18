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

/-- One member of `f`'s mutual block: its type, which family member it takes and at which
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
deriving Inhabited

/-- Read `g`'s signature: the first binder whose type is a family member. -/
def memberOf (fam : Family) (g : Name) : MetaM Member := do
  let info ← getConstInfoDefn g
  forallTelescope info.type fun xs _ => do
    for h : i in [:xs.size] do
      let t ← whnf (← inferType xs[i])
      if let .const c _ := t.getAppFn then
        if let some idx := fam.members.idxOf? c then
          return { fn := g, type := info.type, member := idx, at_ := i, arity := xs.size }
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

/-- The number of leading binders that every member has and that every recursive call in the
block passes through unchanged: the fixed prefix. -/
def fixedPrefix (block : Array Name) (members : Array Member) (fam : Family) : MetaM Nat := do
  let mut k := members.foldl (fun k m => min k m.at_) members[0]!.at_
  for m in members do
    let ind ← getConstInfoInduct fam.members[m.member]!
    k ← forallTelescope m.type fun xs _ => do
      let params := (← whnf (← inferType xs[m.at_]!)).getAppArgs.extract 0 fam.params.size
      let mut k := k
      for ctor in ind.ctors do
        let ctorTy ← instantiateForall (← getConstInfoCtor ctor).type params
        k ← forallTelescope ctorTy fun args _ => do
          let node := mkAppN (mkAppN (mkConst ctor) params) args
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
    let fam₀ ← forallTelescope info.type fun xs _ => do
      for x in xs do
        if let some fam ← familyOf? (← inferType x) then return fam
      throwError "fold_of: {target} takes no value of a free object with a generated fold"
    let members ← block.mapM fun g => (memberOf fam₀ g : MetaM Member)
    let fixedCount ← fixedPrefix block members fam₀
    let algCtor := (← getConstInfoInduct fam₀.algebra).ctors[0]!
    let homCtor := (← getConstInfoInduct fam₀.hom).ctors[0]!
    forallBoundedTelescope info.type fixedCount fun fixed rest => do
      -- the family again, under the fixed binders (its parameters may mention them)
      let fam ← forallTelescope rest fun xs _ => do
        for x in xs do
          if let some fam ← familyOf? (← inferType x) then return fam
        throwError "fold_of: {target} takes no value of a free object with a generated fold"
      let famType := fam.fams[0]!.getPrefix
      let levelParams := info.levelParams.map mkLevelParam
      let memberTy := fun (j : Nat) => mkAppN (mkConst fam.members[j]!) fam.params
      let memberFn := fun (m : Member) => mkAppN (mkConst m.fn levelParams) fixed
      let byMember := fun (i : Nat) => members.find? (·.member == i)
      let withShape := fun {α : Type} (m : Member) (k : Array Expr → Nat → Expr → MetaM α) =>
        FoldOf.withShape fixed fixedCount m k
      -- the carrier per family member: the member's function type over its varying binders,
      -- or `Unit`
      let mut results : Array Expr := #[]
      let mut level : Level := Level.zero
      for i in [:fam.members.size] do
        match byMember i with
        | some m =>
          let carrier ← withShape m fun ys pre body => do
            let e := ys[pre]!
            let acc := ys.eraseIdx! pre
            for y in acc do
              if (← inferType y).containsFVar e.fvarId! then
                throwError "fold_of: {m.fn}: a binder's type depends on the family value"
            if body.containsFVar e.fvarId! then
              throwError "fold_of: {m.fn}: the result type depends on the family value"
            pure (stripParamAnnotations (← mkForallFVars acc body))
          results := results.push carrier
          level ← decLevel (← getLevel carrier)
        | none => results := results.push (mkConst ``Unit)
      let preOf : Name → Nat := fun g =>
        match members.find? (·.fn == g) with
        | some m => m.at_ - fixedCount
        | none => 0
      let childrenOf := fun (args : Array Expr) => do
        let mut out : Array (Nat × Nat) := #[]   -- (argument index, member index)
        for h : k in [:args.size] do
          let t ← whnf (← inferType args[k])
          if let .const c _ := t.getAppFn then
            if let some j := fam.members.idxOf? c then out := out.push (k, j)
        pure out
      -- a call `g fixed pre child post…` becomes `r_child pre post…`; the call may stop short
      -- of the last binders (`vs.mapM (encodeRaw t)`): the carrier is curried the same way
      let abstractCalls := fun (children : Array (Expr × Expr)) (e : Expr) =>
        e.replace fun sub =>
          match sub.getAppFn with
          | .const g _ =>
            if block.contains g && sub.getAppNumArgs > fixedCount + preOf g then
              let args := sub.getAppArgs
              let at_ := fixedCount + preOf g
              if (fixed.zip (args.extract 0 fixedCount)).all (fun (a, b) => a == b) then
                match children.find? (fun (c, _) => c == args[at_]!) with
                | some (_, r) =>
                  some (mkAppN r (args.extract fixedCount at_ ++ args.extract (at_ + 1) args.size))
                | none => none
              else none
            else none
          | _ => none
      -- pass 1: does any arm use a child's value (a paramorphism)?
      let mut needsPara := false
      for i in [:fam.members.size] do
        let some m := byMember i | continue
        let ind ← getConstInfoInduct fam.members[i]!
        for ctor in ind.ctors do
          let ctorTy ← instantiateForall (← getConstInfoCtor ctor).type fam.params
          let usesChild ← forallTelescope ctorTy fun args _ => withShape m fun ys pre _ => do
            let acc := ys.eraseIdx! pre
            let node := mkAppN (mkAppN (mkConst ctor) fam.params) args
            let childFam ← childrenOf args
            let (_, arm) ← armOf m (fixed ++ acc.extract 0 pre) node (acc.extract pre acc.size)
            let marks := childFam.map fun (k, _) =>
              (args[k]!, mkConst (`fold_of_result ++ Name.mkNum .anonymous k))
            let body := abstractCalls marks arm
            if body.find? (fun sub => match sub with
                | .const g _ => block.contains g | _ => false) |>.isSome then
              throwError "fold_of: {m.fn} at {ctor}: a recursive call that is not on an \
                immediate child at the fixed parameters:\n  {← ppExpr arm}"
            pure (childFam.any fun (k, _) => body.containsFVar args[k]!.fvarId!)
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
      -- the algebra: one field per constructor, member order then constructor order, and the
      -- homomorphism equation of each, by `rfl`
      let mut fields : Array Expr := #[]
      let mut homEqs : Array Expr := #[]
      for i in [:fam.members.size] do
        let ind ← getConstInfoInduct fam.members[i]!
        for ctor in ind.ctors do
          let ctorTy ← instantiateForall (← getConstInfoCtor ctor).type fam.params
          let (field, homEq) ← forallTelescope ctorTy fun args _ => do
            let node := mkAppN (mkAppN (mkConst ctor) fam.params) args
            let childFam ← childrenOf args
            let decls := childFam.map fun (k, j) =>
              (Name.mkSimple s!"r{k}", fun (_ : Array Expr) => pure (mkApp R (mkConst fam.fams[j]!)))
            withLocalDeclsD decls fun rs => do
              let fieldArgs := args.mapIdx fun k a =>
                match childFam.findIdx? (·.1 == k) with
                | some c => rs[c]!
                | none => a
              let valueOf := fun (r : Expr) (j : Nat) => if para then fstOf j r else r
              let resultOf := fun (r : Expr) (j : Nat) => if para then sndOf j r else r
              let rebuilt := mkAppN (mkAppN (mkConst ctor) fam.params) (args.mapIdx fun k a =>
                match childFam.findIdx? (·.1 == k) with
                | some c => valueOf rs[c]! childFam[c]!.2
                | none => a)
              -- the result half: the arm as a function of the varying binders, or `()`; and
              -- the member's own value at the node as the same function, for the equation
              -- the result half: the arm as a function of the varying binders, or `()`; and
              -- the equation: `g … node … = M` is the unfold equation, `M` reduces to the
              -- field at the recursive results (a matcher on a constructor; never through
              -- the recursion's `brecOn`), closed by `funext` over the varying binders and
              -- `congrArg (node, ·)` under `para`
              let (result, proof) ← match byMember i with
                | some m => withShape m fun ys pre _ => do
                  let acc := ys.eraseIdx! pre
                  let before := fixed ++ acc.extract 0 pre
                  let after := acc.extract pre acc.size
                  let (_, arm) ← armOf m before node after
                  let calls := (childFam.zip rs).map fun ((k, j), r) => (args[k]!, resultOf r j)
                  let body := abstractCalls calls arm
                  let body := body.replace fun sub =>
                    match childFam.findIdx? (fun (k, _) => sub == args[k]!) with
                    | some c => some (valueOf rs[c]! childFam[c]!.2)
                    | none => none
                  let mut h ← unfoldEqAt m levelParams before node after
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
      -- `f.hom`: each member as a function of the family value, then of its varying binders
      -- (paired with the value under `para`; `()` where the block has no member), then the
      -- equations
      let mut fns : Array Expr := #[]
      for i in [:fam.members.size] do
        let fn ← withLocalDeclD `e (memberTy i) fun e => do
          let r ← match byMember i with
            | some m => withShape m fun ys pre _ => do
              let acc := ys.eraseIdx! pre
              let call := mkAppN (memberFn m) (acc.extract 0 pre ++ #[e] ++ acc.extract pre acc.size)
              mkLambdaFVars acc call
            | none => pure (mkConst ``Unit.unit)
          let r := if para then pair i e r else r
          mkLambdaFVars #[e] r
        fns := fns.push fn
      let homVal := mkAppN (mkConst homCtor (← levelsFor homCtor)) (fam.params ++ #[R, alg] ++ fns ++ homEqs)
      let homTy := mkAppN (mkConst fam.hom (← levelsFor fam.hom)) (fam.params ++ #[R, alg])
      let homName := target ++ `hom
      addDecl <| .defnDecl
        { name := homName, levelParams := info.levelParams
          type := ← mkForallFVars fixed homTy, value := ← mkLambdaFVars fixed homVal
          hints := .abbrev, safety := .safe }
      let hom := mkAppN (mkConst homName levelParams) fixed
      -- `g.eq_cata` per block member: `g fixed pre e post = cata alg e pre post`, the fold's
      -- second component under `para`
      for m in members do
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
      logInfo m!"fold_of{if para then " (paramorphism: the carrier pairs the value)" else ""}: \
        {algName} : {← ppExpr (← mkForallFVars fixed algTy)}"

syntax (name := foldOf) "fold_of " ident : command

@[command_elab foldOf] def elabFoldOf : CommandElab := fun stx => do
  let target ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  liftTermElabM (convert target)

end Effect4.Program.FoldOf
