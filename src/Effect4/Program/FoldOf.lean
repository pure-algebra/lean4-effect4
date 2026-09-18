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

Family members the block does not traverse get the carrier `Unit`. Nothing in `f`'s own
module changes: this is the second file beside it, and `eq_cata` is the connector its callers
move across before `f` is deleted.

What it refuses, by name: a recursive call on something other than an immediate child; an arm
that uses a child's value as well as its result (a paramorphism); an argument after the family
value, or one before it that a recursive call changes (an accumulator — the
fold-returning-a-function shape, not yet handled); a block whose members disagree on their fixed
parameters.

The names it relies on are the generator's (`tools/Effect4Gen/Fold.lean`): for a family root
`X` in namespace `N`, `N.XFam` with one constructor per member in declaration order,
`N.XAlgebra (params…) (R : XFam → Type u)` with fields `<fam>_<ctor>` in member-then-constructor
order, `N.XHom alg` with fields `f_<fam>` then `h_<fam>_<ctor>` in the same order, and
`N.hom_eq_cata_<fam>`, `N.cata_<fam>`.
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

/-- One member of `f`'s mutual block: which family member it takes, after how many fixed
binders, with what result. -/
structure Member where
  fn : Name
  /-- Index into `Family.members`. -/
  member : Nat
  fixed : Nat
  /-- The result type as a lambda over the fixed binders. Refused if anything follows the
  family value. -/
  result : Expr
deriving Inhabited

/-- Read `g`'s signature: the first binder whose type is a family member. -/
def memberOf (fam : Family) (g : Name) : MetaM Member := do
  let info ← getConstInfoDefn g
  forallTelescope info.type fun xs body => do
    for h : i in [:xs.size] do
      let x := xs[i]
      let t ← whnf (← inferType x)
      if let .const c _ := t.getAppFn then
        if let some idx := fam.members.idxOf? c then
          unless i + 1 == xs.size do
            throwError "fold_of: {g} takes arguments after the family value (an accumulator); \
              the fold-returning-a-function shape is not handled yet"
          let result ← mkLambdaFVars (xs.extract 0 i) body
          return { fn := g, member := idx, fixed := i, result }
    throwError "fold_of: {g} takes no value of the family {fam.members}"

/-- Replace every `g fixed… child` — a block member at the fixed parameters on one of
`children` — by that child's result variable. -/
def abstractCalls (block : Array Name) (fixed : Array Expr) (children : Array (Expr × Expr))
    (e : Expr) : Expr :=
  e.replace fun sub =>
    match sub.getAppFn with
    | .const g _ =>
      if block.contains g then
        let args := sub.getAppArgs
        if args.size == fixed.size + 1 &&
            (fixed.zip (args.extract 0 fixed.size)).all (fun (a, b) => a == b) then
          (children.find? (fun (c, _) => c == args.back!)).map (·.2)
        else none
      else none
    | _ => none

/-- `XFam.rec (motive := fun _ => Type u) T₁ … Tₙ`, as a function of the family. -/
def carrierOf (famType : Name) (level : Level) (carriers : Array Expr) : MetaM Expr :=
  withLocalDeclD `fam (mkConst famType) fun famVar => do
    let motive ← mkLambdaFVars #[famVar] (mkSort (mkLevelSucc level))
    let recFn := mkConst (famType ++ `rec) [mkLevelSucc (mkLevelSucc level)]
    mkLambdaFVars #[famVar] (mkAppN recFn (#[motive] ++ carriers ++ #[famVar]))

/-- The arm of block member `m` at constructor application `node`: its unfold equation's
right-hand side with the matcher reduced. -/
def armOf (m : Member) (fixed : Array Expr) (node : Expr) : MetaM Expr := do
  let some eqDef ← getUnfoldEqnFor? m.fn (nonRec := true) | throwError "fold_of: {m.fn} has no unfold equation"
  let eq ← instantiateForall (← getConstInfo eqDef).type (fixed ++ #[node])
  let some (_, _, rhs) := eq.eq? | throwError "fold_of: {eqDef} is not an equation"
  let rhs ← whnfCore rhs
  match ← reduceMatcher? rhs with
  | .reduced e => whnfCore e
  | _ => pure rhs

syntax (name := foldOf) "fold_of " ident : command

@[command_elab foldOf] def elabFoldOf : CommandElab := fun stx => do
  let target ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  liftTermElabM do
    let info ← getConstInfoDefn target
    let block := info.all.toArray
    -- the fixed binders: everything before the first family value in `target`'s signature
    let fixedCount ← forallTelescope info.type fun xs _ => do
      for h : i in [:xs.size] do
        if (← familyOf? (← inferType xs[i])).isSome then return i
      throwError "fold_of: {target} takes no value of a free object with a generated fold"
    forallBoundedTelescope info.type fixedCount fun fixed rest => do
      -- the family, read under the fixed binders (its parameters may mention them)
      let fam ← forallTelescope rest fun xs _ => do
        for x in xs do
          if let some fam ← familyOf? (← inferType x) then return fam
        throwError "fold_of: {target} takes no value of a free object with a generated fold"
      let famType := fam.fams[0]!.getPrefix
      let members ← block.mapM fun g => (memberOf fam g : MetaM Member)
      for m in members do
        unless m.fixed == fixedCount do
          throwError "fold_of: {m.fn} has {m.fixed} fixed parameters, {target} has {fixedCount}"
      let algCtor := (← getConstInfoInduct fam.algebra).ctors[0]!
      let homCtor := (← getConstInfoInduct fam.hom).ctors[0]!
      let levelParams := info.levelParams.map mkLevelParam
      let memberTy := fun (j : Nat) => mkAppN (mkConst fam.members[j]!) fam.params
      let memberFn := fun (m : Member) => mkAppN (mkConst m.fn levelParams) fixed
      -- the result type of each block member at its family member; `Unit` elsewhere
      let mut results : Array Expr := #[]
      let mut level : Level := Level.zero
      for i in [:fam.members.size] do
        match members.find? (·.member == i) with
        | some m =>
          let r ← instantiateLambda m.result fixed
          results := results.push r
          level ← decLevel (← getLevel r)
        | none => results := results.push (mkConst ``Unit)
      -- the arms: for each constructor of a covered member, the unfold equation's right-hand
      -- side with recursive calls named; and whether any arm needs the child itself
      let childrenOf := fun (args : Array Expr) => do
        let mut out : Array (Nat × Nat) := #[]   -- (argument index, member index)
        for h : k in [:args.size] do
          let t ← whnf (← inferType args[k])
          if let .const c _ := t.getAppFn then
            if let some j := fam.members.idxOf? c then out := out.push (k, j)
        pure out
      let mut needsPara := false
      for i in [:fam.members.size] do
        let some m := members.find? (·.member == i) | continue
        let ind ← getConstInfoInduct fam.members[i]!
        for ctor in ind.ctors do
          let ctorTy ← instantiateForall (← getConstInfoCtor ctor).type fam.params
          let usesChild ← forallTelescope ctorTy fun args _ => do
            let node := mkAppN (mkAppN (mkConst ctor) fam.params) args
            let childFam ← childrenOf args
            let arm ← armOf m fixed node
            -- name the recursive calls with placeholders that cannot occur in `arm`
            let marks := childFam.map fun (k, _) => (args[k]!, mkConst (`fold_of_result ++ Name.mkNum .anonymous k))
            let body := abstractCalls block fixed marks arm
            if body.find? (fun sub => match sub with
                | .const g _ => block.contains g | _ => false) |>.isSome then
              throwError "fold_of: {m.fn} at {ctor}: a recursive call that is not on an \
                immediate child at the fixed parameters:\n  {← ppExpr arm}"
            pure (childFam.any fun (k, _) => body.containsFVar args[k]!.fvarId!)
          if usesChild then needsPara := true
      let para := needsPara
      -- the carrier: the result, or (value × result) when an arm needs a child's value
      let carriers ← results.mapIdxM fun j r => do
        if para then pure (mkAppN (mkConst ``Prod [Level.zero, level]) #[memberTy j, r]) else pure r
      let R ← carrierOf famType level carriers
      let algLevelsFor := fun (n : Name) => do
        let c ← getConstInfo n
        pure (c.levelParams.map fun _ => level)
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
              -- under `para`, a result variable holds (value, result)
              let valueOf := fun (r : Expr) (j : Nat) =>
                if para then mkAppN (mkConst ``Prod.fst [Level.zero, level]) #[memberTy j, results[j]!, r] else r
              let resultOf := fun (r : Expr) (j : Nat) =>
                if para then mkAppN (mkConst ``Prod.snd [Level.zero, level]) #[memberTy j, results[j]!, r] else r
              let rebuilt := mkAppN (mkAppN (mkConst ctor) fam.params) (args.mapIdx fun k a =>
                match childFam.findIdx? (·.1 == k) with
                | some c => valueOf rs[c]! childFam[c]!.2
                | none => a)
              let body ← match members.find? (·.member == i) with
                | some m => do
                  let arm ← armOf m fixed node
                  let calls := (childFam.zip rs).map fun ((k, j), r) => (args[k]!, resultOf r j)
                  let body := abstractCalls block fixed calls arm
                  -- a child used as a value: its value half
                  let body := body.replace fun sub =>
                    match childFam.findIdx? (fun (k, _) => sub == args[k]!) with
                    | some c => some (valueOf rs[c]! childFam[c]!.2)
                    | none => none
                  pure body
                | none => pure (mkConst ``Unit.unit)
              let value := if para then mkAppN (mkConst ``Prod.mk [Level.zero, level]) #[memberTy i, results[i]!, rebuilt, body] else body
              let field ← mkLambdaFVars fieldArgs value
              -- the equation: the block member's value at the node (paired with the node
              -- under `para`) is the field at the recursive results — definitionally
              let lhs := match members.find? (·.member == i) with
                | some m => mkApp (memberFn m) node
                | none => mkConst ``Unit.unit
              let lhs := if para then mkAppN (mkConst ``Prod.mk [Level.zero, level]) #[memberTy i, results[i]!, node, lhs] else lhs
              let homEq ← mkLambdaFVars args (← mkEqRefl lhs)
              pure (field, homEq)
          fields := fields.push field
          homEqs := homEqs.push homEq
      -- `f.alg`
      let algVal := mkAppN (mkConst algCtor (← algLevelsFor algCtor)) (fam.params ++ #[R] ++ fields)
      let algTy := mkAppN (mkConst fam.algebra (← algLevelsFor fam.algebra)) (fam.params ++ #[R])
      let algName := target ++ `alg
      addAndCompile <| .defnDecl
        { name := algName, levelParams := info.levelParams
          type := ← mkForallFVars fixed algTy, value := ← mkLambdaFVars fixed algVal
          hints := .abbrev, safety := .safe }
      let alg := mkAppN (mkConst algName levelParams) fixed
      -- `f.hom`: the block's functions (paired with the identity under `para`; `()` where the
      -- block has no member), then the equations
      let mut fns : Array Expr := #[]
      for i in [:fam.members.size] do
        let fn ← withLocalDeclD `e (memberTy i) fun e => do
          let r := match members.find? (·.member == i) with
            | some m => mkApp (memberFn m) e
            | none => mkConst ``Unit.unit
          let r := if para then mkAppN (mkConst ``Prod.mk [Level.zero, level]) #[memberTy i, results[i]!, e, r] else r
          mkLambdaFVars #[e] r
        fns := fns.push fn
      let homVal := mkAppN (mkConst homCtor (← algLevelsFor homCtor)) (fam.params ++ #[R, alg] ++ fns ++ homEqs)
      let homTy := mkAppN (mkConst fam.hom (← algLevelsFor fam.hom)) (fam.params ++ #[R, alg])
      let homName := target ++ `hom
      addDecl <| .defnDecl
        { name := homName, levelParams := info.levelParams
          type := ← mkForallFVars fixed homTy, value := ← mkLambdaFVars fixed homVal
          hints := .abbrev, safety := .safe }
      let hom := mkAppN (mkConst homName levelParams) fixed
      -- `g.eq_cata` per block member: `g e = cata alg e`, or its second component under `para`
      for m in members do
        let j := m.member
        let unique := mkConst fam.uniques[j]! (← algLevelsFor fam.uniques[j]!)
        let (thmTy, thmVal) ← withLocalDeclD `e (memberTy j) fun e => do
          let lhs := mkApp (memberFn m) e
          let cata := mkAppN (mkConst fam.catas[j]! (← algLevelsFor fam.catas[j]!)) (fam.params ++ #[R, alg, e])
          let uniq := mkAppN unique (fam.params ++ #[R, alg, hom, e])
          let (rhs, val) ←
            if para then
              let snd := mkAppN (mkConst ``Prod.snd [Level.zero, level]) #[memberTy j, results[j]!]
              pure (mkApp snd cata, ← mkCongrArg snd uniq)
            else pure (cata, uniq)
          pure (← mkForallFVars (fixed ++ #[e]) (← mkEq lhs rhs), ← mkLambdaFVars (fixed ++ #[e]) val)
        let thmName := m.fn ++ `eq_cata
        addDecl <| .thmDecl { name := thmName, levelParams := info.levelParams, type := thmTy, value := thmVal }
        logInfo m!"fold_of: {thmName} : {← ppExpr thmTy}"
      logInfo m!"fold_of{if para then " (paramorphism: the carrier pairs the value)" else ""}: \
        {algName} : {← ppExpr (← mkForallFVars fixed algTy)}"

end Effect4.Program.FoldOf
