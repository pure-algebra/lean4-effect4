import Lean.Elab.Tactic
import Effect4.Laws.Auto.ListSubset

/-!
# Laws.Auto.SubsetTac — `sub_tac` and `mem_tac`, the subset and membership decisions

Meta code only, inside the gate's implementation boundary (`Test/Audit/AxiomGate.lean`,
`auditImplementationModules`): a tactic elaborator reaches `Classical.choice` through Lean's own
framework, and no theorem lives here. The theory it applies is `Laws/Auto/ListSubset.lean`.

`sub_tac` proves `A ⊆ B`, and `mem_tac` proves `a ∈ B`, when `A` and `B` are lists built from
`++`, `::` and `[]` over atoms once the key traversals in them are unfolded. The unfolding is one
`simp only` with the simp set `keys_norm` — declared here, filled where the traversals are defined
(`attribute [keys_norm] …`) — and the lemmas a call adds with `norm [...]`. Each side is then
reflected to a tree over one table of atoms (`ListSubset.Tree`), the hypotheses of
`sub_tac using h₁, h₂` (inclusions, or memberships read as singleton inclusions) and every
membership hypothesis of the local context over the same element type are reflected the same way —
a hypothesis with holes is instantiated against every atom its left side unifies with — and
`ListSubset.check` decides the inclusion. Atoms are compared syntactically, then up to
reducible unfolding; only when that decision fails are they merged up to full unfolding and the
atoms that unfold to `[]` dropped, and the decision run once more. The proof is one application of
`subset_of_check` whose check the kernel evaluates. There is no search: a refusal names the parts
of the left side that nothing on the right side or in the hypotheses covers, and prints the
normalised goal.
-/

set_option autoImplicit false

open Lean Elab Meta Tactic

namespace Effect4.Laws.SubsetTac

open ListSubset (Tree Hyp)

/- The simp set `keys_norm`: the key traversals and list laws `sub_tac` and `mem_tac` unfold
before deciding, filled where the traversals are defined (`attribute [keys_norm] …`); a call adds
more with `norm [...]`. Registered by a binder-free `initialize` and read back by name
(`getSimpExtension?`), so no handle is declared: `register_simp_attr` would declare two bodyless
initializer-set opaques under hygienic names, which the trust gate cannot admit by exact name
(decisions row 184). -/
initialize do
  discard <| registerSimpAttr `keys_norm
    "the key traversals and list laws `sub_tac` and `mem_tac` unfold before deciding"

/-- `@[keys_norm]`: add a definition or lemma to the unfoldings of `sub_tac` and `mem_tac`. -/
syntax (name := Parser.Attr.keys_norm) "keys_norm"
  (Lean.Parser.Tactic.simpPre <|> Lean.Parser.Tactic.simpPost)? patternIgnore("← " <|> "<- ")? (prio)? : attr

/-- The tree as a term. -/
def quoteTree : Tree → Expr
  | .nil => mkConst ``Tree.nil
  | .atom i => mkApp (mkConst ``Tree.atom) (mkNatLit i)
  | .app l r => mkApp2 (mkConst ``Tree.app) (quoteTree l) (quoteTree r)

/-- The tree with its atoms renamed, some to `[]`. -/
def remap (rep : Array Nat) (isNil : Array Bool) : Tree → Tree
  | .nil => .nil
  | .atom i => if isNil.getD i false then .nil else .atom (rep.getD i i)
  | .app l r => .app (remap rep isNil l) (remap rep isNil r)

/-- The tree with some atoms replaced by trees. -/
def substAtoms (f : Nat → Option Tree) : Tree → Tree
  | .nil => .nil
  | .atom i => (f i).getD (.atom i)
  | .app l r => .app (substAtoms f l) (substAtoms f r)

/-- Does the expression have list structure at its head? -/
def hasListHead (e : Expr) : Bool :=
  e.isAppOfArity ``HAppend.hAppend 6 || e.isAppOfArity ``List.append 3 ||
    e.isAppOfArity ``List.cons 3 || e.isAppOfArity ``List.nil 1

/-- The table of atoms, each a `List α`. -/
structure Atoms where
  table : Array Expr := #[]

/-- The index of `e`: an entry equal to it syntactically, else one equal up to reducible
unfolding, else a new entry. -/
def Atoms.index (st : Atoms) (e : Expr) : MetaM (Nat × Atoms) := do
  if let some i := st.table.findIdx? (· == e) then return (i, st)
  if let some i ← st.table.findIdxM? fun a => withReducible (isDefEq a e) then return (i, st)
  return (st.table.size, { table := st.table.push e })

/-- Reflect a list over `α`: `x ++ y`, `h :: t` (the head as the atom `[h]`), `[]`; anything
else is an atom. -/
def reify (α : Expr) : Expr → Atoms → MetaM (Tree × Atoms)
  | .app (.app (.app (.app (.app (.app (.const ``HAppend.hAppend _) _) _) _) _) x) y, st => do
    let (l, st) ← reify α x st
    let (r, st) ← reify α y st
    return (.app l r, st)
  | .app (.app (.app (.const ``List.append _) _) x) y, st => do
    let (l, st) ← reify α x st
    let (r, st) ← reify α y st
    return (.app l r, st)
  | .app (.app (.app (.const ``List.cons _) _) h) t, st => do
    let (i, st) ← st.index (← mkListLit α [h])
    let (r, st) ← reify α t st
    return (.app (.atom i) r, st)
  | .app (.const ``List.nil _) _, st => return (.nil, st)
  | .mdata _ e, st => reify α e st
  | e, st => do
    let (i, st) ← st.index e
    return (.atom i, st)

/-- The element type of a list type, through abbreviations. -/
def listElem? (ty : Expr) : MetaM (Option Expr) := do
  match ← whnfD ty with
  | .app (.const ``List _) α => return some α
  | _ => return none

/-- `L ⊆ M` over lists: the element type and the two sides. -/
def subsetSides? (ty : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  match ty.consumeMData.getAppFnArgs with
  | (``HasSubset.Subset, #[listTy, _, l, m]) => return (← listElem? listTy).map fun α => (α, l, m)
  | (``List.Subset, #[α, l, m]) => return some (α, l, m)
  | _ => return none

/-- `x ∈ B` over lists: the element type, the element and the list. -/
def memSides? (ty : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  match ty.consumeMData.getAppFnArgs with
  | (``Membership.mem, #[α, listTy, _, coll, x]) =>
    return (← listElem? listTy).map fun _ => (α, x, coll)
  | _ => return none

/-- The simp context of a call: `keys_norm` and the call's own arguments, built as `simp only`
builds them (no default simp set, no default simprocs). -/
def normContext (extra : Syntax) : TacticM (Simp.Context × Simp.SimprocsArray) := do
  let some ext ← getSimpExtension? `keys_norm
    | throwError "sub_tac: the simp set `keys_norm` is not registered"
  let thms ← ext.getTheorems
  let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  let r ← elabSimpArgs extra ctx (simprocs := #[{}]) (eraseLocal := false) (kind := .simp)
  return (r.ctx, r.simprocs)

/-- A hypothesis in reflected form, with its proof of the normalised statement. -/
structure RHyp where
  lhs : Tree
  rhs : Tree
  proof : Expr

/-- A hypothesis with holes, kept until its left side unifies with an atom. -/
structure Pattern where
  stx : Syntax
  proof : Expr
  lhs : Expr
  rhs : Expr

/-- The inclusion a `using` term states, after reducible unfolding: a membership `x ∈ l` is read
as `[x] ⊆ l`. The proof returned proves the inclusion. -/
def hypSides (stx : Syntax) (pf : Expr) : TacticM (Expr × Expr × Expr) := do
  let ty ← instantiateMVars (← inferType pf)
  if let some (_, l, m) ← subsetSides? ty then return (pf, l, m)
  if let some (α, x, coll) ← memSides? ty then
    return (← mkAppM ``ListSubset.singleton_subset_of_mem #[pf], ← mkListLit α [x], coll)
  let ty ← whnfR ty
  if let some (_, l, m) ← subsetSides? ty then return (pf, l, m)
  if let some (α, x, coll) ← memSides? ty then
    return (← mkAppM ``ListSubset.singleton_subset_of_mem #[pf], ← mkListLit α [x], coll)
  throwError "sub_tac using: {stx} has type{indentExpr ty}\nwhich is neither an inclusion nor a membership of lists"

/-- Normalise `l ⊆ m` with the call's simp context and reflect both sides; `pf` proves `l ⊆ m`. -/
def reflectHyp (stx : Syntax) (α : Expr) (l m pf : Expr) (ctx : Simp.Context)
    (simprocs : Simp.SimprocsArray) (st : Atoms) : TacticM (RHyp × Atoms) := do
  let hty ← mkAppM ``HasSubset.Subset #[l, m]
  let (r, _) ← simp hty ctx simprocs
  let pf ← if r.proof?.isSome then r.mkCast (← mkExpectedTypeHint pf hty) else pure pf
  let some (_, l', m') ← subsetSides? r.expr
    | throwError "sub_tac using: after `keys_norm`, {stx} states{indentExpr r.expr}\nwhich is not an inclusion of lists"
  let (lhs, st) ← reify α l' st
  let (rhs, st) ← reify α m' st
  return ({ lhs, rhs, proof := pf }, st)

/-- Decide the main goal, an inclusion or a membership of lists, after `keys_norm`. -/
def decide (hyps : Array Syntax) (extra : Syntax) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let (ctx, simprocs) ← normContext extra
  let (r, _) ← simp target ctx simprocs
  let ty := r.expr
  if ty.isConstOf ``True then
    goal.assign (← mkEqMPR (← r.getProof) (mkConst ``True.intro))
    replaceMainGoal []
    return
  let (α, isMem, lhsE, rhsE) ← match ← subsetSides? ty with
    | some (α, l, m) => pure (α, false, l, m)
    | none => match ← memSides? ty with
      | some (α, x, coll) => pure (α, true, x, coll)
      | none => throwError "sub_tac: after `keys_norm` the goal is{indentExpr ty}\nwhich is neither an inclusion nor a membership of lists"
  let (b, st) ← reify α rhsE {}
  let (a, st) ← if isMem then do
      let (i, st) ← st.index (← mkListLit α [lhsE])
      pure (Tree.atom i, st)
    else reify α lhsE st
  -- the hypotheses: concrete ones reflected at once, ones with holes matched against the atoms
  let mut st := st
  let mut rhyps : Array RHyp := #[]
  let mut patterns : Array Pattern := #[]
  for h in hyps do
    let pf ← Tactic.elabTerm h none
    let (pf, l, m) ← hypSides h pf
    if (← instantiateMVars l).hasExprMVar then
      patterns := patterns.push { stx := h, proof := pf, lhs := l, rhs := m }
    else
      let (rhyp, st') ← reflectHyp h α l m pf ctx simprocs st
      rhyps := rhyps.push rhyp
      st := st'
  -- every membership fact of the local context over the same element type
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let dty ← instantiateMVars decl.type
    let some (β, x, coll) ← memSides? dty | continue
    unless ← withReducible (isDefEq β α) do continue
    let pf ← mkAppM ``ListSubset.singleton_subset_of_mem #[decl.toExpr]
    let (rhyp, st') ← reflectHyp (mkIdent decl.userName) α (← mkListLit α [x]) coll pf ctx simprocs st
    rhyps := rhyps.push rhyp
    st := st'
  let mut tried : Array (Nat × Nat) := #[]
  let mut matched : Array Nat := #[]
  for _ in [:patterns.size + 1] do
    let mut progress := false
    for hp : pi in [:patterns.size] do
      let p := patterns[pi]
      for ai in [:st.table.size] do
        if tried.contains (pi, ai) then continue
        tried := tried.push (pi, ai)
        let c := st.table[ai]!
        let s ← saveState
        let instance? ← do
          if ← isDefEq p.lhs c then
            let pf ← instantiateMVars p.proof
            let m ← instantiateMVars p.rhs
            pure (if pf.hasExprMVar || m.hasExprMVar then none else some (pf, m))
          else pure none
        s.restore
        let some (pf, m) := instance? | continue
        let (rhyp, st') ← reflectHyp p.stx α c m pf ctx simprocs st
        rhyps := rhyps.push rhyp
        st := st'
        matched := matched.push pi
        progress := true
    unless progress do break
  -- the decision, natively. When it fails: merge the atoms equal up to unfolding and drop the
  -- ones that unfold to `[]`; then replace each uncovered atom whose unfolding has list structure
  -- by that structure's tree, and merge again; at most four rounds.
  let mut a := a
  let mut b := b
  let mut hypsL : List Hyp := rhyps.toList.map fun rh => (rh.lhs, rh.rhs)
  let mut merged := 0
  for round in [:5] do
    if ListSubset.check hypsL a b then break
    -- merge every atom not yet compared against the earlier ones
    let n := st.table.size
    let mut isNil : Array Bool := Array.replicate n false
    let mut rep : Array Nat := Array.range n
    for i in [merged:n] do
      if (← whnfD st.table[i]!).isAppOf ``List.nil then isNil := isNil.set! i true
    for i in [merged:n] do
      if isNil[i]! then continue
      for j in [:i] do
        if isNil[j]! || rep[j]! != j then continue
        if ← isDefEq st.table[i]! st.table[j]! then
          rep := rep.set! i j
          break
    merged := n
    a := remap rep isNil a
    b := remap rep isNil b
    hypsL := hypsL.map fun (l, m) => (remap rep isNil l, remap rep isNil m)
    rhyps := rhyps.map fun rh => { rh with lhs := remap rep isNil rh.lhs, rhs := remap rep isNil rh.rhs }
    if ListSubset.check hypsL a b || round == 4 then break
    -- expand the uncovered atoms that unfold to list structure
    let reach := ListSubset.closure hypsL hypsL.length b.atoms
    let uncovered := (a.atoms.filter fun i => !ListSubset.has i reach).eraseDups
    let mut expansions : Array (Nat × Tree) := #[]
    for i in uncovered do
      let e ← whnfD st.table[i]!
      if hasListHead e then
        let (t, st') ← reify α e st
        st := st'
        expansions := expansions.push (i, t)
    if expansions.isEmpty then break
    a := substAtoms (fun i => (expansions.find? (·.1 == i)).map (·.2)) a
  unless ListSubset.check hypsL a b do
    let reach := ListSubset.closure hypsL hypsL.length b.atoms
    let missing := (a.atoms.filter fun i => !ListSubset.has i reach).eraseDups
    let parts := MessageData.joinSep (missing.map fun i => indentExpr st.table[i]!) ""
    let unmatched := patterns.toList.zipIdx.filterMap fun (p, pi) =>
      if matched.contains pi then none else some m!"{p.stx}"
    let viaHyps := if hyps.isEmpty then m!"" else m!" or through the hypotheses"
    let holes := if unmatched.isEmpty then m!"" else
      m!"\nno atom matched the hypotheses with holes: {unmatched}"
    throwError m!"sub_tac: the left side has parts no part of the right side{viaHyps} covers:{parts}\nafter `keys_norm` the goal is{indentExpr ty}{holes}"
  -- the proof: the reflected statement, its soundness premise and the kernel-evaluated check
  let treeTy := mkConst ``Tree
  let hypTy := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) treeTy treeTy
  let listTy ← mkAppM ``List #[α]
  let lsE ← mkListLit listTy st.table.toList
  let mut soundE ← mkAppOptM ``ListSubset.sound_nil #[some α, some lsE]
  let mut hypsE ← mkListLit hypTy []
  for rh in rhyps.reverse do
    let lE := quoteTree rh.lhs
    let mE := quoteTree rh.rhs
    soundE ← mkAppOptM ``ListSubset.sound_cons
      #[some α, some lsE, some lE, some mE, some hypsE, some rh.proof, some soundE]
    let pair := mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) treeTy treeTy lE mE
    hypsE := mkApp3 (mkConst ``List.cons [Level.zero]) hypTy pair hypsE
  let aE := quoteTree a
  let bE := quoteTree b
  let checkE := mkApp3 (mkConst ``ListSubset.check) hypsE aE bE
  let hcTy ← mkEq checkE (mkConst ``Bool.true)
  let hc ← mkExpectedTypeHint (← mkEqRefl (mkConst ``Bool.true)) hcTy
  let pfSub ← mkAppOptM ``ListSubset.subset_of_check
    #[some α, some lsE, some hypsE, some aE, some bE, some soundE, some hc]
  let pf ← if isMem then
      mkAppOptM ``ListSubset.mem_of_singleton_subset #[some α, some lhsE, some rhsE, some pfSub]
    else pure pfSub
  unless ← isDefEq (← inferType pf) ty do
    throwError "sub_tac: the reflected statement does not match the goal{indentExpr ty}"
  let proof ← match r.proof? with
    | none => pure pf
    | some h => mkEqMPR h pf
  goal.assign proof
  replaceMainGoal []

/-- `sub_tac` proves `A ⊆ B`; `sub_tac using h₁, h₂` also carries atoms through the inclusions
(or memberships) `hᵢ`; `norm [...]` adds unfoldings to `keys_norm` for this call. -/
syntax (name := subTacStx) "sub_tac" (" using " term,+)? (" norm " "[" Lean.Parser.Tactic.simpArg,* "]")? : tactic

/-- `mem_tac` proves `a ∈ B`; `using` and `[...]` as for `sub_tac`. -/
syntax (name := memTacStx) "mem_tac" (" using " term,+)? (" [" Lean.Parser.Tactic.simpArg,* "]")? : tactic

@[tactic subTacStx] def evalSubTac : Tactic := fun stx => do
  let hyps := if stx[1].isNone then #[] else stx[1][1].getSepArgs
  let extra := if stx[2].isNone then mkNullNode else mkNullNode #[stx[2][1], stx[2][2], stx[2][3]]
  decide hyps extra

@[tactic memTacStx] def evalMemTac : Tactic := fun stx => do
  let hyps := if stx[1].isNone then #[] else stx[1][1].getSepArgs
  let extra := if stx[2].isNone then mkNullNode else stx[2]
  decide hyps extra

end Effect4.Laws.SubsetTac
