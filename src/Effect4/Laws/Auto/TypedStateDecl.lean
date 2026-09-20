import Effect4.Laws.Auto.Positions
import Effect4.Laws.Auto.TypedSources
import Effect4.Laws.Auto.RuleSets

/-!
The typed-state skeleton as declarations in the current module. The producer constructs
syntax from the census and closed kernel types; it never pretty-prints a type, parses source
text, or writes a source file. Unsupported shapes fail before the command can finish.
-/
open Lean Meta Elab Command Parser.Term
open Effect4.Laws.Auto.Positions Effect4.Program.Typed

namespace Effect4.Laws.Auto.TypedStateDecl

-- These declarations intentionally bind the public vocabulary in the caller's namespace.
-- All reflected global type names are separately rooted by `typeSyntax`.
set_option hygiene false

private def levelSyntax : Level → MetaM (TSyntax `level)
  | .zero => `(level| 0)
  | .succ u => do `(level| $(← levelSyntax u) + 1)
  | .max u v => do `(level| max $(← levelSyntax u) $(← levelSyntax v))
  | .imax u v => do `(level| imax $(← levelSyntax u) $(← levelSyntax v))
  | .param n => return ⟨mkIdent n⟩
  | .mvar _ => throwError "typed state: unresolved universe"

/-- Translate closed type syntax structurally. Names are fully qualified, applications explicit,
and bound variables fresh. No rendering convention is part of this interface. -/
private def typeSyntax : Nat → Array (TSyntax `term) → Expr → MetaM (TSyntax `term)
  | 0, _, _ => throwError "typed state: type syntax exhausted its depth"
  | fuel + 1, bound, e => do
    match e with
    | .const n levels =>
      let us ← levels.toArray.mapM levelSyntax
      `(term| @$(mkIdent (`_root_ ++ n)).{$us,*})
    | .app .. =>
      let f ← typeSyntax fuel bound e.getAppFn
      let args ← e.getAppArgs.mapM (typeSyntax fuel bound)
      `(term| $f $args*)
    | .sort u => `(Sort $(← levelSyntax u))
    | .bvar i =>
      let some x := bound[bound.size - i - 1]? | throwError "typed state: loose type variable"
      return x
    | .forallE _ t b bi =>
      let x := mkIdent (Name.mkSimple s!"arg{bound.size}")
      let t ← typeSyntax fuel bound t
      let b ← typeSyntax fuel (bound.push (← `($x:ident))) b
      match bi with
      | .implicit => `(∀ {$x : $t}, $b)
      | .strictImplicit => `(∀ ⦃$x : $t⦄, $b)
      | .instImplicit => `(∀ [$x : $t], $b)
      | .default => `(∀ ($x : $t), $b)
    | .mdata _ b => typeSyntax fuel bound b
    | .lit (.natVal n) => return ⟨Syntax.mkNumLit (toString n)⟩
    | _ => throwError "typed state: unsupported or open field type {e}"

/-- The source table admits identifier paths, not arbitrary Lean source fragments. -/
private def accessSyntax (path : String) : MetaM (TSyntax `term) := do
  let parts := path.splitOn "."
  unless parts.all (fun p => !p.isEmpty && p.toList.all (fun c => c.isAlphanum || c == '_')) do
    throwError "typed state: not an identifier path: {path}"
  let some first := parts.head? | throwError "typed state: empty identifier path"
  let mut term ← `($(mkIdent (Name.mkSimple first)):ident)
  for p in parts.drop 1 do term ← `(($term).$(mkIdent (Name.mkSimple p)):ident)
  return term

private def expectSyntax (ex : Expected) : MetaM (TSyntax `term) := do
  match ex with
  | .fiber id => `(.fiber $(← accessSyntax id))
  | .promise cell => `(.promise $(← accessSyntax cell))
  | .refColumn => `(Expect.refColumn)
  | .row op => `(.row $(← accessSyntax op))
  | .checker point => `(.checker $(← accessSyntax point))
  | .inherited => `(e)
  | .const ty => `(.const $(← accessSyntax ty))

private def okName (owner : Name) : Ident := mkIdent (Name.mkSimple s!"{owner.getString!}Ok")

/-- Lift a predicate through the observed wrappers. The continuation builds its body at the
carrier; wrappers retain their exact side and their order. -/
private def throughWraps (wraps : List String) (term : TSyntax `term) (depth : Nat)
    (body : TSyntax `term → MetaM (TSyntax `term)) : MetaM (TSyntax `term) := do
  match wraps with
  | [] => body term
  | "Prod.1" :: rest => throughWraps rest (← `(($term).1)) depth body
  | "Prod.2" :: rest => throughWraps rest (← `(($term).2)) depth body
  | w :: rest =>
    let x := mkIdent (Name.mkSimple s!"v{depth}")
    let xt ← `($x:ident)
    if w == "fn" then
      let b ← throughWraps rest (← `($term $xt)) (depth + 1) body
      return ← `(∀ $x:ident, $b)
    let b ← throughWraps rest xt (depth + 1) body
    match w with
    | "List" => `(∀ $x:ident, $xt ∈ $term → $b)
    | "Array" => `(∀ $x:ident, $xt ∈ ($term).toList → $b)
    | "Option" => `(∀ $x:ident, $term = some $xt → $b)
    | "Except.1" => `(∀ $x:ident, $term = .error $xt → $b)
    | "Except.2" => `(∀ $x:ident, $term = .ok $xt → $b)
    | "Sum.1" => `(∀ $x:ident, $term = .inl $xt → $b)
    | "Sum.2" => `(∀ $x:ident, $term = .inr $xt → $b)
    | _ => throwError "typed state: unsupported wrapper {w}"

private def carrierKind (c : Name) : MetaM String := do
  if c == `Effects.Program then return "program"
  if c == `Effect4.Exit then return "exit"
  if c == `Effect4.Cause || c == `Effect4.Reason then return "cause"
  if c == `Effect4.Store.Val || c == `Effect4.Machine.Val then return "value"
  if c == `Effect4.Program.EffName then return "name"
  throwError "typed state: no predicate family for carrier {c}"

structure Predicate where
  name : String
  type : Expr
  column : Bool

structure Emit where
  decls : Array (TSyntax `command) := #[]
  rules : Array (TSyntax `command) := #[]
  preds : Array Predicate := #[]
  emitted : Array (Name × Expr) := #[]
  refused : Array String := #[]
  /-- Position and edge keys a clause was emitted for, or deliberately omitted. -/
  accounted : Array String := #[]
  /-- Field keys whose subtree a whole-field, journal or refused source covers: nothing beneath
  that edge is stated position by position. Coverage follows the field, not the child's type:
  the same type under an uncovered edge elsewhere is still checked. -/
  covered : Array String := #[]

private def addPred (em : Emit) (name : String) (type : Expr) (column := false) : MetaM Emit := do
  if let some old := em.preds.find? (·.name == name) then
    unless old.column == column && (← isDefEq old.type type) do
      throwError "typed state: incompatible uses of predicate {name}"
    return em
  return { em with preds := em.preds.push {name, type, column} }

private def emittable : Source → Bool
  | .program _ | .continuation _ | .value _ | .exit _ | .cause _ | .custom _ | .refused _ => true
  | .hook (some _) => true
  | _ => false

private def columnsUnder (rows : List Row) (ps : Array Positions.Position) (edges : Array Edge) :
    Nat → Name → List Name → MetaM (List String)
  | 0, owner, _ => throwError "typed state: column walk exhausted at {owner}"
  | fuel + 1, owner, seen => do
    if seen.contains owner then return []
    let mut out : List String := []
    for p in ps do
      if p.owner == owner then
        if let some (_, .column c) := rows.find? (·.1 == p.key) then
          unless out.contains c do out := out ++ [c]
    for e in edges do
      if e.parent == owner then
        for c in ← columnsUnder rows ps edges fuel e.child (owner :: seen) do
          unless out.contains c do out := out ++ [c]
    return out

/-- Does an owner beneath a field contribute a clause: a stated position, a whole-field
predicate on one of its edges, a column it owns, or such an owner further down. -/
private def hasPositions (rows : List Row) (ps : Array Positions.Position) (edges : Array Edge)
    (columnOwners : List Name) : Nat → Name → List Name → MetaM Bool
  | 0, owner, _ => throwError "typed state: clause walk exhausted at {owner}"
  | fuel + 1, owner, seen => do
    if seen.contains owner then return false
    if columnOwners.contains owner then
      unless (← columnsUnder rows ps edges fuel owner []).isEmpty do return true
    if ps.any (fun p => p.owner == owner && (rows.find? (·.1 == p.key)).any (emittable ·.2)) then
      return true
    for e in edges do
      if e.parent == owner then
        match rows.find? (·.1 == s!"{e.parent}.{e.field}") with
        | some (_, .custom _) => return true
        | some (_, .journal) | some (_, .refused _) => pure ()
        | _ => if ← hasPositions rows ps edges columnOwners fuel e.child (owner :: seen) then return true
    return false

/-- The keys of the column positions `columnsUnder` reaches from `owner`: what a column owner's
clauses cover, occurrence by occurrence. -/
private def columnKeysUnder (rows : List Row) (ps : Array Positions.Position) (edges : Array Edge) :
    Nat → Name → List Name → MetaM (List String)
  | 0, owner, _ => throwError "typed state: column walk exhausted at {owner}"
  | fuel + 1, owner, seen => do
    if seen.contains owner then return []
    let mut out : List String := []
    for p in ps do
      if p.owner == owner then
        if let some (_, .column _) := rows.find? (·.1 == p.key) then
          unless out.contains p.key do out := out ++ [p.key]
    for e in edges do
      if e.parent == owner then
        for k in ← columnKeysUnder rows ps edges fuel e.child (owner :: seen) do
          unless out.contains k do out := out ++ [k]
    return out

private def headOfChild (child : Name) : Nat → Expr → MetaM (Option Expr)
  | 0, _ => throwError "typed state: child walk exhausted at {child}"
  | fuel + 1, ty => do
    let ty ← whnf ty
    match ty with
    | .forallE n d b bi =>
      withLocalDecl n bi d fun x => headOfChild child fuel (b.instantiate1 x)
    | _ =>
      if ty.getAppFn.isConstOf child then return some ty
      if let .const n _ := ty.getAppFn then
        if defaultWrappers.contains n then
          for a in ty.getAppArgs do
            if let some h ← headOfChild child fuel a then return some h
      return none

private def ownerCtors (ty : Expr) : MetaM (Array (Name × Array (String × Expr))) := do
  let .const owner levels := ty.getAppFn | throwError "typed state: not an owner type: {ty}"
  let iv ← getConstInfoInduct owner
  let mut out := #[]
  for c in iv.ctors do
    let ci ← getConstInfoCtor c
    let cty := ci.type.instantiateLevelParams ci.levelParams levels
    let some cty := instArgs cty ty.getAppArgs.toList | throwError "typed state: arguments do not fit {c}"
    let fields ← forallTelescope cty fun xs _ => do
      let mut acc := #[]
      for i in [:xs.size] do
        let x := xs[i]!
        let fieldTy ← inferType x
        if fieldTy.hasFVar then throwError "typed state: dependent field of {c} needs an explicit adapter"
        acc := acc.push (argLabel (← x.fvarId!.getDecl).userName i, fieldTy)
      return acc
    out := out.push (c, fields)
  return out

private def emitOwner (rows : List Row) (ps : Array Positions.Position) (edges : Array Edge)
    (columnOwners : List Name) :
    Nat → Expr → Emit → MetaM Emit
  | 0, ty, _ => throwError "typed state: owner walk exhausted at {ty}"
  | fuel + 1, ty, em => do
    let ty ← whnf ty
    let .const owner _ := ty.getAppFn | throwError "typed state: not an owner type: {ty}"
    if let some (_, old) := em.emitted.find? (·.1 == owner) then
      unless ← isDefEq old ty do throwError "typed state: multiple instances need distinct names: {owner}"
      return em
    if em.emitted.any (fun (n, _) => okName n == okName owner) then
      throwError "typed state: generated name collision at {owner}"
    let mut em := { em with emitted := em.emitted.push (owner, ty) }
    let ctors ← ownerCtors ty
    let ownerTy ← typeSyntax 256 #[] ty
    let isStruct := isStructure (← getEnv) owner
    let mut arms : Array (TSyntax ``Parser.Term.matchAltExpr) := #[]
    let name := okName owner
    let columns ← if columnOwners.contains owner then
      columnsUnder rows ps edges 64 owner [] else pure []
    if columnOwners.contains owner then
      em := { em with accounted := em.accounted ++ (← columnKeysUnder rows ps edges 64 owner []).toArray }
    for (c, fields) in ctors do
      let mut clauses : Array (TSyntax `term) := #[]
      let mut binders : Array (TSyntax `term) := #[]
      for col in columns do
        em ← addPred em col ty true
        clauses := clauses.push (← `(P.$(mkIdent (Name.mkSimple col)):ident w x))
      let single := ctors.size == 1
      for (fname, fty) in fields do
        -- the census's naming rule: a single constructor's arguments are the owner's fields
        let label := if single then fname else s!"{c.getString!}.{fname}"
        let key := s!"{owner}.{label}"
        let f := mkIdent (Name.mkSimple fname)
        let term ← if isStruct then `(x.$f:ident) else `($f:ident)
        binders := binders.push (← `($f:ident))
        let src? : Option Source := rows.find? (·.1 == key) |>.map (·.2)
        let positions := ps.filter (·.key == key)
        let es := edges.filter (fun e => e.parent == owner && e.field == label)
        if positions.isEmpty && es.isEmpty then continue
        -- One resolution per field. A whole-field source owns the field and everything under
        -- it; otherwise the field's direct positions and its child edges each contribute a
        -- clause, never one instead of the other.
        match src? with
        | some (.custom pred) =>
          em ← addPred em pred fty
          clauses := clauses.push (← `(P.$(mkIdent (Name.mkSimple pred)):ident w e $term))
          em := { em with accounted := em.accounted.push key, covered := em.covered.push key }
        | some (.refused reason) =>
          em := { em with refused := em.refused.push s!"{key}: {reason}",
                          accounted := em.accounted.push key, covered := em.covered.push key }
          clauses := clauses.push (← `(True))
        | some .journal =>
          em := { em with accounted := em.accounted.push key, covered := em.covered.push key }
        | _ =>
          if !positions.isEmpty then
            let some src := src? | throwError "typed state: missing source for {key}"
            match src with
            | .column _ | .hook none => em := { em with accounted := em.accounted.push key }
            | .nested _ => throwError "typed state: a nested source names a child, but {key} is a direct position"
            | _ =>
              for p in positions do
                let kind ← match src with
                  | .continuation _ => pure "continuation"
                  | _ => carrierKind p.carrier
                -- Recover the carrier's type by walking the same wrappers in the field type.
                let some carrierTy ← headOfChild p.carrier 64 fty
                  | throwError "typed state: no carrier type for {key}"
                em ← addPred em kind carrierTy
                let ex ← match src with
                  | .program ex | .continuation ex | .value ex | .exit ex | .cause ex => expectSyntax ex
                  | .hook _ => `(.hook $(Syntax.mkStrLit label))
                  | _ => throwError "typed state: unsupported source at {key}"
                clauses := clauses.push (← throughWraps p.wraps term 0 fun value =>
                  `(P.$(mkIdent (Name.mkSimple kind)):ident w $ex $value))
              em := { em with accounted := em.accounted.push key }
          for edge in es do
            if ← hasPositions rows ps edges columnOwners 64 edge.child [] then
              let ex ← match src? with
                | some (.nested ex) => expectSyntax ex
                | _ => `(e)
              let some childTy ← headOfChild edge.child 64 fty
                | throwError "typed state: no child type at {key}"
              em ← emitOwner rows ps edges columnOwners fuel childTy em
              clauses := clauses.push (← throughWraps edge.wraps term 0 fun value =>
                `($(okName edge.child):ident P w $ex $value))
              em := { em with accounted := em.accounted.push key }
      if isStruct then
        let mut fs : Array (TSyntax ``Parser.Command.structSimpleBinder) := #[]
        let mut accessors : Array Ident := #[]
        if clauses.isEmpty then clauses := #[← `(True)]
        for i in [:clauses.size] do
          let field := Name.mkSimple s!"c{i}"
          fs := fs.push (← `(Parser.Command.structSimpleBinder| $(mkIdent field):ident : $(clauses[i]!)))
          accessors := accessors.push (mkIdent (name.getId ++ field))
        em := {em with decls := em.decls.push (← `(command|
          structure $name:ident {W : Type} (P : Preds W) (w : W) (e : Expect) (x : $ownerTy) : Prop where
            $[$fs:structSimpleBinder]*))}
        em := {em with rules := em.rules.push (← `(command|
          attribute [aesop safe constructors (rule_sets := [Effect4.TypedState])] $name:ident))}
        em := {em with rules := em.rules.push (← `(command|
          attribute [aesop safe forward (rule_sets := [Effect4.TypedState])] $[$accessors:ident]*))}
      else
        let mut body ← `(True)
        if !clauses.isEmpty then
          body := clauses.back!
          for cl in clauses.pop.reverse do body ← `($cl ∧ $body)
        -- Constructor parameters are inferred in patterns; do not expose their type arguments.
        let pattern ← `($(mkIdent c):ident $binders*)
        arms := arms.push (← `(matchAltExpr| | $pattern => $body))
    unless isStruct do
      em := {em with decls := em.decls.push (← `(command|
        def $name:ident {W : Type} (P : Preds W) (w : W) (e : Expect) (x : $ownerTy) : Prop :=
          match x with $arms:matchAlt*))}
      em := {em with rules := em.rules.push (← `(command|
        attribute [aesop norm unfold (rule_sets := [Effect4.TypedState])] $name:ident))}
    return em

syntax (name := typedState) "#typed_state " ident+ " using " ident (" columns " ident+)? : command

@[command_elab typedState] def elabTypedState : CommandElab := fun stx => do
  let roots := stx[1].getArgs.map (·.getId)
  let table ← liftTermElabM <| realizeGlobalConstNoOverloadWithInfo stx[3]
  let columnOwners := if stx[4].isNone then [] else stx[4][1].getArgs.toList.map (·.getId)
  let (em, bundle, tops) ← liftTermElabM do
    let rows ← Effect4.Laws.Auto.TypedSources.readRows table
    let mut ps : Array Positions.Position := #[]
    let mut edges : Array Edge := #[]
    for root in roots do
      let walk ← walkOf root
      for p in walk.positions do unless ps.contains p do ps := ps.push p
      for e in walk.edges do unless edges.contains e do edges := edges.push e
    let keys := rows.map (·.1)
    unless keys.length == keys.eraseDups.length do throwError "typed state: duplicate source rows"
    for p in ps do
      unless keys.contains p.key do throwError "typed state: missing source for {p.key}"
    let mut em : Emit := {}
    let mut tops : Array (TSyntax `command) := #[]
    let mut reach : Array Name := #[]
    for root in roots do
      let ty ← whnf (mkConst root)
      em ← emitOwner rows ps edges columnOwners 64 ty em
      let owner := ty.getAppFn.constName!
      unless reach.contains owner do reach := reach.push owner
      let name := okName root
      unless name == okName owner do
        tops := tops.push (← `(command|
          abbrev $name:ident {W : Type} (P : Preds W) (w : W) (x : $(mkIdent root):ident) : Prop :=
          $(okName owner):ident P w Expect.root x))
    -- Every position and edge the census found under a stated subtree is stated or deliberately
    -- omitted, and every column occurrence was emitted by a column owner whose walk reached it.
    -- Coverage follows the field: the owners in reach are those on a path of uncovered edges
    -- from a root, so a type under a covered edge here and an uncovered edge there is checked
    -- for the uncovered occurrence; and a column predicate's name covers nothing by itself. A
    -- shape the emitter does not understand therefore fails here, by key, instead of weakening
    -- the invariant to `True`.
    for _ in [:edges.size + 1] do
      for e in edges do
        if reach.contains e.parent && !em.covered.contains s!"{e.parent}.{e.field}"
            && !reach.contains e.child then
          reach := reach.push e.child
    for p in ps do
      unless reach.contains p.owner do continue
      match rows.find? (·.1 == p.key) with
      | some (_, .journal) | some (_, .hook none) => pure ()
      | some (_, .column c) =>
        unless em.accounted.contains p.key do
          throwError "typed state: column {c} at {p.key} has no column owner"
      | _ =>
        unless em.accounted.contains p.key do
          throwError "typed state: {p.key} has a source but no clause was emitted"
    for e in edges do
      unless reach.contains e.parent do continue
      let key := s!"{e.parent}.{e.field}"
      match rows.find? (·.1 == key) with
      | some (_, .custom _) | some (_, .nested _) | some (_, .refused _) =>
        unless em.accounted.contains key do
          throwError "typed state: {key} has a source but no clause was emitted"
      | _ => pure ()
    let mut fields : Array (TSyntax ``Parser.Command.structSimpleBinder) := #[]
    for p in em.preds do
      let ty ← typeSyntax 256 #[] p.type
      let ty ← if p.column then `(W → $ty → Prop) else `(W → Expect → $ty → Prop)
      fields := fields.push (← `(Parser.Command.structSimpleBinder| $(mkIdent (Name.mkSimple p.name)):ident : $ty))
    let bundle ← `(command| structure Preds (W : Type) where $[$fields:structSimpleBinder]*)
    return (em, bundle, tops)
  elabCommand bundle
  for decl in em.decls do elabCommand decl
  for top in tops do elabCommand top
  for rule in em.rules do elabCommand rule
  logInfo m!"typed state: {em.decls.size} predicates, {em.preds.size} carrier predicates, {em.refused.size} refusals"

end Effect4.Laws.Auto.TypedStateDecl
