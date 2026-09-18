import Effect4.Laws.Auto.PositionGate

/-!
# Laws.Auto.TypedStateGen — the typed-state skeleton, emitted from positions and sources

`#emit_typed_state R … to "path"` writes a Lean module holding the invariant's **skeleton**: one
`Ok` predicate per owner type reached from the roots, parametric in a bundle `Preds` of the
carrier predicates, nested along the containment edges, with every position's clause taken
from its source row (`Typed/Sources.lean`). A structure owner becomes a `structure … : Prop`
with one field per clause; an owner with several constructors becomes a `def … : T → Prop` by
`match`, with the clauses of each constructor's arguments. Wrappers quantify: a `List` field
gives `∀ v ∈ x.f, …`, an `Option` field `∀ v, x.f = some v → …`, a function `∀ a, … (x.f a)`.

The bundle is emitted too: a field per carrier kind (`program`, `exit`, `value`, `cause`,
`continuation`), one per `custom` name (over the field's own type), one per `column` name
(over the store), and one per used hook. Layer 1 instantiates the bundle; the skeleton is total
over the data by construction and compiles with no predicate in hand. The emitted file is a
generated artefact: regenerate, never edit (`docs/research/2026-09-18-position-census-design.md`
§2D).
-/

open Lean Meta Elab Command
open Effect4.Laws.Auto.Positions
open Effect4.Program.Typed

namespace Effect4.Laws.Auto.TypedStateGen

/-- What a source row says for one position, resolved to an emitted clause. -/
private def expectText (e : Expected) (inherited : String) : String :=
  match e with
  | .fiber id => s!"(.fiber ({id}))"
  | .promise cell => s!"(.promise ({cell}))"
  | .refColumn => "Expect.refColumn"
  | .row op => s!"(.row ({op}))"
  | .checker point => s!"(.checker ({point}))"
  | .inherited => inherited
  | .const ty => s!"(.const ({ty}))"

private def okName (owner : Name) : String := s!"{owner.getString!}Ok"

/-- A type, fully named, on one line. -/
private def oneLine (ty : Expr) : MetaM String := do
  let t ← withOptions (fun o => o.setBool `pp.fullNames true) do
    return toString (← ppExpr ty)
  let mut t := t.replace "\n" " "
  for _ in [:6] do t := t.replace "  " " "
  return t

private def indent (n : Nat) (s : String) : String := "".pushn ' ' n ++ s

/-- Quantify through the wrappers around a field, returning binders, hypotheses and the term the
carrier is read from. `fn` domains are inferred by the elaborator from the application. -/
private def throughWraps (wraps : List String) (term : String) (depth : Nat) :
    String × String × String :=
  -- (binders, hypotheses, accessed term)
  match wraps with
  | [] => ("", "", term)
  | "List" :: rest =>
    let v := s!"v{depth}"
    let (b, h, t) := throughWraps rest v (depth + 1)
    (s!"∀ {v}, " ++ b, s!"{v} ∈ {term} → " ++ h, t)
  | "Array" :: rest =>
    let v := s!"v{depth}"
    let (b, h, t) := throughWraps rest v (depth + 1)
    (s!"∀ {v}, " ++ b, s!"{v} ∈ {term}.toList → " ++ h, t)
  | "Option" :: rest =>
    let v := s!"v{depth}"
    let (b, h, t) := throughWraps rest v (depth + 1)
    (s!"∀ {v}, " ++ b, s!"{term} = some {v} → " ++ h, t)
  | "Prod.1" :: rest => throughWraps rest s!"({term}).1" depth
  | "Prod.2" :: rest => throughWraps rest s!"({term}).2" depth
  | "Except.1" :: rest =>
    let v := s!"v{depth}"
    let (b, h, t) := throughWraps rest v (depth + 1)
    (s!"∀ {v}, " ++ b, s!"{term} = .error {v} → " ++ h, t)
  | "Except.2" :: rest =>
    let v := s!"v{depth}"
    let (b, h, t) := throughWraps rest v (depth + 1)
    (s!"∀ {v}, " ++ b, s!"{term} = .ok {v} → " ++ h, t)
  | "Sum.1" :: rest =>
    let v := s!"v{depth}"
    let (b, h, t) := throughWraps rest v (depth + 1)
    (s!"∀ {v}, " ++ b, s!"{term} = .inl {v} → " ++ h, t)
  | "Sum.2" :: rest =>
    let v := s!"v{depth}"
    let (b, h, t) := throughWraps rest v (depth + 1)
    (s!"∀ {v}, " ++ b, s!"{term} = .inr {v} → " ++ h, t)
  | "fn" :: rest =>
    let a := s!"a{depth}"
    let (b, h, t) := throughWraps rest s!"({term} {a})" (depth + 1)
    (s!"∀ {a}, " ++ b, h, t)
  | w :: _ => ("", s!"False → ", s!"{term} /- REFUSED wrapper {w} -/")

/-- The clause a source row states at a term of the position's carrier. -/
private def clauseOf (kind : String) (src : Source) (inherited : String) (term : String) :
    Option String :=
  match src with
  | .program e => some s!"P.program w {expectText e inherited} {term}"
  | .continuation e => some s!"P.continuation w {expectText e inherited} {term}"
  | .value e => some s!"P.value w {expectText e inherited} {term}"
  | .exit e => some s!"P.exit w {expectText e inherited} {term}"
  | .cause e => some s!"P.cause w {expectText e inherited} {term}"
  | .custom name => some s!"P.{name} w {inherited} {term}"
  | .hook (some _) => some s!"P.{kind} w (.hook \"{term}\") {term}"
  | .hook none => none
  | .column _ => none
  | .journal => none
  | .refused _ => none
  | .nested _ => none

private def carrierKind (c : Name) : String :=
  if c == `Effects.Program then "program"
  else if c == `Effect4.Exit then "exit"
  else if c == `Effect4.Cause || c == `Effect4.Reason then "cause"
  else if c == `Effect4.Store.Val || c == `Effect4.Machine.Val then "value"
  else "program"

structure Emit where
  decls : Array String := #[]
  /-- The `aesop` registrations: each structure as `safe constructors`, each accessor as
  `safe forward`, each sum-typed `def` as `norm unfold`. -/
  rules : Array String := #[]
  /-- The bundle's fields, by name, with their argument type text. -/
  preds : Array (String × String) := #[]
  emitted : Array Name := #[]
  refused : Array String := #[]

private def addPred (em : Emit) (name ty : String) : Emit :=
  if em.preds.any (·.1 == name) then em else { em with preds := em.preds.push (name, ty) }

/-- Does a row give a clause of its own (not a column, the journal, an unused hook, or an edge)? -/
private def emittable : Source → Bool
  | .program _ | .continuation _ | .value _ | .exit _ | .cause _ | .custom _ | .refused _ => true
  | .hook (some _) => true
  | _ => false

/-- Do any positions with a clause lie under `owner`, transitively, through edges that are not
themselves skipped by an edge row? -/
private def hasPositions (rows : List Effect4.Program.Typed.Row) (ps : Array Positions.Position)
    (edges : Array Edge) : Nat → Name → List Name → Bool
  | 0, _, _ => false
  | fuel + 1, owner, seen =>
    if seen.contains owner then false
    else (ps.any fun p => p.owner == owner && (rows.find? (·.1 == p.key)).any (emittable ·.2)) ||
      edges.any fun e => e.parent == owner &&
        (match rows.find? (·.1 == s!"{e.parent}.{e.field}") with
          | some (_, .custom _) => true
          | some (_, .journal) | some (_, .refused _) => false
          | _ => hasPositions rows ps edges fuel e.child (owner :: seen))

/-- The column names of the positions under `owner`, transitively. -/
private def columnsUnder (rows : List Effect4.Program.Typed.Row) (ps : Array Positions.Position)
    (edges : Array Edge) : Nat → Name → List Name → List String
  | 0, _, _ => []
  | fuel + 1, owner, seen => Id.run do
  if seen.contains owner then return []
  let mut out : List String := []
  for p in ps do
    if p.owner == owner then
      if let some (_, .column c) := rows.find? (·.1 == p.key) then
        unless out.contains c do out := out ++ [c]
  for e in edges do
    if e.parent == owner then
      for c in columnsUnder rows ps edges fuel e.child (owner :: seen) do
        unless out.contains c do out := out ++ [c]
  return out

/-- The field types of an owner at the roots' instantiation, per constructor. -/
private def ownerCtors (owner : Name) (args : Array Expr) (levels : List Level) :
    MetaM (Array (Name × Array (String × Expr × String))) := do
  let iv ← getConstInfoInduct owner
  let mut out := #[]
  for c in iv.ctors do
    let ci ← getConstInfoCtor c
    let cty := ci.type.instantiateLevelParams ci.levelParams levels
    let some cty := instArgs cty args.toList | throwError "emit: {args.size} arguments do not fit {c}"
    let fields ← forallTelescope cty fun xs _ => do
      let mut acc := #[]
      let mut i := 0
      for x in xs do
        let name := argLabel (← x.fvarId!.getDecl).userName i
        let ty ← inferType x
        let tyText ← oneLine ty
        acc := acc.push (name, ty, tyText)
        i := i + 1
      return acc
    out := out.push (c, fields)
  return out

/-- The instantiation of `child` a field type reaches, under the wrappers and functions. -/
private def headOfChild (child : Name) : Nat → Expr → MetaM (Option (Name × Array Expr × List Level))
  | 0, _ => return none
  | fuel + 1, ty => do
  let ty ← whnf ty
  match ty with
  | .forallE _ _ b _ => headOfChild child fuel b
  | _ =>
    match ty.getAppFn with
    | .const n ls =>
      if n == child then return some (n, ty.getAppArgs, ls)
      if defaultWrappers.contains n then
        for a in ty.getAppArgs do
          if let some h ← headOfChild child fuel a then return some h
        return none
      return none
    | _ => return none

/-- The type constant and arguments a field type reaches, after the wrappers and functions. -/
private def headOf : Nat → Expr → MetaM (Option (Name × Array Expr × List Level))
  | 0, _ => return none
  | fuel + 1, ty => do
  let ty ← whnf ty
  match ty with
  | .forallE _ _ b _ => headOf fuel b
  | _ =>
    match ty.getAppFn with
    | .const n ls =>
      if defaultWrappers.contains n then
        -- the last carrier-bearing argument
        let mut out := none
        for a in ty.getAppArgs do
          if let some h ← headOf fuel a then out := some h
        return out
      else return some (n, ty.getAppArgs, ls)
    | _ => return none

/-- Emit the `Ok` of one owner, and of the owners it reaches, into `em`. -/
private def emitOwner (rows : List Effect4.Program.Typed.Row) (ps : Array Positions.Position) (edges : Array Edge) :
    Nat → Name → Array Expr → List Level → Emit → MetaM Emit
  | 0, owner, _, _, _ => throwError "emit: the owner walk ran out of depth at {owner}"
  | fuel + 1, owner, args, levels, em => do
  if em.emitted.contains owner then return em
  let mut em := { em with emitted := em.emitted.push owner }
  let ctors ← ownerCtors owner args levels
  let ownerTy ← oneLine (mkAppN (mkConst owner levels) args)
  let isStruct := ctors.size == 1
  let mut lines : Array String := #[]
  let mut arms : Array String := #[]
  -- the store's columns, once, at the store
  let columns := if owner == `Effect4.Machine.Stores then columnsUnder rows ps edges 64 owner [] else []
  for (c, fields) in ctors do
    let mut clauses : Array String := #[]
    let mut binders : Array String := #[]
    for name in columns do
      em := addPred em name ownerTy
      clauses := clauses.push s!"P.{name} w x"
    for (fname, fty, ftyText) in fields do
      let label := if isStruct then fname else s!"{c.getString!}.{fname}"
      let key := s!"{owner}.{label}"
      let term := if isStruct then s!"x.{fname}" else fname
      binders := binders.push fname
      let position := ps.find? (·.key == key)
      let edgeRow := rows.find? (·.1 == key)
      match position with
      | some p =>
        match rows.find? (·.1 == key) with
        | none => throwError "emit: no source row for {key}"
        | some (_, src) =>
          match src with
          | .custom name =>
            em := addPred em name ftyText
            clauses := clauses.push s!"P.{name} w e {term}"
          | .refused reason =>
            em := { em with refused := em.refused.push s!"{key}: {reason}" }
            clauses := clauses.push s!"True  -- REFUSED {key}: {reason}"
          | .hook (some _) =>
            let kind := carrierKind p.carrier
            em := addPred em kind ""
            let (b, h, t) := throughWraps p.wraps term 0
            clauses := clauses.push s!"{b}{h}P.{kind} w (.hook \"{label}\") {t}"
          | .column _ | .hook none | .journal | .nested _ => pure ()
          | _ =>
            let kind := carrierKind p.carrier
            em := addPred em kind ""
            let (b, h, t) := throughWraps p.wraps term 0
            if let some cl := clauseOf kind src "e" t then
              clauses := clauses.push s!"{b}{h}{cl}"
      | none =>
        -- the edges out of this field, one per child reached
        for edge in edges.filter (fun e => e.parent == owner && e.field == label) do
          match edgeRow with
          | some (_, .custom name) =>
            em := addPred em name ftyText
            unless clauses.contains s!"P.{name} w e {term}" do
              clauses := clauses.push s!"P.{name} w e {term}"
          | some (_, .journal) => pure ()
          | some (_, .refused reason) =>
            em := { em with refused := em.refused.push s!"{key}: {reason}" }
            unless clauses.any (·.startsWith "True  -- REFUSED") do
              clauses := clauses.push s!"True  -- REFUSED {key}: {reason}"
          | _ =>
            if hasPositions rows ps edges 64 edge.child [] then
              let passed := match edgeRow with
                | some (_, .nested ex) => expectText ex "e"
                | _ => "e"
              let some (child, cargs, cls) ← headOfChild edge.child 64 fty
                | throwError "emit: no head for {key} at {edge.child}"
              em ← emitOwner rows ps edges fuel child cargs cls em
              let (b, h, t) := throughWraps edge.wraps term 0
              clauses := clauses.push s!"{b}{h}{okName child} P w {passed} {t}"
    if isStruct then
      lines := lines.push s!"structure {okName owner} (P : Preds W) (w : W) (e : Expect) (x : {ownerTy}) : Prop where"
      if clauses.isEmpty then lines := lines.push (indent 2 "trivial : True")
      let mut i := 0
      let mut accessors : Array String := #[]
      for cl in clauses do
        lines := lines.push (indent 2 s!"c{i} : {cl}")
        accessors := accessors.push s!"{okName owner}.c{i}"
        i := i + 1
      em := { em with rules := em.rules.push s!"attribute [aesop safe constructors] {okName owner}" }
      unless accessors.isEmpty do
        em := { em with rules := em.rules.push s!"attribute [aesop safe forward] {" ".intercalate accessors.toList}" }
    else
      -- a binder no clause mentions is anonymous
      let mentions (b cl : String) : Bool :=
        let code : String := (cl.splitOn "--").headD ""
        (code.splitOn b).length > 1
      let used := binders.map fun b => if clauses.any (mentions b) then b else s!"_{b}"
      let pat := if binders.isEmpty then s!".{c.getString!}" else s!".{c.getString!} " ++ " ".intercalate used.toList
      let body := if clauses.isEmpty then "True" else " ∧ ".intercalate clauses.toList
      arms := arms.push (indent 2 s!"| {pat} => {body}")
  unless isStruct do
    lines := #[s!"def {okName owner} (P : Preds W) (w : W) (e : Expect) : {ownerTy} → Prop"] ++ arms
    em := { em with rules := em.rules.push s!"attribute [aesop norm unfold] {okName owner}" }
  return { em with decls := em.decls.push ("\n".intercalate lines.toList) }

syntax (name := emitTypedState) "#emit_typed_state " ident+ " to " str : command

@[command_elab emitTypedState] def elabEmit : CommandElab := fun stx => do
  let roots := stx[1].getArgs.map (·.getId)
  let path := stx[3].isStrLit?.getD ""
  liftTermElabM do
    let rows ← Effect4.Laws.Auto.TypedSources.readRows
    let mut ps : Array Positions.Position := #[]
    let mut edges : Array Edge := #[]
    let mut em : Emit := {}
    let mut tops : Array String := #[]
    for root in roots do
      let w ← walkOf root
      ps := ps ++ w.positions; edges := edges ++ w.edges
    for root in roots do
      let ci ← getConstInfo root
      let v := match ci.value? with
        | some v => v
        | none => mkConst root (ci.levelParams.map mkLevelParam)
      let some (owner, args, ls) ← headOf 64 v | throwError "emit: no head for {root}"
      em ← emitOwner rows ps edges 64 owner args ls em
      tops := tops.push s!"abbrev {root.getString!}Ok (P : Preds W) (w : W) (x : {root}) : Prop := {okName owner} P w Expect.root x"
    -- the bundle
    let mut bundle : Array String := #["structure Preds (W : Type) where"]
    for (name, ty) in em.preds do
      let field := match name with
        | "program" => "program : W → Expect → Effect4.Program.Sched.RProgram → Prop"
        | "exit" => "exit : W → Expect → Effect4.Machine.ExitV → Prop"
        | "value" => "value : W → Expect → Effect4.Store.Val → Prop"
        | "cause" => "cause : W → Expect → Effect4.Machine.CauseV → Prop"
        | "continuation" => "continuation : W → Expect → (Effect4.Machine.ExitV → Effect4.Program.Sched.RProgram) → Prop"
        | "HeapNat" | "PromiseTable" => s!"{name} : W → {ty} → Prop"
        | _ => s!"{name} : W → Expect → {ty} → Prop"
      bundle := bundle.push (indent 2 field)
    let header := s!"import Effect4.Laws.Program.EvaluateR
import Aesop

/-!
# Typed/State — the typed-state skeleton (GENERATED)

Emitted by `#emit_typed_state` (`Laws/Auto/TypedStateGen.lean`, run as `lake env lean scripts/lean/TypedStateEmit.lean`) from the position census of
{roots.toList} and the source table `Typed/Sources.lean`. One `Ok` per owner, nested along the
containment edges, parametric in the carrier predicates `Preds`. Regenerate; never edit.
-/

set_option autoImplicit false

namespace Effect4.Program.Typed

-- `W` is the typing tables and the store: layer 1 instantiates it.
" ++ "variable {W : Type}" ++ s!"

/-- Where a position's expected type comes from, as data the predicates read. -/
inductive Expect
  | root
  | fiber (id : Effect4.FiberId)
  | promise (cell : Effect4.Machine.DeferredKey)
  | refColumn
  | row (op : Effect4.Program.NativeOp)
  | checker (point : Effect4.Program.Point)
  | const (ty : Effect4.Program.EffTy)
  | hook (name : String)

"
    let footer := "\n\nend Effect4.Program.Typed\n"
    let refusedNote := if em.refused.isEmpty then "" else
      "\n/-! ## Refused (named debt; each is a decisions or DI row)\n" ++
      "\n".intercalate (em.refused.toList.map (s!"- {·}")) ++ "\n-/\n"
    let body := "\n".intercalate bundle.toList ++ "\n\n" ++
      "\n\n".intercalate em.decls.toList ++ "\n\n" ++ "\n".intercalate tops.toList ++
      "\n\n/-! ## The search: `repeat constructor` on the intro side, the accessors on the elim side -/\n\n" ++
      "\n".intercalate em.rules.toList
    IO.FS.writeFile path (header ++ body ++ refusedNote ++ footer)
    logInfo m!"emitted {em.decls.size} Ok predicates, {em.preds.size} bundle fields, {em.refused.size} refused, to {path}"

end Effect4.Laws.Auto.TypedStateGen
