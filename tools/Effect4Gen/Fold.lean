import Lean
import Tools.GeneratedStamp

/-!
# Effect4Gen.Fold — the fold of a free object, and the companions of a nested one

    lake env lean -M 4096 --run tools/Effect4Gen/Fold.lean --group <G> --imports <M,…>
      --out <file> [--append <guards>] [--kind <Type>=elim[:<prefix>]]… <Type>…

From the constructor declarations of each named family, nothing hand-listed:

* **a plain block** (no member under a container): the algebra `XAlgebra`, the fold
  `cata_<fam>`, the homomorphism `XHom` with its uniqueness `hom_eq_cata_<fam>`, `foldMap`, the
  path fold `foldMapAt`, and the monadic half (`XMAlgebra`, `foldM`, `foldM_eq_cata`,
  `foldM_id`, `foldM_natural`, the `MonadMorphism` they quantify over);
* **a nested block** (a member under `List`, `Option`, a product or a one-parameter record): the
  same pure fold with one helper per composite position (`cata_pos_*` and their map lemmas), one
  public equation per constructor, and **no monadic half and no path fold** (below);
* **`--kind <Type>=elim`**: instead of a fold, the companions Lean does not derive for a nested
  one-member family — the single-motive eliminator `T.ind` (registered
  `@[induction_eliminator]`), the structural equality `T.beq` with `T.beq_iff` and the
  `DecidableEq` instance over it, and the structural `Repr` printing the derived text — into a
  module between the declaration and its functions (decisions rows 119 and 171; probe Q, Q1).
  Refused by name: a parameterised or indexed family, a mutual block, a family with no member
  under a container (derive it), a one-parameter-structure position.
* **`--extras [--namespace NS]`** (probe U, decisions row 182): instead of the fold, the generic
  families every table-driven traversal is read through, from the declaration of a plain block —
  the tags with their names and binders, the payload by sort, `build`/`kids` and the view law, the
  per-constructor table type, the layer algebra, the head and paired folds with their connectors,
  fusion and the banana split from uniqueness, the per-layer invariant. Without the flag nothing
  of it is emitted and every output is today's. Refused by name: a nested block (its layer is
  `ArgF`'s; the nested extension is owed), a constructor with two payload arguments.

## The monadic-fold decision (seat W2, 2026-10-01; probe Q, Q3)

A block with a nested position gets no monadic half and no path fold. A `foldM` over a nested
position needs a `sequence` per position type (a list of monadic results is not a monadic
list), and nothing reads one: at `74dae8d2`, `git grep -nwE
'foldMapAt_ty|TyMAlgebra|foldM_ty|foldM_eq_cata_ty|foldM_id_ty|foldM_natural_ty|TyAlgebra\.toM'
-- src Test tools ':!src/Effect4/Program/Fold.lean'` finds nothing (tested; seat W2's log
`gen/fold-monadic-consumers.log`), and `SchemaFold` and `ValFold` have been nested blocks without
one since they landed. So when `Ty` becomes nested (the wave's append) the `Ty` block loses
exactly these nine declarations: `foldMapAt_ty`, `TyMAlgebra`, `TyAlgebra.toM`,
`TyMAlgebra.map`, `TyMAlgebra.toSeq`, `foldM_ty`, `foldM_eq_cata_ty`, `foldM_id_ty`,
`foldM_natural_ty`. A consumer that needs one later adds the per-position `sequence` here first;
the plain blocks (`Eff`, `Term`, `CauseTerm`) keep theirs.
-/

open Lean Meta Elab

namespace Effect4Gen.Fold

def famLabel : Name → String
  | `Effect4.Program.Eff => "eff"
  | `Effect4.Program.Stmt => "stmt"
  | `Effect4.Program.Stmts => "stmts"
  | `Effect4.Program.Effs => "effs"
  | `Effect4.Program.ActionTerm => "action"
  | `Effect4.Program.LayerTerm => "layer"
  | `Effect4.Program.LayerTerms => "layers"
  | `Effect4.Program.Ty => "ty"
  | `Effect4.Program.Term => "term"
  | `Effect4.Program.Terms => "terms"
  | `Effect4.Program.CauseTerm => "cause"
  | n => n.componentsRev.head!.toString.toLower

def shortName (n : Name) : String := n.componentsRev.head!.toString

def srcOf (e : Expr) : MetaM String := do
  withOptions (fun o => (o.setBool `pp.fullNames true).setBool `pp.universes false) do
    return toString (← ppExpr e)

/-- The first character lowered: `ElementOf` ↦ `elementOf`, for a helper's name. -/
def lowerFirst (s : String) : String :=
  match s.toList with
  | [] => s
  | c :: rest => String.ofList (c.toLower :: rest)

/-- A name fragment for a leaf type: its last dotted component, lowered. -/
def leafHint (ty : String) : String :=
  let kept := ty.foldl (fun acc c => if c.isAlphanum || c == '.' then acc.push c else acc) ""
  let last := ((kept.splitOn ".").reverse.head? ).getD ""
  if last.isEmpty then "leaf" else lowerFirst last

/--
Where a member of the family under fold sits inside a constructor argument's type.

`leaf` names no member (the argument crosses the fold unchanged); `direct` is the argument
that *is* a member, which is the only case the generator read before this position language
existed. The four composite cases are the containers the estate's carriers actually use.
`record` is a structure with exactly one type parameter applied directly to a member.
-/
inductive Pos where
  /-- Names no member of the family; the printed type is kept for the algebra's field. -/
  | leaf (ty : String)
  /-- Is a member of the family, by the label `famLabel` gives it. -/
  | direct (fam : String)
  | list (p : Pos)
  | option (p : Pos)
  /-- A product with at least one non-`leaf` side. -/
  | prod (a b : Pos)
  /-- A one-parameter structure applied to a member: its full name, its short name, the
  parameter's position, and every field with its own position. -/
  | record (struct : String) (short : String) (arg : Pos) (fields : List (String × Pos))

instance : Inhabited Pos := ⟨.leaf ""⟩

def Pos.isLeaf : Pos → Bool
  | .leaf _ => true
  | _ => false

/-- A faithful serialization: two positions with the same key emit the same helper. -/
partial def Pos.key : Pos → String
  | .leaf ty => "L<" ++ ty ++ ">"
  | .direct f => "D<" ++ f ++ ">"
  | .list p => "List<" ++ p.key ++ ">"
  | .option p => "Option<" ++ p.key ++ ">"
  | .prod a b => "Prod<" ++ a.key ++ "," ++ b.key ++ ">"
  | .record s _ arg flds =>
    "Rec<" ++ s ++ "," ++ arg.key ++ "," ++
      String.intercalate ";" (flds.map fun f => f.1 ++ ":" ++ f.2.key) ++ ">"

/-- The helper's name suffix, derived from the position and not from a counter, so that
reordering the constructors does not rename a helper. -/
partial def Pos.suffix : Pos → String
  | .leaf ty => leafHint ty
  | .direct f => f
  | .list p => "list_" ++ p.suffix
  | .option p => "option_" ++ p.suffix
  | .prod a b => "prod_" ++ a.suffix ++ "_" ++ b.suffix
  | .record _ short arg _ => lowerFirst short ++ "_" ++ arg.suffix

/-- The same type with every member replaced by the carrier `R .x`. `paren` asks for a form
usable as the argument of an application. -/
partial def Pos.carrier : Pos → Bool → String
  | p, paren =>
    let bare := match p with
      | .leaf ty => ty
      | .direct f => s!"R .{f}"
      | .list q => s!"List {q.carrier true}"
      | .option q => s!"Option {q.carrier true}"
      | .prod a b => s!"{a.carrier true} × {b.carrier false}"
      | .record s _ arg _ => s!"{s} {arg.carrier true}"
    if paren && bare.any (· == ' ') then "(" ++ bare ++ ")" else bare

/-- The type as the carrier reads it, with every member spelled by `famType`. -/
partial def Pos.source (famType : String → String) : Pos → Bool → String
  | p, paren =>
    let bare := match p with
      | .leaf ty => ty
      | .direct f => famType f
      | .list q => s!"List {q.source famType true}"
      | .option q => s!"Option {q.source famType true}"
      | .prod a b => s!"{a.source famType true} × {b.source famType false}"
      | .record s _ arg _ => s!"{s} {arg.source famType true}"
    if paren && bare.any (· == ' ') then "(" ++ bare ++ ")" else bare

def parenArg (s : String) : String := if s.any (· == ' ') then "(" ++ s ++ ")" else s

/-- The container's own map of `fn`, as a function. `none` at a leaf (nothing to map). -/
partial def Pos.mapFn (fn : String → String) : Pos → Option String
  | .leaf _ => none
  | .direct f => some (fn f)
  | .list q => (q.mapFn fn).map fun g => s!"List.map {parenArg g}"
  | .option q => (q.mapFn fn).map fun g => s!"Option.map {parenArg g}"
  | .prod a b =>
    match a.mapFn fn, b.mapFn fn with
    | none, some g => some s!"prodMapSnd {parenArg g}"
    | some g, none => some s!"prodMapFst {parenArg g}"
    | some ga, some gb => some s!"prodMapBoth {parenArg ga} {parenArg gb}"
    | none, none => none
  | .record s _ arg _ => (arg.mapFn fn).map fun g => s!"{s}.map {parenArg g}"

def Pos.mapFn! (fn : String → String) (p : Pos) : String :=
  (p.mapFn fn).getD "«no map for a leaf position»"

/-- The container's own map of `fn` applied to `arg`, in the dot form the equations use.
Bare: `Pos.appliedArg` is the form to pass as an argument. -/
def Pos.applied (fn : String → String) (p : Pos) (arg : String) : String :=
  match p with
  | .leaf _ => arg
  | .direct f => s!"{fn f} {arg}"
  | .list q => s!"{arg}.map {parenArg (q.mapFn! fn)}"
  | .option q => s!"{arg}.map {parenArg (q.mapFn! fn)}"
  | .record _ _ a _ => s!"{arg}.map {parenArg (a.mapFn! fn)}"
  | .prod _ _ => s!"{p.mapFn! fn} {arg}"

/-- The same, parenthesized where an application would otherwise split it. -/
def Pos.appliedArg (fn : String → String) (p : Pos) (arg : String) : String :=
  parenArg (p.applied fn arg)

/-- Every composite position inside this one, children before parents, itself last. -/
partial def Pos.composites : Pos → List Pos
  | .leaf _ => []
  | .direct _ => []
  | .list q => q.composites ++ [.list q]
  | .option q => q.composites ++ [.option q]
  | .prod a b => a.composites ++ b.composites ++ [.prod a b]
  | .record s sh arg flds =>
    arg.composites ++ flds.foldl (fun acc f => acc ++ f.2.composites) [] ++
      [.record s sh arg flds]

/-- The immediate children of a composite position, each with the binder the emitted match
gives it. A leaf child keeps its binder and is copied across. -/
def Pos.childBinders : Pos → List (String × Pos)
  | .leaf _ => []
  | .direct _ => []
  | .list q => [("x", q)]
  | .option q => [("y", q)]
  | .prod a b => [("u", a), ("v", b)]
  | .record _ _ _ flds => flds

structure Arg where
  name : String
  pos : Pos
  tyText : String
  /-- The binder's name in the constructor's declaration (`inner`, `left`, …). -/
  binder : String := ""

/-- Today's reading of an argument: the label of the member it is, when it is one. -/
def Arg.recFam (a : Arg) : Option String :=
  match a.pos with
  | .direct f => some f
  | _ => none

/-- The `do`-binder that receives a recursive argument's folded value in `foldM`: `a3 ↦ x3`. -/
def bindName (a : Arg) : String := "x" ++ a.name.drop 1

structure CtorRow where
  fam : String
  ctor : String
  field : String
  args : List Arg

/-- Does the expression name a member of the family anywhere inside it? -/
def mentionsMember (members : List Name) (e : Expr) : Bool :=
  (e.find? fun s => match s with
    | .const m _ => members.contains m
    | _ => false).isSome

/-- Binder names the emitted code uses for itself; a structure field spelled like one of
them would capture it. -/
def reservedBinders : List String :=
  ["alg", "hom", "node", "x", "xs", "y", "u", "v", "op", "unit", "R", "M", "N", "f", "p"]

/--
The position of one constructor argument.

The type is `whnfR`'d first, so an `abbrev` (`Element := ElementOf Representation`) reads
through. An argument that names a member in a way the language does not cover — an arrow, an
`Array`, a two-parameter structure, a structure applied to something other than a member —
is an error naming the constructor and the argument. That refusal is the drift guard for the
next constructor someone adds: it can never be read as a leaf by accident.
-/
partial def posOf (members : List Name) (ctor arg : String) (ty : Expr) : MetaM Pos := do
  let txt ← srcOf ty
  let refuse (why : String) : MetaM Unit := do
    throwError "{ctor}.{arg} : {txt} — {why}. The fold generator's position language covers \
a member, a `List`, an `Option`, a product, and a one-parameter structure applied to a \
member. Extend `Effect4Gen.Fold.posOf` (and the emission for the new case) rather than \
reading this argument as a leaf."
  let ty' ← whnfR ty
  let head := ty'.getAppFn
  let as := ty'.getAppArgs
  match head with
  | .const n us =>
    if members.contains n then return .direct (famLabel n)
    if n == ``List && as.size == 1 then
      let p ← posOf members ctor arg as[0]!
      return if p.isLeaf then .leaf txt else .list p
    if n == ``Option && as.size == 1 then
      let p ← posOf members ctor arg as[0]!
      return if p.isLeaf then .leaf txt else .option p
    if n == ``Prod && as.size == 2 then
      let a ← posOf members ctor arg as[0]!
      let b ← posOf members ctor arg as[1]!
      return if a.isLeaf && b.isLeaf then .leaf txt else .prod a b
    let env ← getEnv
    if isStructure env n && as.size == 1 && mentionsMember members ty' then
      let iv ← getConstInfoInduct n
      unless iv.numParams == 1 do
        refuse s!"`{n}` takes {iv.numParams} parameters; only a one-parameter structure is read"
      let argPos ← posOf members ctor arg as[0]!
      if argPos.isLeaf then return .leaf txt
      unless (match argPos with | .direct _ => true | _ => false) do
        refuse s!"`{n}` is applied to a composite type; only a structure applied directly to \
a member is read (its functor map would not be the parameter's)"
      -- The emitted equations are stated with the structure's own functor map. When the
      -- structure already carries a `map`, the generator cannot check that it *is* the
      -- functor map, so it refuses rather than trusting the name. `Array` is refused here:
      -- it is a one-parameter structure with a `map` of its own, and folding through its
      -- `toList` field is not what anyone asking for an `Array` child means.
      if env.contains (Name.str n "map") then
        refuse s!"`{n}` already carries a `{n}.map`; the generator states its equations with \
the structure's functor map and cannot check that an existing one is it"
      let cval := getStructureCtor env n
      let fields := getStructureFields env n
      unless fields.size == cval.numFields do
        refuse s!"`{n}` has {fields.size} fields and {cval.numFields} constructor arguments"
      let cinfo ← getConstInfo cval.name
      let ctorTy ← instantiateForall (cinfo.instantiateTypeLevelParams us) #[as[0]!]
      let flds ← forallBoundedTelescope ctorTy cval.numFields fun xs _ => do
        let mut acc : List (String × Pos) := []
        let mut i := 0
        for x in xs do
          let fname := fields[i]!.toString
          if reservedBinders.contains fname then
            refuse s!"`{n}.{fname}` is spelled like a binder the emitted code uses"
          let fieldTy ← inferType x
          if ← Meta.isProp fieldTy then
            refuse s!"`{n}.{fname}` is a proof field; only plain data is rebuilt"
          if (fieldTy.find? fun e =>
              e.isFVar && xs.any (fun y => y.isFVar && y.fvarId! == e.fvarId!)).isSome then
            refuse s!"`{n}.{fname}` depends on another field; only a non-dependent \
structure is rebuilt"
          let p ← posOf members ctor arg fieldTy
          acc := acc ++ [(fname, p)]
          i := i + 1
        return acc
      return .record n.toString (shortName n) argPos flds
    if mentionsMember members ty' then refuse "the type names a member of the family"
    return .leaf txt
  | _ =>
    if mentionsMember members ty' then refuse "the type names a member of the family"
    return .leaf txt

def readBlock (root : Name) : MetaM (Bool × String × List (String × Name × List CtorRow)) := do
  let iv ← getConstInfoInduct root
  let members := iv.all
  let isParam := iv.numParams > 0
  let blockName := match root with
    | `Effect4.Program.Eff => "Eff"
    | `Effect4.Program.Ty => "Ty"
    | `Effect4.Program.Term => "Term"
    | `Effect4.Program.CauseTerm => "CauseTerm"
    | n => shortName n
  let mut out := []
  for fam in members do
    let fv ← getConstInfoInduct fam
    let label := famLabel fam
    let mut rows := []
    for c in fv.ctors do
      let ci ← getConstInfoCtor c
      let args ← forallBoundedTelescope ci.type (ci.numParams + ci.numFields) fun xs _ => do
        let mut acc := []
        let mut i := 0
        for x in xs[ci.numParams:] do
          let ty ← inferType x
          let pos ← posOf members (shortName c) s!"a{i}" ty
          acc := acc ++ [({ name := s!"a{i}", pos, tyText := ← srcOf ty,
                            binder := (← x.fvarId!.getUserName).toString } : Arg)]
          i := i + 1
        return acc
      rows := rows ++ [({ fam := label, ctor := shortName c,
                          field := s!"{label}_{shortName c}", args } : CtorRow)]
    out := out ++ [(label, fam, rows)]
  return (isParam, blockName, out)

/-- Does any constructor of the block hold a member under a container? -/
def blockNested (block : List (String × Name × List CtorRow)) : Bool :=
  block.any fun (_, _, rows) => rows.any fun r =>
    r.args.any fun a => match a.pos with
      | .leaf _ => false
      | .direct _ => false
      | _ => true

def recComb (calls : List String) : String :=
  match calls with
  | [] => ""
  | [c] => c
  | c :: rest => s!"op {c} ({recComb rest})"

def emitBlock (root : Name) : MetaM (String × List String) := do
  let (isParam, blockName, block) ← readBlock root
  let labels := block.map (·.1)
  let famType := s!"{blockName}Fam"
  let algType := s!"{blockName}Algebra"
  let homType := s!"{blockName}Hom"
  let opParam := if isParam then "(Op : Type) " else ""
  let opArg := if isParam then "{Op : Type} " else ""
  let opApp := if isParam then " Op" else ""
  let mut s := ""
  s := s ++ s!"inductive {famType} where\n"
  for l in labels do s := s ++ s!"  | {l}\n"
  s := s ++ "deriving DecidableEq, Repr\n\n"

  s := s ++ s!"structure {algType} {opParam}(R : {famType} → Type u) where\n"
  for (label, _, rows) in block do
    for r in rows do
      let argTexts := r.args.map fun a =>
        match a.recFam with
        | some f => s!"R .{f}"
        | none => s!"({a.tyText})"
      let arrow := String.intercalate " → " (argTexts ++ [s!"R .{label}"])
      s := s ++ s!"  {r.field} : {arrow}\n"
  s := s ++ "\n"

  let isMutual := block.length > 1
  if isMutual then s := s ++ "mutual\n"
  for (label, fam, rows) in block do
    s := s ++ s!"def cata_{label} {opArg}\{R : {famType} → Type u} (alg : {algType}{opApp} R)\n"
    s := s ++ s!"    (node : {fam}{opApp}) : R .{label} :=\n"
    s := s ++ "  match node with\n"
    for r in rows do
      let pat := if r.args.isEmpty then s!"  | .{r.ctor} =>"
        else s!"  | .{r.ctor} " ++ String.intercalate " " (r.args.map (·.name)) ++ " =>"
      let callArgs := r.args.map fun a =>
        match a.recFam with
        | some f => s!"(cata_{f} alg {a.name})"
        | none => a.name
      s := s ++ pat ++ s!" alg.{r.field}"
      for c in callArgs do s := s ++ " " ++ c
      s := s ++ "\n"
    s := s ++ "termination_by structural node\n"
  if isMutual then s := s ++ "end\n\n" else s := s ++ "\n"

  s := s ++ s!"structure {homType} {opArg}\{R : {famType} → Type u} (alg : {algType}{opApp} R) where\n"
  for (label, fam, _) in block do
    s := s ++ s!"  f_{label} : {fam}{opApp} → R .{label}\n"
  for (label, _, rows) in block do
    for r in rows do
      let binders := String.intercalate " " (r.args.map (·.name))
      let lhsArgs := if r.args.isEmpty then "" else " " ++ binders
      let rhsArgs := String.intercalate " " (r.args.map fun a =>
        match a.recFam with
        | some f => s!"(f_{f} {a.name})"
        | none => a.name)
      let rhsArgs := if rhsArgs.isEmpty then "" else " " ++ rhsArgs
      let quant := if r.args.isEmpty then "" else s!"∀ {binders}, "
      s := s ++ s!"  h_{r.field} : {quant}f_{label} (.{r.ctor}{lhsArgs}) = alg.{r.field}{rhsArgs}\n"
  s := s ++ "\n"

  let mut receipts := []
  if isMutual then s := s ++ "mutual\n"
  for (label, fam, rows) in block do
    s := s ++ s!"theorem hom_eq_cata_{label} {opArg}\{R : {famType} → Type u}\n"
    s := s ++ s!"    \{alg : {algType}{opApp} R} (hom : {homType} alg) (node : {fam}{opApp}) :\n"
    s := s ++ s!"    hom.f_{label} node = cata_{label} alg node := by\n"
    s := s ++ "  match node with\n"
    for r in rows do
      let binders := String.intercalate " " (r.args.map (·.name))
      let pat := if r.args.isEmpty then s!"  | .{r.ctor} =>" else s!"  | .{r.ctor} {binders} =>"
      let rewrites := (r.args.filterMap fun a =>
        a.recFam.map fun f => s!"hom_eq_cata_{f} hom {a.name}")
      let rwList := String.intercalate ", " ((s!"hom.h_{r.field}" ++
        (if r.args.isEmpty then "" else " " ++ binders)) :: rewrites)
      s := s ++ pat ++ s!"\n    simp only [cata_{label}, {rwList}]\n"
    s := s ++ "termination_by structural node\n"
    receipts := receipts ++ [s!"hom_eq_cata_{label}"]
  if isMutual then s := s ++ "end\n\n" else s := s ++ "\n"

  -- The self carrier and the identity algebra: the fold that rebuilds the tree. A rewrite
  -- is one override of it (`onRef`, and `frontierMap` on the frontier), and `cata_id_*`
  -- says the identity algebra folds to the identity.
  s := s ++ s!"abbrev {blockName}SelfCarrier {opParam}: {famType} → Type\n"
  for (label, fam, _) in block do
    s := s ++ s!"  | .{label} => {fam}{opApp}\n"
  s := s ++ "\n"
  s := s ++ s!"def {algType}.id {opParam}: {algType}{opApp} ({blockName}SelfCarrier{opApp}) where\n"
  for (_, fam, rows) in block do
    for r in rows do
      let binders := String.intercalate " " (r.args.map (·.name))
      let lhs := if r.args.isEmpty then "" else " " ++ binders
      s := s ++ s!"  {r.field}{lhs} := {fam}.{r.ctor}{lhs}\n"
  s := s ++ "\n"
  if isMutual then s := s ++ "mutual\n"
  for (label, fam, rows) in block do
    s := s ++ s!"@[simp] theorem cata_id_{label} {opArg}(node : {fam}{opApp}) :\n"
    s := s ++ s!"    cata_{label} ({algType}.id{opApp}) node = node := by\n"
    s := s ++ "  match node with\n"
    for r in rows do
      let binders := String.intercalate " " (r.args.map (·.name))
      let pat := if r.args.isEmpty then s!"  | .{r.ctor} =>" else s!"  | .{r.ctor} {binders} =>"
      let ihs := r.args.filterMap fun a => a.recFam.map fun f => s!"cata_id_{f} {a.name}"
      let lemmas := String.intercalate ", " ([s!"cata_{label}"] ++ ihs)
      s := s ++ pat ++ s!"\n    simp only [{lemmas}]\n    rfl\n"
    s := s ++ "termination_by structural node\n"
    receipts := receipts ++ [s!"cata_id_{label}"]
  if isMutual then s := s ++ "end\n\n" else s := s ++ "\n"

  if blockName == "Eff" then
    s := s ++ "/-- The identity algebra with the reference slot replaced: every `LayerTerm.ref` rewritten\n"
    s := s ++ "by one fold, everything else rebuilt as it was. -/\n"
    s := s ++ "def EffAlgebra.onRef {Op : Type} (f : List Nat → Effect4.Program.LayerTerm Op) :\n"
    s := s ++ "    EffAlgebra Op (EffSelfCarrier Op) :=\n  { EffAlgebra.id Op with layer_ref := f }\n\n"

  -- The path fold: `foldMap` with the node's path threaded to every child, child `i` at
  -- `p ++ [i]` in the order the recursive arguments are declared (`Node.child`'s index).
  let fAtParams := String.intercalate " " (block.map fun (l, f, _) =>
    s!"(f_{l} : {f}{opApp} → List Nat → M := fun _ _ => unit)")
  let fAtArgs := String.intercalate " " (block.map fun (l, _, _) => s!"f_{l}")
  if isMutual then s := s ++ "mutual\n"
  for (label, fam, rows) in block do
    s := s ++ s!"def foldMapAt_{label} {opArg}\{M : Type u} (unit : M) (op : M → M → M) (p : List Nat) (node : {fam}{opApp})\n"
    s := s ++ s!"    {fAtParams} : M :=\n"
    s := s ++ "  match node with\n"
    for r in rows do
      let binders := String.intercalate " " (r.args.map (·.name))
      let pat := if r.args.isEmpty then s!"  | .{r.ctor} =>" else s!"  | .{r.ctor} {binders} =>"
      let recArgs := r.args.filter (·.recFam.isSome)
      let childCalls := recArgs.zipIdx.map fun (a, i) =>
        s!"(foldMapAt_{a.recFam.getD label} unit op (p ++ [{i}]) {a.name} {fAtArgs})"
      let nodeExpr := if binders.isEmpty then s!".{r.ctor}" else s!".{r.ctor} {binders}"
      let rhs := match childCalls with
        | [] => s!"f_{label} ({nodeExpr}) p"
        | _ => s!"op (f_{label} ({nodeExpr}) p) ({recComb childCalls})"
      s := s ++ pat ++ s!"\n    {rhs}\n"
    s := s ++ "termination_by structural node\n"
  if isMutual then s := s ++ "end\n\n" else s := s ++ "\n"

  -- foldMap
  let fParams := String.intercalate " " (block.map fun (l, f, _) =>
    s!"(f_{l} : {f}{opApp} → M := fun _ => unit)")
  let fArgs := String.intercalate " " (block.map fun (l, _, _) => s!"f_{l}")
  if isMutual then s := s ++ "mutual\n"
  for (label, fam, rows) in block do
    s := s ++ s!"def foldMap_{label} {opArg}\{M : Type u} (unit : M) (op : M → M → M) (node : {fam}{opApp})\n"
    s := s ++ s!"    {fParams} : M :=\n"
    s := s ++ "  match node with\n"
    for r in rows do
      let binders := String.intercalate " " (r.args.map (·.name))
      let pat := if r.args.isEmpty then s!"  | .{r.ctor} =>" else s!"  | .{r.ctor} {binders} =>"
      let childCalls := r.args.filterMap fun a =>
        a.recFam.map fun f => s!"(foldMap_{f} unit op {a.name} {fArgs})"
      let nodeExpr := if binders.isEmpty then s!".{r.ctor}" else s!".{r.ctor} {binders}"
      let rhs := match childCalls with
        | [] => s!"f_{label} ({nodeExpr})"
        | _ => s!"op (f_{label} ({nodeExpr})) ({recComb childCalls})"
      s := s ++ pat ++ s!"\n    {rhs}\n"
    s := s ++ "termination_by structural node\n"
  if isMutual then s := s ++ "end\n\n" else s := s ++ "\n"

  -- The Kleisli algebra: the same slots, each returning in `M`. A recursive argument
  -- arrives already folded; a non-recursive one arrives as itself.
  let malgType := s!"{blockName}MAlgebra"
  s := s ++ s!"structure {malgType} {opParam}(M : Type u → Type v) (R : {famType} → Type u) where\n"
  for (label, _, rows) in block do
    for r in rows do
      let argTexts := r.args.map fun a =>
        match a.recFam with
        | some f => s!"R .{f}"
        | none => s!"({a.tyText})"
      let arrow := String.intercalate " → " (argTexts ++ [s!"M (R .{label})"])
      s := s ++ s!"  {r.field} : {arrow}\n"
  s := s ++ "\n"

  s := s ++ s!"def {algType}.toM {opArg}\{M : Type u → Type v} [Monad M] \{R : {famType} → Type u}\n"
  s := s ++ s!"    (alg : {algType}{opApp} R) : {malgType}{opApp} M R where\n"
  for (_, _, rows) in block do
    for r in rows do
      let binders := String.intercalate " " (r.args.map (·.name))
      let lhs := if r.args.isEmpty then "" else " " ++ binders
      let rhs := if r.args.isEmpty then s!"pure alg.{r.field}"
        else s!"pure (alg.{r.field} {binders})"
      s := s ++ s!"  {r.field}{lhs} := {rhs}\n"
  s := s ++ "\n"

  s := s ++ s!"def {malgType}.map {opArg}\{M : Type u → Type v} \{N : Type u → Type w}\n"
  s := s ++ s!"    \{R : {famType} → Type u} (φ : ∀ \{α}, M α → N α)\n"
  s := s ++ s!"    (alg : {malgType}{opApp} M R) : {malgType}{opApp} N R where\n"
  for (_, _, rows) in block do
    for r in rows do
      let binders := String.intercalate " " (r.args.map (·.name))
      let lhs := if r.args.isEmpty then "" else " " ++ binders
      let rhs := if r.args.isEmpty then s!"φ alg.{r.field}"
        else s!"φ (alg.{r.field} {binders})"
      s := s ++ s!"  {r.field}{lhs} := {rhs}\n"
  s := s ++ "\n"

  -- The sequencing algebra: a plain algebra on the carrier `fun f => M (R f)`, whose
  -- slots bind their already-monadic children in declaration order before applying.
  s := s ++ s!"def {malgType}.toSeq {opArg}\{M : Type u → Type v} [Monad M]\n"
  s := s ++ s!"    \{R : {famType} → Type u} (alg : {malgType}{opApp} M R) :\n"
  s := s ++ s!"    {algType}{opApp} (fun f => M (R f)) where\n"
  for (_, _, rows) in block do
    for r in rows do
      let binders := String.intercalate " " (r.args.map (·.name))
      let lhs := if r.args.isEmpty then "" else " " ++ binders
      let recArgs := r.args.filter (·.recFam.isSome)
      let callArgs := String.intercalate " " (r.args.map fun a =>
        match a.recFam with
        | some _ => bindName a
        | none => a.name)
      let apply := if r.args.isEmpty then s!"alg.{r.field}" else s!"alg.{r.field} {callArgs}"
      if recArgs.isEmpty then
        s := s ++ s!"  {r.field}{lhs} := {apply}\n"
      else
        s := s ++ s!"  {r.field}{lhs} := do\n"
        for a in recArgs do s := s ++ s!"    let {bindName a} ← {a.name}\n"
        s := s ++ s!"    {apply}\n"
  s := s ++ "\n"

  if isMutual then s := s ++ "mutual\n"
  for (label, fam, rows) in block do
    s := s ++ s!"def foldM_{label} {opArg}\{M : Type u → Type v} [Monad M] \{R : {famType} → Type u}\n"
    s := s ++ s!"    (alg : {malgType}{opApp} M R) (node : {fam}{opApp}) : M (R .{label}) :=\n"
    s := s ++ "  match node with\n"
    for r in rows do
      let binders := String.intercalate " " (r.args.map (·.name))
      let pat := if r.args.isEmpty then s!"  | .{r.ctor} =>" else s!"  | .{r.ctor} {binders} =>"
      let recArgs := r.args.filter (·.recFam.isSome)
      let callArgs := String.intercalate " " (r.args.map fun a =>
        match a.recFam with
        | some _ => bindName a
        | none => a.name)
      let apply := if r.args.isEmpty then s!"alg.{r.field}" else s!"alg.{r.field} {callArgs}"
      if recArgs.isEmpty then
        s := s ++ s!"{pat} {apply}\n"
      else
        s := s ++ s!"{pat} do\n"
        for a in recArgs do
          s := s ++ s!"      let {bindName a} ← foldM_{a.recFam.getD label} alg {a.name}\n"
        s := s ++ s!"      {apply}\n"
    s := s ++ "termination_by structural node\n"
  if isMutual then s := s ++ "end\n\n" else s := s ++ "\n"

  if isMutual then s := s ++ "mutual\n"
  for (label, fam, rows) in block do
    s := s ++ s!"theorem foldM_eq_cata_{label} {opArg}\{M : Type u → Type v} [Monad M]\n"
    s := s ++ s!"    \{R : {famType} → Type u} (alg : {malgType}{opApp} M R) (node : {fam}{opApp}) :\n"
    s := s ++ s!"    foldM_{label} alg node = cata_{label} alg.toSeq node := by\n"
    s := s ++ "  match node with\n"
    for r in rows do
      let binders := String.intercalate " " (r.args.map (·.name))
      let pat := if r.args.isEmpty then s!"  | .{r.ctor} =>" else s!"  | .{r.ctor} {binders} =>"
      let ihs := r.args.filterMap fun a =>
        a.recFam.map fun f => s!"foldM_eq_cata_{f} alg {a.name}"
      let lemmas := String.intercalate ", "
        ([s!"foldM_{label}", s!"cata_{label}", s!"{malgType}.toSeq"] ++ ihs)
      s := s ++ pat ++ s!"\n    simp only [{lemmas}]\n"
    s := s ++ "termination_by structural node\n"
    receipts := receipts ++ [s!"foldM_eq_cata_{label}"]
  if isMutual then s := s ++ "end\n\n" else s := s ++ "\n"

  -- In the identity monad the monadic fold is the plain fold. The induction is
  -- `foldM_eq_cata_*`'s; what is left is `(alg.toM).toSeq = alg`, which is `rfl`.
  for (label, fam, _) in block do
    s := s ++ s!"theorem foldM_id_{label} {opArg}\{R : {famType} → Type u} (alg : {algType}{opApp} R)\n"
    s := s ++ s!"    (node : {fam}{opApp}) :\n"
    s := s ++ s!"    foldM_{label} (M := Id) alg.toM node = cata_{label} alg node := by\n"
    s := s ++ s!"  rw [foldM_eq_cata_{label}]\n"
    s := s ++ "  rfl\n\n"
    receipts := receipts ++ [s!"foldM_id_{label}"]

  if isMutual then s := s ++ "mutual\n"
  for (label, fam, rows) in block do
    s := s ++ s!"theorem foldM_natural_{label} {opArg}\{M : Type u → Type v} \{N : Type u → Type w}\n"
    s := s ++ s!"    [Monad M] [Monad N] \{R : {famType} → Type u} (φ : MonadMorphism M N)\n"
    s := s ++ s!"    (alg : {malgType}{opApp} M R) (node : {fam}{opApp}) :\n"
    s := s ++ s!"    φ.toFun (foldM_{label} alg node) = foldM_{label} (alg.map φ.toFun) node := by\n"
    s := s ++ "  match node with\n"
    for r in rows do
      let binders := String.intercalate " " (r.args.map (·.name))
      let pat := if r.args.isEmpty then s!"  | .{r.ctor} =>" else s!"  | .{r.ctor} {binders} =>"
      let ihs := r.args.filterMap fun a =>
        a.recFam.map fun f => s!"foldM_natural_{f} φ alg {a.name}"
      let bindLemma := if ihs.isEmpty then [] else ["φ.map_bind"]
      let lemmas := String.intercalate ", "
        ([s!"foldM_{label}", s!"{malgType}.map"] ++ bindLemma ++ ihs)
      s := s ++ pat ++ s!"\n    simp only [{lemmas}]\n"
    s := s ++ "termination_by structural node\n"
    receipts := receipts ++ [s!"foldM_natural_{label}"]
  if isMutual then s := s ++ "end\n\n" else s := s ++ "\n"

  return (s, receipts)

/-! ## A block whose children sit under containers

The emission for a family with a composite position. It differs from the plain one above in
four ways, all forced by the nesting: one structurally recursive helper per distinct
composite position inside the family's one mutual block; a helper-is-the-container's-map
lemma per helper; a public constructor equation per constructor, stated with the containers'
maps (what a consumer's proofs rewrite with); and no monadic half, because a `foldM` over a
nested position needs a `sequence` per position type and has no consumer on these carriers
(the ready packet, §2.8).
-/

namespace Nested

/-- The name a composite position's fold helper carries. -/
def cataName (p : Pos) : String := s!"cata_pos_{p.suffix}"

/-- The folded child at binder `v`: the member's fold, a helper, or the binder itself. -/
def child (p : Pos) (v : String) : String :=
  match p with
  | .leaf _ => v
  | .direct f => s!"cata_{f} alg {v}"
  | _ => s!"{cataName p} alg {v}"

/-- The rewrite that turns a child's map form into its helper, for the `Hom` proofs. -/
def homChild (p : Pos) (v : String) : Option String :=
  match p with
  | .leaf _ => none
  | .direct f => some s!"hom_eq_cata_{f} hom {v}"
  | _ => some s!"hom_pos_{p.suffix} hom {v}"

/-- The rewrite that says a child of the identity fold is itself. -/
def idChild (p : Pos) (v : String) : Option String :=
  match p with
  | .leaf _ => none
  | .direct f => some s!"cata_id_{f} {v}"
  | _ => some s!"cata_id_pos_{p.suffix} {v}"

/-- The `_eq` lemma of a child, when the child is itself composite. -/
def childEq (p : Pos) : Option String :=
  match p with
  | .leaf _ => none
  | .direct _ => none
  | _ => some s!"{cataName p}_eq"

/-- The pair-literal equation a product's proofs rewrite with. Never the definition of the
product map itself: unfolding it opens an inner application on a variable before the
induction hypothesis can reach it (the ready packet, §2.3). -/
def prodLemma (a b : Pos) : String :=
  if a.isLeaf then "prodMapSnd_mk" else if b.isLeaf then "prodMapFst_mk" else "prodMapBoth_mk"

/-- The lemma that opens a composite position's own container. -/
def openLemma : Pos → List String
  | .record s _ _ _ => [s!"{s}.map"]
  | .prod a b => [prodLemma a b]
  | _ => []

/-- The rewrites that fuse two maps at a position, for a record's own composition law.
`none` when the position holds a product: the product maps' fusion is not stated here. -/
partial def fuseLemmas : Pos → Option (List String)
  | .leaf _ => some []
  | .direct _ => some []
  | .list q => (fuseLemmas q).map fun ls => "List.map_map" :: ls
  | .option q => (fuseLemmas q).map fun ls => "Option.map_map" :: ls
  | .record s _ _ flds =>
    flds.foldl (fun acc f =>
      match acc, fuseLemmas f.2 with
      | some a, some b => some (a ++ b)
      | _, _ => none) (some [s!"{s}.map_map"])
  | .prod _ _ => none

/-- The rewrites that erase a map at the identity at a position, for a record's own identity
law: each container's lemma in its function form — `List.map (fun a => a) = id` directly under
the record, `List.map id = id` under another container whose own rewrite has already left
`id`. `none` when the position holds a product, as for `fuseLemmas`. -/
partial def idLemmas : Pos → Option (List String)
  | .leaf _ => some []
  | .direct _ => some []
  | .list q => (idLemmas q).map fun ls =>
    (if q matches .direct _ then "List.map_id_fun'" else "List.map_id_fun") :: ls
  | .option q => (idLemmas q).map fun ls =>
    (if q matches .direct _ then "Option.map_id_fun'" else "Option.map_id_fun") :: ls
  | .record s _ _ flds =>
    flds.foldl (fun acc f =>
      match acc, idLemmas f.2 with
      | some a, some b => some (a ++ b)
      | _, _ => none) (some [s!"{s}.map_id"])
  | .prod _ _ => none

/-- The binder the emitted match gives a composite position's scrutinee. -/
def scrutinee : Pos → String
  | .list _ => "xs"
  | _ => "x"

/-- One arm of a composite position's match, given a way to build each child. -/
def arms (p : Pos) (build : Pos → String → String) : List (String × String) :=
  match p with
  | .list q => [("[]", "[]"), ("x :: rest", s!"{build q "x"} :: {cataName p} alg rest")]
  | .option q => [("none", "none"), ("some y", s!"some ({build q "y"})")]
  | .prod a b => [("(u, v)", s!"({build a "u"}, {build b "v"})")]
  | .record _ _ _ flds =>
    let pat := "⟨" ++ String.intercalate ", " (flds.map (·.1)) ++ "⟩"
    let rhs := "⟨" ++ String.intercalate ", " (flds.map fun f => build f.2 f.1) ++ "⟩"
    [(pat, rhs)]
  | _ => []

end Nested

open Nested in
def emitNestedBlock (ns : Name) (root : Name) (emittedIn : List String) :
    MetaM (String × List String × List String) := do
  let (isParam, blockName, block) ← readBlock root
  let labels := block.map (·.1)
  let famType := s!"{blockName}Fam"
  let algType := s!"{blockName}Algebra"
  let homType := s!"{blockName}Hom"
  let opParam := if isParam then "(Op : Type) " else ""
  let opArg := if isParam then "{Op : Type} " else ""
  let opApp := if isParam then " Op" else ""
  let famSrc : String → String := fun l =>
    match block.find? (fun b => b.1 == l) with
    | some (_, fam, _) => s!"{fam.toString}{opApp}"
    | none => l
  let src : Pos → String := fun p => p.source famSrc false
  let cataFn : String → String := fun f => s!"cata_{f} alg"
  let homFn : String → String := fun f => s!"hom.f_{f}"

  -- Every distinct composite position of the family, children before parents.
  let mut comps : List Pos := []
  let mut seenKeys : List String := []
  for (_, _, rows) in block do
    for r in rows do
      for a in r.args do
        for c in a.pos.composites do
          unless seenKeys.contains c.key do
            seenKeys := seenKeys ++ [c.key]
            comps := comps ++ [c]
  -- Two distinct positions that would take the same helper name is a generator bug, not a
  -- Lean error to discover later.
  for p in comps do
    for q in comps do
      if p.key != q.key && p.suffix == q.suffix then
        throwError "the fold generator derives one helper name `{p.suffix}` for two \
positions: {p.key} and {q.key}"

  let mut s := ""
  s := s ++ s!"inductive {famType} where\n"
  for l in labels do s := s ++ s!"  | {l}\n"
  s := s ++ "deriving DecidableEq, Repr\n\n"

  s := s ++ s!"structure {algType} {opParam}(R : {famType} → Type u) where\n"
  for (label, _, rows) in block do
    for r in rows do
      let argTexts := r.args.map fun a =>
        match a.pos with
        | .leaf ty => s!"({ty})"
        | p => p.carrier false
      let arrow := String.intercalate " → " (argTexts ++ [s!"R .{label}"])
      s := s ++ s!"  {r.field} : {arrow}\n"
  s := s ++ "\n"

  -- The containers' functor maps. `List`, `Option` and the products' are the ones the
  -- public equations are stated with; a one-parameter record that has no `map` gets one
  -- here, once per file.
  let mut emitted := emittedIn
  let mut receiptsAux : List String := []
  for p in comps do
    match p with
    | .record st _ _ flds =>
      let mapName := st ++ ".map"
      unless emitted.contains mapName || (← getEnv).contains (Name.str st.toName "map") do
        emitted := emitted ++ [mapName]
        s := s ++ s!"/-- The functor map of `{st}`, which the structure itself does not carry. -/\n"
        s := s ++ s!"def _root_.{mapName} \{α : Type u} \{β : Type v} (f : α → β)\n"
        s := s ++ s!"    (x : {st} α) : {st} β :=\n"
        let fieldTexts := flds.map fun fld =>
          s!"{fld.1} := {fld.2.applied (fun _ => "f") s!"x.{fld.1}"}"
        s := s ++ "  { " ++ String.intercalate "\n    " fieldTexts ++ " }\n\n"
        -- The functor's composition law. A consumer that folds twice meets
        -- `map g (map f x)` on one side and `map (g ∘ f) x` on the other, and neither
        -- reduces to the other under a `List.map` where the map is not applied.
        let fuse := (flds.foldl (fun acc f =>
          match acc, fuseLemmas f.2 with
          | some a, some b => some (a ++ b)
          | _, _ => none) (some [])).map (·.eraseDups)
        match fuse with
        | none => pure ()
        | some ls =>
          let lemmas := String.intercalate ", "
            ([mapName] ++ ls ++ (if ls.isEmpty then [] else ["Function.comp_def"]))
          s := s ++ s!"/-- Two maps of `{st}` fuse into one. -/\n"
          s := s ++ s!"theorem _root_.{st}.map_map \{α : Type u} \{β : Type v} \{γ : Type w}\n"
          s := s ++ s!"    (g : β → γ) (f : α → β) (x : {st} α) :\n"
          s := s ++ s!"    {mapName} g ({mapName} f x) = {mapName} (fun a => g (f a)) x := by\n"
          s := s ++ "  cases x\n"
          s := s ++ s!"  simp only [{lemmas}]\n\n"
          receiptsAux := receiptsAux ++ [s!"{st}.map_map"]
        -- The functor's identity law, the other half of what a paired fold reads its values
        -- back through (`fold_of`'s container paramorphism meets
        -- `map Prod.fst (map (fun e => (e, f e)) x)` and needs it to be `x`).
        let ident := (flds.foldl (fun acc f =>
          match acc, idLemmas f.2 with
          | some a, some b => some (a ++ b)
          | _, _ => none) (some [])).map (·.eraseDups)
        match ident with
        | none => pure ()
        | some ls =>
          let lemmas := String.intercalate ", "
            ([mapName] ++ ls ++ (if ls.isEmpty then [] else ["id_eq"]))
          s := s ++ s!"/-- The map of `{st}` at the identity is the identity. -/\n"
          s := s ++ s!"theorem _root_.{st}.map_id \{α : Type u} (x : {st} α) :\n"
          s := s ++ s!"    {mapName} (fun a => a) x = x := by\n"
          s := s ++ "  cases x\n"
          s := s ++ s!"  simp only [{lemmas}]\n\n"
          receiptsAux := receiptsAux ++ [s!"{st}.map_id"]
    | .prod a b =>
      let (nm, sig, body, eqn) :=
        if a.isLeaf then
          ("prodMapSnd", "(f : β → γ) (x : α × β) : α × γ", "(x.1, f x.2)",
            "(f : β → γ) (a : α) (b : β) :\n    prodMapSnd f (a, b) = (a, f b)")
        else if b.isLeaf then
          ("prodMapFst", "(f : α → γ) (x : α × β) : γ × β", "(f x.1, x.2)",
            "(f : α → γ) (a : α) (b : β) :\n    prodMapFst f (a, b) = (f a, b)")
        else
          ("prodMapBoth", "(f : α → γ) (g : β → δ) (x : α × β) : γ × δ", "(f x.1, g x.2)",
            "(f : α → γ) (g : β → δ) (a : α) (b : β) :\n    prodMapBoth f g (a, b) = (f a, g b)")
      unless emitted.contains nm || (← getEnv).contains (Name.str ns nm) do
        emitted := emitted ++ [nm]
        let univs := if nm == "prodMapBoth"
          then "{α : Type u} {β : Type v} {γ : Type w} {δ : Type w}"
          else "{α : Type u} {β : Type v} {γ : Type w}"
        s := s ++ "/-- The map of a product's components. -/\n"
        s := s ++ s!"def {nm} {univs} {sig} := {body}\n\n"
        s := s ++ "/-- The only equation the proofs use: on a pair literal. Unfolding the map itself\n"
        s := s ++ "would also open an inner application on a variable, before the induction hypothesis\n"
        s := s ++ "could rewrite it. -/\n"
        s := s ++ s!"theorem {nm}_mk {univs} {eqn} := rfl\n\n"
    | _ => pure ()

  -- The fold: one function per member, one helper per composite position, all structural
  -- in one mutual block.
  s := s ++ "mutual\n"
  for (label, fam, rows) in block do
    s := s ++ s!"def cata_{label} {opArg}\{R : {famType} → Type u} (alg : {algType}{opApp} R)\n"
    s := s ++ s!"    (node : {fam}{opApp}) : R .{label} :=\n"
    s := s ++ "  match node with\n"
    for r in rows do
      let pat := if r.args.isEmpty then s!"  | .{r.ctor} =>"
        else s!"  | .{r.ctor} " ++ String.intercalate " " (r.args.map (·.name)) ++ " =>"
      let callArgs := r.args.map fun a =>
        match a.pos with
        | .leaf _ => a.name
        | p => s!"({child p a.name})"
      s := s ++ pat ++ s!" alg.{r.field}"
      for c in callArgs do s := s ++ " " ++ c
      s := s ++ "\n"
    s := s ++ "termination_by structural node\n"
  for p in comps do
    let v := scrutinee p
    s := s ++ s!"def {cataName p} {opArg}\{R : {famType} → Type u} (alg : {algType}{opApp} R)\n"
    s := s ++ s!"    ({v} : {src p}) : {p.carrier false} :=\n"
    s := s ++ s!"  match {v} with\n"
    for (pat, rhs) in arms p child do
      s := s ++ s!"  | {pat} => {rhs}\n"
    s := s ++ s!"termination_by structural {v}\n"
  s := s ++ "end\n\n"

  -- Each helper is the container's own map of the fold. These are what the public
  -- constructor equations and every consumer's proof are stated with.
  let mut receipts : List String := receiptsAux
  for p in comps do
    let v := scrutinee p
    let stmt := s!"{cataName p} alg {v} = {p.applied cataFn v}"
    s := s ++ s!"theorem {cataName p}_eq {opArg}\{R : {famType} → Type u}\n"
    s := s ++ s!"    (alg : {algType}{opApp} R) ({v} : {src p}) :\n"
    s := s ++ s!"    {stmt} := by\n"
    let inner := (p.childBinders.filterMap fun c => childEq c.2).eraseDups
    match p with
    | .list q =>
      s := s ++ s!"  induction {v} with\n"
      s := s ++ s!"  | nil => simp only [{cataName p}, List.map_nil]\n"
      let lemmas := String.intercalate ", "
        ([cataName p, "List.map_cons", "ih"] ++ (childEq q).toList)
      s := s ++ s!"  | cons x rest ih => simp only [{lemmas}]\n"
    | .option q =>
      s := s ++ s!"  cases {v} with\n"
      s := s ++ s!"  | none => simp only [{cataName p}, Option.map_none]\n"
      let lemmas := String.intercalate ", "
        ([cataName p, "Option.map_some"] ++ (childEq q).toList)
      s := s ++ s!"  | some y => simp only [{lemmas}]\n"
    | .prod a b =>
      let lemmas := String.intercalate ", " ([cataName p, prodLemma a b] ++ inner)
      s := s ++ s!"  cases {v} with\n"
      s := s ++ s!"  | mk u v => simp only [{lemmas}]\n"
    | .record st _ _ flds =>
      let binders := String.intercalate " " (flds.map (·.1))
      let lemmas := String.intercalate ", " ([cataName p, s!"{st}.map"] ++ inner)
      s := s ++ s!"  cases {v} with\n"
      s := s ++ s!"  | mk {binders} => simp only [{lemmas}]\n"
    | _ => pure ()
    s := s ++ "\n"
    receipts := receipts ++ [s!"{cataName p}_eq"]

  -- One public constructor equation per constructor, stated with the containers' maps.
  for (label, _, rows) in block do
    for r in rows do
      let binderGroups := String.join (r.args.map fun a => s!" ({a.name} : {src a.pos})")
      let lhsArgs := if r.args.isEmpty then ""
        else " " ++ String.intercalate " " (r.args.map (·.name))
      let rhsArgs := String.join (r.args.map fun a => " " ++ a.pos.appliedArg cataFn a.name)
      s := s ++ s!"@[simp] theorem cata_{label}_{r.ctor} {opArg}\{R : {famType} → Type u}\n"
      s := s ++ s!"    (alg : {algType}{opApp} R){binderGroups} :\n"
      s := s ++ s!"    cata_{label} alg (.{r.ctor}{lhsArgs}) =\n"
      s := s ++ s!"      alg.{r.field}{rhsArgs} := "
      let eqs := (r.args.filterMap fun a => childEq a.pos).eraseDups
      if eqs.isEmpty then
        s := s ++ "rfl\n\n"
      else
        let lemmas := String.intercalate ", " ([s!"cata_{label}"] ++ eqs)
        s := s ++ s!"by\n  simp only [{lemmas}]\n\n"
      receipts := receipts ++ [s!"cata_{label}_{r.ctor}"]

  -- Uniqueness: any family of functions satisfying the constructor equations is the fold.
  s := s ++ s!"structure {homType} {opArg}\{R : {famType} → Type u} (alg : {algType}{opApp} R) where\n"
  for (label, fam, _) in block do
    s := s ++ s!"  f_{label} : {fam}{opApp} → R .{label}\n"
  for (label, _, rows) in block do
    for r in rows do
      let binders := String.intercalate " " (r.args.map (·.name))
      let lhsArgs := if r.args.isEmpty then "" else " " ++ binders
      let rhsArgs := String.join (r.args.map fun a =>
        " " ++ a.pos.appliedArg (fun f => s!"f_{f}") a.name)
      let quant := if r.args.isEmpty then "" else s!"∀ {binders}, "
      s := s ++ s!"  h_{r.field} : {quant}f_{label} (.{r.ctor}{lhsArgs}) =\n"
      s := s ++ s!"    alg.{r.field}{rhsArgs}\n"
  s := s ++ "\n"

  s := s ++ "mutual\n"
  for (label, fam, rows) in block do
    s := s ++ s!"theorem hom_eq_cata_{label} {opArg}\{R : {famType} → Type u}\n"
    s := s ++ s!"    \{alg : {algType}{opApp} R} (hom : {homType} alg) (node : {fam}{opApp}) :\n"
    s := s ++ s!"    hom.f_{label} node = cata_{label} alg node := by\n"
    s := s ++ "  match node with\n"
    for r in rows do
      let binders := String.intercalate " " (r.args.map (·.name))
      let pat := if r.args.isEmpty then s!"  | .{r.ctor} =>" else s!"  | .{r.ctor} {binders} =>"
      let rewrites := r.args.filterMap fun a => homChild a.pos a.name
      let rwList := String.intercalate ", " ((s!"hom.h_{r.field}" ++
        (if r.args.isEmpty then "" else " " ++ binders)) :: rewrites)
      s := s ++ pat ++ s!"\n    simp only [cata_{label}, {rwList}]\n"
    s := s ++ "termination_by structural node\n"
    receipts := receipts ++ [s!"hom_eq_cata_{label}"]
  for p in comps do
    let v := scrutinee p
    s := s ++ s!"theorem hom_pos_{p.suffix} {opArg}\{R : {famType} → Type u}\n"
    s := s ++ s!"    \{alg : {algType}{opApp} R} (hom : {homType} alg) ({v} : {src p}) :\n"
    s := s ++ s!"    {p.applied homFn v} = {cataName p} alg {v} := by\n"
    s := s ++ s!"  match {v} with\n"
    match p with
    | .list q =>
      s := s ++ s!"  | [] => simp only [{cataName p}, List.map_nil]\n"
      let lemmas := String.intercalate ", " ([cataName p, "List.map_cons"] ++
        (homChild q "x").toList ++ [s!"hom_pos_{p.suffix} hom rest"])
      s := s ++ s!"  | x :: rest => simp only [{lemmas}]\n"
    | .option q =>
      s := s ++ s!"  | none => simp only [{cataName p}, Option.map_none]\n"
      let lemmas := String.intercalate ", " ([cataName p, "Option.map_some"] ++
        (homChild q "y").toList)
      s := s ++ s!"  | some y => simp only [{lemmas}]\n"
    | .prod a b =>
      let lemmas := String.intercalate ", " ([cataName p, prodLemma a b] ++
        (homChild a "u").toList ++ (homChild b "v").toList)
      s := s ++ s!"  | (u, v) => simp only [{lemmas}]\n"
    | .record st _ _ flds =>
      let pat := "⟨" ++ String.intercalate ", " (flds.map (·.1)) ++ "⟩"
      let lemmas := String.intercalate ", " ([cataName p, s!"{st}.map"] ++
        flds.filterMap fun f => homChild f.2 f.1)
      s := s ++ s!"  | {pat} => simp only [{lemmas}]\n"
    | _ => pure ()
    s := s ++ s!"termination_by structural {v}\n"
    receipts := receipts ++ [s!"hom_pos_{p.suffix}"]
  s := s ++ "end\n\n"

  -- The identity algebra rebuilds the tree.
  s := s ++ s!"abbrev {blockName}SelfCarrier {opParam}: {famType} → Type\n"
  for (label, fam, _) in block do
    s := s ++ s!"  | .{label} => {fam}{opApp}\n"
  s := s ++ "\n"
  s := s ++ s!"def {algType}.id {opParam}: {algType}{opApp} ({blockName}SelfCarrier{opApp}) where\n"
  for (_, fam, rows) in block do
    for r in rows do
      let binders := String.intercalate " " (r.args.map (·.name))
      let lhs := if r.args.isEmpty then "" else " " ++ binders
      s := s ++ s!"  {r.field}{lhs} := {fam}.{r.ctor}{lhs}\n"
  s := s ++ "\n"
  s := s ++ "mutual\n"
  for (label, fam, rows) in block do
    s := s ++ s!"@[simp] theorem cata_id_{label} {opArg}(node : {fam}{opApp}) :\n"
    s := s ++ s!"    cata_{label} ({algType}.id{opApp}) node = node := by\n"
    s := s ++ "  match node with\n"
    for r in rows do
      let binders := String.intercalate " " (r.args.map (·.name))
      let pat := if r.args.isEmpty then s!"  | .{r.ctor} =>" else s!"  | .{r.ctor} {binders} =>"
      let ihs := r.args.filterMap fun a => idChild a.pos a.name
      let lemmas := String.intercalate ", " ([s!"cata_{label}"] ++ ihs)
      s := s ++ pat ++ s!"\n    simp only [{lemmas}]\n    rfl\n"
    s := s ++ "termination_by structural node\n"
    receipts := receipts ++ [s!"cata_id_{label}"]
  for p in comps do
    let v := scrutinee p
    s := s ++ s!"theorem cata_id_pos_{p.suffix} {opArg}({v} : {src p}) :\n"
    s := s ++ s!"    {cataName p} ({algType}.id{opApp}) {v} = {v} := by\n"
    s := s ++ s!"  match {v} with\n"
    match p with
    | .list q =>
      s := s ++ s!"  | [] => simp only [{cataName p}]\n"
      let lemmas := String.intercalate ", " ([cataName p] ++ (idChild q "x").toList ++
        [s!"cata_id_pos_{p.suffix} rest"])
      s := s ++ s!"  | x :: rest => simp only [{lemmas}]\n"
    | .option q =>
      s := s ++ s!"  | none => simp only [{cataName p}]\n"
      let lemmas := String.intercalate ", " ([cataName p] ++ (idChild q "y").toList)
      s := s ++ s!"  | some y => simp only [{lemmas}]\n"
    | .prod a b =>
      let lemmas := String.intercalate ", " ([cataName p] ++ (idChild a "u").toList ++
        (idChild b "v").toList)
      s := s ++ s!"  | (u, v) => simp only [{lemmas}]\n"
    | .record _ _ _ flds =>
      let pat := "⟨" ++ String.intercalate ", " (flds.map (·.1)) ++ "⟩"
      let lemmas := String.intercalate ", " ([cataName p] ++
        flds.filterMap fun f => idChild f.2 f.1)
      s := s ++ s!"  | {pat} => simp only [{lemmas}]\n"
    | _ => pure ()
    s := s ++ s!"termination_by structural {v}\n"
    receipts := receipts ++ [s!"cata_id_pos_{p.suffix}"]
  s := s ++ "end\n\n"

  -- The monoid fold: one hook per sort, the children combined left to right, `unit` for an
  -- empty list or a `none`.
  let fParams := String.intercalate " " (block.map fun (l, f, _) =>
    s!"(f_{l} : {f.toString}{opApp} → M := fun _ => unit)")
  let fArgs := String.intercalate " " (block.map fun (l, _, _) => s!"f_{l}")
  let mapCall : Pos → String → String := fun p v =>
    match p with
    | .direct f => s!"(foldMap_{f} unit op {v} {fArgs})"
    | _ => s!"(foldMap_pos_{p.suffix} unit op {v} {fArgs})"
  s := s ++ "mutual\n"
  for (label, fam, rows) in block do
    s := s ++ s!"def foldMap_{label} {opArg}\{M : Type u} (unit : M) (op : M → M → M) (node : {fam}{opApp})\n"
    s := s ++ s!"    {fParams} : M :=\n"
    s := s ++ "  match node with\n"
    for r in rows do
      let binders := String.intercalate " " (r.args.map (·.name))
      let pat := if r.args.isEmpty then s!"  | .{r.ctor} =>" else s!"  | .{r.ctor} {binders} =>"
      let childCalls := r.args.filterMap fun a =>
        if a.pos.isLeaf then none else some (mapCall a.pos a.name)
      let nodeExpr := if binders.isEmpty then s!".{r.ctor}" else s!".{r.ctor} {binders}"
      let rhs := match childCalls with
        | [] => s!"f_{label} ({nodeExpr})"
        | _ => s!"op (f_{label} ({nodeExpr})) ({recComb childCalls})"
      s := s ++ pat ++ s!"\n    {rhs}\n"
    s := s ++ "termination_by structural node\n"
  for p in comps do
    let v := scrutinee p
    s := s ++ s!"def foldMap_pos_{p.suffix} {opArg}\{M : Type u} (unit : M) (op : M → M → M) ({v} : {src p})\n"
    s := s ++ s!"    {fParams} : M :=\n"
    s := s ++ s!"  match {v} with\n"
    match p with
    | .list q =>
      s := s ++ "  | [] => unit\n"
      s := s ++ s!"  | x :: rest => op {mapCall q "x"} (foldMap_pos_{p.suffix} unit op rest {fArgs})\n"
    | .option q =>
      s := s ++ "  | none => unit\n"
      s := s ++ s!"  | some y => {mapCall q "y"}\n"
    | .prod a b =>
      let l := if a.isLeaf then "_" else "u"
      let r := if b.isLeaf then "_" else "v"
      let calls := (if a.isLeaf then [] else [mapCall a "u"]) ++
        (if b.isLeaf then [] else [mapCall b "v"])
      s := s ++ s!"  | ({l}, {r}) => {recComb calls}\n"
    | .record _ _ _ flds =>
      let pat := "⟨" ++ String.intercalate ", "
        (flds.map fun f => if f.2.isLeaf then "_" else f.1) ++ "⟩"
      let calls := flds.filterMap fun f =>
        if f.2.isLeaf then none else some (mapCall f.2 f.1)
      s := s ++ s!"  | {pat} => {recComb calls}\n"
    | _ => pure ()
    s := s ++ s!"termination_by structural {v}\n"
  s := s ++ "end\n\n"

  return (s, receipts, emitted)

/-- A frontier slot under weakening at `cut`. -/
def weakenOf (tyText : String) (arg : String) : String :=
  if tyText == "Effect4.Program.Term" then s!"(Effect4.Program.Term.weaken cut {arg})"
  else if tyText == "Effect4.Program.CauseTerm" then s!"(Effect4.Program.CauseTerm.weaken cut {arg})"
  else if tyText == "Option Effect4.Program.Term" then
    s!"({arg}.map (Effect4.Program.Term.weaken cut))"
  else arg

/-- A frontier slot under the maps: a term through `g`, a cause through `gc`, an optional
term through `g` inside, anything else as it is. -/
def mapOf (tyText : String) (arg : String) : String :=
  if tyText == "Effect4.Program.Term" then s!"(g {arg})"
  else if tyText == "Effect4.Program.CauseTerm" then s!"(gc {arg})"
  else if tyText == "Option Effect4.Program.Term" then s!"({arg}.map g)"
  else arg

def emitFrontier (root : Name) (frontier : List Name) : MetaM (String × List String) := do
  let iv ← getConstInfoInduct root
  let _ := iv
  let mut block := []
  for fam in frontier do
    let fv ← getConstInfoInduct fam
    let label := famLabel fam
    let mut rows := []
    for c in fv.ctors do
      let ci ← getConstInfoCtor c
      let args ← forallBoundedTelescope ci.type (ci.numParams + ci.numFields) fun xs _ => do
        let mut acc := []
        let mut i := 0
        for x in xs[ci.numParams:] do
          let ty ← inferType x
          let tyText ← srcOf ty
          -- The frontier is a chosen sub-family: a sort outside it (a closed `LayerTerm`)
          -- is a constant of this signature, so the reading here stays by head constant.
          let pos := match ty.getAppFn with
            | .const n _ => if frontier.contains n then Pos.direct (famLabel n) else Pos.leaf tyText
            | _ => Pos.leaf tyText
          acc := acc ++ [({ name := s!"a{i}", pos, tyText } : Arg)]
          i := i + 1
        return acc
      rows := rows ++ [({ fam := label, ctor := shortName c, field := s!"{label}_{shortName c}", args } : CtorRow)]
    block := block ++ [(label, fam, rows)]
  let labels := block.map (·.1)
  let mut s := ""
  s := s ++ "inductive EffFrontierFam where\n"
  for l in labels do s := s ++ s!"  | {l}\n"
  s := s ++ "deriving DecidableEq, Repr\n\n"

  s := s ++ "structure EffFrontierAlgebra (Op : Type) (R : EffFrontierFam → Type u) where\n"
  for (label, _, rows) in block do
    for r in rows do
      let argTexts := r.args.map fun a =>
        match a.recFam with
        | some f => s!"R .{f}"
        | none => s!"({a.tyText})"
      s := s ++ s!"  {r.field} : " ++ String.intercalate " → " (argTexts ++ [s!"R .{label}"]) ++ "\n"
  s := s ++ "\nmutual\n"
  for (label, fam, rows) in block do
    s := s ++ s!"def cata_frontier_{label} \{Op : Type} \{R : EffFrontierFam → Type u} (alg : EffFrontierAlgebra Op R)\n"
    s := s ++ s!"    (node : {fam} Op) : R .{label} :=\n  match node with\n"
    for r in rows do
      let binders := String.intercalate " " (r.args.map (·.name))
      let pat := if r.args.isEmpty then s!"  | .{r.ctor} =>" else s!"  | .{r.ctor} {binders} =>"
      let callArgs := r.args.map fun a =>
        match a.recFam with
        | some f => s!"(cata_frontier_{f} alg {a.name})"
        | none => a.name
      s := s ++ pat ++ s!" alg.{r.field}"
      for c in callArgs do s := s ++ " " ++ c
      s := s ++ "\n"
    s := s ++ "termination_by structural node\n"
  s := s ++ "end\n\n"

  s := s ++ "abbrev frontierSelfCarrier (Op : Type) : EffFrontierFam → Type\n"
  for (label, fam, _) in block do
    s := s ++ s!"  | .{label} => {fam} Op\n"
  s := s ++ "\n"

  s := s ++ "/-- The term frontier mapped: `g` on every term slot, `gc` on every cause slot, of the\n"
  s := s ++ "open sorts; closed layers are constants of this signature and stay as they are. -/\n"
  s := s ++ "def frontierMap {Op : Type} (g : Effect4.Program.Term → Effect4.Program.Term)\n"
  s := s ++ "    (gc : Effect4.Program.CauseTerm → Effect4.Program.CauseTerm) :\n"
  s := s ++ "    EffFrontierAlgebra Op (frontierSelfCarrier Op) where\n"
  for (_, _, rows) in block do
    for r in rows do
      let binders := String.intercalate " " (r.args.map (·.name))
      let lhs := if r.args.isEmpty then "" else " " ++ binders
      let rhsArgs := r.args.map fun a =>
        match a.recFam with
        | some _ => a.name
        | none => mapOf a.tyText a.name
      let rhs := if rhsArgs.isEmpty then "" else " " ++ String.intercalate " " rhsArgs
      s := s ++ s!"  {r.field}{lhs} := .{r.ctor}{rhs}\n"
  s := s ++ "\n/-- Weakening at a cut is the frontier map of the term weakening. -/\n"
  s := s ++ "def weakenAlg {Op : Type} (cut : Nat) : EffFrontierAlgebra Op (frontierSelfCarrier Op) :=\n"
  s := s ++ "  frontierMap (Effect4.Program.Term.weaken cut) (Effect4.Program.CauseTerm.weaken cut)\n"
  -- Weakening at each open sort, from the rows: the frontier's terms through `Term.weaken`,
  -- the open children recursively, closed layers untouched. No hand-written arm; the
  -- theorem below says it is the frontier fold of `weakenAlg`.
  s := s ++ "\nmutual\n"
  for (_, fam, rows) in block do
    s := s ++ s!"def {shortName fam}.weaken \{Op : Type} (cut : Nat) : {fam} Op → {fam} Op\n"
    for r in rows do
      let binders := String.intercalate " " (r.args.map (·.name))
      let pat := if r.args.isEmpty then s!"  | .{r.ctor} =>" else s!"  | .{r.ctor} {binders} =>"
      let rhsArgs := r.args.map fun a =>
        match a.recFam with
        | some f =>
          let childFam := ((block.find? (·.1 == f)).map (·.2.1)).getD fam
          s!"({shortName childFam}.weaken cut {a.name})"
        | none => weakenOf a.tyText a.name
      let rhs := if rhsArgs.isEmpty then "" else " " ++ String.intercalate " " rhsArgs
      s := s ++ pat ++ s!" .{r.ctor}{rhs}\n"
  s := s ++ "end\n"
  s := s ++ "\nmutual\n"
  let mut receipts := []
  for (label, fam, rows) in block do
    let handName := s!"{fam}.weaken"
    s := s ++ s!"theorem weaken_eq_cata_{label} \{Op : Type} (cut : Nat) (node : {fam} Op) :\n"
    s := s ++ s!"    {handName} cut node = cata_frontier_{label} (weakenAlg cut) node := by\n"
    s := s ++ "  match node with\n"
    for r in rows do
      let binders := String.intercalate " " (r.args.map (·.name))
      let pat := if r.args.isEmpty then s!"  | .{r.ctor} =>" else s!"  | .{r.ctor} {binders} =>"
      let ihs := r.args.filterMap fun a =>
        a.recFam.map fun f => s!"weaken_eq_cata_{f} cut {a.name}"
      let lemmas := String.intercalate ", "
        ([s!"{handName}", s!"cata_frontier_{label}", "weakenAlg", "frontierMap"] ++ ihs)
      s := s ++ pat ++ s!"\n    simp only [{lemmas}]\n"
    s := s ++ "termination_by structural node\n"
    receipts := receipts ++ [s!"weaken_eq_cata_{label}"]
  s := s ++ "end\n\n"
  return (s, receipts)

/-! ## The nested companions: eliminator, equality, `Repr` (`--kind <Type>=elim`)

Lean 4.33.1 gives a nested inductive (a member under a `List`, an `Option` or a product) no
`induction` ("…because it is a nested inductive type"), no derived `DecidableEq` (the handler
returns early on a nested type, `Lean/Elab/Deriving/DecEq.lean`: `if indVal.isNested then return
false`) and only a `partial` derived `Repr` (an `opaque` over an `_unsafe_rec`, which the trust gate
refuses). The tree wrote the three by hand twice (`Store.Val.ind`, `Val.beq`, `Val.beq_iff`,
`Val.render`; `Json.ind`, `Json.beq`, `Json.beq_iff`). This emission writes them from the fold's
own position language, so a third nested family costs a manifest row, not a third hand copy:

* `T.ind`: the single-motive eliminator in membership form, registered
  `@[induction_eliminator]` so `induction t with | c … ih` keeps its text. One hypothesis per
  constructor; a member under a container arrives as `∀ x ∈ xs, motive x`, a product's member
  side projected. Built from `T.rec` as the environment declares it: one motive per auxiliary
  type, each container constructor's minor premise discharged by a fixed term.
* `T.beq` and one helper per composite position, structural, a leaf compared by `decide` (never
  `==`: at `String`/`Nat` the `LawfulBEq` route reaches `Classical.choice`); `T.beq_pos_*_iff` per
  position; `T.beq_iff` by `induction … using T.ind`; the `DecidableEq` instance is
  `decidable_of_iff` over it, so the computation and its proof stay apart.
* `T.repr` and its helpers, structural, printing exactly what the derived `Repr` prints (the
  constructor's full name, `Format.line`-separated arguments, `Repr.addAppParen`) and a container
  as the core instance prints it (`List.repr`, `Prod.repr`'s tuple flattening, `Option.repr`).

Refused by name: a parameterised or indexed family, a mutual block, a family with no nested
position (derive it), a one-parameter structure position (no nested family of the estate has
one), a field spelled `motive`.
-/

namespace Elim

def keywords : List String :=
  ["fun", "match", "with", "at", "by", "do", "from", "have", "show", "if", "then", "else", "let",
   "in", "open", "where", "deriving", "structure", "inductive", "theorem", "def", "instance",
   "end", "namespace", "section", "import", "mutual", "for", "unless", "return", "try", "catch",
   "finally", "break", "continue", "macro", "syntax", "local", "private", "protected", "partial",
   "unsafe", "variable", "universe", "example", "abbrev", "class", "extends", "forall", "Type",
   "Prop", "Sort", "this"]

/-- A name as source text, quoted where it would read as a keyword. -/
def ident (s : String) : String := if keywords.contains s then s!"«{s}»" else s

/-- One constructor: its full name, its short name, and each field's name, position and type. -/
structure ECtor where
  full : Name
  short : String
  fields : List (String × Pos × String)

/-- The constructors of a one-member family, the fields by their declared names. -/
def readECtors (root : Name) (members : List Name) : MetaM (List ECtor) := do
  let iv ← getConstInfoInduct root
  iv.ctors.mapM fun c => do
    let ci ← getConstInfoCtor c
    let fields ← forallBoundedTelescope ci.type (ci.numParams + ci.numFields) fun xs _ => do
      let mut acc : List (String × Pos × String) := []
      let mut i := 0
      for x in xs[ci.numParams:] do
        let ty ← inferType x
        let nm ← x.fvarId!.getUserName
        let nm := if nm.isAnonymous || nm.hasMacroScopes then s!"a{i}" else nm.toString
        if nm == "motive" then
          throwError "elim: {c}.{nm} is spelled like the eliminator's motive"
        let pos ← posOf members (shortName c) nm ty
        if (match pos with | .record .. => true | _ => false) then
          throwError "elim: {c}.{nm} sits under a one-parameter structure; this emission reads \
            `List`, `Option` and products only"
        acc := acc ++ [(nm, pos, ← srcOf ty)]
        i := i + 1
      return acc
    return { full := c, short := shortName c, fields }

/-- The induction hypothesis a member at position `p` contributes about the value `e`, with `m`
the motive applied: `none` at a leaf. `d` numbers the bound variables of nested quantifiers. -/
partial def ihAt (m : String → String) : Pos → String → Nat → Option String
  | .leaf _, _, _ => none
  | .direct _, e, _ => some (m e)
  | .list q, e, d => (ihAt m q s!"x{d}" (d + 1)).map fun b => s!"∀ x{d} ∈ {e}, {b}"
  | .option q, e, d => (ihAt m q s!"x{d}" (d + 1)).map fun b => s!"∀ x{d} ∈ {e}, {b}"
  | .prod a b, e, d =>
    match ihAt m a s!"{e}.1" d, ihAt m b s!"{e}.2" d with
    | none, none => none
    | some s, none => some s
    | none, some t => some t
    | some s, some t => some s!"({s}) ∧ ({t})"
  | .record .., _, _ => none

/-- How many induction hypotheses a product's constructor minor receives: one per side that is
not a leaf. -/
def prodSides (a b : Pos) : Nat := (if a.isLeaf then 0 else 1) + (if b.isLeaf then 0 else 1)

/-- A constructor pattern or application: `.c a0 a1`, or `.c` with no field. -/
def ctorApp (c : ECtor) (args : List String) : String :=
  if args.isEmpty then s!".{ident c.short}"
  else s!".{ident c.short} " ++ String.intercalate " " args

/-- The comparison of two values at a position. -/
def cmpAt (pfx : String) (p : Pos) (l r : String) : String :=
  match p with
  | .leaf _ => s!"decide ({l} = {r})"
  | .direct _ => s!"{pfx}.beq {l} {r}"
  | _ => s!"{pfx}.beq_pos_{p.suffix} {l} {r}"

/-- The rewrite that turns one position's comparison into an equality, given the hypothesis
`ih` about the left value; `none` when the leaf rule `decide_eq_true_eq` does it. -/
def iffAt (pfx : String) (p : Pos) (ih r : String) : Option String :=
  match p with
  | .leaf _ => none
  | .direct _ => some s!"{ih} {r}"
  | _ => some s!"{pfx}.beq_pos_{p.suffix}_iff {ih} {r}"

/-- The components of a product's right spine, left to right, and whether the last is a leaf
(whose own product structure, if any, `reprTuple` flattens as core's instance does). -/
partial def spine : Pos → List Pos
  | .prod a b => a :: (match b with | .prod .. => spine b | _ => [b])
  | p => [p]

def emitElim (root : Name) (pfxIn : Option String) : MetaM String := do
  let iv ← getConstInfoInduct root
  unless iv.numParams == 0 && iv.numIndices == 0 do
    throwError "elim: {root} has parameters or indices; this emission reads a plain family"
  unless iv.all.length == 1 do
    throwError "elim: {root} is mutual ({iv.all}); one eliminator per member is not emitted here"
  let members := iv.all
  let ctors ← readECtors root members
  unless ctors.any (fun c => c.fields.any fun f => match f.2.1 with
      | .leaf _ | .direct _ => false | _ => true) do
    throwError "elim: {root} has no member under a container; derive `DecidableEq` and `Repr` \
      and use `induction` as they are"
  let T := s!"_root_.{root}"
  -- Declarations are named relative to the file's namespace (the root's prefix): inside a
  -- `mutual` block a `_root_.`-qualified self-reference is not the function being defined.
  let pfx := pfxIn.getD (shortName root)
  let instNs := match pfxIn with
    | some p => if p.toName.getPrefix.isAnonymous then "" else p.toName.getPrefix.toString ++ "."
    | none => ""
  let short := shortName root
  let srcP : Pos → String := fun p => p.source (fun _ => T) false
  -- every distinct composite position, children before parents (the fold's own order)
  let mut comps : List Pos := []
  for c in ctors do
    for (_, p, _) in c.fields do
      for q in p.composites do
        unless comps.any (·.key == q.key) do comps := comps ++ [q]
  let mut s := ""
  -- ## The eliminator
  let motive : String → String := fun e => s!"motive {e}"
  s := s ++ s!"/-- The single-motive induction principle of `{root}`, membership form: one\n"
  s := s ++ "hypothesis per constructor, a member under a container quantified by membership.\n"
  s := s ++ "Registered as the induction eliminator, so `induction t with` keeps its arms. -/\n"
  s := s ++ "@[elab_as_elim, induction_eliminator]\n"
  s := s ++ s!"theorem {pfx}.ind \{motive : {T} → Prop}\n"
  for c in ctors do
    let body :=
      if c.fields.isEmpty then s!"motive {ctorApp c []}"
      else
        let binders := String.intercalate " " (c.fields.map fun (n, _, ty) => s!"({ident n} : {ty})")
        let ihs := c.fields.filterMap fun (n, p, _) =>
          (ihAt motive p (ident n) 0).map fun h => if p matches .direct _ then h else s!"({h})"
        let concl := s!"motive ({ctorApp c (c.fields.map fun (n, _, _) => ident n)})"
        s!"∀ {binders}, " ++ String.join (ihs.map (· ++ " → ")) ++ concl
    s := s ++ s!"    ({ident c.short} : {body})\n"
  s := s ++ "    : ∀ t, motive t := fun t =>\n"
  let recName := root ++ `rec
  let rv ← getConstInfoRec recName
  let (motiveArgs, minorArgs) ← forallBoundedTelescope rv.type
      (rv.numParams + rv.numMotives + rv.numMinors) fun xs _ => do
    let motives := xs[rv.numParams:rv.numParams + rv.numMotives].toArray
    let minors := xs[rv.numParams + rv.numMotives:rv.numParams + rv.numMotives + rv.numMinors].toArray
    -- each motive's auxiliary type, as a position of the family
    let mut mPos : Array (Option Pos) := #[]
    let mut margs : List String := []
    for h : j in [:motives.size] do
      let mv := motives[j]
      let nm ← mv.fvarId!.getUserName
      let dom := (← inferType mv).bindingDomain!
      if j == 0 then
        mPos := mPos.push none
        margs := margs ++ [s!"({nm} := motive)"]
      else
        let p ← posOf members "rec" s!"motive {j}" dom
        let some body := ihAt motive p "e" 0
          | throwError "elim: the auxiliary type {← srcOf dom} names no member"
        mPos := mPos.push (some p)
        margs := margs ++ [s!"({nm} := fun e => {body})"]
    let mut mins : List String := []
    for mn in minors do
      let mty ← inferType mn
      let txt ← forallTelescope mty fun _ concl => do
        let some k := motives.findIdx? (· == concl.getAppFn)
          | throwError "elim: a minor premise of {recName} concludes at no motive"
        let .const cName _ := concl.appArg!.getAppFn
          | throwError "elim: a minor premise of {recName} is not at a constructor"
        if k == 0 then
          return ident (shortName cName)
        let p := (mPos[k]!).getD (.leaf "")
        if cName == ``List.nil || cName == ``Option.none then
          return "(fun _ hx => nomatch hx)"
        else if cName == ``List.cons then
          return "(fun _ _ ihHead ihTail => by\n      intro _ hx\n      cases hx with\n      \
            | head => exact ihHead\n      | tail _ hx' => exact ihTail _ hx')"
        else if cName == ``Option.some then
          return "(fun _ ih _ hx => by\n      cases hx\n      exact ih)"
        else if cName == ``Prod.mk then
          match p with
          | .prod a b =>
            if prodSides a b == 2 then return "(fun _ _ iha ihb => ⟨iha, ihb⟩)"
            else return "(fun _ _ ih => ih)"
          | _ => throwError "elim: a `Prod.mk` minor at a position that is not a product"
        else
          throwError "elim: the auxiliary constructor {cName} has no discharge in this emission"
      mins := mins ++ [txt]
    return (margs, mins)
  s := s ++ s!"  {T}.rec " ++ String.intercalate "\n    " motiveArgs ++ "\n"
  for m in minorArgs do s := s ++ s!"    {m}\n"
  s := s ++ "    t\n\n"
  -- ## The equality
  s := s ++ s!"mutual\n/-- Structural equality on `{root}` as a Boolean; leaves compared by `decide`. -/\n"
  s := s ++ s!"def {pfx}.beq : {T} → {T} → Bool\n"
  for c in ctors do
    let as := (List.range c.fields.length).map fun i => s!"a{i}"
    let bs := (List.range c.fields.length).map fun i => s!"b{i}"
    let cmps := (c.fields.zipIdx).map fun ((_, p, _), i) => cmpAt pfx p s!"a{i}" s!"b{i}"
    let rhs := if cmps.isEmpty then "true" else String.intercalate " && " cmps
    s := s ++ s!"  | {ctorApp c as}, {ctorApp c bs} => {rhs}\n"
  if ctors.length > 1 then s := s ++ "  | _, _ => false\n"
  s := s ++ "termination_by structural a _ => a\n"
  for p in comps do
    s := s ++ s!"def {pfx}.beq_pos_{p.suffix} : {srcP p} → {srcP p} → Bool\n"
    match p with
    | .list q =>
      s := s ++ "  | [], [] => true\n"
      s := s ++ s!"  | x :: xs, y :: ys => {cmpAt pfx q "x" "y"} && {pfx}.beq_pos_{p.suffix} xs ys\n"
      s := s ++ "  | _, _ => false\n"
    | .option q =>
      s := s ++ "  | none, none => true\n"
      s := s ++ s!"  | some x, some y => {cmpAt pfx q "x" "y"}\n"
      s := s ++ "  | _, _ => false\n"
    | .prod a b =>
      s := s ++ s!"  | (u0, v0), (u1, v1) => {cmpAt pfx a "u0" "u1"} && {cmpAt pfx b "v0" "v1"}\n"
    | _ => throwError "elim: no comparison for the position {p.key}"
    s := s ++ "termination_by structural x _ => x\n"
  s := s ++ "end\n\n"
  -- the comparison is equality, position by position, children first
  let beqIff : String → String := fun e => s!"(∀ b, {pfx}.beq {e} b = true ↔ {e} = b)"
  for p in comps do
    let h := s!"{pfx}.beq_pos_{p.suffix}"
    let v := match p with | .list _ => "xs" | _ => "x"
    let some ih := ihAt beqIff p v 0
      | throwError "elim: the position {p.key} names no member"
    s := s ++ s!"theorem {h}_iff \{{v} : {srcP p}} (ih : {ih}) :\n"
    s := s ++ s!"    ∀ y, {h} {v} y = true ↔ {v} = y := by\n"
    match p with
    | .prod a b =>
      let ihA := if prodSides a b == 2 then "ih.1" else "ih"
      let ihB := if prodSides a b == 2 then "ih.2" else "ih"
      let ls := ([h, "Bool.and_eq_true"] ++
        (if a.isLeaf || b.isLeaf then ["decide_eq_true_eq"] else []) ++
        (iffAt pfx a ihA "u1").toList ++ (iffAt pfx b ihB "v1").toList ++ ["Prod.mk.injEq"])
      s := s ++ "  intro y\n  obtain ⟨u0, v0⟩ := x\n  obtain ⟨u1, v1⟩ := y\n"
      s := s ++ s!"  simp only [{String.intercalate ", " ls}]\n\n"
    | .list q =>
      let elemIh := "(ih x List.mem_cons_self)"
      let elem := (iffAt pfx q elemIh "y").toList
      let elem := if q.isLeaf then ["decide_eq_true_eq"] else elem
      let ls := [h, "Bool.and_eq_true"] ++ elem ++
        ["iht (fun z hz => ih z (List.mem_cons_of_mem x hz)) ys", "List.cons.injEq"]
      s := s ++ "  induction xs with\n  | nil =>\n    intro y\n    cases y with\n"
      s := s ++ s!"    | nil => simp only [{h}]\n"
      s := s ++ s!"    | cons _ _ => simp only [{h}, Bool.false_eq_true, reduceCtorEq]\n"
      s := s ++ "  | cons x xs iht =>\n    intro y\n    cases y with\n"
      s := s ++ s!"    | nil => simp only [{h}, Bool.false_eq_true, reduceCtorEq]\n"
      s := s ++ s!"    | cons y ys =>\n      simp only [{String.intercalate ", " ls}]\n\n"
    | .option q =>
      let elem := (iffAt pfx q "(ih x rfl)" "y").toList
      let elem := if q.isLeaf then ["decide_eq_true_eq"] else elem
      s := s ++ "  intro y\n  cases x with\n  | none =>\n    cases y with\n"
      s := s ++ s!"    | none => simp only [{h}]\n"
      s := s ++ s!"    | some _ => simp only [{h}, Bool.false_eq_true, reduceCtorEq]\n"
      s := s ++ "  | some x =>\n    cases y with\n"
      s := s ++ s!"    | none => simp only [{h}, Bool.false_eq_true, reduceCtorEq]\n"
      s := s ++ s!"    | some y => simp only [{String.intercalate ", " ([h] ++ elem ++ ["Option.some.injEq"])}]\n\n"
    | _ => throwError "elim: no lemma for the position {p.key}"
  s := s ++ s!"/-- `beq` decides structural equality. -/\n"
  s := s ++ s!"theorem {pfx}.beq_iff : ∀ a b : {T}, {pfx}.beq a b = true ↔ a = b := by\n"
  s := s ++ s!"  intro a\n  induction a using {pfx}.ind with\n"
  for c in ctors do
    let names := c.fields.map fun (n, _, _) => ident n
    let ihNames := (c.fields.zipIdx).filterMap fun ((_, p, _), i) =>
      if p.isLeaf then none else some s!"ih{i}"
    let pat := String.intercalate " " ([ident c.short] ++ names ++ ihNames)
    let mut ls : List String := [s!"{pfx}.beq"]
    if ctors.length > 1 then ls := ls ++ ["Bool.false_eq_true", "reduceCtorEq"]
    if c.fields.length ≥ 2 then ls := ls ++ ["Bool.and_eq_true"]
    if c.fields.any (fun f => f.2.1.isLeaf) then ls := ls ++ ["decide_eq_true_eq"]
    for ((_, p, _), i) in c.fields.zipIdx do
      match p with
      | .leaf _ => pure ()
      | .direct _ => ls := ls ++ [s!"ih{i}"]
      | _ => ls := ls ++ [s!"{pfx}.beq_pos_{p.suffix}_iff ih{i}"]
    if !c.fields.isEmpty then ls := ls ++ [s!"{c.full}.injEq"]
    s := s ++ s!"  | {pat} =>\n    intro b\n    cases b <;> simp only [{String.intercalate ", " ls}]\n"
  s := s ++ "\n"
  s := s ++ s!"/-- Decidable structural equality, by `beq` and its proof. -/\n"
  s := s ++ s!"instance {instNs}instDecidableEq{short} : DecidableEq {T} := fun a b =>\n"
  s := s ++ s!"  decidable_of_iff _ ({pfx}.beq_iff a b)\n\n"
  -- ## Repr
  let argFmt : Pos → String → String := fun p e =>
    match p with
    | .leaf _ => s!"_root_.reprArg {e}"
    | .direct _ => s!"{pfx}.repr {e} max_prec"
    | .list _ => s!"(match {e} with | [] => Std.Format.text \"[]\" | _ => Std.Format.bracket \"[\" \
        (Std.Format.joinSep ({pfx}.repr_items_{p.suffix} {e}) (\",\" ++ Std.Format.line)) \"]\")"
    | .prod .. => s!"Std.Format.bracket \"(\" (Std.Format.joinSep ({pfx}.repr_tuple_{p.suffix} {e}) \
        (\",\" ++ Std.Format.line)) \")\""
    | .option _ => s!"{pfx}.repr_pos_{p.suffix} {e} max_prec"
    | .record .. => "«record»"
  let elemFmt : Pos → String → String := fun p e =>
    match p with
    | .leaf _ => s!"_root_.repr {e}"
    | .direct _ => s!"{pfx}.repr {e} 0"
    | .option _ => s!"{pfx}.repr_pos_{p.suffix} {e} 0"
    | _ => argFmt p e
  s := s ++ s!"mutual\n/-- The derived `Repr`'s text, structurally (the derived one is `partial` here). -/\n"
  s := s ++ s!"def {pfx}.repr : {T} → Nat → Std.Format\n"
  for c in ctors do
    let as := (List.range c.fields.length).map fun i => s!"a{i}"
    let parts := (c.fields.zipIdx).map fun ((_, p, _), i) => argFmt p s!"a{i}"
    let body := String.join ([s!"Std.Format.text \"{c.full}\""] ++
      parts.map fun x => s!" ++ Std.Format.line ++ {x}")
    s := s ++ s!"  | {ctorApp c as}, prec => Repr.addAppParen (Std.Format.group (Std.Format.nest \
      (if prec >= max_prec then 1 else 2) ({body}))) prec\n"
  s := s ++ "termination_by structural t _ => t\n"
  for p in comps do
    match p with
    | .list q =>
      s := s ++ s!"def {pfx}.repr_items_{p.suffix} : {srcP p} → List Std.Format\n"
      s := s ++ "  | [] => []\n"
      s := s ++ s!"  | x :: xs => ({elemFmt q "x"}) :: {pfx}.repr_items_{p.suffix} xs\n"
      s := s ++ "termination_by structural xs => xs\n"
    | .prod a b =>
      s := s ++ s!"def {pfx}.repr_tuple_{p.suffix} : {srcP p} → List Std.Format\n"
      let rest := match b with
        | .prod .. => s!"{pfx}.repr_tuple_{b.suffix} v"
        | .leaf _ => "(ReprTuple.reprTuple v []).reverse"
        | _ => s!"[{elemFmt b "v"}]"
      s := s ++ s!"  | (u, v) => ({elemFmt a "u"}) :: {rest}\n"
      s := s ++ "termination_by structural x => x\n"
    | .option q =>
      s := s ++ s!"def {pfx}.repr_pos_{p.suffix} : {srcP p} → Nat → Std.Format\n"
      s := s ++ "  | none, _ => Std.Format.text \"none\"\n"
      s := s ++ s!"  | some y, prec => Repr.addAppParen (Std.Format.text \"some \" ++ {argFmt q "y"}) prec\n"
      s := s ++ "termination_by structural x _ => x\n"
    | _ => throwError "elim: no printer for the position {p.key}"
  s := s ++ "end\n\n"
  s := s ++ s!"instance {instNs}instRepr{short} : Repr {T} := ⟨{pfx}.repr⟩\n\n"
  s := s ++ "/-! ## Receipts -/\n\n"
  s := s ++ s!"#print axioms {pfx}.ind\n#print axioms {pfx}.beq_iff\n"
  s := s ++ s!"#print axioms {instNs}instDecidableEq{short}\n#print axioms {instNs}instRepr{short}\n"
  for p in comps do
    s := s ++ s!"#print axioms {pfx}.beq_pos_{p.suffix}_iff\n"
  return s

end Elim


/-! ## The generic fold families of a plain block (probe U)

For a non-nested, non-mutual block (`Ty`), the one-level view and the generic families every
table-driven traversal is read through: the tags and their names and binders, the payload
sorts, `build`/`kids` and the view law, the per-constructor table type, the layer algebra, the
head fold and the paired fold with their connectors, fusion and the banana split from
uniqueness, and the per-layer invariant. All of it is read off the constructor rows; nothing
here is hand-listed. A block with a composite position (`record`'s `List (String × Ty)`) or a
constructor with two payload arguments is refused by name: its layer needs `ArgF`'s positions
(the `LayerView` emitter's), not one payload and a list of children.
-/

namespace Extras

/-- A payload sort's constructor name in `<Block>Leaf`. -/
def leafCtor (tyText : String) : String :=
  match tyText with
  | "String" => "str"
  | "Nat" => "nat"
  | "Bool" => "bool"
  | t => lowerFirst (leafHint t)

def joinArgs (xs : List String) : String := String.intercalate " " xs

/-- The fixed helpers, once per file: how `foldMap_*` combines a node with its children. -/
def helpers : String :=
  "/-- The children combined the way `foldMap_*` combines them: none, one, or\n" ++
  "`op c₀ (op c₁ …)`. -/\n" ++
  "def recCombine {M : Type u} (op : M → M → M) : List M → Option M\n" ++
  "  | [] => none\n" ++
  "  | [c] => some c\n" ++
  "  | c :: rest => (recCombine op rest).map (op c)\n\n" ++
  "/-- The node's contribution, then its children. -/\n" ++
  "def nodeThen {M : Type u} (op : M → M → M) (here : M) (kids : List M) : M :=\n" ++
  "  match recCombine op kids with\n" ++
  "  | none => here\n" ++
  "  | some k => op here k\n\n"

def emitExtras (root : Name) : MetaM String := do
  let (isParam, blockName, block) ← readBlock root
  if isParam then throwError "extras: {root} takes parameters; the plain-block extras do not"
  if block.length != 1 then throwError "extras: {root} is mutual; the plain-block extras do not"
  if blockNested block then
    throwError "extras: {root} holds a member under a container; its layer is `ArgF`'s \
(tools/Effect4Gen/LayerView.lean), not one payload and a list of children"
  let (label, fam, rows) := block.head!
  let famT := fam.toString
  let ctorT := s!"{blockName}Ctor"
  let leafT := s!"{blockName}Leaf"
  let tableT := s!"{blockName}Table"
  let algT := s!"{blockName}Algebra"
  let homT := s!"{blockName}Hom"
  let famE := s!"{blockName}Fam"
  let low := lowerFirst blockName
  let viewCtor := s!"{low}Ctor"
  let viewLeaf := s!"{low}Leaf"
  let viewBuild := s!"{low}Build"
  let viewKids := s!"{low}Kids"
  -- every constructor: at most one payload argument, which precedes no child
  for r in rows do
    let leaves := r.args.filter (·.pos.isLeaf)
    if leaves.length > 1 then
      throwError "extras: {r.ctor} has {leaves.length} payload arguments; one is read"
  let sorts : List String := rows.foldl (fun acc r =>
    r.args.foldl (fun acc a => if a.pos.isLeaf && !(acc.contains a.tyText) then acc ++ [a.tyText] else acc) acc) []
  let leafOf (r : CtorRow) : Option Arg := r.args.find? (·.pos.isLeaf)
  let kidsOf (r : CtorRow) : List Arg := r.args.filter (·.recFam.isSome)
  let pat (r : CtorRow) : String :=
    if r.args.isEmpty then s!".{r.ctor}" else s!".{r.ctor} {joinArgs (r.args.map (·.name))}"
  let wild (r : CtorRow) : String :=
    if r.args.isEmpty then s!".{r.ctor}" else s!".{r.ctor} {joinArgs (r.args.map fun _ => "_")}"
  let leafExpr (r : CtorRow) : String :=
    match leafOf r with
    | some a => s!"(.{leafCtor a.tyText} {a.name})"
    | none => ".none"
  let kidList (r : CtorRow) (f : Arg → String) : String :=
    "[" ++ String.intercalate ", " ((kidsOf r).map f) ++ "]"
  let arity (r : CtorRow) : String :=
    match r.args.length with
    | 0 => "rfl"
    | 1 => "fun _ => rfl"
    | 2 => "fun _ _ => rfl"
    | n => "fun " ++ joinArgs (List.replicate n "_") ++ " => rfl"
  let homRfl : String := String.intercalate "\n" (rows.map fun r => s!"      h_{r.field} := {arity r}")
  let mut s := ""
  -- the tags
  s := s ++ s!"/-- The constructor tags of `{famT}`, in declaration order. -/\n"
  s := s ++ s!"inductive {ctorT} where\n"
  for r in rows do s := s ++ s!"  | {r.ctor}\n"
  s := s ++ "deriving DecidableEq, Repr\n\n"
  s := s ++ s!"/-- Every tag, in declaration order. -/\n"
  s := s ++ s!"def {ctorT}.all : List {ctorT} :=\n  [" ++
    String.intercalate ", " (rows.map fun r => s!".{r.ctor}") ++ "]\n\n"
  s := s ++ s!"/-- The tag of a node: one level, no recursion. -/\n"
  s := s ++ s!"def {viewCtor} : {famT} → {ctorT}\n"
  for r in rows do s := s ++ s!"  | {wild r} => .{r.ctor}\n"
  s := s ++ "\n"
  s := s ++ s!"/-- The constructor's name, as the declaration spells it. -/\n"
  s := s ++ s!"def {ctorT}.name : {ctorT} → String\n"
  for r in rows do s := s ++ s!"  | .{r.ctor} => \"{r.ctor}\"\n"
  s := s ++ "\n"
  s := s ++ s!"/-- The constructor's binder names, in declaration order. -/\n"
  s := s ++ s!"def {ctorT}.binders : {ctorT} → List String\n"
  for r in rows do
    s := s ++ s!"  | .{r.ctor} => [" ++ String.intercalate ", " (r.args.map fun a => s!"\"{a.binder}\"") ++ "]\n"
  s := s ++ "\n"
  -- the payload
  s := s ++ s!"/-- The non-recursive payload of a node, by sort. -/\n"
  s := s ++ s!"inductive {leafT} where\n  | none\n"
  for t in sorts do s := s ++ s!"  | {leafCtor t} (v : {t})\n"
  s := s ++ "deriving DecidableEq, Repr\n\n"
  s := s ++ s!"/-- The payload of a node: one level, no recursion. -/\n"
  s := s ++ s!"def {viewLeaf} : {famT} → {leafT}\n"
  let leafPat (r : CtorRow) : String :=
    if r.args.isEmpty then s!".{r.ctor}" else
      s!".{r.ctor} " ++ joinArgs (r.args.map fun a => if a.pos.isLeaf then a.name else "_")
  for r in rows do s := s ++ s!"  | {leafPat r} => {leafExpr r}\n"
  s := s ++ "\n"
  -- build, kids, the view law
  let first := (rows.find? (·.args.isEmpty)).map (·.ctor)
  let some dflt := first | throwError "extras: {root} has no nullary constructor for `build`'s refusal"
  s := s ++ s!"/-- A node from its tag, payload and children; a tag whose payload or arity does not\n"
  s := s ++ s!"match is `{dflt}`. -/\n"
  s := s ++ s!"def {viewBuild} : {ctorT} → {leafT} → List {famT} → {famT}\n"
  for r in rows do
    let lp := match leafOf r with
      | some a => s!".{leafCtor a.tyText} {a.name}"
      | none => ".none"
    s := s ++ s!"  | .{r.ctor}, {lp}, {kidList r (·.name)} => {pat r}\n"
  s := s ++ s!"  | _, _, _ => .{dflt}\n\n"
  s := s ++ s!"/-- The children of a node, in declaration order. -/\n"
  s := s ++ s!"def {viewKids} : {famT} → List {famT}\n"
  let kidPat (r : CtorRow) : String :=
    if r.args.isEmpty then s!".{r.ctor}" else
      s!".{r.ctor} " ++ joinArgs (r.args.map fun a => if a.recFam.isSome then a.name else "_")
  for r in rows do s := s ++ s!"  | {kidPat r} => {kidList r (·.name)}\n"
  s := s ++ "\n"
  s := s ++ s!"/-- A node is rebuilt from its view. -/\n"
  s := s ++ s!"theorem {viewBuild}_view (t : {famT}) : {viewBuild} ({viewCtor} t) ({viewLeaf} t) ({viewKids} t) = t := by\n"
  s := s ++ "  cases t <;> rfl\n\n"
  -- the table
  s := s ++ s!"/-- One row per constructor. -/\n"
  s := s ++ s!"structure {tableT} (α : Type u) where\n"
  for r in rows do s := s ++ s!"  {r.ctor} : α\n"
  s := s ++ "\n"
  s := s ++ s!"/-- A row by tag. -/\n"
  s := s ++ s!"def {tableT}.get \{α : Type u} (t : {tableT} α) : {ctorT} → α\n"
  for r in rows do s := s ++ s!"  | .{r.ctor} => t.{r.ctor}\n"
  s := s ++ "\n"
  -- the layer algebra
  s := s ++ s!"/-- A layer function as an algebra: every constructor hands its tag, its payload and its\n"
  s := s ++ s!"folded children (declaration order) to one function. -/\n"
  s := s ++ s!"def {algT}.ofLayer \{R : Type u} (layer : {ctorT} → {leafT} → List R → R) :\n"
  s := s ++ s!"    {algT} (fun _ => R) where\n"
  for r in rows do
    let lhs := if r.args.isEmpty then "" else " " ++ joinArgs (r.args.map (·.name))
    s := s ++ s!"  {r.field}{lhs} := layer .{r.ctor} {leafExpr r} {kidList r (·.name)}\n"
  s := s ++ "\n"
  s := s ++ s!"/-- The fold of a layer function, one layer down. -/\n"
  s := s ++ s!"theorem cata_ofLayer_view \{R : Type u} (layer : {ctorT} → {leafT} → List R → R) (t : {famT}) :\n"
  s := s ++ s!"    cata_{label} ({algT}.ofLayer layer) t =\n"
  s := s ++ s!"      layer ({viewCtor} t) ({viewLeaf} t) (({viewKids} t).map (cata_{label} ({algT}.ofLayer layer))) := by\n"
  s := s ++ "  cases t <;> rfl\n\n"
  let specs := (rows.filter fun r => !(kidsOf r).isEmpty).map fun r => s!"{famT}.{r.ctor}.sizeOf_spec"
  s := s ++ s!"/-- A child is smaller. -/\n"
  s := s ++ s!"theorem sizeOf_{viewKids} \{t k : {famT}} (h : k ∈ {viewKids} t) : sizeOf k < sizeOf t := by\n"
  s := s ++ s!"  cases t <;> simp only [{viewKids}, List.mem_cons, List.not_mem_nil, or_false] at h <;>\n"
  s := s ++ "    rcases h with rfl | rfl <;> simp only [" ++ String.intercalate ", " specs ++ "] <;> omega\n\n"
  s := s ++ s!"/-- **The fold of a layer function keeps every property its layers keep.** -/\n"
  s := s ++ s!"theorem cata_ofLayer_inv \{R : Type u} (layer : {ctorT} → {leafT} → List R → R) (P : R → Prop)\n"
  s := s ++ s!"    (h : ∀ c l kids, (∀ k ∈ kids, P k) → P (layer c l kids)) (t : {famT}) :\n"
  s := s ++ s!"    P (cata_{label} ({algT}.ofLayer layer) t) := by\n"
  s := s ++ "  rw [cata_ofLayer_view]\n  apply h\n  intro k hk\n"
  s := s ++ "  obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hk\n"
  s := s ++ "  exact cata_ofLayer_inv layer P h k'\n"
  s := s ++ "termination_by sizeOf t\n"
  s := s ++ s!"decreasing_by exact sizeOf_{viewKids} hk'\n\n"
  -- the head fold and its connector
  s := s ++ s!"/-- The monoid fold whose node contribution reads only the node's layer, as an algebra. -/\n"
  s := s ++ s!"def {algT}.headAlg \{M : Type u} (op : M → M → M) (g : {ctorT} → {leafT} → M) :\n"
  s := s ++ s!"    {algT} (fun _ => M) :=\n"
  s := s ++ s!"  {algT}.ofLayer fun c l kids => nodeThen op (g c l) kids\n\n"
  s := s ++ s!"/-- **Connector, once for every head fold.** -/\n"
  s := s ++ s!"theorem foldMap_head_eq_cata \{M : Type u} (unit : M) (op : M → M → M)\n"
  s := s ++ s!"    (g : {ctorT} → {leafT} → M) (t : {famT}) :\n"
  s := s ++ s!"    foldMap_{label} unit op t (fun s => g ({viewCtor} s) ({viewLeaf} s)) =\n"
  s := s ++ s!"      cata_{label} ({algT}.headAlg op g) t :=\n"
  s := s ++ s!"  hom_eq_cata_{label} (alg := {algT}.headAlg op g)\n"
  s := s ++ s!"    \{ f_{label} := fun s => foldMap_{label} unit op s (fun s => g ({viewCtor} s) ({viewLeaf} s))\n"
  s := s ++ homRfl ++ " } t\n\n"
  -- the paired fold and its connector
  s := s ++ s!"/-- The general monoid fold (its hook reads the whole node) as the paired catamorphism. -/\n"
  s := s ++ s!"def {algT}.paraAlg \{M : Type u} (op : M → M → M) (f : {famT} → M) :\n"
  s := s ++ s!"    {algT} (fun _ => {famT} × M) where\n"
  for r in rows do
    let lhs := if r.args.isEmpty then "" else " " ++ joinArgs (r.args.map (·.name))
    let node := if r.args.isEmpty then s!".{r.ctor}" else
      s!".{r.ctor} " ++ joinArgs (r.args.map fun a => if a.recFam.isSome then s!"{a.name}.1" else a.name)
    let kids := (kidsOf r).map fun a => s!"{a.name}.2"
    let rhs := match kids with
      | [] => s!"f ({node})"
      | _ => s!"op (f ({node})) ({recComb kids})"
    s := s ++ s!"  {r.field}{lhs} := ({node}, {rhs})\n"
  s := s ++ "\n"
  s := s ++ s!"/-- **Connector, once for every monoid fold.** -/\n"
  s := s ++ s!"theorem foldMap_eq_cata \{M : Type u} (unit : M) (op : M → M → M) (f : {famT} → M) (t : {famT}) :\n"
  s := s ++ s!"    (t, foldMap_{label} unit op t f) = cata_{label} ({algT}.paraAlg op f) t :=\n"
  s := s ++ s!"  hom_eq_cata_{label} (alg := {algT}.paraAlg op f)\n"
  s := s ++ s!"    \{ f_{label} := fun s => (s, foldMap_{label} unit op s f)\n"
  s := s ++ homRfl ++ " } t\n\n"
  -- fusion
  s := s ++ s!"/-- An algebra morphism `h` from `alg` to `alg'`, one square per constructor, each\n"
  s := s ++ s!"defaulting to `rfl`. -/\n"
  s := s ++ s!"structure {algT}.Commutes \{R : {famE} → Type u} \{S : {famE} → Type v}\n"
  s := s ++ s!"    (h : R .{label} → S .{label}) (alg : {algT} R) (alg' : {algT} S) : Prop where\n"
  for r in rows do
    let binders := joinArgs (r.args.map (·.name))
    let quant := if r.args.isEmpty then "" else s!"∀ {binders}, "
    let lhsArgs := if r.args.isEmpty then "" else " " ++ binders
    let rhsArgs := String.join (r.args.map fun a => if a.recFam.isSome then s!" (h {a.name})" else s!" {a.name}")
    s := s ++ s!"  {r.field} : {quant}h (alg.{r.field}{lhsArgs}) = alg'.{r.field}{rhsArgs} := by\n    intros; rfl\n"
  s := s ++ "\n"
  s := s ++ s!"/-- **Fusion, from uniqueness.** -/\n"
  s := s ++ s!"theorem cata_fusion_{label} \{R : {famE} → Type u} \{S : {famE} → Type v}\n"
  s := s ++ s!"    \{h : R .{label} → S .{label}} \{alg : {algT} R} \{alg' : {algT} S}\n"
  s := s ++ s!"    (c : {algT}.Commutes h alg alg') (t : {famT}) :\n"
  s := s ++ s!"    h (cata_{label} alg t) = cata_{label} alg' t :=\n"
  s := s ++ s!"  hom_eq_cata_{label} (alg := alg')\n"
  s := s ++ s!"    \{ f_{label} := fun s => h (cata_{label} alg s)\n"
  let fusionFields := rows.map fun r =>
    if (kidsOf r).isEmpty then s!"      h_{r.field} := c.{r.field}"
    else
      let binders := joinArgs (r.args.map (·.name))
      let callArgs := joinArgs (r.args.map fun a => if a.recFam.isSome then s!"(cata_{label} alg {a.name})" else a.name)
      s!"      h_{r.field} := fun {binders} => c.{r.field} {callArgs}"
  s := s ++ String.intercalate "\n" fusionFields ++ " } t\n\n"
  -- the banana split
  s := s ++ s!"/-- Two algebras run side by side. -/\n"
  s := s ++ s!"def {algT}.prod \{R : {famE} → Type u} \{S : {famE} → Type v}\n"
  s := s ++ s!"    (a : {algT} R) (b : {algT} S) : {algT} (fun f => R f × S f) where\n"
  for r in rows do
    let lhs := if r.args.isEmpty then "" else " " ++ joinArgs (r.args.map (·.name))
    let side (w : String) (proj : String) : String :=
      if r.args.isEmpty then s!"{w}.{r.field}" else
        s!"{w}.{r.field} " ++ joinArgs (r.args.map fun a => if a.recFam.isSome then s!"{a.name}.{proj}" else a.name)
    s := s ++ s!"  {r.field}{lhs} := ({side "a" "1"}, {side "b" "2"})\n"
  s := s ++ "\n"
  s := s ++ s!"/-- **The banana split, from uniqueness.** -/\n"
  s := s ++ s!"theorem cata_prod_{label} \{R : {famE} → Type u} \{S : {famE} → Type v}\n"
  s := s ++ s!"    (a : {algT} R) (b : {algT} S) (t : {famT}) :\n"
  s := s ++ s!"    cata_{label} ({algT}.prod a b) t = (cata_{label} a t, cata_{label} b t) :=\n"
  s := s ++ s!"  (hom_eq_cata_{label} (alg := {algT}.prod a b)\n"
  s := s ++ s!"    \{ f_{label} := fun s => (cata_{label} a s, cata_{label} b s)\n"
  s := s ++ homRfl ++ " } t).symm\n\n"
  let _ := homT
  return s
def receipts (root : Name) : MetaM (List String) := do
  let (_, blockName, block) ← readBlock root
  let (label, _, _) := block.head!
  let low := lowerFirst blockName
  return [s!"{low}Build_view", "cata_ofLayer_view", s!"sizeOf_{low}Kids", "cata_ofLayer_inv",
    "foldMap_head_eq_cata", "foldMap_eq_cata", s!"cata_fusion_{label}", s!"cata_prod_{label}"]

end Extras


structure Args where
  group : String := "Fold"
  imports : List String := []
  out : Option String := none
  headerOut : Option String := none
  append : Option String := none
  kinds : List (String × String) := []
  types : List String := []
  /-- Emit only the generic fold families of each (plain) block, into `ns` (probe U). -/
  extras : Bool := false
  ns : Option String := none

partial def parseArgs : List String → Args → Except String Args
  | [], a => .ok a
  | "--group" :: g :: rest, a => parseArgs rest { a with group := g }
  | "--imports" :: i :: rest, a =>
    parseArgs rest { a with imports := (i.splitOn ",").filter (· != "") }
  | "--out" :: o :: rest, a => parseArgs rest { a with out := some o }
  | "--header-out" :: o :: rest, a => parseArgs rest { a with headerOut := some o }
  | "--append" :: p :: rest, a => parseArgs rest { a with append := some p }
  | "--extras" :: rest, a => parseArgs rest { a with extras := true }
  | "--namespace" :: n :: rest, a => parseArgs rest { a with ns := some n }
  | "--kind" :: k :: rest, a =>
    match k.splitOn "=" with
    | [ty, kind] => if ty.isEmpty || kind.isEmpty then .error s!"--kind {k}: expected <Type>=<kind>"
      else parseArgs rest { a with kinds := a.kinds ++ [(ty, kind)] }
    | _ => .error s!"--kind {k}: expected <Type>=<kind>"
  | t :: rest, a =>
    if t.startsWith "--" then
      if rest.isEmpty then .error s!"{t} needs a value" else .error s!"unknown option {t}"
    else parseArgs rest { a with types := a.types ++ [t] }

def runExtras (args : Args) : MetaM (Array String) := do
  let ns := args.ns.getD "Effect4.Program"
  let outPath := (args.headerOut.orElse (fun _ => args.out) |>.getD "<stdout>").replace "\\" "/"
  let head := "lake env lean -M 4096 --run tools/Effect4Gen/Fold.lean --extras --group " ++ args.group
    ++ " --imports " ++ String.intercalate "," args.imports ++ " --out " ++ outPath
    ++ (match args.ns with | some n => " --namespace " ++ n | none => "")
    ++ (match args.append with | some p => " --append " ++ p.replace "\\" "/" | none => "")
    ++ String.join (args.types.map fun t => " " ++ t)
  let mut lines : Array String := #[
    "-- GENERATED by tools/Effect4Gen/Fold.lean (--extras) from the Lean environment. Do not edit.",
    "-- Regenerate:", "--   " ++ head]
  lines := lines ++ (args.imports.map fun i => s!"import {i}").toArray
  lines := lines ++ #["", "set_option autoImplicit false", "", "namespace " ++ ns, "",
    "open Effect4.Program", "", "universe u v w", "", Extras.helpers]
  let mut receipts : List String := []
  for t in args.types do
    lines := lines.push (← Extras.emitExtras t.toName)
    receipts := receipts ++ (← Extras.receipts t.toName)
  lines := lines ++ #["/-! ## Receipts -/", ""]
  for r in receipts do lines := lines.push s!"#print axioms {r}"
  lines := lines ++ #["", "end " ++ ns, ""]
  if let some p := args.append then
    let txt ← IO.FS.readFile p
    lines := lines ++ (txt.splitOn "\n").toArray.map (·.replace "\r" "")
  return lines

def run (args : Args) : MetaM (Array String) := do
  if args.extras then return ← runExtras args
  -- The blocks first: the emitted header depends on whether any of them has a monadic half,
  -- and the namespace is the first carrier's own prefix.
  let mut blockTexts : Array String := #[]
  let mut allReceipts : List String := []
  let mut anyMonadic := false
  let mut emittedAux : List String := []
  let namespaceName :=
    match args.types.head? with
    | some t => ((t.splitOn "@").head!).toName.getPrefix
    | none => `Effect4.Program
  for t in args.types do
    let root := t.toName
    -- `--kind <Type>=elim[:<prefix>]`: the nested companions instead of the fold
    match args.kinds.find? (fun (ty, k) => ty == t && (k == "elim" || k.startsWith "elim:")) with
    | some (_, k) =>
      let pfx := if k.startsWith "elim:" then some (k.drop 5).toString else none
      blockTexts := blockTexts.push (← Elim.emitElim root pfx)
      continue
    | none => pure ()
    let (_, _, block) ← readBlock root
    if blockNested block then
      let (blockText, blockReceipts, aux) ← emitNestedBlock namespaceName root emittedAux
      emittedAux := aux
      blockTexts := blockTexts.push blockText
      allReceipts := allReceipts ++ blockReceipts
    else
      anyMonadic := true
      let (blockText, blockReceipts) ← emitBlock root
      blockTexts := blockTexts.push blockText
      allReceipts := allReceipts ++ blockReceipts

  let mut lines : Array String := #[]
  let outPath := (args.headerOut.orElse (fun _ => args.out) |>.getD "<stdout>").replace "\\" "/"
  let head := "lake env lean -M 4096 --run tools/Effect4Gen/Fold.lean --group " ++ args.group
    ++ " --imports " ++ String.intercalate "," args.imports
    ++ " --out " ++ outPath
    ++ (match args.append with | some p => " --append " ++ p.replace "\\" "/" | none => "")
    ++ String.join (args.kinds.map fun (t, k) => " --kind " ++ t ++ "=" ++ k)
  let mut cmdLines : Array String := #["--   " ++ head ++ " \\"]
  let mut cur := "--    "
  for t in args.types do
    if cur.length + t.length + 1 > 96 then
      cmdLines := cmdLines.push (cur ++ " \\")
      cur := "--    " ++ t
    else
      cur := cur ++ " " ++ t
  cmdLines := cmdLines.push cur
  lines := lines ++ #["-- GENERATED by tools/Effect4Gen/Fold.lean from the Lean environment. Do not edit.",
    "-- Regenerate (tools/Effect4Gen/Driver.lean runs this for every group; --verify refuses a diff):"]
  lines := lines ++ cmdLines
  if let some p := args.append then
    let rep := p.replace "\\" "/"
    lines := lines.push s!"-- Acceptance guards appended verbatim from: {rep}"
  lines := lines ++ (args.imports.map fun i => s!"import {i}").toArray
  lines := lines ++ #[
    "",
    "set_option autoImplicit false",
    "",
    "namespace " ++ namespaceName.toString,
    "",
    "universe u v w",
    ""
  ]
  if anyMonadic then
    lines := lines ++ #[
      "/-- A monad morphism: a family of maps `M α → N α` that preserves `pure` and `bind`.",
      "Lean core has no such class and this estate does not depend on Mathlib, so the",
      "structure is emitted here, once, beside the monadic folds that quantify over it.",
      "The naturality of `foldM_*` needs exactly these two equations and no monad law. -/",
      "structure MonadMorphism (M : Type u → Type v) (N : Type u → Type w)",
      "    [Monad M] [Monad N] where",
      "  toFun : ∀ {α}, M α → N α",
      "  map_pure : ∀ {α} (a : α), toFun (pure a) = pure a",
      "  map_bind : ∀ {α β} (x : M α) (f : α → M β),",
      "    toFun (x >>= f) = toFun x >>= fun a => toFun (f a)",
      ""
    ]

  for blockText in blockTexts do
    lines := lines.push blockText

  if args.types.contains "Effect4.Program.Eff" then
    let (frontierText, frontierReceipts) ← emitFrontier `Effect4.Program.Eff [
      `Effect4.Program.Eff, `Effect4.Program.Stmt, `Effect4.Program.Stmts,
      `Effect4.Program.Effs, `Effect4.Program.ActionTerm]
    lines := lines.push frontierText
    allReceipts := allReceipts ++ frontierReceipts

  if !allReceipts.isEmpty then
    lines := lines ++ #["/-! ## Receipts -/", ""]
  for r in allReceipts do
    lines := lines.push s!"#print axioms {r}"
  lines := lines ++ #["", "end " ++ namespaceName.toString, ""]

  if let some p := args.append then
    let txt ← IO.FS.readFile p
    lines := lines ++ (txt.splitOn "\n").toArray.map (·.replace "\r" "")

  return lines

end Effect4Gen.Fold

open Effect4Gen.Fold in
def main (argv : List String) : IO Unit := do
  let args ← match parseArgs argv {} with
    | .ok a => pure a
    | .error e => throw (IO.userError e)
  if args.imports.isEmpty then
    throw (IO.userError "--imports names the modules the emitted file imports; none given")
  if args.types.isEmpty then
    throw (IO.userError "no types to generate")
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules (args.imports.map fun i => { module := i.toName }).toArray {} 0
  let ctx : Core.Context := { fileName := "<gen>", fileMap := default }
  let act : MetaM Unit := do
    let lines ← run args
    let stamp := Tools.GeneratedStamp.note "tools/Effect4Gen/Fold.lean"
    let text := "-- " ++ stamp ++ "\n" ++ String.intercalate "\n" lines.toList ++ "\n"
    match args.out with
    | some p => IO.FS.writeFile p text
    | none => IO.println text
  let _ ← (act.run' {}).toIO ctx { env := env }
