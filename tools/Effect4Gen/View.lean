import Lean
import Tools.GeneratedStamp

/-!
# Effect4Gen.View — the relational view of `Ty` (tooling plan 1.4)

From the constructor declarations of `Ty` and the variance table read off rc.112
(`tools/Effect4Gen/variances.json`, `tools/Tools/Variances.lean`), nothing hand-listed:

* `Variance`, `Variance.holds` — how a relation reads a recursive argument (or the core's, when
  the core declares `Ty.Variance` for a head whose arguments read a declared variance by name).
* `Ty.args : Ty → List (Variance × Ty)` — the immediate children with the variance the order
  reads them at, a head of variable arity included (below).
* `Ty.sameHead`, `Ty.topRule`, `Ty.argsBelow` — the head test and the top rule; and the
  order's cross-head rules, from one of two sources (below): today's literal rule `Ty.litRule`,
  or the core's leaf-order table.
* `Ty.sub_eq_args` — **the** law: between two members that are neither a cross-head rule nor the
  top, `sub` is the variance-wise comparison of corresponding arguments. Everything a relational
  proof needs to know about `Ty`'s constructors, in one statement, so the proofs of the order
  stop naming constructors and a new one costs a declared variance line instead of an arm in
  every proof.
* `Ty.sameHead_refl/symm/trans`, `Ty.args_congr`, `Ty.sizeOf_args`, `Ty.eq_of_sameHead`,
  `Ty.argsBelow_refl`, `Variance.holds_trans`, `Variance.holds_antisymm` — the small laws those
  proofs stand on.
* `Effect4.Program.AdmitsSub` — one field per constructor and one per cross-head rule: what an
  admission algebra must satisfy for its fold to respect `sub` (tooling plan 1.5;
  `Laws/Program/Admits.lean` proves `cata_admits_sub` from it, once).

## Heads of variable arity (decisions row 171; probe Q, Q2)

Three kinds are read from the declaration, each needing a `heads` row with an arity word in
`variances.json`: a field list (`List (String × Ty)` or `List (String × Ty × P)`; its names
and modifiers in canonical order are the head's payload, its children read through the core's
`canon`), an item list (`List Ty`; the length is the head), and an applied head (`String` then
`List Ty`; each argument at the named declaration's variance, `argVariance`). The dispatch's
case numbers are computed from the heads, and `eq_of_sameHead`/`argsBelow_antisymm` gain the
canonical-head premises (`headCanon`). A family with no such head gets today's text.

## The order's cross-head rules: one table (decisions row 177; probe P, question 3)

When the core declares the leaf-order table — `Ty.leafEdges : List (LeafHead × LeafHead)` over
`Ty.LeafHead`, with `LeafHead.all`, `leafHead`, `leafReach`, `leafLe`, `leafRule` consulted by
`sub` before its rows, and the four `sub` lemmas `leafRule_of_left_none`,
`leafRule_of_right_none`, `ite_leafRule_false`, `sub_of_leafRule` — the view reads the table
from the environment, refuses it if its closure is cyclic, and emits the table's laws, each by
`decide` over `LeafHead.all` (`leafLe_trans`, `leafLe_antisymm`, `leafLe_iff_path`,
`leafRule_trans`, `leafRule_asymm`, …), `leafHead_facts` per leaf head, one probe per ordered
pair of leaf heads, and the order's laws restated over the table: `sub_eq_args` and
`sub_eq_false_of_not_sameHead` take `hleaf : leafRule a b = false`, and
`sub_eq_leafRule_of_not_sameHead` says `sub` at two different heads IS the declared edge — false
exactly where the table declares none. A new edge is a row of the core's table: no arm of `sub`,
no line of this generator. When the core declares no table (the tree until the wave's append),
the one cross-head rule is today's literal rule `lit < string` and the view is today's text, byte
for byte (`litRule` and its three lemmas).

## Why the emitted file lives under the Laws

`sub_eq_args`'s one proof is `fun_cases Ty.sub a b` and one `aesop` call, and **nothing under
the core root `Effect4` imports aesop** — that is what keeps the core's import closure, and the
LCNF/OCaml pipeline cut from it, free of proof search (`lakefile.toml`, the aesop require). The
view is proof-only: no runtime reader, no face and no emitter reads `Ty.args`. So the output is
`src/Effect4/Laws/Program/TyView.lean`, and `Ty.args` stays out of the case-site policy and out
of the core's exhaustiveness inventory.

## What the generator refuses

* a constructor with a recursive (`Ty`-typed) field and no row in the variance table's `heads`,
  or a row whose variance list is not the constructor's recursive arity — a new parametrised
  constructor cannot be generated against a guess;
* a `heads` row naming no constructor of `Ty`;
* a non-recursive field whose type is not one `sameHead` knows how to compare (`String`, `Nat`),
  so a new payload sort is named rather than dropped from the head comparison;
* a field that is not first-order, which the carrier rule of `Ty.lean`'s header already refuses;
* a head of variable arity whose row has no arity word (or the wrong one), a list of children in
  a shape the view does not read, or a missing `canon`/`argVariance` it reads through;
* a leaf-order table whose closure is cyclic (two different heads each below the other: the
  order would not be antisymmetric), an edge from a head to itself, a `LeafHead` constructor
  that names no childless constructor of `Ty` (or names `never`, `union` or `unknown`, the
  structural rules), or a table whose companions in the core are missing.

The *semantic* check — that `sub`'s arm really is the variance-wise comparison of corresponding
positions — is emitted rather than performed here, and is stronger for it. The file carries one
`#guard` pair per position per head (a covariant position admits `lit "a"` below `string` and
not the reverse; a contravariant one the reverse; an invariant one neither) and one crossing
probe per head of arity two or more (distinct atoms at every position, which answers `false`
when the arms are positional and `true` when two are compared out of order); and
`sub_eq_args`'s own proof fails outright if `args` disagrees with `sub`. A wrong table therefore
fails `python3 scripts/generate.py --only derived`, which builds each emitted module after
installing it.

The emitted proofs use `aesop` or `simp only`, never `first`/`try`/`simp_all`: the output is
audited source under `src/Effect4/Laws` and is counted by the proof-shape ratchet.
-/

open Lean Meta Elab

namespace Effect4Gen.View

/-! ## The variance table -/

inductive Variance where
  | co | contra | inv
deriving BEq, Repr, Inhabited

def Variance.text : Variance → String
  | .co => "co"
  | .contra => "contra"
  | .inv => "inv"

def Variance.ofText : String → Option Variance
  | "co" => some .co
  | "contra" => some .contra
  | "inv" => some .inv
  | _ => none

structure Head where
  /-- The `Ty` constructor's short name. -/
  name : String
  variance : List Variance
  /-- Where the declaration comes from, for the emitted comment. -/
  cite : String
  /-- `"arity"`: `""` for a fixed head; `"each"` (one variance read at every child) or
  `"byName"` (each argument at the named declaration's variance) for a head of variable arity. -/
  arity : String := ""
deriving Repr

/-- The `heads` rows of `tools/Effect4Gen/variances.json`. A row with an unknown variance word
is refused rather than defaulted. -/
def readHeads (text : String) : Except String (List Head) := do
  let j ← Json.parse text
  let fmt ← j.getObjValAs? String "format"
  unless fmt == "effect4-variances-v1" do
    throw s!"variances.json: unknown format {fmt}"
  let arr ← (← j.getObjVal? "heads").getArr?
  let mut out : List Head := []
  for row in arr do
    let name ← row.getObjValAs? String "head"
    let vs ← (← row.getObjVal? "variance").getArr?
    let mut variance : List Variance := []
    for v in vs do
      let w ← v.getStr?
      let some v := Variance.ofText w
        | throw s!"variances.json: head {name} has variance word {w}, which is not co/contra/inv"
      variance := variance ++ [v]
    let cite :=
      match row.getObjValAs? String "cite" with
      | .ok c => c
      | .error _ =>
        if (row.getObjValAs? String "source").toOption == some "declarations" then
          "rc.112's declared variances, by name (Ty.declaredVariance)"
        else (row.getObjValAs? String "spelling").toOption.getD "(the printer's spelling)"
    let arity ← match row.getObjVal? "arity" with
      | .ok v => do
        let a ← v.getStr?
        unless a == "each" || a == "byName" do
          throw s!"variances.json: head {name} has arity {a}; the arity words are `each` and `byName`"
        pure a
      | .error _ => pure ""
    out := out ++ [({ name := name, variance := variance, cite := cite, arity := arity } : Head)]
  return out

/-! ## The constructor declarations -/

/-- One field of a constructor: a `Ty` child, a payload `sameHead` compares by `==`, a list of
`Ty` children (`List Ty`), or a field list `List (String × Ty)`/`List (String × Ty × P)` whose
`Ty` sits at the selector `child`, its payload components at `payloads` (selector, type), the
element's printed type with the member written `{M}`. -/
inductive Field where
  | child (name : String)
  | payload (name : String) (ty : String)
  | childList (name : String)
  | fieldList (name : String) (child : String) (payloads : List (String × String)) (elem : String)
deriving Repr

/-- A head of variable arity, as the view reads it. -/
inductive VarKind where
  /-- a field list read in canonical order (`Ty.canon`), its payloads the head (`record`) -/
  | fields (nm ch : String) (ps : List (String × String)) (elem : String)
  /-- a `List Ty` at one variance, position the order, the arity the head (`tuple`) -/
  | items (nm : String)
  /-- a name and a `List Ty`, argument `i` at the name's declared variance (`app`) -/
  | applied (pn nm : String)
deriving Repr

structure Ctor where
  name : String
  fields : List Field
deriving Repr

def Ctor.children (c : Ctor) : List String :=
  c.fields.filterMap fun f => match f with | .child n => some n | _ => none

def Ctor.payloads (c : Ctor) : List (String × String) :=
  c.fields.filterMap fun f => match f with | .payload n t => some (n, t) | _ => none

/-- The constructor's variable kind, when it has one: exactly one field list, exactly one `List
Ty`, or a `String` name followed by one `List Ty`. -/
def Ctor.varKind? (c : Ctor) : Option VarKind :=
  match c.fields with
  | [.fieldList nm ch ps e] => some (.fields nm ch ps e)
  | [.childList nm] => some (.items nm)
  | [.payload pn "String", .childList nm] => some (.applied pn nm)
  | _ => none

/-- Does the constructor hold a list of children in a shape the view does not read? -/
def Ctor.unreadList (c : Ctor) : Bool :=
  c.varKind?.isNone && c.fields.any fun f => match f with
    | .childList _ | .fieldList .. => true
    | _ => false

/-- A field-list element's payload as an expression of the element `p`. -/
def payText (ps : List (String × String)) : String :=
  match ps with
  | [(sel, _)] => "p" ++ sel
  | _ => "(" ++ String.intercalate ", " (ps.map fun q => "p" ++ q.1) ++ ")"

/-- The payload sorts `sameHead` can compare. A field of any other type is refused by name. -/
def knownPayload : List String := ["String", "Nat"]

/-- The payload sorts a field-list element may carry beside its name. -/
def knownElemPayload : List String := ["String", "Nat", "Bool"]

def shortName (n : Name) : String := n.componentsRev.head!.toString

def srcOf (e : Expr) : MetaM String := do
  withOptions (fun o => (o.setBool `pp.fullNames true).setBool `pp.universes false) do
    return toString (← ppExpr e)

/-- A field list `List (String × Ty)` or `List (String × Ty × P)`, `P` a known element payload:
the child's selector, the payload selectors with their types, and the element type with the
member written `{M}`. `none` for any other type. -/
def fieldElem (root : Name) (ty : Expr) : MetaM (Option (String × List (String × String) × String)) := do
  let ty ← whnfR ty
  unless ty.isAppOfArity ``List 1 do return none
  let e ← whnfR ty.appArg!
  unless e.isAppOfArity ``Prod 2 do return none
  let a := e.appFn!.appArg!
  let b := e.appArg!
  unless (← srcOf a) == "String" do return none
  if b.isConstOf root then return some (".2", [(".1", "String")], "String × {M}")
  if b.isAppOfArity ``Prod 2 && b.appFn!.appArg!.isConstOf root then
    let p ← srcOf b.appArg!
    if knownElemPayload.contains p then
      return some (".2.1", [(".1", "String"), (".2.2", p)], "String × {M} × " ++ p)
  return none

/-- `Ty`'s constructors with their fields: the walk of `Fold.readBlock`/`Main.ctorFields`. -/
def readCtors (root : Name) : MetaM (List Ctor) := do
  let iv ← getConstInfoInduct root
  let mut out : List Ctor := []
  for c in iv.ctors do
    let ci ← getConstInfoCtor c
    let fields ← forallBoundedTelescope ci.type (ci.numParams + ci.numFields) fun xs _ => do
      let mut acc : List Field := []
      let mut i : Nat := 0
      for x in xs[ci.numParams:] do
        let ty ← inferType x
        let nm ← x.fvarId!.getUserName
        let nm := if nm.toString.isEmpty then s!"a{i}" else nm.toString
        match ty.getAppFn with
        | .const n _ =>
          if n == root then
            acc := acc ++ [Field.child nm]
          else if ty.isAppOfArity ``List 1 && ty.appArg!.isConstOf root then
            acc := acc ++ [Field.childList nm]
          else if let some fl ← fieldElem root ty then
            let (ch, ps, e) := fl
            acc := acc ++ [Field.fieldList nm ch ps e]
          else
            let tyText ← srcOf ty
            unless knownPayload.contains tyText do
              throwError "View: constructor {c} field {nm} has type {tyText}, which `sameHead` \
                does not know how to compare; add it to `knownPayload` in \
                tools/Effect4Gen/View.lean"
            acc := acc ++ [Field.payload nm tyText]
        | _ =>
          throwError "View: constructor {c} field {nm} is not first-order; the carrier rule in \
            src/Effect4/Program/Ty.lean's header refuses it"
        i := i + 1
      return acc
    out := out ++ [({ name := shortName c, fields := fields } : Ctor)]
  return out

/-! ## The leaf-order table (decisions row 177)

Read from the environment when the core declares it, never from a file: `sub` consults the same
declaration (`leafRule`), so the view cannot state laws about a table the order does not read. -/

/-- The core's leaf-order table: the leaf heads in `LeafHead`'s declaration order (each the short
name of the `Ty` constructor it stands for) and the declared edges, both by short name. -/
structure LeafTable where
  heads : List String
  edges : List (String × String)
deriving Repr

/-- What the emitted laws read in the core beside the table, under `Ty`. -/
def leafCompanions : List Name :=
  [`LeafHead, `LeafHead.all, `leafHead, `leafEdges, `leafReach, `leafLe, `leafRule,
   `leafRule_of_left_none, `leafRule_of_right_none, `ite_leafRule_false, `sub_of_leafRule]

/-- A `LeafHead` constructor constant, by its short name. -/
def leafConst? (e : Expr) : Option String :=
  match e.consumeMData with
  | .const n _ => some (shortName n)
  | _ => none

/-- A reduced list literal of leaf-head pairs, `[(x, y), …]`. The fuel bounds the walk; a table
longer than it is refused rather than truncated. -/
def readEdgeList : Nat → Expr → MetaM (List (String × String))
  | 0, _ => throwError "View: `leafEdges` is longer than the reader's bound (1024 edges)"
  | fuel + 1, e => do
    let e := e.consumeMData
    if e.isAppOfArity ``List.nil 1 then return []
    unless e.isAppOfArity ``List.cons 3 do
      throwError "View: `leafEdges` does not reduce to a list literal of pairs: {e}"
    let p := (e.getArg! 1).consumeMData
    let some x := (if p.isAppOfArity ``Prod.mk 4 then leafConst? (p.getArg! 2) else none)
      | throwError "View: an element of `leafEdges` is not a pair of `LeafHead` constructors: {p}"
    let some y := leafConst? (p.getArg! 3)
      | throwError "View: an element of `leafEdges` is not a pair of `LeafHead` constructors: {p}"
    return (x, y) :: (← readEdgeList fuel (e.getArg! 2))

/-- The core's table, when it declares one (`<T>.leafEdges`); `none` otherwise, and then the one
cross-head rule is today's literal rule. A table with a companion missing is refused by name. -/
def readLeafTable (T : Name) : MetaM (Option LeafTable) := do
  let env ← getEnv
  unless env.contains (T ++ `leafEdges) do return none
  for n in leafCompanions do
    unless env.contains (T ++ n) do
      throwError "View: the core declares `{T ++ `leafEdges}` but not `{T ++ n}`, which the \
        table's laws read (decisions row 177; probe P's `P2Ty.lean:666-722`, `:1140-1160`)"
  let heads := (← getConstInfoInduct (T ++ `LeafHead)).ctors.map shortName
  let edges ← readEdgeList 1024 (← reduce (mkConst (T ++ `leafEdges)))
  return some { heads, edges }

/-- Every head the table's closure reaches from `x` (`x` itself included). -/
def LeafTable.reach (t : LeafTable) (x : String) : List String := Id.run do
  let mut seen : List String := [x]
  let mut frontier : List String := [x]
  for _ in [:t.heads.length + 1] do
    let next := (frontier.flatMap fun a =>
      t.edges.filterMap fun (u, v) => if u == a && !seen.contains v then some v else none).eraseDups
    if next.isEmpty then break
    seen := seen ++ next
    frontier := next
  return seen

/-- The closure: `x ⊑ y` when `y` is reachable from `x`. -/
def LeafTable.le (t : LeafTable) (x y : String) : Bool := (t.reach x).contains y

/-- The refusals that need the constructors: a head that is not a childless constructor of `Ty`
or names a structural rule, an edge from a head to itself, a cyclic closure. -/
def LeafTable.check (t : LeafTable) (T : Name) (ctors : List Ctor) : Except String Unit := do
  for h in t.heads do
    if ["never", "union", "unknown"].contains h then
      throw s!"View: `{T}.LeafHead.{h}` names `{h}`, one of the order's structural rules \
        (the empty union, the union, the top); the leaf table relates leaf heads only"
    match ctors.find? (·.name == h) with
    | none => throw s!"View: `{T}.LeafHead.{h}` names no constructor of `{T}`"
    | some c =>
      unless c.children.isEmpty && c.varKind?.isNone do
        throw s!"View: `{T}.LeafHead.{h}` names `{T}.{h}`, which has children; the leaf table \
          relates childless heads only (their congruence is equality)"
  for (x, y) in t.edges do
    if x == y then
      throw s!"View: `{T}.leafEdges` declares `{x}` below itself; an edge joins two different heads"
  for x in t.heads do
    for y in t.heads do
      if x != y && t.le x y && t.le y x then
        throw s!"View: the leaf-order table `{T}.leafEdges` is cyclic: its closure puts `{x}` \
          below `{y}` and `{y}` below `{x}`, so the order would not be antisymmetric \
          (`leafLe_antisymm`); the edges are {t.edges}"

/-! ## The join of the two, and the refusals -/

structure Row where
  ctor : Ctor
  /-- `none` when the constructor has no `Ty` child, so it needs no variance row. -/
  head : Option Head

/-- The one place a new constructor is refused: a `Ty` child with no declared variance. -/
def rows (ctors : List Ctor) (heads : List Head) : Except String (List Row) := Id.run do
  let mut out : List Row := []
  for c in ctors do
    let n := c.children.length
    if c.unreadList then
      return .error s!"View: `Ty.{c.name}` holds a list of children in a shape the view does not \
        read (one field list, one `List Ty`, or a `String` name and a `List Ty`)"
    match heads.find? (fun h => h.name == c.name) with
    | some h =>
      if let some k := c.varKind? then
        let ok := match k with
          | .fields .. | .items _ => h.arity == "each" && h.variance == [Variance.co]
          | .applied .. => h.arity == "byName"
        unless ok do
          return .error s!"View: `Ty.{c.name}` has variable arity: a field list or a `List Ty` needs \
            a row with \"arity\": \"each\" and the one variance co; a name and a `List Ty` needs \
            \"arity\": \"byName\" (tools/Effect4Gen/variances.json)"
        out := out ++ [({ ctor := c, head := some h } : Row)]
        continue
      if h.arity != "" then
        return .error s!"View: `Ty.{c.name}` has fixed arity but its row says \"arity\": \"{h.arity}\""
      if h.variance.length != n then
        return .error s!"View: `Ty.{c.name}` has {n} recursive field(s) but \
          tools/Effect4Gen/variances.json declares {h.variance.length} variance(s) for it"
      out := out ++ [({ ctor := c, head := some h } : Row)]
    | none =>
      if n != 0 || c.varKind?.isSome then
        return .error s!"View: `Ty.{c.name}` has {n} recursive field(s) and no row in \
          tools/Effect4Gen/variances.json's `heads`; declare its variance from rc.112 \
          (tools/Tools/Variances.lean) before generating the view"
      out := out ++ [({ ctor := c, head := none } : Row)]
  for h in heads do
    unless ctors.any (fun c => c.name == h.name) do
      return .error s!"View: tools/Effect4Gen/variances.json declares a variance for \
        `{h.name}`, which is no constructor of `Ty`"
  return .ok out

/-- Constructors `sameHead` must answer `false` on, with the reason. `union` is not a
congruence: the order distributes it on the left and chooses on the right, so it is row
structure and not a head. -/
def notCongruent : List (String × String) :=
  [("union", "the order distributes a union on the left and chooses on the right " ++
      "(`sub_union_left`/`sub_union_right`), so it is row structure and not a head")]

/-! ## The emitter

Every block is a list of lines joined at the end, so no emitted text is a multi-line Lean
string literal. -/

private def join (ls : List String) : String := String.intercalate "\n" ls

private def repeatStr (n : Nat) (s : String) : List String := (List.range n).map fun _ => s

private def patOf (c : Ctor) (suffix : String) : String :=
  if c.fields.isEmpty then s!".{c.name}"
  else s!".{c.name} " ++ String.intercalate " " (c.fields.map fun f =>
    match f with
      | .child n => n ++ suffix
      | .payload n _ => n ++ suffix
      | .childList n => n ++ suffix
      | .fieldList n _ _ _ => n ++ suffix)

def emitVariance (coreVariance : Bool := false) : List String :=
  if coreVariance then
    [ "-- `Variance` and `Variance.holds` are the core's (`TyVariance`, generated from",
      "-- variances.json), which `sub` itself reads for a reference's declared variances.", "" ]
  else
  [ "/-- How a relation reads a recursive argument: as rc.112 declares the parameter",
    "(`Fiber<out A, out E>` covariant, `Ref<in out A>` invariant; decisions row 55). -/",
    "inductive Variance where",
    "  | co",
    "  | contra",
    "  | inv",
    "deriving DecidableEq, Repr",
    "",
    "/-- A Boolean relation lifted through a variance. -/",
    "def Variance.holds (r : Ty → Ty → Bool) : Variance → Ty → Ty → Bool",
    "  | .co,     x, y => r x y",
    "  | .contra, x, y => r y x",
    "  | .inv,    x, y => r x y && r y x",
    "" ]

def emitArgs (rs : List Row) : List String := Id.run do
  let mut s : List String :=
    [ "/-- The immediate `Ty` children of a type, each with the variance the order reads it at.",
      "Not one row of this is declared here: every variance comes from",
      "`tools/Effect4Gen/variances.json`, which `tools/Tools/Variances.lean` reads off the",
      "vendored rc.112 sources. -/",
      "def args : Ty → List (Variance × Ty)" ]
  for r in rs do
    let kids := r.ctor.children
    if let some k := r.ctor.varKind? then
      let cite := (r.head.map (fun h => s!"  -- {h.cite}")).getD ""
      let line := match k with
        | .fields _ ch _ _ => s!"  | .{r.ctor.name} fs => (canon fs).map fun p => (.co, p{ch}){cite}"
        | .items _ => s!"  | .{r.ctor.name} xs => xs.map fun x => (.co, x){cite}"
        | .applied _ _ => s!"  | .{r.ctor.name} n xs => xs.zipIdx.map fun p => (argVariance n p.2, p.1){cite}"
      s := s ++ [line]
      continue
    let body :=
      if kids.isEmpty then "[]"
      else
        let vs := (r.head.map (fun h => h.variance)).getD []
        "[" ++ String.intercalate ", "
          ((kids.zip vs).map fun p => s!"(.{p.2.text}, {p.1})") ++ "]"
    let cite := match r.head with
      | some h => if kids.isEmpty then "" else s!"  -- {h.cite}"
      | none => ""
    let c := r.ctor
    let lhs :=
      if c.fields.isEmpty then s!".{c.name}"
      else s!".{c.name} " ++ String.intercalate " " (c.fields.map fun f =>
        match f with | .child nm => nm | _ => "_")
    s := s ++ [s!"  | {lhs} => {body}{cite}"]
  return s ++ [""]

def emitSameHead (rs : List Row) : List String := Id.run do
  let mut s : List String :=
    [ "/-- Same constructor and equal non-recursive payload. -/",
      "def sameHead : Ty → Ty → Bool" ]
  for r in rs do
    let c := r.ctor
    if notCongruent.any (fun p => p.1 == c.name) then continue
    if let some k := c.varKind? then
      let lines := match k with
        | .fields _ _ ps _ =>
          [ s!"  | .{c.name} fs1, .{c.name} fs2 =>",
            s!"    decide ((canon fs1).map (fun p => {payText ps}) = (canon fs2).map (fun p => {payText ps}))" ]
        | .items _ =>
          [ s!"  | .{c.name} xs1, .{c.name} xs2 => decide (xs1.length = xs2.length)" ]
        | .applied _ _ =>
          [ s!"  | .{c.name} n1 xs1, .{c.name} n2 xs2 => decide (n1 = n2) && decide (xs1.length = xs2.length)" ]
      s := s ++ lines
      continue
    let ps := c.payloads
    let body :=
      if ps.isEmpty then "true"
      -- `decide (x = y)`, not `x == y`: at `String` and `Nat` the `LawfulBEq` instance reaches
      -- `Classical.choice`, and `decide` through the derived `DecidableEq` reaches no axiom
      else String.intercalate " && " (ps.map fun p => s!"decide ({p.1}1 = {p.1}2)")
    let side (suffix : String) : String :=
      if c.fields.isEmpty then s!".{c.name}"
      else s!".{c.name} " ++ String.intercalate " " (c.fields.map fun f =>
        match f with | .payload n _ => n ++ suffix | _ => "_")
    let l := side "1"
    let rgt := side "2"
    s := s ++ [s!"  | {l}, {rgt} => {body}"]
  for p in notCongruent do
    s := s ++ [s!"  -- `{p.1}` is deliberately absent: {p.2}"]
  return s ++ ["  | _, _ => false", ""]

def emitRules (hasTable : Bool := false) : List String :=
  if hasTable then
  [ "-- The order's cross-head rules are the core's leaf-order table (`leafEdges`, decisions",
    "-- row 177), which `sub` consults through `leafRule` before its rows; its laws are below.",
    "",
    "/-- The top (decisions row 46), the one rule beside the congruences that the leaf table does",
    "not hold (`sub_unknown`). -/",
    "def topRule : Ty → Ty → Bool",
    "  | _, .unknown => true",
    "  | _, _        => false",
    "",
    "/-- The variance-wise comparison of corresponding arguments. -/",
    "def argsBelow (r : Ty → Ty → Bool) (a b : Ty) : Bool :=",
    "  (a.args.zip b.args).all fun p => p.1.1.holds r p.1.2 p.2.2",
    "" ]
  else
  [ "/-- The literal rule: one of the order's rules between members that is not a congruence",
    "(`sub_lit_string`). -/",
    "def litRule : Ty → Ty → Bool",
    "  | .lit _, .string => true",
    "  | _, _            => false",
    "",
    "/-- The top (decisions row 46), the other one (`sub_unknown`). -/",
    "def topRule : Ty → Ty → Bool",
    "  | _, .unknown => true",
    "  | _, _        => false",
    "",
    "/-- The variance-wise comparison of corresponding arguments. -/",
    "def argsBelow (r : Ty → Ty → Bool) (a b : Ty) : Bool :=",
    "  (a.args.zip b.args).all fun p => p.1.1.holds r p.1.2 p.2.2",
    "" ]

/-- What heads of variable arity need beside the laws: the list facts their children are read
through (fixed text), the canonicity predicate (`headCanon`, `true` except at a field list), and
per field-list constructor the measure of a field and the field list from its payloads and
children. Empty when no head has variable arity, so the view of a family without one is
byte-identical to what the generator wrote before. -/
def emitVarHelpers (rs : List Row) : List String := Id.run do
  let vrs := rs.filter fun r => r.ctor.varKind?.isSome
  if vrs.isEmpty then return []
  let frs := vrs.filter fun r => match r.ctor.varKind? with | some (.fields ..) => true | _ => false
  let ars := vrs.filter fun r => match r.ctor.varKind? with | some (.applied ..) => true | _ => false
  let mut s : List String :=
    [ "/-! ### What a head of variable arity reads its children through -/",
      "",
      "/-- A list zipped with itself compares each child with itself, at any variance. -/",
      "theorem zip_self_all (r : Ty → Ty → Bool) (hr : ∀ x, r x x = true) :",
      "    ∀ (l : List (Variance × Ty)), (l.zip l).all (fun p => p.1.1.holds r p.1.2 p.2.2) = true",
      "  | [] => rfl",
      "  | (v, t) :: rest => by",
      "    simp only [List.zip_cons_cons, List.all_cons, zip_self_all r hr rest, Bool.and_true]",
      "    cases v <;> simp only [Variance.holds, hr, Bool.and_self]",
      "",
      "theorem map_const_eq {α β : Type} (c : β) {l l' : List α} (h : l.length = l'.length) :",
      "    l.map (fun _ => c) = l'.map (fun _ => c) := by",
      "  rw [List.map_const', List.map_const', h]",
      "",
      "/-- `all` over an attached list reads the values: `sub`'s variable arms attach for their",
      "termination, the view does not. -/",
      "theorem all_attach_eq {α : Type} (l : List α) (f : α → Bool) :",
      "    (l.attach.all fun x => f x.1) = l.all f := by",
      "  have h := List.all_map (l := l.attach) (f := Subtype.val) (p := f)",
      "  rw [List.attach_map_subtype_val] at h",
      "  exact h.symm",
      "" ] ++
    (if ars.isEmpty then [] else
    [ "/-- Two argument lists of one length are read at the same variances. -/",
      "theorem map_zipIdx_snd_eq {α β : Type} (f : Nat → β) {xs ys : List α}",
      "    (h : xs.length = ys.length) :",
      "    xs.zipIdx.map (fun p => f p.2) = ys.zipIdx.map (fun p => f p.2) := by",
      "  have hx : xs.zipIdx.map (fun p => f p.2) = (xs.zipIdx.map Prod.snd).map f := by",
      "    rw [List.map_map]; rfl",
      "  have hy : ys.zipIdx.map (fun p => f p.2) = (ys.zipIdx.map Prod.snd).map f := by",
      "    rw [List.map_map]; rfl",
      "  rw [hx, hy, List.zipIdx_map_snd, List.zipIdx_map_snd, h]",
      "",
      "theorem map_fst_zipIdx {α : Type} (l : List α) : l.zipIdx.map (fun p => p.1) = l :=",
      "  List.zipIdx_map_fst 0 l",
      "" ]) ++
    [ "/-- A head whose children are read in canonical order is in that order already. -/",
      "def headCanon : Ty → Bool" ]
  for r in frs do
    s := s ++ [s!"  | .{r.ctor.name} fs => decide (canon fs = fs)"]
  s := s ++ [ "  | _ => true", "",
    "theorem headCanon_of_args_nil {t : Ty} (h : t.args = []) : headCanon t = true := by" ]
  if frs.isEmpty then
    s := s ++ [ "  cases t <;> rfl", "" ]
  else
    s := s ++ [ "  cases t" ]
    for r in frs do
      s := s ++
        [ s!"  case {r.ctor.name} fs =>",
          "    have hf : fs = [] := canon_eq_nil (List.map_eq_nil_iff.mp h)",
          "    subst hf",
          "    rfl" ]
    s := s ++ [ "  all_goals rfl", "" ]
  for r in frs do
    let some (.fields _ ch ps elem) := r.ctor.varKind? | continue
    let el := elem.replace "{M}" "Ty"
    let c := r.ctor.name
    let triple := ch != ".2"
    s := s ++
      [ s!"/-- A field's type is smaller than its `{c}`'s field list. -/",
        s!"theorem sizeOf_field_lt_{c} \{p : {el}} \{fs : List ({el})} (h : p ∈ fs) :",
        s!"    sizeOf p{ch} < sizeOf fs := by",
        "  have hp : sizeOf p < sizeOf fs := List.sizeOf_lt_of_mem h",
        (if triple then "  obtain ⟨n, t, b⟩ := p" else "  obtain ⟨n, t⟩ := p"),
        "  simp only [Prod.mk.sizeOf_spec] at hp",
        "  simp only",
        "  omega",
        "",
        s!"/-- Two field lists with the same payloads and the same children are equal. -/",
        s!"theorem eq_of_fields_{c} :",
        s!"    ∀ \{l l' : List ({el})}, l.map (fun p => {payText ps}) = l'.map (fun p => {payText ps}) →",
        s!"      l.map (fun p => p{ch}) = l'.map (fun p => p{ch}) → l = l'",
        "  | [], [], _, _ => rfl",
        "  | [], _ :: _, h, _ => absurd h (List.cons_ne_nil _ _).symm",
        "  | _ :: _, [], h, _ => absurd h (List.cons_ne_nil _ _)" ] ++
      (if triple then
        [ "  | (a, b, c) :: l, (a', b', c') :: l', h1, h2 => by",
          "    simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at h1 h2",
          s!"    rw [h1.1.1, h1.1.2, h2.1, eq_of_fields_{c} h1.2 h2.2]" ]
       else
        [ "  | (a, b) :: l, (a', b') :: l', h1, h2 => by",
          "    simp only [List.map_cons, List.cons.injEq] at h1 h2",
          s!"    rw [h1.1, h2.1, eq_of_fields_{c} h1.2 h2.2]" ]) ++ [""]
  return s

/-- A closed term of a constructor, for a probe: a payload is `"a"` or `0` by its type. -/
def sampleOf (ctors : List Ctor) (c : String) : String :=
  match ctors.find? (·.name == c) with
  | some k =>
    if k.fields.isEmpty then s!".{c}" else
    let args := k.fields.map fun f => match f with
      | .payload _ "String" => "\"a\"" | .payload _ "Nat" => "0" | .payload _ _ => "default"
      | .child _ => ".nat" | .childList _ => "[]" | .fieldList .. => "[]"
    s!"(.{c} " ++ String.intercalate " " args ++ ")"
  | none => s!".{c}"

/-- The table's probes: at every ordered pair of different leaf heads, `sub` is the closure — an
edge accepted and its converse refused, a pair the closure derives (`nat ⊑ number` through
`int`) accepted, every other pair refused. A `sub` that disagrees with its own table makes this
file red. -/
def emitLeafProbes (ctors : List Ctor) (t : LeafTable) : List String := Id.run do
  let mut s : List String :=
    [ "/-! ### The leaf-order table's probes: at two different leaf heads, `sub` is the closure -/", "" ]
  for x in t.heads do
    for y in t.heads do
      if x == y then continue
      let le := t.le x y
      let why :=
        if t.edges.contains (x, y) then "  -- a declared edge"
        else if le then "  -- derived through the closure, not an entry"
        else if t.edges.contains (y, x) then "  -- the converse of a declared edge"
        else ""
      s := s ++ [s!"#guard {if le then "" else "!"}Ty.sub {sampleOf ctors x} {sampleOf ctors y}{why}"]
  return s ++ [""]

/-- The table's laws (probe P, `P3View.lean:666-826`), each over the finite head domain by
`decide` or from those: they name no edge, so a new edge regenerates them unchanged. The
`normalize` facts are emitted when the core declares `normalize`. -/
def emitLeafLaws (t : LeafTable) (hasNormalize : Bool) : List String :=
  let facts := if hasNormalize then "t.args = [] ∧ isMember t = true ∧ normalize t = t"
    else "t.args = [] ∧ isMember t = true"
  let factsPf := if hasNormalize then "⟨rfl, rfl, rfl⟩" else "⟨rfl, rfl⟩"
  let isMemberOf := if hasNormalize then ".2.1" else ".2"
  [ "/-! ### The leaf-order table's laws (decisions row 177)",
    "",
    "The closure's laws are checked over the finite head domain (`LeafHead.all`) by `decide`, so",
    "they are regenerated with the table and name no edge; a leaf head's type carries the facts the",
    "order's proofs read. Transcribed from probe P (`P3View.lean:666-826`). -/",
    "",
    "theorem LeafHead.mem_all (x : LeafHead) : x ∈ LeafHead.all := by",
    "  cases x <;> decide",
    "",
    "/-- The closure's specification: a path of declared edges. -/",
    "inductive LeafPath (edges : List (LeafHead × LeafHead)) : LeafHead → LeafHead → Prop",
    "  | refl (x : LeafHead) : LeafPath edges x x",
    "  | step {x y z : LeafHead} : (x, y) ∈ edges → LeafPath edges y z → LeafPath edges x z",
    "",
    "/-- The search finds only paths (any table, any fuel). -/",
    "theorem leafReach_sound (edges : List (LeafHead × LeafHead)) :",
    "    ∀ (n : Nat) (x y : LeafHead), leafReach edges n x y = true → LeafPath edges x y",
    "  | 0, x, y, h => by",
    "    rw [leafReach] at h",
    "    rw [of_decide_eq_true h]",
    "    exact .refl y",
    "  | n + 1, x, y, h => by",
    "    rw [leafReach, Bool.or_eq_true, List.any_eq_true] at h",
    "    rcases h with h | ⟨e, he, hstep⟩",
    "    · rw [of_decide_eq_true h]",
    "      exact .refl y",
    "    · rw [Bool.and_eq_true] at hstep",
    "      have hx : e.1 = x := of_decide_eq_true hstep.1",
    "      subst hx",
    "      exact .step he (leafReach_sound edges n e.2 y hstep.2)",
    "",
    "theorem leafLe_refl (x : LeafHead) : leafLe x x = true := by",
    "  cases x <;> rfl",
    "",
    "/-- **Transitivity of the leaf order** (checked over the finite domain). -/",
    "theorem leafLe_trans {x y z : LeafHead} (hxy : leafLe x y = true) (hyz : leafLe y z = true) :",
    "    leafLe x z = true := by",
    "  have h : ∀ x ∈ LeafHead.all, ∀ y ∈ LeafHead.all, ∀ z ∈ LeafHead.all,",
    "      leafLe x y = true → leafLe y z = true → leafLe x z = true := by decide",
    "  exact h x (LeafHead.mem_all x) y (LeafHead.mem_all y) z (LeafHead.mem_all z) hxy hyz",
    "",
    "/-- **The table is acyclic**, as the closure's antisymmetry (checked over the finite domain):",
    "what `sub`'s antisymmetry reads (`leafRule_asymm`) and its transitivity at a payload head",
    "(`leafRule_trans`). A cyclic table is refused before this file is written. -/",
    "theorem leafLe_antisymm {x y : LeafHead} (hxy : leafLe x y = true) (hyx : leafLe y x = true) :",
    "    x = y := by",
    "  have h : ∀ x ∈ LeafHead.all, ∀ y ∈ LeafHead.all,",
    "      leafLe x y = true → leafLe y x = true → x = y := by decide",
    "  exact h x (LeafHead.mem_all x) y (LeafHead.mem_all y) hxy hyx",
    "",
    "/-- Every declared edge is in the closure, and none is a loop. -/",
    "theorem leafLe_of_edge {x y : LeafHead} (h : (x, y) ∈ leafEdges) : leafLe x y = true := by",
    "  have hall : ∀ e ∈ leafEdges, leafLe e.1 e.2 = true := by decide",
    "  exact hall (x, y) h",
    "",
    "theorem leafEdge_ne {x y : LeafHead} (h : (x, y) ∈ leafEdges) : x ≠ y := by",
    "  have hall : ∀ e ∈ leafEdges, e.1 ≠ e.2 := by decide",
    "  exact hall (x, y) h",
    "",
    "/-- **The leaf order is the table's reflexive-transitive closure.** -/",
    "theorem leafLe_iff_path {x y : LeafHead} : leafLe x y = true ↔ LeafPath leafEdges x y := by",
    "  constructor",
    "  · exact leafReach_sound leafEdges _ x y",
    "  · intro h",
    "    induction h with",
    "    | refl x => exact leafLe_refl x",
    "    | step he _ ih => exact leafLe_trans (leafLe_of_edge he) ih",
    "",
    "/-- The acyclicity in path form: two paths that close a loop are both empty. -/",
    "theorem leafEdges_acyclic {x y : LeafHead} (hxy : LeafPath leafEdges x y)",
    "    (hyx : LeafPath leafEdges y x) : x = y :=",
    "  leafLe_antisymm (leafLe_iff_path.mpr hxy) (leafLe_iff_path.mpr hyx)",
    "",
    "/-- A leaf head's type is a childless member" ++
      (if hasNormalize then " and its own normal form" else "") ++ ": one case per leaf head. -/",
    "theorem leafHead_facts {t : Ty} {x : LeafHead} (h : leafHead t = some x) :",
    s!"    {facts} := by",
    "  cases t",
    s!"  case {String.intercalate " | " t.heads} => exact {factsPf}",
    "  all_goals cases h",
    "",
    "/-- The table's rule, unpacked. -/",
    "theorem leafRule_eq_true {a b : Ty} (h : leafRule a b = true) :",
    "    ∃ x y, leafHead a = some x ∧ leafHead b = some y ∧ x ≠ y ∧ leafLe x y = true := by",
    "  unfold leafRule at h",
    "  split at h",
    "  · rename_i x y hx hy",
    "    rw [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h",
    "    exact ⟨x, y, hx, hy, h.1, h.2⟩",
    "  · exact Bool.noConfusion h",
    "",
    "/-- The table's rule, packed. -/",
    "theorem leafRule_of_heads {a b : Ty} {x y : LeafHead} (ha : leafHead a = some x)",
    "    (hb : leafHead b = some y) (hne : x ≠ y) (hle : leafLe x y = true) : leafRule a b = true := by",
    "  unfold leafRule",
    "  rw [ha, hb]",
    "  show (!decide (x = y) && leafLe x y) = true",
    "  rw [decide_eq_false hne, hle]",
    "  rfl",
    "",
    "/-- A declared edge between two types' leaf heads is a rule of the order. -/",
    "theorem leafRule_of_edge {a b : Ty} {x y : LeafHead} (he : (x, y) ∈ leafEdges)",
    "    (ha : leafHead a = some x) (hb : leafHead b = some y) : leafRule a b = true :=",
    "  leafRule_of_heads ha hb (leafEdge_ne he) (leafLe_of_edge he)",
    "",
    "/-- The table's rule is between childless members. -/",
    "theorem leafRule_args {a b : Ty} (h : leafRule a b = true) :",
    "    a.args = [] ∧ b.args = [] ∧ isMember a = true ∧ isMember b = true := by",
    "  obtain ⟨x, y, hx, hy, -, -⟩ := leafRule_eq_true h",
    "  exact ⟨(leafHead_facts hx).1, (leafHead_facts hy).1, (leafHead_facts hx)" ++ isMemberOf ++ ",",
    "    (leafHead_facts hy)" ++ isMemberOf ++ "⟩",
    "",
    "/-- **The rule composes**: the closure is transitive, and the composite relates different",
    "heads because the table is acyclic. -/",
    "theorem leafRule_trans {a b c : Ty} (hab : leafRule a b = true) (hbc : leafRule b c = true) :",
    "    leafRule a c = true := by",
    "  obtain ⟨x, y, hx, hy, hxy, hlxy⟩ := leafRule_eq_true hab",
    "  obtain ⟨y', z, hy', hz, -, hlyz⟩ := leafRule_eq_true hbc",
    "  rw [hy] at hy'",
    "  cases hy'",
    "  refine leafRule_of_heads hx hz ?_ (leafLe_trans hlxy hlyz)",
    "  intro hxz",
    "  subst hxz",
    "  exact hxy (leafLe_antisymm hlxy hlyz)",
    "",
    "/-- The rule is asymmetric (the table is acyclic). -/",
    "theorem leafRule_asymm {a b : Ty} (h : leafRule a b = true) : leafRule b a = false := by",
    "  cases hba : leafRule b a with",
    "  | false => rfl",
    "  | true =>",
    "    obtain ⟨x, y, hx, hy, hxy, hlxy⟩ := leafRule_eq_true h",
    "    obtain ⟨y', x', hy', hx', -, hlyx⟩ := leafRule_eq_true hba",
    "    rw [hx] at hx'",
    "    rw [hy] at hy'",
    "    cases hx'",
    "    cases hy'",
    "    exact absurd (leafLe_antisymm hlxy hlyx) hxy",
    "",
    "/-- Neither side of a rule is the top. -/",
    "theorem leafRule_ne_unknown {a b : Ty} (h : leafRule a b = true) :",
    "    a ≠ .unknown ∧ b ≠ .unknown := by",
    "  obtain ⟨x, y, hx, hy, -, -⟩ := leafRule_eq_true h",
    "  refine ⟨?_, ?_⟩",
    "  · rintro rfl",
    "    cases hx",
    "  · rintro rfl",
    "    cases hy",
    "",
    "/-- A rule relates two different heads. -/",
    "theorem leafRule_sameHead {a b : Ty} (h : leafRule a b = true) : sameHead a b = false := by",
    "  cases hs : sameHead a b with",
    "  | false => rfl",
    "  | true =>",
    "    obtain ⟨x, y, hx, hy, hxy, -⟩ := leafRule_eq_true h",
    "    have hab : a = b := eq_of_sameHead_nil hs (leafHead_facts hx).1",
    "    subst hab",
    "    rw [hx] at hy",
    "    cases hy",
    "    exact absurd rfl hxy",
    "" ] ++
  (if hasNormalize then
  [ "/-- Both sides of a rule are their own normal forms. -/",
    "theorem leafRule_normalize {a b : Ty} (h : leafRule a b = true) :",
    "    normalize a = a ∧ normalize b = b := by",
    "  obtain ⟨x, y, hx, hy, -, -⟩ := leafRule_eq_true h",
    "  exact ⟨(leafHead_facts hx).2.2, (leafHead_facts hy).2.2⟩",
    "" ] else []) ++
  [ "/-- **Different heads: `sub` IS the declared edge.** At two members with different heads, not",
    "the top, the order answers the table's rule: `true` on the closure of a declared edge, `false`",
    "exactly where the table declares none (Codex, 19:30; probe Q's `sub_eq_edgeRule_of_not_sameHead`",
    "over probe P's table). -/",
    "theorem sub_eq_leafRule_of_not_sameHead (a b : Ty) (ha : isMember a = true)",
    "    (hb : isMember b = true) (htop : topRule a b = false) (hh : sameHead a b = false) :",
    "    sub a b = leafRule a b := by",
    "  cases hl : leafRule a b with",
    "  | true => exact sub_of_leafRule hl",
    "  | false => exact sub_eq_false_of_not_sameHead a b ha hb hl htop hh",
    "" ]

/-- The probes that make a wrong variance, or a crossed pair of arms, a red build. -/
def emitProbes (rs : List Row) : List String := Id.run do
  let atoms := [".nat", ".bool", ".unit", ".int"]
  let mut s : List String :=
    [ "/-! ### The variance probes",
      "",
      "One pair per position per head: a covariant position admits `lit \"a\"` below `string`",
      "and not the reverse, a contravariant one the reverse, an invariant one neither. Then one",
      "crossing probe per head of arity two or more: distinct atoms at every position, which",
      "answers `false` when the arms are positional and `true` when two are compared out of",
      "order. A variance row that does not match `sub`'s arm makes this file red, which makes",
      "`python3 scripts/generate.py --only derived` fail. -/",
      "" ]
  for r in rs do
    let some h := r.head | continue
    if let some k := r.ctor.varKind? then
      let c := r.ctor.name
      match k with
      | .fields _ ch ps _ =>
        let el (name ty : String) : String :=
          if ch == ".2" then s!"(\"{name}\", {ty})" else s!"(\"{name}\", {ty}, false)"
        let r_ (els : List String) : String := s!"(.{c} [" ++ String.intercalate ", " els ++ "])"
        s := s ++
          [ s!"-- `{c}`: every field co, read in canonical order; the head is the canonical payload list",
            s!"#guard Ty.sub {r_ [el "a" "(.lit \"a\")"]} {r_ [el "a" ".string"]}",
            s!"#guard !Ty.sub {r_ [el "a" ".string"]} {r_ [el "a" "(.lit \"a\")"]}",
            s!"#guard !Ty.sub {r_ [el "a" ".nat", el "b" ".bool"]} {r_ [el "a" ".bool", el "b" ".unit"]}",
            "-- TY-10's positive control: a permuted field list is below its canonical order, both ways",
            s!"#guard Ty.sub {r_ [el "b" ".nat", el "a" ".bool"]} {r_ [el "a" ".bool", el "b" ".nat"]}",
            s!"#guard Ty.sub {r_ [el "a" ".bool", el "b" ".nat"]} {r_ [el "b" ".nat", el "a" ".bool"]}",
            "-- names are the head's payload; width is not a rule",
            s!"#guard !Ty.sub {r_ [el "a" ".nat"]} {r_ [el "b" ".nat"]}",
            s!"#guard !Ty.sub {r_ [el "a" ".nat", el "b" ".nat"]} {r_ [el "a" ".nat"]}" ] ++
          (if ps.length > 1 then
            [ "-- a modifier is payload too: the exact rule does not put a required field below an optional one",
              s!"#guard !Ty.sub (.{c} [(\"a\", .nat, false)]) (.{c} [(\"a\", .nat, true)])" ]
           else []) ++ [""]
      | .items _ =>
        s := s ++
          [ s!"-- `{c}`: every item co, by position; the head is the arity",
            s!"#guard Ty.sub (.{c} [.lit \"a\", .nat]) (.{c} [.string, .nat])",
            s!"#guard !Ty.sub (.{c} [.string, .nat]) (.{c} [.lit \"a\", .nat])",
            s!"#guard !Ty.sub (.{c} [.nat, .bool]) (.{c} [.bool, .unit])",
            s!"#guard !Ty.sub (.{c} [.nat]) (.{c} [.nat, .nat])", "" ]
      | .applied _ _ =>
        s := s ++
          [ s!"-- `{c}`: each argument at the name's declared variance (rc.112, `declaredVariance`);",
            "-- invariant where nothing is declared; the head is the name and the arity",
            s!"#guard Ty.sub (.{c} \"Fiber.Fiber\" [.lit \"a\", .nat]) (.{c} \"Fiber.Fiber\" [.string, .nat])",
            s!"#guard !Ty.sub (.{c} \"Fiber.Fiber\" [.string, .nat]) (.{c} \"Fiber.Fiber\" [.lit \"a\", .nat])",
            s!"#guard !Ty.sub (.{c} \"Ref.Ref\" [.lit \"a\"]) (.{c} \"Ref.Ref\" [.string])",
            s!"#guard Ty.sub (.{c} \"Layer.Layer\" [.string, .nat, .nat]) (.{c} \"Layer.Layer\" [.lit \"a\", .nat, .nat])",
            s!"#guard !Ty.sub (.{c} \"Undeclared.Name\" [.lit \"a\"]) (.{c} \"Undeclared.Name\" [.string])",
            s!"#guard !Ty.sub (.{c} \"Fiber.Fiber\" [.nat, .nat]) (.{c} \"Exit.Exit\" [.nat, .nat])",
            s!"#guard !Ty.sub (.{c} \"Fiber.Fiber\" [.nat]) (.{c} \"Fiber.Fiber\" [.nat, .nat])", "" ]
      continue
    let n := r.ctor.children.length
    if n == 0 then continue
    -- a head `sameHead` refuses is not a congruence, so `sub_eq_args` never reads its `args`
    if notCongruent.any (fun p => p.1 == r.ctor.name) then continue
    let mk (f : Nat → String) : String :=
      s!"(.{r.ctor.name} " ++ String.intercalate " " ((List.range n).map f) ++ ")"
    for i in [0:n] do
      let lo := mk fun j => if j == i then "(.lit \"a\")" else ".nat"
      let hi := mk fun j => if j == i then ".string" else ".nat"
      let v : Variance := h.variance[i]!
      let up := if v == .co then "" else "!"
      let down := if v == .contra then "" else "!"
      s := s ++ [s!"#guard {up}Ty.sub {lo} {hi}", s!"#guard {down}Ty.sub {hi} {lo}"]
    if n >= 2 then
      let a := mk fun j => atoms[j % atoms.length]!
      let b := mk fun j => atoms[(j + 1) % atoms.length]!
      s := s ++ [s!"#guard !Ty.sub {a} {b}"]
    s := s ++ [""]
  return s

def emitSizeOf (rs : List Row) : List String := Id.run do
  let mut s : List String :=
    [ "/-- A child is smaller: the termination measure of every relational law. One arm per",
      "constructor, so the script names no shape it was not given. -/",
      "theorem sizeOf_args {t : Ty} {v : Variance} {x : Ty} (h : (v, x) ∈ t.args) :",
      "    sizeOf x < sizeOf t := by",
      "  cases t" ]
  for r in rs do
    let c := r.ctor
    let n := c.children.length
    if let some k := c.varKind? then
      let lines := match k with
        | .fields .. =>
          [ s!"  case {c.name} fs =>",
            "    simp only [args, List.mem_map, Prod.mk.injEq] at h",
            "    obtain ⟨p, hp, _, hpx⟩ := h",
            s!"    have hlt := sizeOf_field_lt_{c.name} (mem_canon hp)",
            "    rw [hpx] at hlt",
            s!"    simp only [Ty.{c.name}.sizeOf_spec]",
            "    omega" ]
        | .items _ =>
          [ s!"  case {c.name} xs =>",
            "    simp only [args, List.mem_map, Prod.mk.injEq] at h",
            "    obtain ⟨y, hy, _, hyx⟩ := h",
            "    have hlt := List.sizeOf_lt_of_mem hy",
            "    rw [hyx] at hlt",
            s!"    simp only [Ty.{c.name}.sizeOf_spec]",
            "    omega" ]
        | .applied .. =>
          [ s!"  case {c.name} nm xs =>",
            "    simp only [args, List.mem_map, Prod.mk.injEq] at h",
            "    obtain ⟨p, hp, _, hpx⟩ := h",
            "    have hlt := List.sizeOf_lt_of_mem (List.fst_mem_of_mem_zipIdx hp)",
            "    rw [hpx] at hlt",
            s!"    simp only [Ty.{c.name}.sizeOf_spec]",
            "    omega" ]
      s := s ++ lines
      continue
    let binders :=
      if c.fields.isEmpty then ""
      else " " ++ String.intercalate " " (c.fields.map fun f =>
        match f with
          | .child nm => nm
          | .payload nm _ => nm
          | .childList nm => nm
          | .fieldList nm _ _ _ => nm)
    if n == 0 then
      s := s ++ [s!"  case {c.name}{binders} => simp only [args, List.not_mem_nil] at h"]
    else
      let pats := String.intercalate " | " (repeatStr n "⟨-, rfl⟩")
      -- one child leaves one goal, so `;` rather than `<;>`: the linter counts the difference
      let tail :=
        if n == 1 then s!"; simp only [Ty.{c.name}.sizeOf_spec]; omega"
        else s!" <;> simp only [Ty.{c.name}.sizeOf_spec] <;> omega"
      s := s ++
        [ s!"  case {c.name}{binders} =>",
          "    simp only [args, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h",
          s!"    rcases h with {pats}{tail}" ]
  return s ++ [""]

/-- The two steps every relational law over the order takes, stated once over
`Variance.holds` rather than once per constructor: composition at a common head under a
measure (`argsBelow_trans`) and two-sidedness at a common head (`argsBelow_antisymm`), with
the inversions of the two rules that sit beside the congruences. Constructor-independent, so
this block is fixed text — it is here rather than in a hand module because the view is the
order's whole vocabulary and a consumer should need no second import to reason about it.
Emitted after `sizeOf_args`, which the measure arguments use. -/
def emitOrderLaws (hasVar : Bool) (table : Bool := false) : List String :=
  [ "/-! ### The order's two generic steps -/",
      "",
      "/-- Composition at each variance under a measure: the composed pair is read at the same",
      "triple, whichever way round the variance turns it, so one bound serves every arm. -/",
      "theorem Variance.holds_trans_of {r : Ty → Ty → Bool} (v : Variance) {x y z : Ty} {m : Nat}",
      "    (hm : sizeOf x + sizeOf y + sizeOf z < m)",
      "    (htrans : ∀ p q s, sizeOf p + sizeOf q + sizeOf s < m →",
      "      r p q = true → r q s = true → r p s = true)",
      "    (h : v.holds r x y = true) (h' : v.holds r y z = true) : v.holds r x z = true := by",
      "  cases v",
      "  case co => exact htrans x y z hm h h'",
      "  case contra => exact htrans z y x (by omega) h' h",
      "  case inv =>",
      "    simp only [Variance.holds, Bool.and_eq_true_iff] at h h' ⊢",
      "    exact ⟨htrans x y z hm h.1 h'.1, htrans z y x (by omega) h'.2 h.2⟩",
      "",
      "/-- The list step of `argsBelow_trans`: corresponding positions compose, position by",
      "position, with the variance carried by the first list (the second and third agree with it). -/",
      "private theorem zipAll_trans {r : Ty → Ty → Bool} :",
      "    ∀ (xs ys zs : List (Variance × Ty)),",
      "      xs.map Prod.fst = ys.map Prod.fst → ys.map Prod.fst = zs.map Prod.fst →",
      "      (∀ x ∈ xs, ∀ y ∈ ys, ∀ z ∈ zs, ∀ v : Variance,",
      "        v.holds r x.2 y.2 = true → v.holds r y.2 z.2 = true → v.holds r x.2 z.2 = true) →",
      "      (xs.zip ys).all (fun p => p.1.1.holds r p.1.2 p.2.2) = true →",
      "      (ys.zip zs).all (fun p => p.1.1.holds r p.1.2 p.2.2) = true →",
      "      (xs.zip zs).all (fun p => p.1.1.holds r p.1.2 p.2.2) = true",
      "  | [], _, _, _, _, _, _, _ => rfl",
      "  | _ :: _, [], _, h1, _, _, _, _ => by",
      "    simp only [List.map_cons, List.map_nil] at h1",
      "    exact absurd h1 (List.cons_ne_nil _ _)",
      "  | _ :: _, _ :: _, [], _, h2, _, _, _ => by",
      "    simp only [List.map_cons, List.map_nil] at h2",
      "    exact absurd h2 (List.cons_ne_nil _ _)",
      "  | x :: xs, y :: ys, z :: zs, h1, h2, hstep, hxy, hyz => by",
      "    simp only [List.map_cons, List.cons.injEq] at h1 h2",
      "    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true_iff] at hxy hyz ⊢",
      "    refine ⟨?_, ?_⟩",
      "    · refine hstep x List.mem_cons_self y List.mem_cons_self z List.mem_cons_self x.1 hxy.1 ?_",
      "      rw [h1.1]",
      "      exact hyz.1",
      "    · exact zipAll_trans xs ys zs h1.2 h2.2",
      "        (fun a ha b hb c hc => hstep a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)",
      "          c (List.mem_cons_of_mem _ hc))",
      "        hxy.2 hyz.2",
      "",
      "/-- **The order's transitive step, once.** At a common head the variance-wise comparison",
      "composes, given transitivity at every strictly smaller triple — which is exactly the",
      "induction hypothesis a proof by the triple measure has. No constructor is named. -/",
      "theorem argsBelow_trans {r : Ty → Ty → Bool} {a b c : Ty}",
      "    (hab : sameHead a b = true) (hbc : sameHead b c = true)",
      "    (htrans : ∀ x y z, sizeOf x + sizeOf y + sizeOf z < sizeOf a + sizeOf b + sizeOf c →",
      "      r x y = true → r y z = true → r x z = true)",
      "    (h1 : argsBelow r a b = true) (h2 : argsBelow r b c = true) :",
      "    argsBelow r a c = true := by",
      "  refine zipAll_trans a.args b.args c.args (args_congr hab).2 (args_congr hbc).2 ?_ h1 h2",
      "  intro x hx y hy z hz v",
      "  refine Variance.holds_trans_of v ?_ htrans",
      "  have hxa : sizeOf x.2 < sizeOf a := sizeOf_args hx",
      "  have hyb : sizeOf y.2 < sizeOf b := sizeOf_args hy",
      "  have hzc : sizeOf z.2 < sizeOf c := sizeOf_args hz",
      "  omega",
      "",
      "/-- The list step of `argsBelow_antisymm`. -/",
      "private theorem zipAll_antisymm {r : Ty → Ty → Bool} :",
      "    ∀ (xs ys : List (Variance × Ty)),",
      "      xs.map Prod.fst = ys.map Prod.fst →",
      "      (∀ x ∈ xs, ∀ y ∈ ys, r x.2 y.2 = true → r y.2 x.2 = true → x.2 = y.2) →",
      "      (xs.zip ys).all (fun p => p.1.1.holds r p.1.2 p.2.2) = true →",
      "      (ys.zip xs).all (fun p => p.1.1.holds r p.1.2 p.2.2) = true →",
      "      xs.map Prod.snd = ys.map Prod.snd",
      "  | [], [], _, _, _, _ => rfl",
      "  | _ :: _, [], h, _, _, _ => by",
      "    simp only [List.map_cons, List.map_nil] at h",
      "    exact absurd h (List.cons_ne_nil _ _)",
      "  | [], _ :: _, h, _, _, _ => by",
      "    simp only [List.map_cons, List.map_nil] at h",
      "    exact absurd h.symm (List.cons_ne_nil _ _)",
      "  | x :: xs, y :: ys, h, hstep, hxy, hyx => by",
      "    simp only [List.map_cons, List.cons.injEq] at h",
      "    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true_iff] at hxy hyx",
      "    simp only [List.map_cons, List.cons.injEq]",
      "    refine ⟨?_, zipAll_antisymm xs ys h.2",
      "      (fun a ha b hb => hstep a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))",
      "      hxy.2 hyx.2⟩",
      "    have hback : x.1.holds r y.2 x.2 = true := by rw [h.1]; exact hyx.1",
      "    obtain ⟨hf, hb⟩ := Variance.holds_antisymm x.1 hxy.1 hback",
      "    exact hstep x List.mem_cons_self y List.mem_cons_self hf hb",
      "",
      "/-- A child of the node, read through `args.map Prod.snd`: the shape every consumer of",
      "the two steps below has, and the one `sizeOf_args` is applied at. -/",
      "theorem sizeOf_args_mem {t x : Ty} (h : x ∈ t.args.map Prod.snd) : sizeOf x < sizeOf t := by",
      "  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h",
      "  exact sizeOf_args hp",
      "",
      "/-- **The order's antisymmetric step, once.** At a common head, two-sided comparison makes",
      "the children agree; `eq_of_sameHead` then makes the nodes agree.",
      "",
      "Its element step is stated over MEMBERSHIP where `argsBelow_trans`'s is stated over the",
      "measure, and the difference is not a slip. Transitivity composes, and at a contravariant",
      "or invariant position it composes the triple the other way round, so no membership",
      "hypothesis it could be given covers both directions while a symmetric measure does.",
      "Antisymmetry does not compose: its element step is a predicate at one pair, and a caller",
      "that carries a side condition on the children (normality, closedness) needs the",
      "membership to discharge it. Each is the weakest hypothesis that does its own job, and",
      "membership gives the measure back through `sizeOf_args_mem`. -/",
      "theorem argsBelow_antisymm {r : Ty → Ty → Bool} {a b : Ty} (hab : sameHead a b = true)",
      "    (heq : ∀ x ∈ a.args.map Prod.snd, ∀ y ∈ b.args.map Prod.snd,",
      "      r x y = true → r y x = true → x = y)",
      (if hasVar then "    (h1 : argsBelow r a b = true) (h2 : argsBelow r b a = true)\n    (hca : headCanon a = true) (hcb : headCanon b = true) : a = b := by"
       else "    (h1 : argsBelow r a b = true) (h2 : argsBelow r b a = true) : a = b := by"),
      (if hasVar then "  refine eq_of_sameHead hab (zipAll_antisymm a.args b.args (args_congr hab).2 ?_ h1 h2) hca hcb"
       else "  refine eq_of_sameHead hab (zipAll_antisymm a.args b.args (args_congr hab).2 ?_ h1 h2)"),
      "  intro x hx y hy hxy hyx",
      "  exact heq x.2 (List.mem_map_of_mem hx) y.2 (List.mem_map_of_mem hy) hxy hyx",
      "",
      "/-! ### The two rules beside the congruences, as inversions -/",
      "",
      "/-- The top is the only right-hand side the top rule fires at. -/",
      "theorem topRule_eq_false {a b : Ty} (h : b ≠ .unknown) : topRule a b = false := by",
      "  cases b",
      "  case unknown => exact absurd rfl h",
      "  all_goals rfl",
      "" ] ++
    -- with the leaf table, `litRule` and its three lemmas are gone (the table's laws replace
    -- them, emitted after this block)
    (if table then [] else
    [ "/-- The literal rule fires only into `string`. -/",
      "theorem litRule_eq_false {a b : Ty} (h : b ≠ .string) : litRule a b = false := by",
      "  cases b",
      "  case string => exact absurd rfl h",
      "  all_goals cases a <;> rfl",
      "" ]) ++
    [ "/-- At a head with no children, `sameHead` IS equality: a node is its head and its children,",
      "and there are none. -/",
      "theorem eq_of_sameHead_nil {a b : Ty} (h : sameHead a b = true) (hx : a.args = []) : a = b := by",
      "  have hlen := (args_congr h).1",
      "  rw [hx, List.length_nil] at hlen",
      "  have hb : b.args = [] := List.eq_nil_of_length_eq_zero hlen.symm",
      (if hasVar then "  exact eq_of_sameHead h (by rw [hx, hb]) (headCanon_of_args_nil hx) (headCanon_of_args_nil hb)"
       else "  exact eq_of_sameHead h (by rw [hx, hb])"),
      "" ] ++
    (if table then [] else
    [ "/-- The literal rule fires at exactly one pair of shapes. -/",
      "theorem litRule_eq_true {a b : Ty} (h : litRule a b = true) :",
      "    ∃ s, a = .lit s ∧ b = .string := by",
      "  cases a",
      "  case lit s =>",
      "    cases b",
      "    case string => exact ⟨s, rfl, rfl⟩",
      "    all_goals exact Bool.noConfusion h",
      "  all_goals exact Bool.noConfusion h",
    "",
      "/-- …so it does not fire whenever either side is known not to be that shape. -/",
      "theorem litRule_eq_false_of_head {a b : Ty} (h : ¬ ∃ s, a = .lit s ∧ b = .string) :",
      "    litRule a b = false := by",
      "  cases hl : litRule a b",
      "  · rfl",
      "  · exact absurd (litRule_eq_true hl) h",
    "" ])

/-- One lemma per congruence arm: `sub` at a pair of nodes with the same head IS the
variance-wise comparison of their arguments. Generated, so a new constructor adds a lemma
rather than an alternative inside an existing proof. -/
def emitArmLemmas (rs : List Row) (table : Bool := false) : List String := Id.run do
  let mut s : List String :=
    [ "/-! ### The congruence arms, one lemma each",
      "",
      "A1 of the tooling plan's assumption table asked whether ONE generated proof closes over",
      "the whole square of constructors. It does — `fun_cases Ty.sub a b` plus one `aesop` — but",
      "that proof reaches `Classical.choice` through aesop's search, and this file is audited",
      "source whose ceiling is `[propext, Quot.sound]`. So the plan's designed fallback is what",
      "lands: one lemma per congruence arm, and a dispatcher over `fun_cases` that names no",
      "constructor of its own. Each lemma is the idiom of `Ty.lean`'s `sub_*_of_ne`, with the",
      "reflexive case folded in so no caller carries an inequality. -/",
      "" ]
  for r in rs do
    let c := r.ctor
    if let some k := c.varKind? then
      let (bind, lhsA, rhsA, tail, fn) : String × String × String × List String × String := match k with
        | .fields _ ch _ elem =>
          let el := elem.replace "{M}" "Ty"
          (s!"(fs gs : List ({el}))", "fs", "gs", ["Prod.map", "Variance.holds"],
           s!"(fun (pq : ({el}) × ({el})) => sub pq.1{ch} pq.2{ch})")
        | .items _ =>
          ("(xs ys : List Ty)", "xs", "ys", ["Prod.map", "Variance.holds"],
           "(fun (pq : Ty × Ty) => sub pq.1 pq.2)")
        | .applied _ _ =>
          ("(n1 : String) (xs : List Ty) (n2 : String) (ys : List Ty)", "n1 xs", "n2 ys",
           ["Prod.map", "Variance.holds_eq_select"],
           "(fun (pq : (Ty × Nat) × (Ty × Nat)) =>\n      (argVariance n1 pq.1.2).select (sub pq.1.1 pq.2.1) (sub pq.2.1 pq.1.1))")
      s := s ++
        [ s!"/-- The `{c.name}` arm: under the head, `sub` is the comparison of corresponding",
          "children. It reads `sub`'s arm in the form `decide (head) && (zip).attach.all …`, the one",
          "form this generator proves. -/",
          s!"theorem sub_args_{c.name} {bind}",
          s!"    (hh : sameHead (.{c.name} {lhsA}) (.{c.name} {rhsA}) = true) :",
          s!"    sub (.{c.name} {lhsA}) (.{c.name} {rhsA}) = argsBelow sub (.{c.name} {lhsA}) (.{c.name} {rhsA}) := by",
          s!"  by_cases h : Ty.{c.name} {lhsA} = Ty.{c.name} {rhsA}",
          "  · rw [h, sub_refl, argsBelow_refl]",
          "  · simp only [sameHead] at hh",
          "    conv => lhs; unfold sub" ] ++
        -- with the leaf table, `sub` consults `leafRule` before its rows: a variable head is no
        -- leaf head, so the table's line is `false` there (`leafRule_of_left_none`)
        (if table then
          [ s!"    rw [if_neg h, ite_leafRule_false (leafRule_of_left_none (.{c.name} {lhsA}) (.{c.name} {rhsA}) rfl)]",
            "    simp only [hh, Bool.true_and, argsBelow, args, List.zip_map, List.all_map," ]
         else
          [ "    simp only [h, ↓reduceIte, hh, Bool.true_and, argsBelow, args, List.zip_map, List.all_map," ]) ++
        [ "      Function.comp_def, " ++ String.intercalate ", " tail ++ "]",
          s!"    exact all_attach_eq _ {fn}",
          "" ]
      continue
    let n := c.children.length
    if n == 0 then continue
    if notCongruent.any (fun p => p.1 == c.name) then continue
    let xs := (List.range n).map fun i => s!"x{i}"
    let ys := (List.range n).map fun i => s!"y{i}"
    let binders := String.intercalate " " (xs ++ ys)
    let lhs := s!"(.{c.name} " ++ String.intercalate " " xs ++ ")"
    let rhs := s!"(.{c.name} " ++ String.intercalate " " ys ++ ")"
    let lhsQ := s!"Ty.{c.name} " ++ String.intercalate " " xs
    let rhsQ := s!"Ty.{c.name} " ++ String.intercalate " " ys
    -- an invariant position contributes two conjuncts, so only those arms nest deeply
    -- enough to need associativity; a covariant pair matches `argsBelow` as written
    let vs := (r.head.map (fun h => h.variance)).getD []
    let assoc := if n >= 2 && vs.any (fun v => v == .inv) then ", Bool.and_assoc" else ""
    s := s ++
      [ s!"theorem sub_args_{c.name} ({binders} : Ty) :",
        s!"    sub {lhs} {rhs} = argsBelow sub {lhs} {rhs} := by",
        s!"  by_cases h : {lhsQ} = {rhsQ}",
        "  · rw [h, sub_refl, argsBelow_refl]",
        "  · conv => lhs; unfold sub" ] ++
      (if table then
        [ s!"    rw [if_neg h, ite_leafRule_false (leafRule_of_left_none {lhs} {rhs} rfl)]",
          "    simp only [argsBelow, args, Variance.holds, List.zip, List.zipWith," ]
       else
        [ "    simp only [h, ↓reduceIte, argsBelow, args, Variance.holds, List.zip, List.zipWith," ]) ++
      [ s!"      List.all_cons, List.all_nil, Bool.and_true{assoc}]",
        "" ]
  return s

/-- The two directions, then the law. The `false` direction is `fun_cases Ty.sub`, where the
catch-all is `rfl`; the `true` direction is `fun_cases Ty.sameHead`, one arm lemma per case. -/
def emitDispatch (rs : List Row) (table : Bool := false) : List String := Id.run do
  -- `sub`'s arms in order: six rules, one congruence arm per head with children (declaration
  -- order, `union` excepted), then the catch-all; its `fun_cases` number is computed, not
  -- written, since every appended head moves it. A variable head's arm is not constant at a
  -- different head, so it gets its own case.
  let cong := rs.filter fun r => r.head.isSome &&
    (r.ctor.children.length != 0 || r.ctor.varKind?.isSome) &&
    !notCongruent.any (fun p => p.1 == r.ctor.name)
  let varCases : List String := (cong.zipIdx.filterMap fun (r, k) =>
    if r.ctor.varKind?.isSome then
      some [s!"  case case{7 + k} =>", "    simp only [sameHead] at hh", "    simp only [hh, Bool.false_and]"]
    else none).flatten
  let catchAll := 7 + cong.length
  -- the six fixed cases: today `sub`'s reflexive line, its four structural arms and the literal
  -- arm; with the leaf table, the reflexive line, the table's line (`leafRule`, before the rows)
  -- and the four structural arms, so the congruences keep their numbers either way
  let fixed : List String :=
    if table then
      [ "  case case1 => rw [sameHead_refl _ ha] at hh; exact Bool.noConfusion hh",
        "  case case2 _ hl => rw [hleaf] at hl; exact Bool.noConfusion hl",
        "  case case3 => exact Bool.noConfusion ha",
        "  case case4 => exact Bool.noConfusion ha",
        "  case case5 => exact Bool.noConfusion hb",
        "  case case6 => exact Bool.noConfusion htop" ]
    else
      [ "  case case1 => rw [sameHead_refl _ ha] at hh; exact Bool.noConfusion hh",
        "  case case2 => exact Bool.noConfusion ha",
        "  case case3 => exact Bool.noConfusion ha",
        "  case case4 => exact Bool.noConfusion hb",
        "  case case5 => exact Bool.noConfusion htop",
        "  case case6 => exact Bool.noConfusion hlit" ]
  let (hyp, hypName) := if table then ("(hleaf : leafRule a b = false)", "hleaf")
    else ("(hlit : litRule a b = false)", "hlit")
  let mut s : List String :=
    (if table then
      [ "/-- Different heads, no declared edge: the order answers `false`. The hypothesis `hleaf` is",
        "the leaf table's (`leafRule`, decisions row 177), so the conclusion is false only where the",
        "table declares no edge (`sub_eq_leafRule_of_not_sameHead` below states the other half).",
        "`fun_cases Ty.sub` makes the catch-all into `rfl`, because the arm it takes IS `false`. -/" ]
     else
      [ "/-- Different heads: the order answers `false`. `fun_cases Ty.sub` makes the catch-all —",
        "the one case a square-of-constructors proof cannot discharge without search — into `rfl`,",
        "because the arm it takes IS `false`. -/" ]) ++
    [ "theorem sub_eq_false_of_not_sameHead (a b : Ty) (ha : isMember a = true)",
      s!"    (hb : isMember b = true) {hyp} (htop : topRule a b = false)",
      "    (hh : sameHead a b = false) : sub a b = false := by",
      "  fun_cases Ty.sub a b" ] ++ fixed ++ varCases ++
    [ s!"  case case{catchAll} => rfl",
      "  -- the congruence arms: `sameHead` answers `true` at a matching head, so `hh` is absurd",
      "  all_goals simp only [sameHead, Bool.true_eq_false] at hh",
      "",
      "/-- Same head: the order IS the variance-wise comparison. `fun_cases Ty.sameHead` splits on",
      "the head test's own arms, so there is one case per constructor and no square. -/",
      "theorem sub_eq_argsBelow_of_sameHead (a b : Ty) (hh : sameHead a b = true) :",
      "    sub a b = argsBelow sub a b := by",
      "  revert hh",
      "  fun_cases Ty.sameHead a b" ]
  let mut i : Nat := 0
  for r in rs do
    let c := r.ctor
    if notCongruent.any (fun p => p.1 == c.name) then continue
    i := i + 1
    if c.varKind?.isSome then
      let unders := String.intercalate " " (repeatStr (2 * c.fields.length) "_")
      s := s ++ [s!"  case case{i} => intro hh; exact sub_args_{c.name} {unders} hh"]
      continue
    let n := c.children.length
    let ps := c.payloads
    if n != 0 then
      let unders := String.intercalate " " (repeatStr (2 * n) "_")
      s := s ++ [s!"  case case{i} => intro _; exact sub_args_{c.name} {unders}"]
    else if ps.isEmpty then
      s := s ++ [s!"  case case{i} => intro _; rw [sub_refl, argsBelow_refl]"]
    else if ps.length == 1 then
      s := s ++
        [ s!"  case case{i} =>",
          "    intro hh",
          "    have hp := of_decide_eq_true hh",
          "    subst hp",
          "    rw [sub_refl, argsBelow_refl]" ]
    else
      let rfls := String.intercalate ", " (repeatStr ps.length "rfl")
      s := s ++
        [ s!"  case case{i} =>",
          "    intro hh",
          "    simp only [Bool.and_eq_true, decide_eq_true_eq] at hh",
          s!"    obtain ⟨{rfls}⟩ := hh",
          "    rw [sub_refl, argsBelow_refl]" ]
  s := s ++
    [ s!"  case case{i + 1} => intro hh; exact Bool.noConfusion hh",
      "",
      "/-- **`sub` between union members is the variance-wise comparison of corresponding",
      "arguments.** Everything a relational proof needs to know about `Ty`'s constructors, in one",
      "statement: the exceptional rules are excluded by the four hypotheses, and the congruence",
      "arms are the right-hand side. The two directions above are the proof, and neither names a",
      "constructor: a new one adds an arm lemma and a `case`, both generated. -/",
      "theorem sub_eq_args (a b : Ty) (ha : isMember a = true) (hb : isMember b = true)",
      s!"    {hyp} (htop : topRule a b = false) :",
      "    sub a b = (sameHead a b && argsBelow sub a b) := by",
      "  cases hh : sameHead a b",
      "  · rw [Bool.false_and]",
      s!"    exact sub_eq_false_of_not_sameHead a b ha hb {hypName} htop hh",
      "  · rw [Bool.true_and]",
      "    exact sub_eq_argsBelow_of_sameHead a b hh",
      "" ]
  return s

def emitLaws (rs : List Row) : List String :=
  -- only a constructor with fields has an `injEq`
  let injEqs := String.intercalate ", "
    ((rs.filter fun r => !r.ctor.fields.isEmpty).map fun r => s!"Ty.{r.ctor.name}.injEq")
  let vrs := rs.filter fun r => r.ctor.varKind?.isSome
  let hasVar := !vrs.isEmpty
  let hasFields := vrs.any fun r => match r.ctor.varKind? with | some (.fields ..) => true | _ => false
  let binders : VarKind → String := fun k => match k with
    | .fields .. => "fs" | .items _ => "xs" | .applied .. => "n xs"
  let reflCases := vrs.filterMap fun r => r.ctor.varKind?.map fun k =>
    s!"  case {r.ctor.name} {binders k} => exact zip_self_all sub sub_refl _"
  let congrCases := (vrs.filterMap fun r => r.ctor.varKind?.map fun k =>
    let c := r.ctor.name
    match k with
    | .fields .. =>
      [ s!"  case {c}.{c} fs gs =>",
        "    have hl := congrArg List.length (of_decide_eq_true h)",
        "    simp only [List.length_map] at hl",
        "    simp only [args, List.length_map, List.map_map, Function.comp_def]",
        "    exact ⟨hl, map_const_eq _ hl⟩" ]
    | .items _ =>
      [ s!"  case {c}.{c} xs ys =>",
        "    have hl : xs.length = ys.length := of_decide_eq_true h",
        "    simp only [args, List.length_map, List.map_map, Function.comp_def]",
        "    exact ⟨hl, map_const_eq _ hl⟩" ]
    | .applied .. =>
      [ s!"  case {c}.{c} n1 xs n2 ys =>",
        "    simp only [sameHead, Bool.and_eq_true, decide_eq_true_eq] at h",
        "    obtain ⟨rfl, hl⟩ := h",
        "    simp only [args, List.length_map, List.length_zipIdx, List.map_map, Function.comp_def]",
        "    exact ⟨hl, map_zipIdx_snd_eq _ hl⟩" ]).flatten
  let eqCases := (vrs.filterMap fun r => r.ctor.varKind?.map fun k =>
    let c := r.ctor.name
    match k with
    | .fields .. =>
      [ s!"  case {c}.{c} fs gs =>",
        "    have hn := of_decide_eq_true h",
        "    simp only [args, List.map_map, Function.comp_def] at hx",
        s!"    have hc : canon fs = canon gs := eq_of_fields_{c} hn hx",
        "    have hf : canon fs = fs := of_decide_eq_true hca",
        "    have hg : canon gs = gs := of_decide_eq_true hcb",
        "    rw [← hf, ← hg, hc]" ]
    | .items _ =>
      [ s!"  case {c}.{c} xs ys =>",
        "    simp only [args, List.map_map, Function.comp_def, List.map_id'] at hx",
        "    rw [hx]" ]
    | .applied .. =>
      [ s!"  case {c}.{c} n1 xs n2 ys =>",
        "    simp only [sameHead, Bool.and_eq_true, decide_eq_true_eq] at h",
        "    obtain ⟨rfl, _⟩ := h",
        "    simp only [args, List.map_map, Function.comp_def] at hx",
        "    rw [map_fst_zipIdx, map_fst_zipIdx] at hx",
        "    rw [hx]" ]).flatten
  [ "/-- `union` is the one head `sameHead` refuses, so reflexivity is stated at a member; an",
    "`isMember` hypothesis is exactly what every caller of the view has: the one goal the",
    "normalisation leaves is that head, and `isMember` is `false` there. -/",
    "theorem sameHead_refl (t : Ty) (h : isMember t = true) : sameHead t t = true := by",
    "  cases t <;> simp only [sameHead, decide_eq_true_eq" ++
      (if rs.any (fun r => match r.ctor.varKind? with | some (.applied ..) => true | _ => false)
        then ", Bool.and_eq_true, and_self]"
       else if rs.any (fun r => r.ctor.payloads.length >= 2) then ", and_self]" else "]") ++ "",
    "  exact h",
    "",
    "theorem sameHead_symm {a b : Ty} (h : sameHead a b = true) : sameHead b a = true := by",
    "  cases a <;> cases b <;> aesop (add norm simp [sameHead])",
    "",
    "/-- `fun_cases` on `sameHead` itself, so the split is its own arm list and not the square of",
    "the alphabet: one case per arm, then one `cases c` inside each. -/",
    "theorem sameHead_trans {a b c : Ty} (hab : sameHead a b = true)",
    "    (hbc : sameHead b c = true) : sameHead a c = true := by",
    "  fun_cases Ty.sameHead a b <;> cases c <;> aesop (add norm simp [sameHead])",
    "",
    "/-- The variance-wise comparison of a node with itself, from `sub_refl`. -/",
    "theorem argsBelow_refl (t : Ty) : argsBelow sub t t = true := by" ] ++
  (if hasVar then [ "  cases t" ] ++ reflCases ++ [ "  all_goals",
    "    simp only [argsBelow, args, Variance.holds, List.zip, List.zipWith, List.all_cons,",
    "      List.all_nil, Bool.and_true, sub_refl]" ]
   else [ "  cases t <;>",
    "    simp only [argsBelow, args, Variance.holds, List.zip, List.zipWith, List.all_cons,",
    "      List.all_nil, Bool.and_true, sub_refl]" ]) ++
  [ "",
    "/-- Corresponding arguments correspond: same length, same variances. -/",
    "theorem args_congr {a b : Ty} (h : sameHead a b = true) :",
    "    a.args.length = b.args.length ∧ a.args.map Prod.fst = b.args.map Prod.fst := by" ] ++
  (if hasVar then [ "  cases a <;> cases b" ] ++ congrCases ++
      [ "  all_goals aesop (add norm simp [sameHead, args])" ]
   else [ "  cases a <;> cases b <;> aesop (add norm simp [sameHead, args])" ]) ++
  (if hasVar then
    [ "",
      "/-- A node is its head and its children, read in canonical order: at a field list the" ,
      "children are in that order, so the node must be (`headCanon`); a permuted record has its",
      "canonical record's head and children and is another term. -/",
      "theorem eq_of_sameHead {a b : Ty} (h : sameHead a b = true)",
      "    (hx : a.args.map Prod.snd = b.args.map Prod.snd)",
      "    (hca : headCanon a = true) (hcb : headCanon b = true) : a = b := by",
      "  cases a <;> cases b" ] ++ eqCases ++
    [ "  all_goals aesop (add norm simp [sameHead, args, " ++ injEqs ++ "])" ]
   else
    [ "",
      "/-- A node is its head and its children. -/",
      "theorem eq_of_sameHead {a b : Ty} (h : sameHead a b = true)",
      "    (hx : a.args.map Prod.snd = b.args.map Prod.snd) : a = b := by",
      "  cases a <;> cases b <;> aesop (add norm simp [sameHead, args, " ++ injEqs ++ "])" ]) ++
  (if hasFields then [] else []) ++
  [ "",
    "/-- Composition at each variance, once, for every relational law that needs it. -/",
    "theorem Variance.holds_trans {r : Ty → Ty → Bool} (v : Variance)",
    "    (htrans : ∀ x y z, r x y = true → r y z = true → r x z = true) {x y z : Ty}",
    "    (h : v.holds r x y = true) (h' : v.holds r y z = true) : v.holds r x z = true := by",
    "  cases v <;> aesop (add norm simp [Variance.holds])",
    "",
    "/-- And at each variance, a two-sided comparison gives the relation both ways. -/",
    "theorem Variance.holds_antisymm {r : Ty → Ty → Bool} (v : Variance) {x y : Ty}",
    "    (h : v.holds r x y = true) (h' : v.holds r y x = true) :",
    "    r x y = true ∧ r y x = true := by",
    "  cases v <;> aesop (add norm simp [Variance.holds])",
    "" ]

/-- `AdmitsSub`: one field per constructor, the condition under which an admission algebra's
fold respects `sub`. The carrier is the paramorphic one `fold_of` gives (`Ty × Adm`), so each
field reads the arm's second component. -/
def emitAdmits (rs : List Row) (table : Option LeafTable := none) : List String := Id.run do
  let mut s : List String :=
    [ "/-- A value-admission carrier: a predicate on a value and an allocation table.",
      "`Val.hasTy` at a fixed type is one (`Folds/Ty.lean`'s `fold_of`). -/",
      "abbrev Adm := Effect4.Machine.Val → List String → Bool",
      "",
      "/-- The pointwise order: `p` admits no more than `q`. -/",
      "def Adm.le (p q : Adm) : Prop := ∀ v al, p v al = true → q v al = true",
      "",
      "theorem Adm.le_refl (p : Adm) : Adm.le p p := fun _ _ h => h",
      "",
      "theorem Adm.le_trans {p q r : Adm} (h : Adm.le p q) (h' : Adm.le q r) : Adm.le p r :=",
      "  fun v al hv => h' v al (h v al hv)",
      "",
      "/-- The algebra's carrier as `fold_of` builds it: the node rebuilt beside its result",
      "(a paramorphism, `FoldOf.lean`). -/",
      "abbrev AdmCarrier : TyFam → Type := fun fam => TyFam.rec (Ty × Adm) fam",
      "",
      "/-- **One field per constructor**: what an admission algebra must satisfy for its fold to",
      "respect `sub`. The empty union admits nothing and the top admits everything; a union is",
      (if table.isSome then
        "the disjunction of its members; each declared leaf edge is an inclusion; a covariant argument is"
       else "the disjunction of its members; the literal rule is an inclusion; a covariant argument is"),
      "monotone, a contravariant one antitone, and an invariant one is IGNORED — which is",
      "decisions row 44 (a handle is coarse by kind; the world's tables type what it holds)",
      "stated as a law. A new constructor adds a field here and one line to each instance, at a",
      "place the compiler names. -/",
      "structure AdmitsSub (alg : TyAlgebra AdmCarrier) : Prop where" ]
  -- the exceptional rules first, in the order of `sub`'s own arms
  s := s ++
    [ "  /-- the empty union admits nothing -/",
      "  never : ∀ v al, (alg.ty_never).2 v al = false",
      "  /-- a union is the disjunction of its members -/",
      "  union : ∀ p q v al, (alg.ty_union p q).2 v al = ((p.2 v al) || (q.2 v al))",
      "  /-- the top admits everything (decisions row 46) -/",
      "  top : ∀ v al, (alg.ty_unknown).2 v al = true" ] ++
    (match table with
      | none =>
        [ "  /-- the literal rule -/",
          "  lit_string : ∀ s, Adm.le (alg.ty_lit s).2 (alg.ty_string).2" ]
      | some tb =>
        -- one inclusion per declared edge, the closure by `Adm.le_trans` (no derived pair is a
        -- field); the payloads of each side are quantified, `lit`'s keeping its spelling `s`
        tb.edges.flatMap fun (x, y) =>
          let pay (c : String) (pre : String) : List (String × String) :=
            match rs.find? (·.ctor.name == c) with
            | some r => r.ctor.payloads.zipIdx.map fun ((_, ty), i) =>
                (if pre == "s" && i == 0 then "s" else s!"{pre}{i}", ty)
            | none => []
          let px := pay x "s"
          let py := pay y "t"
          let binders := (px ++ py).map fun (n, ty) => s!"({n} : {ty})"
          let app (c : String) (ps : List (String × String)) : String :=
            if ps.isEmpty then s!"(alg.ty_{c}).2"
            else s!"(alg.ty_{c} " ++ String.intercalate " " (ps.map Prod.fst) ++ ").2"
          let pre := if binders.isEmpty then "" else "∀ " ++ String.intercalate " " binders ++ ", "
          [ s!"  /-- the declared leaf edge `{x} ⊑ {y}` (decisions row 177) -/",
            s!"  {x}_{y} : {pre}Adm.le {app x px} {app y py}" ]) ++
    [ "  /-- a template parameter has no inhabitant -/",
      "  var : ∀ i v al, (alg.ty_var i).2 v al = false" ]
  for r in rs do
    let c := r.ctor
    let some h := r.head | continue
    if let some k := c.varKind? then
      let lines := match k with
        | .fields _ ch ps elem =>
          let el := elem.replace "{M}" "AdmCarrier .ty"
          [ s!"  /-- every field co, the payloads equal in canonical order ({h.cite}) -/",
            s!"  {c.name} : ∀ (ps qs : List ({el})),",
            s!"    (Ty.canon ps).map (fun p => {payText ps}) = (Ty.canon qs).map (fun p => {payText ps}) →",
            s!"    (∀ p q, (p, q) ∈ (Ty.canon ps).zip (Ty.canon qs) → Adm.le (p{ch}).2 (q{ch}).2) →",
            s!"    Adm.le (alg.ty_{c.name} ps).2 (alg.ty_{c.name} qs).2" ]
        | .items _ =>
          [ s!"  /-- every item co, by position ({h.cite}) -/",
            s!"  {c.name} : ∀ (ps qs : List (AdmCarrier .ty)), ps.length = qs.length →",
            "    (∀ p q, (p, q) ∈ ps.zip qs → Adm.le p.2 q.2) →",
            s!"    Adm.le (alg.ty_{c.name} ps).2 (alg.ty_{c.name} qs).2" ]
        | .applied _ _ =>
          [ s!"  /-- each argument at the name's declared variance, an invariant one ignored ({h.cite}) -/",
            s!"  {c.name} : ∀ (n : String) (ps qs : List (AdmCarrier .ty)), ps.length = qs.length →",
            "    (∀ p q, (p, q) ∈ ps.zipIdx.zip qs.zipIdx → match Ty.argVariance n p.2 with",
            "      | .co => Adm.le p.1.2 q.1.2 | .contra => Adm.le q.1.2 p.1.2 | .inv => True) →",
            s!"    Adm.le (alg.ty_{c.name} n ps).2 (alg.ty_{c.name} n qs).2" ]
      s := s ++ lines
      continue
    let kids := c.children
    if kids.isEmpty then continue
    if notCongruent.any (fun p => p.1 == c.name) then continue
    let n := kids.length
    let vs := h.variance
    let ps := (List.range n).map fun i => s!"p{i}"
    let qs := (List.range n).map fun i => s!"q{i}"
    let binders := String.intercalate " " (ps ++ qs)
    let hyps := (List.range n).filterMap fun i =>
      match (vs[i]! : Variance) with
      | .co => some s!"Adm.le (p{i}).2 (q{i}).2"
      | .contra => some s!"Adm.le (q{i}).2 (p{i}).2"
      | .inv => none
    let doc := String.intercalate ", " ((List.range n).map fun i =>
      s!"argument {i} " ++ (vs[i]!: Variance).text)
    let lhs := s!"(alg.ty_{c.name} " ++ String.intercalate " " ps ++ ").2"
    let rhs := s!"(alg.ty_{c.name} " ++ String.intercalate " " qs ++ ").2"
    s := s ++ [s!"  /-- {doc} ({h.cite}) -/"]
    if vs.all (fun v => v == .inv) then
      s := s ++ [s!"  {c.name} : ∀ {binders}, {lhs} = {rhs}"]
    else
      let pre := if hyps.isEmpty then "" else String.intercalate " → " hyps ++ " → "
      s := s ++ [s!"  {c.name} : ∀ {binders}, {pre}Adm.le {lhs} {rhs}"]
  return s ++ [""]

/-- `AdmitsExtend`: one field per constructor, the condition under which an admission algebra's
fold preserves extension of the allocation table. -/
def emitAdmitsExtend (ns : String) (rs : List Row) : List String := Id.run do
  let mut s : List String :=
    [ "/-- The allocation table `after` agrees with `before` at every index `before` has. -/",
      "def Extends (before after : List String) : Prop :=",
      "  ∀ (i : Nat) (target : String), before[i]? = some target → after[i]? = some target",
      "",
      "/-- A registration appends, and an append extends. -/",
      "theorem extends_append (before added : List String) : Extends before (before ++ added) := by",
      "  intro i target h",
      "  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]",
      "  exact h",
      "",
      "/-- Pointwise monotonicity in the allocation table: if `Extends a b`, what is admitted",
      "at `a` is admitted at `b`. -/",
      "def Adm.Extends (p : Adm) : Prop :=",
      s!"  ∀ v a b, {ns}.Extends a b → p v a = true → p v b = true",
      "",
      "/-- **One field per constructor**: what an admission algebra must satisfy for its fold to",
      "preserve extension of the allocation table. -/",
      "structure AdmitsExtend (alg : TyAlgebra AdmCarrier) : Prop where" ]
  for r in rs do
    let c := r.ctor
    if let some k := c.varKind? then
      let line := match k with
        | .fields _ ch _ elem =>
          let el := elem.replace "{M}" "AdmCarrier .ty"
          s!"  {c.name} : ∀ (ps : List ({el})), (∀ p ∈ ps, Adm.Extends (p{ch}).2) → Adm.Extends (alg.ty_{c.name} ps).2"
        | .items _ =>
          s!"  {c.name} : ∀ (ps : List (AdmCarrier .ty)), (∀ p ∈ ps, Adm.Extends p.2) → Adm.Extends (alg.ty_{c.name} ps).2"
        | .applied _ _ =>
          s!"  {c.name} : ∀ (n : String) (ps : List (AdmCarrier .ty)), (∀ p ∈ ps, Adm.Extends p.2) → \
            Adm.Extends (alg.ty_{c.name} n ps).2"
      s := s ++ [line]
      continue
    let n := c.children.length
    let ps := c.payloads
    if n == 0 && ps.isEmpty then
      s := s ++ [s!"  {c.name} : Adm.Extends (alg.ty_{c.name}).2"]
    else if n == 0 then
      let binders := String.intercalate " " (ps.map fun (name, ty) => s!"({name} : {ty})")
      let args := String.intercalate " " (ps.map Prod.fst)
      s := s ++ [s!"  {c.name} : ∀ {binders}, Adm.Extends (alg.ty_{c.name} {args}).2"]
    else if ps.isEmpty then
      let pVars := (List.range n).map fun i => s!"p{i}"
      let binders := String.intercalate " " pVars
      let hyps := (List.range n).map fun i => s!"Adm.Extends (p{i}).2"
      let pre := String.intercalate " → " hyps ++ " → "
      let args := String.intercalate " " pVars
      s := s ++ [s!"  {c.name} : ∀ {binders}, {pre}Adm.Extends (alg.ty_{c.name} {args}).2"]
    else
      let pVars := (List.range n).map fun i => s!"p{i}"
      let payloadBinders := String.intercalate " " (ps.map fun (name, ty) => s!"({name} : {ty})")
      let binders := payloadBinders ++ " " ++ String.intercalate " " pVars
      let hyps := (List.range n).map fun i => s!"Adm.Extends (p{i}).2"
      let pre := String.intercalate " → " hyps ++ " → "
      let payloadArgs := String.intercalate " " (ps.map Prod.fst)
      let args := payloadArgs ++ " " ++ String.intercalate " " pVars
      s := s ++ [s!"  {c.name} : ∀ {binders}, {pre}Adm.Extends (alg.ty_{c.name} {args}).2"]
  return s ++ [""]

structure Args where
  group : String := ""
  imports : List String := []
  out : Option String := none
  headerOut : Option String := none
  append : Option String := none
  types : List String := []
  /-- The variance table; overridable so a mutation probe can point at a scratch copy. -/
  variances : String := "tools/Effect4Gen/variances.json"

partial def parseArgs : List String → Args → Except String Args
  | [], a => .ok a
  | "--group" :: g :: rest, a => parseArgs rest { a with group := g }
  | "--imports" :: i :: rest, a =>
    parseArgs rest { a with imports := (i.splitOn ",").filter (· != "") }
  | "--out" :: o :: rest, a => parseArgs rest { a with out := some o }
  | "--header-out" :: o :: rest, a => parseArgs rest { a with headerOut := some o }
  | "--append" :: p :: rest, a => parseArgs rest { a with append := some p }
  | "--variances" :: p :: rest, a => parseArgs rest { a with variances := p }
  | t :: rest, a =>
    if t.startsWith "--" then
      if rest.isEmpty then .error s!"{t} needs a value" else .error s!"unknown option {t}"
    else parseArgs rest { a with types := a.types ++ [t] }

def run (args : Args) (heads : List Head) : MetaM (Array String) := do
  let outPath := (args.headerOut.orElse (fun _ => args.out) |>.getD "<stdout>").replace "\\" "/"
  let head := "lake env lean -M 4096 --run tools/Effect4Gen/View.lean --group " ++ args.group
    ++ " --imports " ++ String.intercalate "," args.imports
    ++ " --out " ++ outPath
    ++ (match args.append with | some p => " --append " ++ p.replace "\\" "/" | none => "")
    ++ String.join (args.types.map fun t => " " ++ t)
  let mut lines : Array String := #[
    "-- GENERATED by tools/Effect4Gen/View.lean from the Lean environment and",
    "-- tools/Effect4Gen/variances.json (rc.112's own declarations). Do not edit.",
    "-- Regenerate (tools/Effect4Gen/Driver.lean runs this for every group; --verify refuses a diff):",
    "--   " ++ head]
  if let some p := args.append then
    lines := lines.push s!"-- Acceptance guards appended verbatim from: {p.replace "\\" "/"}"
  lines := lines ++ (args.imports.map fun i => s!"import {i}").toArray
  -- the namespace is the first type's own prefix, as `Fold.lean`'s `run` derives it
  let ns := match args.types.head? with
    | some t => t.toName.getPrefix.toString
    | none => "Effect4.Program"
  lines := lines ++ #["", "set_option autoImplicit false", "", "namespace " ++ ns, ""]
  for t in args.types do
    let ctors ← readCtors t.toName
    -- the leaf-order table first: a cyclic table is refused before anything else is read
    let table? ← readLeafTable t.toName
    if let some tb := table? then
      if let .error e := tb.check t.toName ctors then throwError e
    let rs ← match rows ctors heads with
      | .error e => throwError e
      | .ok rs => pure rs
    -- what a head of variable arity reads must exist in `Ty.lean` (the canonical order and its
    -- two facts) and in the core variance module (a reference's declared variances); refused
    -- by name otherwise
    let kinds := rs.filterMap (·.ctor.varKind?)
    let hasVar := !kinds.isEmpty
    let needs : List Name :=
      (if kinds.any (fun k => match k with | .fields .. => true | _ => false)
        then [`canon, `mem_canon, `canon_eq_nil] else []) ++
      (if kinds.any (fun k => match k with | .applied .. => true | _ => false)
        then [`argVariance, `Variance.select, `Variance.holds_eq_select] else [])
    for nm in needs do
      unless (← getEnv).contains (t.toName ++ nm) do
        throwError "View: `{t}` has a head of variable arity, which the view reads through \
          `{t.toName ++ nm}`; it is not in the environment"
    -- a core `Ty.Variance` (the variance module `sub` reads) replaces the view's own
    let coreVariance := (← getEnv).contains (t.toName ++ `Variance)
    -- the cross-head rules: the core's leaf-order table when it declares one (its laws, the
    -- order's laws restated over it), today's literal rule otherwise (today's text)
    let hasTable := table?.isSome
    let hasNormalize := (← getEnv).contains (t.toName ++ `normalize)
    let leafProbes := match table? with | some tb => emitLeafProbes ctors tb | none => []
    let leafLaws := match table? with | some tb => emitLeafLaws tb hasNormalize | none => []
    lines := lines.push (join (["namespace Ty", ""] ++ emitVariance coreVariance ++ emitArgs rs ++
      emitSameHead rs ++ emitRules hasTable ++ emitProbes rs ++ leafProbes ++ emitVarHelpers rs ++
      emitLaws rs ++ emitArmLemmas rs hasTable ++ emitDispatch rs hasTable ++ emitSizeOf rs ++
      emitOrderLaws hasVar hasTable ++ leafLaws ++
      ["end Ty", ""] ++ emitAdmits rs table? ++ emitAdmitsExtend ns rs))
  lines := lines ++ #["end " ++ ns, ""]
  if let some p := args.append then
    let txt ← IO.FS.readFile p
    lines := lines ++ (txt.splitOn "\n").toArray.map (·.replace "\r" "")
  return lines

end Effect4Gen.View

open Effect4Gen.View in
def main (argv : List String) : IO Unit := do
  let args ← match parseArgs argv {} with
    | .ok a => pure a
    | .error e => throw (IO.userError e)
  if args.imports.isEmpty then
    throw (IO.userError "--imports names the modules the emitted file imports; none given")
  if args.types.isEmpty then
    throw (IO.userError "no types to generate")
  let variancesText ← IO.FS.readFile ⟨args.variances⟩
  let heads ← match readHeads variancesText with
    | .ok h => pure h
    | .error e => throw (IO.userError e)
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules (args.imports.map fun i => { module := i.toName }).toArray {} 0
  let ctx : Core.Context := { fileName := "<gen>", fileMap := default }
  let act : MetaM Unit := do
    let lines ← run args heads
    let stamp := Tools.GeneratedStamp.note "tools/Effect4Gen/View.lean"
    let text := "-- " ++ stamp ++ "\n" ++ String.intercalate "\n" lines.toList ++ "\n"
    match args.out with
    | some p => IO.FS.writeFile p text
    | none => IO.println text
  let _ ← (act.run' {}).toIO ctx { env := env }
