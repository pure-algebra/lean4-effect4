import Lean
import Tools.GeneratedStamp

/-!
# Effect4Gen.View — the relational view of `Ty` (tooling plan 1.4)

From the constructor declarations of `Ty` and the variance table read off rc.112
(`tools/Effect4Gen/variances.json`, `tools/Tools/Variances.lean`), nothing hand-listed:

* `Variance`, `Variance.holds` — how a relation reads a recursive argument.
* `Ty.args : Ty → List (Variance × Ty)` — the immediate children with the variance the order
  reads them at.
* `Ty.sameHead`, `Ty.litRule`, `Ty.topRule`, `Ty.argsBelow` — the head test and the rules the
  order has beside its congruences.
* `Ty.sub_eq_args` — **the** law: between two members that are neither the literal rule nor the
  top, `sub` is the variance-wise comparison of corresponding arguments. Everything a relational
  proof needs to know about `Ty`'s constructors, in one statement, so the proofs of the order
  stop naming constructors and a new one costs a declared variance line instead of an arm in
  every proof.
* `Ty.sameHead_refl/symm/trans`, `Ty.args_congr`, `Ty.sizeOf_args`, `Ty.eq_of_sameHead`,
  `Ty.argsBelow_refl`, `Variance.holds_trans`, `Variance.holds_antisymm` — the small laws those
  proofs stand on.
* `Effect4.Program.AdmitsSub` — one field per constructor: what an admission algebra must
  satisfy for its fold to respect `sub` (tooling plan 1.5; `Laws/Program/Admits.lean` proves
  `cata_admits_sub` from it, once).

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
* a field that is not first-order, which the carrier rule of `Ty.lean`'s header already refuses.

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
  /-- `"arity": "each"`: a head of variable arity, its one variance read at every child. -/
  each : Bool := false
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
      | .error _ => (row.getObjValAs? String "spelling").toOption.getD "(the printer's spelling)"
    let each ← match row.getObjVal? "arity" with
      | .ok v => do
        let a ← v.getStr?
        unless a == "each" do
          throw s!"variances.json: head {name} has arity {a}; the one arity word is `each`"
        pure true
      | .error _ => pure false
    out := out ++ [({ name := name, variance := variance, cite := cite, each := each } : Head)]
  return out

/-! ## The constructor declarations -/

/-- One field of a constructor: a `Ty` child, a payload `sameHead` compares by `==`, or a
field list (variable arity): a `List` of elements `String × Ty` (or `String × Ty × P`), the `Ty`
at the selector `child`, the payload components at `payloads` (selector, type), the element's
printed type with the member written `{M}`. -/
inductive Field where
  | child (name : String)
  | payload (name : String) (ty : String)
  | fieldList (name : String) (child : String) (payloads : List (String × String)) (elem : String)
deriving Repr

structure Ctor where
  name : String
  fields : List Field
deriving Repr

def Ctor.children (c : Ctor) : List String :=
  c.fields.filterMap fun f => match f with | .child n => some n | _ => none

def Ctor.payloads (c : Ctor) : List (String × String) :=
  c.fields.filterMap fun f => match f with | .payload n t => some (n, t) | _ => none

/-- The field list of a head of variable arity: (name, child selector, payloads, element). -/
def Ctor.fieldList? (c : Ctor) : Option (String × String × List (String × String) × String) :=
  c.fields.findSome? fun f => match f with
    | .fieldList n ch ps e => some (n, ch, ps, e)
    | _ => none

/-- A field-list element's payload as an expression of the element `p`: its one selector, or the
tuple of them. -/
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
member written `{M}`. `none` for any other type, which the caller refuses as before. -/
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
    let isVar := c.fieldList?.isSome
    match heads.find? (fun h => h.name == c.name) with
    | some h =>
      if isVar then
        unless h.each && h.variance.length == 1 && c.fields.length == 1 do
          return .error s!"View: `Ty.{c.name}` has a field list (variable arity): its row in \
            tools/Effect4Gen/variances.json must say \"arity\": \"each\" with one variance, and \
            the constructor must have that one field"
        unless h.variance == [Variance.co] do
          return .error s!"View: `Ty.{c.name}`: a variable-arity head is read covariantly only \
            (its arm lemma reads `sub` at each field)"
        out := out ++ [({ ctor := c, head := some h } : Row)]
        continue
      if h.each then
        return .error s!"View: `Ty.{c.name}` has fixed arity but its row says \"arity\": \"each\""
      if h.variance.length != n then
        return .error s!"View: `Ty.{c.name}` has {n} recursive field(s) but \
          tools/Effect4Gen/variances.json declares {h.variance.length} variance(s) for it"
      out := out ++ [({ ctor := c, head := some h } : Row)]
    | none =>
      if n != 0 || isVar then
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
    match f with | .child n => n ++ suffix | .payload n _ => n ++ suffix | .fieldList n _ _ _ => n ++ suffix)

def emitVariance : List String :=
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
    if let some (nm, ch, _, _) := r.ctor.fieldList? then
      let v := ((r.head.map (fun h => h.variance)).getD [.co]).headD .co
      let cite := (r.head.map (fun h => s!"  -- {h.cite}")).getD ""
      s := s ++ [s!"  | .{r.ctor.name} {nm} => (canon {nm}).map fun p => (.{v.text}, p{ch}){cite}"]
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
    if let some (nm, _, ps, _) := c.fieldList? then
      -- the head of a field list is its payloads (the names, and any modifier) in canonical order
      let pay := payText ps
      s := s ++ [s!"  | .{c.name} {nm}1, .{c.name} {nm}2 =>",
        s!"    decide ((canon {nm}1).map (fun p => {pay}) = (canon {nm}2).map (fun p => {pay}))"]
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

def emitRules : List String :=
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

/-- What a head of variable arity needs beside the laws: the list facts its children are read
through (fixed text), and per field-list constructor its `headCanon` arm, the measure of a field,
and the field list from its payloads and children. Empty when no head has variable arity, so
the view of a family without one is byte-identical to what the generator wrote before. -/
def emitVarHelpers (rs : List Row) : List String := Id.run do
  let vrs := rs.filter fun r => r.ctor.fieldList?.isSome
  if vrs.isEmpty then return []
  let mut s : List String :=
    [ "/-! ### What a head of variable arity reads its children through -/",
      "",
      "/-- A list zipped with itself compares each child with itself. -/",
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
      "/-- `all` over an attached list reads the values: `sub`'s field-list arm attaches for its",
      "termination, the view does not. -/",
      "theorem all_attach_eq {α : Type} (l : List α) (f : α → Bool) :",
      "    (l.attach.all fun x => f x.1) = l.all f := by",
      "  have h := List.all_map (l := l.attach) (f := Subtype.val) (p := f)",
      "  rw [List.attach_map_subtype_val] at h",
      "  exact h.symm",
      "",
      "/-- A head whose children are read in canonical order is in that order already. -/",
      "def headCanon : Ty → Bool" ]
  for r in vrs do
    let some (nm, _, _, _) := r.ctor.fieldList? | continue
    s := s ++ [s!"  | .{r.ctor.name} {nm} => decide (canon {nm} = {nm})"]
  s := s ++ [ "  | _ => true", "",
    "theorem headCanon_of_args_nil {t : Ty} (h : t.args = []) : headCanon t = true := by",
    "  cases t" ]
  for r in vrs do
    s := s ++
      [ s!"  case {r.ctor.name} fields =>",
        "    have hf : fields = [] := canon_eq_nil (List.map_eq_nil_iff.mp h)",
        "    subst hf",
        "    rfl" ]
  s := s ++ [ "  all_goals rfl", "" ]
  for r in vrs do
    let some (_, ch, ps, elem) := r.ctor.fieldList? | continue
    let el := elem.replace "{M}" "Ty"
    let c := r.ctor.name
    let triple := ch != ".2"
    let pay := payText ps
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
        s!"    ∀ \{l l' : List ({el})}, l.map (fun p => {pay}) = l'.map (fun p => {pay}) →",
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
    if let some (_, ch, ps, _) := r.ctor.fieldList? then
      -- an element: the name, the field's type, and `false` for a flag the element carries
      let el (name ty : String) : String :=
        if ch == ".2" then s!"(\"{name}\", {ty})" else s!"(\"{name}\", {ty}, false)"
      let rec_ (els : List String) : String := s!"(.{r.ctor.name} [" ++ String.intercalate ", " els ++ "])"
      let c := r.ctor.name
      s := s ++
        [ s!"-- `{c}`: variable arity, every field {h.variance.headD .co |>.text}; the head is the canonical name list",
          s!"#guard Ty.sub {rec_ [el "a" "(.lit \"a\")"]} {rec_ [el "a" ".string"]}",
          s!"#guard !Ty.sub {rec_ [el "a" ".string"]} {rec_ [el "a" "(.lit \"a\")"]}",
          s!"#guard !Ty.sub {rec_ [el "a" ".nat", el "b" ".bool"]} {rec_ [el "a" ".bool", el "b" ".unit"]}",
          s!"-- TY-10's positive control: a permuted field list is below its canonical order, both ways",
          s!"#guard Ty.sub {rec_ [el "b" ".nat", el "a" ".bool"]} {rec_ [el "a" ".bool", el "b" ".nat"]}",
          s!"#guard Ty.sub {rec_ [el "a" ".bool", el "b" ".nat"]} {rec_ [el "b" ".nat", el "a" ".bool"]}",
          s!"-- names are the head's payload; width is not a rule",
          s!"#guard !Ty.sub {rec_ [el "a" ".nat"]} {rec_ [el "b" ".nat"]}",
          s!"#guard !Ty.sub {rec_ [el "a" ".nat", el "b" ".nat"]} {rec_ [el "a" ".nat"]}" ]
      if ps.length > 1 then
        s := s ++
          [ s!"-- a modifier is payload too: the exact rule does not put a required field below an optional one",
            s!"#guard !Ty.sub (.{c} [(\"a\", .nat, false)]) (.{c} [(\"a\", .nat, true)])" ]
      s := s ++ [""]
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
    if let some (nm, _, _, _) := c.fieldList? then
      s := s ++
        [ s!"  case {c.name} {nm} =>",
          "    simp only [args, List.mem_map, Prod.mk.injEq] at h",
          "    obtain ⟨p, hp, _, hpx⟩ := h",
          s!"    have hlt := sizeOf_field_lt_{c.name} (mem_canon hp)",
          "    rw [hpx] at hlt",
          s!"    simp only [Ty.{c.name}.sizeOf_spec]",
          "    omega" ]
      continue
    let binders :=
      if c.fields.isEmpty then ""
      else " " ++ String.intercalate " " (c.fields.map fun f =>
        match f with | .child nm => nm | .payload nm _ => nm | .fieldList nm _ _ _ => nm)
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
def emitOrderLaws (hasVar : Bool) : List String :=
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
      "",
      "/-- The literal rule fires only into `string`. -/",
      "theorem litRule_eq_false {a b : Ty} (h : b ≠ .string) : litRule a b = false := by",
      "  cases b",
      "  case string => exact absurd rfl h",
      "  all_goals cases a <;> rfl",
      "",
      "/-- At a head with no children, `sameHead` IS equality: a node is its head and its children,",
      "and there are none. -/",
      "theorem eq_of_sameHead_nil {a b : Ty} (h : sameHead a b = true) (hx : a.args = []) : a = b := by",
      "  have hlen := (args_congr h).1",
      "  rw [hx, List.length_nil] at hlen",
      "  have hb : b.args = [] := List.eq_nil_of_length_eq_zero hlen.symm",
      (if hasVar then "  exact eq_of_sameHead h (by rw [hx, hb]) (headCanon_of_args_nil hx) (headCanon_of_args_nil hb)"
       else "  exact eq_of_sameHead h (by rw [hx, hb])"),
      "",
      "/-- The literal rule fires at exactly one pair of shapes. -/",
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
    "" ]

/-- One lemma per congruence arm: `sub` at a pair of nodes with the same head IS the
variance-wise comparison of their arguments. Generated, so a new constructor adds a lemma
rather than an alternative inside an existing proof. -/
def emitArmLemmas (rs : List Row) : List String := Id.run do
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
    if let some (_, ch, _, elem) := c.fieldList? then
      let el := elem.replace "{M}" "Ty"
      s := s ++
        [ s!"/-- The field-list arm: under the head (the canonical name lists equal), `sub` is the",
          "fieldwise comparison in canonical order. It reads `sub`'s arm in the form",
          "`decide (names) && (zip).attach.all …`, the one form this generator proves. -/",
          s!"theorem sub_args_{c.name} (fs gs : List ({el}))",
          s!"    (hh : sameHead (.{c.name} fs) (.{c.name} gs) = true) :",
          s!"    sub (.{c.name} fs) (.{c.name} gs) = argsBelow sub (.{c.name} fs) (.{c.name} gs) := by",
          s!"  by_cases h : Ty.{c.name} fs = Ty.{c.name} gs",
          "  · rw [h, sub_refl, argsBelow_refl]",
          "  · simp only [sameHead] at hh",
          "    conv => lhs; unfold sub",
          "    simp only [h, ↓reduceIte, hh, Bool.true_and, argsBelow, args, List.zip_map, List.all_map,",
          "      Function.comp_def, Prod.map, Variance.holds]",
          s!"    exact all_attach_eq _ (fun (pq : ({el}) × ({el})) => sub pq.1{ch} pq.2{ch})",
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
        "  · conv => lhs; unfold sub",
        "    simp only [h, ↓reduceIte, argsBelow, args, Variance.holds, List.zip, List.zipWith,",
        s!"      List.all_cons, List.all_nil, Bool.and_true{assoc}]",
        "" ]
  return s

/-- The two directions, then the law. The `false` direction is `fun_cases Ty.sub`, where the
catch-all is `rfl`; the `true` direction is `fun_cases Ty.sameHead`, one arm lemma per case. -/
def emitDispatch (rs : List Row) : List String := Id.run do
  -- `sub`'s arms in order: six rules, one congruence arm per head with children (declaration
  -- order, `union` excepted), then the catch-all, so its `fun_cases` number is computed, not
  -- written: an appended head moves it. A field-list arm's value is not constant at a
  -- different head, so it gets its own case.
  let cong := rs.filter fun r => r.head.isSome &&
    (r.ctor.children.length != 0 || r.ctor.fieldList?.isSome) &&
    !notCongruent.any (fun p => p.1 == r.ctor.name)
  let varCases : List String := (cong.zipIdx.filterMap fun (r, k) =>
    if r.ctor.fieldList?.isSome then
      some [s!"  case case{7 + k} =>", "    simp only [sameHead] at hh", "    simp only [hh, Bool.false_and]"]
    else none).flatten
  let catchAll := 7 + cong.length
  let mut s : List String :=
    [ "/-- Different heads: the order answers `false`. `fun_cases Ty.sub` makes the catch-all —",
      "the one case a square-of-constructors proof cannot discharge without search — into `rfl`,",
      "because the arm it takes IS `false`. -/",
      "theorem sub_eq_false_of_not_sameHead (a b : Ty) (ha : isMember a = true)",
      "    (hb : isMember b = true) (hlit : litRule a b = false) (htop : topRule a b = false)",
      "    (hh : sameHead a b = false) : sub a b = false := by",
      "  fun_cases Ty.sub a b",
      "  case case1 => rw [sameHead_refl _ ha] at hh; exact Bool.noConfusion hh",
      "  case case2 => exact Bool.noConfusion ha",
      "  case case3 => exact Bool.noConfusion ha",
      "  case case4 => exact Bool.noConfusion hb",
      "  case case5 => exact Bool.noConfusion htop",
      "  case case6 => exact Bool.noConfusion hlit" ] ++ varCases ++
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
    if c.fieldList?.isSome then
      s := s ++ [s!"  case case{i} => intro hh; exact sub_args_{c.name} _ _ hh"]
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
      "    (hlit : litRule a b = false) (htop : topRule a b = false) :",
      "    sub a b = (sameHead a b && argsBelow sub a b) := by",
      "  cases hh : sameHead a b",
      "  · rw [Bool.false_and]",
      "    exact sub_eq_false_of_not_sameHead a b ha hb hlit htop hh",
      "  · rw [Bool.true_and]",
      "    exact sub_eq_argsBelow_of_sameHead a b hh",
      "" ]
  return s

def emitLaws (rs : List Row) : List String :=
  -- only a constructor with fields has an `injEq`
  let injEqs := String.intercalate ", "
    ((rs.filter fun r => !r.ctor.fields.isEmpty).map fun r => s!"Ty.{r.ctor.name}.injEq")
  let vrs := rs.filter fun r => r.ctor.fieldList?.isSome
  let hasVar := !vrs.isEmpty
  let reflCases := vrs.map fun r =>
    s!"  case {r.ctor.name} fields => exact zip_self_all sub sub_refl _"
  let congrCases := (vrs.map fun r =>
    [ s!"  case {r.ctor.name}.{r.ctor.name} fs gs =>",
      "    have hl := congrArg List.length (of_decide_eq_true h)",
      "    simp only [List.length_map] at hl",
      "    simp only [args, List.length_map, List.map_map, Function.comp_def]",
      "    exact ⟨hl, map_const_eq _ hl⟩" ]).flatten
  let eqCases := (vrs.map fun r =>
    [ s!"  case {r.ctor.name}.{r.ctor.name} fs gs =>",
      "    have hn := of_decide_eq_true h",
      "    simp only [args, List.map_map, Function.comp_def] at hx",
      s!"    have hc : canon fs = canon gs := eq_of_fields_{r.ctor.name} hn hx",
      "    have hf : canon fs = fs := of_decide_eq_true hca",
      "    have hg : canon gs = gs := of_decide_eq_true hcb",
      "    rw [← hf, ← hg, hc]" ]).flatten
  [ "/-- `union` is the one head `sameHead` refuses, so reflexivity is stated at a member; an",
    "`isMember` hypothesis is exactly what every caller of the view has: the one goal the",
    "normalisation leaves is that head, and `isMember` is `false` there. -/",
    "theorem sameHead_refl (t : Ty) (h : isMember t = true) : sameHead t t = true := by",
    "  cases t <;> simp only [sameHead, decide_eq_true_eq" ++
      (if rs.any (fun r => r.ctor.payloads.length >= 2) then ", and_self]" else "]") ++ "",
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
      "/-- A node is its head and its children, read in canonical order: at a head of variable",
      "arity the children are in that order, so the node must be (`headCanon`); a permuted record",
      "has its canonical record's head and children and is a different term. -/",
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
def emitAdmits (rs : List Row) : List String := Id.run do
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
      "the disjunction of its members; the literal rule is an inclusion; a covariant argument is",
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
      "  top : ∀ v al, (alg.ty_unknown).2 v al = true",
      "  /-- the literal rule -/",
      "  lit_string : ∀ s, Adm.le (alg.ty_lit s).2 (alg.ty_string).2",
      "  /-- a template parameter has no inhabitant -/",
      "  var : ∀ i v al, (alg.ty_var i).2 v al = false" ]
  for r in rs do
    let c := r.ctor
    let some h := r.head | continue
    if let some (_, ch, ps, elem) := c.fieldList? then
      let el := elem.replace "{M}" "AdmCarrier .ty"
      let pay := payText ps
      s := s ++
        [ s!"  /-- every field co, the names equal in canonical order ({h.cite}) -/",
          s!"  {c.name} : ∀ (ps qs : List ({el})),",
          s!"    (Ty.canon ps).map (fun p => {pay}) = (Ty.canon qs).map (fun p => {pay}) →",
          s!"    (∀ p q, (p, q) ∈ (Ty.canon ps).zip (Ty.canon qs) → Adm.le (p{ch}).2 (q{ch}).2) →",
          s!"    Adm.le (alg.ty_{c.name} ps).2 (alg.ty_{c.name} qs).2" ]
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
    if let some (_, ch, _, elem) := c.fieldList? then
      let el := elem.replace "{M}" "AdmCarrier .ty"
      s := s ++ [s!"  {c.name} : ∀ (ps : List ({el})), (∀ p ∈ ps, Adm.Extends (p{ch}).2) → \
        Adm.Extends (alg.ty_{c.name} ps).2"]
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
    let rs ← match rows ctors heads with
      | .error e => throwError e
      | .ok rs => pure rs
    -- a head of variable arity reads its children through `Ty.lean`'s canonical order: the
    -- order and the two facts the laws use must exist, or the view is refused by name
    let hasVar := rs.any fun r => r.ctor.fieldList?.isSome
    if hasVar then
      for nm in ["canon", "mem_canon", "canon_eq_nil"] do
        unless (← getEnv).contains (t.toName ++ nm.toName) do
          throwError "View: `{t}` has a head of variable arity, which the view reads through \
            `{t}.{nm}`; it is not in the environment (the order and its facts belong to Ty.lean)"
    lines := lines.push (join (["namespace Ty", ""] ++ emitVariance ++ emitArgs rs ++
      emitSameHead rs ++ emitRules ++ emitProbes rs ++ emitVarHelpers rs ++ emitLaws rs ++ emitArmLemmas rs ++ emitDispatch rs ++ emitSizeOf rs ++ emitOrderLaws hasVar ++
      ["end Ty", ""] ++ emitAdmits rs ++ emitAdmitsExtend ns rs))
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
  let heads ← match readHeads (← IO.FS.readFile ⟨args.variances⟩) with
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
