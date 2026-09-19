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
    out := out ++ [({ name := name, variance := variance, cite := cite } : Head)]
  return out

/-! ## The constructor declarations -/

/-- One field of a constructor: a `Ty` child, or a payload `sameHead` compares by `==`. -/
inductive Field where
  | child (name : String)
  | payload (name : String) (ty : String)
deriving Repr

structure Ctor where
  name : String
  fields : List Field
deriving Repr

def Ctor.children (c : Ctor) : List String :=
  c.fields.filterMap fun f => match f with | .child n => some n | .payload _ _ => none

def Ctor.payloads (c : Ctor) : List (String × String) :=
  c.fields.filterMap fun f => match f with | .child _ => none | .payload n t => some (n, t)

/-- The payload sorts `sameHead` can compare. A field of any other type is refused by name. -/
def knownPayload : List String := ["String", "Nat"]

def shortName (n : Name) : String := n.componentsRev.head!.toString

def srcOf (e : Expr) : MetaM String := do
  withOptions (fun o => (o.setBool `pp.fullNames true).setBool `pp.universes false) do
    return toString (← ppExpr e)

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
    match heads.find? (fun h => h.name == c.name) with
    | some h =>
      if h.variance.length != n then
        return .error s!"View: `Ty.{c.name}` has {n} recursive field(s) but \
          tools/Effect4Gen/variances.json declares {h.variance.length} variance(s) for it"
      out := out ++ [({ ctor := c, head := some h } : Row)]
    | none =>
      if n != 0 then
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
    match f with | .child n => n ++ suffix | .payload n _ => n ++ suffix)

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
        match f with | .child nm => nm | .payload _ _ => "_")
    s := s ++ [s!"  | {lhs} => {body}{cite}"]
  return s ++ [""]

def emitSameHead (rs : List Row) : List String := Id.run do
  let mut s : List String :=
    [ "/-- Same constructor and equal non-recursive payload. -/",
      "def sameHead : Ty → Ty → Bool" ]
  for r in rs do
    let c := r.ctor
    if notCongruent.any (fun p => p.1 == c.name) then continue
    let ps := c.payloads
    let body :=
      if ps.isEmpty then "true"
      -- `decide (x = y)`, not `x == y`: at `String` and `Nat` the `LawfulBEq` instance reaches
      -- `Classical.choice`, and `decide` through the derived `DecidableEq` reaches no axiom
      else String.intercalate " && " (ps.map fun p => s!"decide ({p.1}1 = {p.1}2)")
    let side (suffix : String) : String :=
      if c.fields.isEmpty then s!".{c.name}"
      else s!".{c.name} " ++ String.intercalate " " (c.fields.map fun f =>
        match f with | .child _ => "_" | .payload n _ => n ++ suffix)
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
    let binders :=
      if c.fields.isEmpty then ""
      else " " ++ String.intercalate " " (c.fields.map fun f =>
        match f with | .child nm => nm | .payload nm _ => nm)
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
def emitOrderLaws : List String :=
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
      "    (h1 : argsBelow r a b = true) (h2 : argsBelow r b a = true) : a = b := by",
      "  refine eq_of_sameHead hab (zipAll_antisymm a.args b.args (args_congr hab).2 ?_ h1 h2)",
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
      "  exact eq_of_sameHead h (by rw [hx, hb])",
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
      "  case case6 => exact Bool.noConfusion hlit",
      "  case case16 => rfl",
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
    "theorem argsBelow_refl (t : Ty) : argsBelow sub t t = true := by",
    "  cases t <;>",
    "    simp only [argsBelow, args, Variance.holds, List.zip, List.zipWith, List.all_cons,",
    "      List.all_nil, Bool.and_true, sub_refl]",
    "",
    "/-- Corresponding arguments correspond: same length, same variances. -/",
    "theorem args_congr {a b : Ty} (h : sameHead a b = true) :",
    "    a.args.length = b.args.length ∧ a.args.map Prod.fst = b.args.map Prod.fst := by",
    "  cases a <;> cases b <;> aesop (add norm simp [sameHead, args])",
    "",
    "/-- A node is its head and its children. -/",
    "theorem eq_of_sameHead {a b : Ty} (h : sameHead a b = true)",
    "    (hx : a.args.map Prod.snd = b.args.map Prod.snd) : a = b := by",
    "  cases a <;> cases b <;> aesop (add norm simp [sameHead, args, " ++ injEqs ++ "])",
    "",
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
  lines := lines ++ #["", "set_option autoImplicit false", "", "namespace Effect4.Program", ""]
  for t in args.types do
    let ctors ← readCtors t.toName
    let rs ← match rows ctors heads with
      | .error e => throwError e
      | .ok rs => pure rs
    lines := lines.push (join (["namespace Ty", ""] ++ emitVariance ++ emitArgs rs ++
      emitSameHead rs ++ emitRules ++ emitProbes rs ++ emitLaws rs ++ emitArmLemmas rs ++ emitDispatch rs ++ emitSizeOf rs ++ emitOrderLaws ++
      ["end Ty", ""] ++ emitAdmits rs))
  lines := lines ++ #["end Effect4.Program", ""]
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
