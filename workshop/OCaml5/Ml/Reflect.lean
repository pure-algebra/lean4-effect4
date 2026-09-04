import OCaml5.Ml.Render

/-!
# OCaml5.Ml.Reflect

The description layer: what a *Lean* declaration looks like, and the two mappings that turn one
into an `OCaml5.Ml.Syntax` type declaration.

This is a **reflected description**, not Lean metaprogramming. `StructDesc` and `InductiveDesc`
are ordinary data; a caller populates them by hand from a Lean file, and `toTypeDecl` turns one
into a `TypeDecl`. Nothing here inspects a Lean declaration. When the mapping is settled, an
elaborator that builds these values from `Lean.Expr` is a separate, later step, and these types
are the interface it would target.

## The division of labour

The renderer owns everything mechanical: order, arity, mutability, layout, and the names. This
module owns the two things a renderer cannot decide.

* **Names.** `mangleField`, `typeName`, `ctorName` and `tyVarName` (`OCaml5.Ml.Identifier`), plus
  the per-type constructor prefix and the per-constructor override, which are *not* derivable:
  they are how one OCaml module keeps two Lean types' constructors from colliding.
* **Types.** `Subst` is one visible list per module saying what each Lean type head becomes. A
  head with no entry falls through to `typeName` applied to its own name, so a carrier that *is*
  transcribed needs no entry; an entry is exactly a decision someone made by hand.

## Every divergence is declared

The point of `FieldKind` and `CtorArg.erased` is that a rendered type may differ from its Lean
spelling only in a way the description **names**. Four vocabularies, from the P5 report §11:

| kind | meaning |
| --- | --- |
| `literal` (= `keep`) | rendered, as written |
| `substitute` | rendered, with no Lean counterpart; the description says why |
| `erased` | not rendered, and the Lean field is not needed by the port |
| `hole` | not rendered, and the port must supply something in its place |

`erased` and `hole` differ in what they oblige: an erasure is a decision that the OCaml side does
without the field, a hole is a promise that a human writes it. `StructDesc.holes` lists the
second so a check can insist, and `StructDesc.erasures` the first so a count can.
-/

namespace OCaml5.Ml

/-! ## Lean types, and the substitution -/

/-- A Lean type expression, as much of one as the description needs: a head and its arguments. -/
inductive LTy where
  | app (head : String) (args : List LTy)
deriving Repr, Inhabited

namespace LTy
def nm (h : String) : LTy := .app h []
def opt (t : LTy) : LTy := .app "Option" [t]
def lst (t : LTy) : LTy := .app "List" [t]
def arr (t : LTy) : LTy := .app "Array" [t]
def nat : LTy := .app "Nat" []
def int : LTy := .app "Int" []
def bool : LTy := .app "Bool" []
def str : LTy := .app "String" []
def unit : LTy := .app "Unit" []
/-- The head of a Lean type, which is what `Subst` is keyed on. -/
def head : LTy → String | .app h _ => h
end LTy

/-- What each Lean type head becomes in OCaml. Keyed on the **head only**: `Exit β ε δ ι α` and
`Exit β' ε' δ' ι' α'` are both `exitv` when the module is one profile of a family and its
arguments are fixed by a fixture. A head with no entry falls through to `typeName` applied to its
own name, with its arguments lowered — so a carrier that *is* transcribed needs no entry. -/
abbrev Subst := List (String × Ty)

private def substLookup : Subst → String → Option Ty
  | [], _ => none
  | (k, v) :: rest, n => if k == n then some v else substLookup rest n

/-- The Lean type heads every profile maps the same way: the base types and the two containers.
A `Subst` never needs an entry for these, and `Check` reports one that shadows them. -/
def builtinHeads : List String :=
  ["Nat", "Int", "Bool", "String", "Char", "Float", "Unit", "Option", "List", "Array"]

mutual

/-- One Lean type as one OCaml type, against a substitution table. -/
def lowerTy (tbl : Subst) : LTy → Ty
  | .app "Nat" [] => Ty.int
  | .app "Int" [] => Ty.int
  | .app "Bool" [] => Ty.bool
  | .app "String" [] => Ty.string
  | .app "Char" [] => Ty.char
  | .app "Float" [] => Ty.float
  | .app "Unit" [] => Ty.unit
  | .app "Option" [t] => Ty.option (lowerTy tbl t)
  | .app "List" [t] => Ty.list (lowerTy tbl t)
  | .app "Array" [t] => Ty.array (lowerTy tbl t)
  | .app h args =>
      match substLookup tbl h with
      | some t => t
      | none => .con (typeName h) (lowerTys tbl args)

def lowerTys (tbl : Subst) : List LTy → List Ty
  | [] => []
  | t :: rest => lowerTy tbl t :: lowerTys tbl rest

end

/-! ## What becomes of one member -/

/-- What becomes of one Lean field. -/
inductive FieldKind where
  /-- Rendered, as written. Spelled `literal` in the report's vocabulary. -/
  | keep
  /-- Not rendered. The note says what the port must fill in, and `StructDesc.holes` names it so
  a check can insist that something does. -/
  | hole (note : String)
  /-- An OCaml field with no Lean counterpart. This is the one divergence a simulation relation
  cannot state as an equality, so a `substitute` should carry a `leading` comment saying what it
  stands for. -/
  | substitute
  /-- Not rendered, and nothing stands in its place: the port does without it. Unlike a `hole`,
  an erasure obliges nobody. -/
  | erased (note : String)
deriving Repr, Inhabited

namespace FieldKind
/-- The report's name for `keep`. -/
def literal : FieldKind := .keep
/-- Whether the field reaches the OCaml record. -/
def rendered : FieldKind → Bool
  | .keep => true
  | .substitute => true
  | .hole _ => false
  | .erased _ => false
end FieldKind

/-- One field of a Lean `structure`, and what becomes of it. -/
structure FieldDesc where
  leanName : String
  leanTy : LTy
  isMutable : Bool := false
  kind : FieldKind := .keep
  /-- Only for a `substitute`, whose name is not a mangled Lean name. -/
  ocamlName : Option String := none
  comment : Option String := none
  leading : List String := []
deriving Repr, Inhabited

/-- One argument of a Lean constructor. -/
structure CtorArg where
  leanName : String
  leanTy : LTy
  /-- Dropped from the OCaml arity. Every use is a divergence and is counted by
  `InductiveDesc.erasures`. -/
  erased : Bool := false
deriving Repr, Inhabited

/-- One constructor of a Lean `inductive`. -/
structure CtorDesc where
  leanName : String
  args : List CtorArg := []
  /-- Overrides `ctorName`, for a name that would collide inside one module. Not derivable:
  it is a fact about the target module, not about the Lean type. -/
  ocamlName : Option String := none
  comment : Option String := none
  /-- The GADT return type, for a constructor of an extensible or indexed variant. -/
  result : Option LTy := none
deriving Repr, Inhabited

/-! ## Structures -/

/-- A Lean `structure`, in Lean field order. -/
structure StructDesc where
  leanName : String
  /-- Where it lives, for the generated comment: `"Fibers.lean:157"`. -/
  site : String
  subst : Subst
  fields : List FieldDesc
  /-- The Lean type parameters, in order, by their Lean names (`"ν"`, `"α"`). They become OCaml
  type variables through `tyVarName`; a variance is set here when the parameter is phantom. -/
  leanParams : List String := []
  /-- Variances for `leanParams`, positionally; shorter than `leanParams` means the rest are
  invariant. Only a variance makes a parameter no field determines legal. -/
  variances : List Variance := []
deriving Repr, Inhabited

/-- The OCaml name of a described field. -/
def FieldDesc.ocaml (d : FieldDesc) : String :=
  match d.ocamlName with
  | some n => n
  | none => mangleField d.leanName

private def toField (tbl : Subst) (d : FieldDesc) : Field :=
  { name := d.ocaml, ty := lowerTy tbl d.leanTy, isMutable := d.isMutable, comment := d.comment,
    leading := d.leading }

/-- A declared type parameter lowers to its own type variable. These entries are prepended to
the description's `Subst`, so a **parameter wins over the table**: a family's `ν` is `'nu` inside
a declaration that binds `ν`, and whatever the table says everywhere else. -/
def paramSubst (leanParams : List String) : Subst :=
  leanParams.map fun p => (p, Ty.var (tyVarName p))

/-- The OCaml type parameters of a description: `leanParams` through `tyVarName`, with the
variance at the same index. -/
private def toTyParams (leanParams : List String) (variances : List Variance) : List TyParam :=
  leanParams.zipIdx.map fun (p, i) =>
    { name := tyVarName p, variance := variances.getD i .invariant }

/-- The Lean fields this description refuses to render, with the note saying what must fill
them. -/
def StructDesc.holes (d : StructDesc) : List (String × String) :=
  d.fields.filterMap fun f =>
    match f.kind with
    | .hole note => some (f.leanName, note)
    | _ => none

/-- The Lean fields this description drops outright. -/
def StructDesc.erasures (d : StructDesc) : List (String × String) :=
  d.fields.filterMap fun f =>
    match f.kind with
    | .erased note => some (f.leanName, note)
    | _ => none

/-- The fields with no Lean counterpart. -/
def StructDesc.substitutes (d : StructDesc) : List String :=
  d.fields.filterMap fun f =>
    match f.kind with
    | .substitute => some f.ocaml
    | _ => none

/-- The fields that reach the OCaml record. -/
def StructDesc.renderedFields (d : StructDesc) : List FieldDesc :=
  d.fields.filter (·.kind.rendered)

/-- The OCaml record: same order, same arity minus the holes and erasures, `mutable` where the
description says so, field names mangled. -/
def StructDesc.typeDecl (d : StructDesc) : TypeDecl :=
  { name := typeName d.leanName,
    tparams := toTyParams d.leanParams d.variances,
    body := .record (d.renderedFields.map (toField (paramSubst d.leanParams ++ d.subst))) }

/-- The record as a structure item. -/
def StructDesc.decl (d : StructDesc) : Decl := .types [d.typeDecl]

/-- The comment the generator puts above the record: the Lean site, the field count, and every
hole, so that a refusal is visible in the output and not only in the description. -/
def StructDesc.header (d : StructDesc) : Decl :=
  .comment (s!"`{d.leanName}` (`{d.site}`), {d.fields.length} Lean fields, "
    ++ s!"{d.renderedFields.length}"
    ++ " rendered. Generated by OCaml5.Ml."
    ++ String.join (d.holes.map fun h => s!"\n     HOLE {h.1}: {h.2}")
    ++ String.join (d.erasures.map fun h => s!"\n     ERASED {h.1}: {h.2}"))

/-! ## Inductives -/

/-- A Lean `inductive`, in Lean constructor order. -/
structure InductiveDesc where
  leanName : String
  site : String
  /-- Prepended to every constructor name; when empty the initial is capitalised instead.
  Not derivable — see the module docstring. -/
  ctorPrefix : String := ""
  subst : Subst
  ctors : List CtorDesc
  /-- As `StructDesc.leanParams`. -/
  leanParams : List String := []
  variances : List Variance := []
deriving Repr, Inhabited

/-- The OCaml name of a described constructor, under a prefix. -/
def CtorDesc.ocaml (pfx : String) (c : CtorDesc) : String :=
  match c.ocamlName with
  | some n => n
  | none => ctorName pfx c.leanName

private def toCtor (tbl : Subst) (pfx : String) (c : CtorDesc) : Ctor :=
  { name := CtorDesc.ocaml pfx c,
    args := lowerTys tbl ((c.args.filter fun a => !a.erased).map (·.leanTy)),
    result := c.result.map (lowerTy tbl),
    comment := c.comment }

/-- The OCaml variant: same order, arity for arity except where an argument is explicitly
`erased`. -/
def InductiveDesc.typeDecl (d : InductiveDesc) : TypeDecl :=
  { name := typeName d.leanName,
    tparams := toTyParams d.leanParams d.variances,
    body := .variant (d.ctors.map (toCtor (paramSubst d.leanParams ++ d.subst) d.ctorPrefix)) }

/-- The variant as a structure item. -/
def InductiveDesc.decl (d : InductiveDesc) : Decl := .types [d.typeDecl]

/-- The Lean arity of each constructor, and the OCaml one; equal unless an argument is erased. -/
def InductiveDesc.arities (d : InductiveDesc) : List (String × Nat × Nat) :=
  d.ctors.map fun c =>
    (c.leanName, c.args.length, (c.args.filter fun a => !a.erased).length)

/-- Every erasure, as `(constructor, argument)`. -/
def InductiveDesc.erasures (d : InductiveDesc) : List (String × String) :=
  d.ctors.flatMap fun c =>
    (c.args.filter (·.erased)).map fun a => (c.leanName, a.leanName)

/-- The comment above the variant. -/
def InductiveDesc.header (d : InductiveDesc) : Decl :=
  .comment (s!"`{d.leanName}` (`{d.site}`), {d.ctors.length} constructors"
    ++ (if d.ctorPrefix.isEmpty then "" else s!", prefix `{d.ctorPrefix}`")
    ++ ". Generated by OCaml5.Ml."
    ++ String.join (d.erasures.map fun e => s!"\n     ERASED {e.1}.{e.2}"))

/-! ## One vocabulary over both -/

/-- The description of one Lean declaration: a `structure` or an `inductive`. This is what an
elaborator would produce and what a generator consumes. -/
inductive TypeDesc where
  | struct (d : StructDesc)
  | induct (d : InductiveDesc)
deriving Repr, Inhabited

namespace TypeDesc

/-- The Lean name of the described declaration. -/
def leanName : TypeDesc → String
  | .struct d => d.leanName
  | .induct d => d.leanName

/-- Where the Lean declaration lives. -/
def site : TypeDesc → String
  | .struct d => d.site
  | .induct d => d.site

/-- The substitution table the description is read against. -/
def subst : TypeDesc → Subst
  | .struct d => d.subst
  | .induct d => d.subst

/-- The OCaml name of the type. -/
def ocamlName (d : TypeDesc) : String := typeName d.leanName

/-- Every place this description diverges from the Lean spelling, as
`(kind, member, note)`. Empty means the OCaml type is the Lean type, member for member. -/
def divergences : TypeDesc → List (String × String × String)
  | .struct d =>
      (d.holes.map fun h => ("hole", h.1, h.2))
        ++ (d.erasures.map fun h => ("erased", h.1, h.2))
        ++ (d.substitutes.map fun n => ("substitute", n, "no Lean counterpart"))
  | .induct d => d.erasures.map fun e => ("erased", e.1 ++ "." ++ e.2, "dropped argument")

end TypeDesc

/-- The one function this module exists for: a described Lean declaration as an OCaml `type`
declaration. Total, and a function of the description alone. -/
def toTypeDecl : TypeDesc → TypeDecl
  | .struct d => d.typeDecl
  | .induct d => d.typeDecl

/-- The declaration as a structure item. -/
def TypeDesc.decl (d : TypeDesc) : Decl := .types [toTypeDecl d]

/-- The generated comment above it. -/
def TypeDesc.header : TypeDesc → Decl
  | .struct d => d.header
  | .induct d => d.header

/-- A whole group as one `and`-joined declaration, which is what a set of mutually recursive
Lean carriers becomes. -/
def toTypeDecls (ds : List TypeDesc) : Decl := .types (ds.map toTypeDecl)

/-! ## The other direction: an OCaml library type, described

`toTypeDecl` goes Lean → OCaml. This goes **OCaml → Lean**: given a type declaration as
`Ml.Syntax` data — from a signature written here, or, once the `effect4` switch exists, parsed
out of a real `.mli` by `tools/ml-check.sh`'s ppxlib lane — it produces the `TypeDesc` a Lean
carrier would be described by. That is what lets a library type be *named* in Lean rather than
retyped, and it is the same description the forward direction consumes, so the two compose.

Three things are lossy and are named rather than hidden:

* `int` lifts to `Int`, not `Nat`. OCaml's `int` is signed and 63-bit (`Profile`'s
  `Int.wraps_63`); `Nat` is the wrong carrier for it and `lowerTy` maps both back to `int`.
* A form `LTy` cannot spell — an arrow, a tuple, a polymorphic variant — lifts to a reserved
  head (`Arrow`, `Tuple`, `Opaque`) whose arguments are lifted in turn. `lowerTy` does not
  understand those heads, so a description carrying one does not round-trip; `liftFaithful`
  decides whether one does.
* An abbreviation, an abstract type and an extensible one describe no members, so `ofTypeDecl`
  answers `none` for them.

The round trip that does hold is the one that matters: for a record or variant whose members are
built from constructors, base types, `option`, `list`, `array` and the declaration's own
parameters, `toTypeDecl (ofTypeDecl inv d) = d`.
-/

/-- What each OCaml type-constructor name becomes as a Lean head. The inverse of `Subst`, and
like it a per-module list of decisions. A name with no entry falls through to
`leanTypeName`. -/
abbrev InvSubst := List (String × String)

private def invLookup : InvSubst → String → Option String
  | [], _ => none
  | (k, v) :: rest, n => if k == n then some v else invLookup rest n

/-- The inverse of `typeName` on a snake_case OCaml type name: `run_fiber` → `RunFiber`. -/
def leanTypeName (s : String) : String :=
  let u := unmangleField s
  match u.toList with
  | [] => u
  | c :: rest => String.ofList (Char.ofNat (if c.isLower then c.toNat - 32 else c.toNat) :: rest)

/-- The inverse of `ctorName ""`: `ResumeAwait` → `resumeAwait`. -/
def leanCtorName (s : String) : String :=
  match s.toList with
  | [] => s
  | c :: rest => String.ofList (Char.ofNat (if c.isUpper then c.toNat + 32 else c.toNat) :: rest)

/-- The reserved `LTy` heads a lift uses for a form `LTy` cannot spell. -/
def liftedHeads : List String := ["Arrow", "Tuple", "PolyVariant", "Opaque"]

mutual

/-- One OCaml type as one Lean type. -/
def liftTy (inv : InvSubst) : Ty → LTy
  | .con "int" [] => .int
  | .con "bool" [] => .bool
  | .con "string" [] => .str
  | .con "char" [] => .app "Char" []
  | .con "float" [] => .app "Float" []
  | .con "unit" [] => .unit
  | .con "option" [t] => .opt (liftTy inv t)
  | .con "list" [t] => .lst (liftTy inv t)
  | .con "array" [t] => .arr (liftTy inv t)
  | .var n => .nm n
  | .anon => .app "Opaque" []
  | .con n args =>
      match invLookup inv n with
      | some h => .app h (liftTys inv args)
      | none => .app (leanTypeName n) (liftTys inv args)
  | .arrow x y => .app "Arrow" [liftTy inv x, liftTy inv y]
  | .larrow _ x y => .app "Arrow" [liftTy inv x, liftTy inv y]
  | .tuple ps => .app "Tuple" (liftTys inv ps)
  | .polyVariant _ _ => .app "PolyVariant" []
  | .asVar t _ => liftTy inv t

def liftTys (inv : InvSubst) : List Ty → List LTy
  | [] => []
  | t :: rest => liftTy inv t :: liftTys inv rest

end

/-! `liftFaithful t`: whether a lifted type round-trips, i.e. uses none of the reserved heads. -/
mutual
def liftFaithful : LTy → Bool
  | .app h args => !(liftedHeads.contains h) && liftFaithfuls args
def liftFaithfuls : List LTy → Bool
  | [] => true
  | t :: rest => liftFaithful t && liftFaithfuls rest
end

private def liftField (inv : InvSubst) (f : Field) : FieldDesc :=
  { leanName := unmangleField f.name, leanTy := liftTy inv f.ty, isMutable := f.isMutable,
    kind := .keep, ocamlName := some f.name, comment := f.comment, leading := f.leading }

private def liftCtorArgs (inv : InvSubst) (i : Nat) : List Ty → List CtorArg
  | [] => []
  | t :: rest =>
      { leanName := "a" ++ toString i, leanTy := liftTy inv t }
        :: liftCtorArgs inv (i + 1) rest

private def liftCtor (inv : InvSubst) (c : Ctor) : CtorDesc :=
  { leanName := leanCtorName c.name, args := liftCtorArgs inv 0 c.args,
    ocamlName := some c.name, comment := c.comment,
    result := c.result.map (liftTy inv) }

private def tparamsOf (d : TypeDecl) : List String × List Variance :=
  if d.tparams.isEmpty then (d.params, [])
  else (d.tparams.map (·.name), d.tparams.map (·.variance))

/-- An OCaml type declaration as a Lean description. `none` for an abbreviation, an abstract
type or an extensible one: they describe no members. `site` says where the declaration came
from, which for a library type is its `.mli`. -/
def ofTypeDecl (inv : InvSubst) (site : String) (d : TypeDecl) : Option TypeDesc :=
  let (ps, vs) := tparamsOf d
  match d.body with
  | .record fs =>
      some (.struct { leanName := leanTypeName d.name, site := site, subst := [],
                      leanParams := ps, variances := vs, fields := fs.map (liftField inv) })
  | .variant cs =>
      some (.induct { leanName := leanTypeName d.name, site := site, subst := [],
                      leanParams := ps, variances := vs, ctors := cs.map (liftCtor inv) })
  | _ => none

/-- Every type a signature declares, described. This is how a library `.mli`, once it is
`Ml.Syntax` data, becomes something a Lean carrier can be stated against. -/
def ofSigItems (inv : InvSubst) (site : String) : List SigItem → List TypeDesc
  | [] => []
  | .types group :: rest =>
      group.filterMap (ofTypeDecl inv site) ++ ofSigItems inv site rest
  | _ :: rest => ofSigItems inv site rest

/-- Every type a module type declares. -/
def ofModTy (inv : InvSubst) (site : String) : ModTy → List TypeDesc
  | .sig items => ofSigItems inv site items
  | .functor _ _ res => ofModTy inv site res
  | .withType base _ _ _ => ofModTy inv site base
  | .path _ => []

/-! ## Checks -/

private def probeSubst : Subst := [("FiberId", Ty.int), ("ν", Ty.string)]

#guard renderTy (lowerTy probeSubst (.lst (.nm "FiberId"))) == "int list"
#guard renderTy (lowerTy probeSubst (.opt (.nm "ν"))) == "string option"
#guard renderTy (lowerTy probeSubst (.app "RunFiber" [.nm "ν"])) == "string run_fiber"
#guard renderTy (lowerTy probeSubst (.nm "Nat")) == "int"

private def probeStruct : StructDesc where
  leanName := "Pending"
  site := "Fibers.lean:81"
  subst := probeSubst
  leanParams := ["ν"]
  fields :=
    [{ leanName := "token", leanTy := .nat },
     { leanName := "exit", leanTy := .opt (.nm "ν"), isMutable := true },
     { leanName := "step", leanTy := .nm "Prim", kind := .hole "the OCaml 5 stack" },
     { leanName := "control", leanTy := .nm "Control", kind := .substitute,
       ocamlName := some "control" }]

-- `ν` is in `probeSubst` as `string` and is also a declared parameter of `Pending`, so the
-- parameter wins: `'nu option`, not `string option`.
#guard renderDecl (TypeDesc.struct probeStruct).decl ==
  "type 'nu pending = { token : int; mutable exit_ : 'nu option; control : control }"
#guard probeStruct.holes == [("step", "the OCaml 5 stack")]
#guard probeStruct.substitutes == ["control"]
#guard (TypeDesc.struct probeStruct).divergences.map (·.1) == ["hole", "substitute"]

private def probeInductive : InductiveDesc where
  leanName := "Task"
  site := "Fibers.lean:104"
  ctorPrefix := "T"
  subst := probeSubst
  ctors :=
    [{ leanName := "start", args := [⟨"owner", .nm "FiberId", false⟩] },
     { leanName := "resume", args := [⟨"owner", .nm "FiberId", false⟩,
                                      ⟨"context", .nm "χ", true⟩] }]

#guard renderDecl (TypeDesc.induct probeInductive).decl ==
  "type task = Tstart of int | Tresume of int"
#guard probeInductive.erasures == [("resume", "context")]
#guard probeInductive.arities == [("start", 1, 1), ("resume", 2, 1)]

-- A phantom parameter: no field determines `'b`, so it carries a variance and OCaml accepts it.
private def phantomStruct : StructDesc where
  leanName := "Tagged"
  site := "probe"
  subst := []
  leanParams := ["α", "β"]
  variances := [.invariant, .covariant]
  fields := [{ leanName := "value", leanTy := .nm "α" }]

#guard renderDecl (TypeDesc.struct phantomStruct).decl == "type ('a, +'b) tagged = { value : 'a }"

-- The other direction, and the round trip.
private def libRecord : TypeDecl :=
  { name := "pending", params := ["nu"],
    body := .record [{ name := "token", ty := Ty.int },
                     { name := "exit_", ty := Ty.option (.var "nu"), isMutable := true },
                     { name := "kids", ty := Ty.list (.con "fiber" []) }] }

private def libVariant : TypeDecl :=
  { name := "task", params := ["b"],
    body := .variant [{ name := "Tstart", args := [Ty.int] },
                      { name := "Tresume", args := [Ty.int, .var "b"] }] }

#guard leanTypeName "run_fiber" == "RunFiber"
#guard leanTypeName "pending" == "Pending"
#guard leanCtorName "ResumeAwait" == "resumeAwait"
#guard typeName (leanTypeName "run_fiber") == "run_fiber"

-- A record and a variant both round-trip: OCaml → description → OCaml renders the same bytes.
-- (Text and not `BEq`: `TypeDecl` nests through three lists and the deriving handler does not
-- apply, and the bytes are what every other check in the estate compares anyway.)
private def rt (d : TypeDecl) : Bool :=
  match (ofTypeDecl [] "probe.mli" d).map toTypeDecl with
  | none => false
  | some d' => renderDecl (.types [d']) == renderDecl (.types [d])

#guard rt libRecord
#guard rt libVariant

-- …and the description that comes back is a real one: named, sited, with its Lean field names.
#guard ((ofTypeDecl [] "probe.mli" libRecord).map TypeDesc.leanName) == some "Pending"
#guard (match ofTypeDecl [] "probe.mli" libRecord with
        | some (.struct d) => d.fields.map (·.leanName)
        | _ => []) == ["token", "exit", "kids"]
#guard (match ofTypeDecl [] "probe.mli" libVariant with
        | some (.induct d) => d.ctors.map (·.leanName)
        | _ => []) == ["tstart", "tresume"]

-- An abbreviation describes no members.
#guard (ofTypeDecl [] "probe.mli" { name := "id", body := .alias Ty.int }).isNone

-- The lossy heads are named, and `liftFaithful` decides which lifts round-trip.
#guard liftFaithful (liftTy [] (Ty.list Ty.int))
#guard !(liftFaithful (liftTy [] (.arrow Ty.int Ty.int)))
#guard !(liftFaithful (liftTy [] (.tuple [Ty.int, Ty.bool])))
#guard renderTy (lowerTy [] (liftTy [] (Ty.option (.con "run_fiber" [])))) == "run_fiber option"

-- A whole signature: every type it declares, described.
#guard (ofModTy [] "probe.mli" (.sig [.types [libRecord, libVariant],
                                      .val "f" (.arrow Ty.int Ty.int)])).length == 2

end OCaml5.Ml
