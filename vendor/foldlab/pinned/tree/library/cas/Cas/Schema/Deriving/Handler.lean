import Cas.Schema.Deriving.Util
import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util

/-!
# `deriving Described`

An opt-in deriving handler for non-recursive types. It uses Lean's
own deriving utilities for parameters, instance binders, names, and
registration, while emitting ordinary definitions and proofs for the
kernel to check.

Two paths, one architecture:

- a **structure** derives as `Ast.struct`, fields canonically sorted by
  JSON name (unchanged since the increment that landed it — the
  emission is byte-identical);
- a **non-recursive inductive** derives as `Ast.union … .oneOf` of
  per-constructor tagged structs, Effect's `TaggedUnion` shape
  (DERIVING-DESIGN §2, UNION-DESIGN.md stage 2).

## Constructor order is a spelling choice, and it is made here

Union member order IS the code's identity (`UNION-DESIGN.md` call 1 —
members are never sorted by the carrier, and two orders are two
addresses). A generator therefore has to PICK one spelling, and this
handler picks **ascending tag string**, not source order. The reason is
determinism across the five seats: the same inductive, however its
constructors are shuffled in the source, derives one code at one
address, exactly as reordering a structure's fields does not move its
address. Source order remains recoverable from the type; the code's
order is canonical.

This is a D1 register note in waiting: R17's union row says order is
semantic and never rearranged by the CARRIER, and that stays true —
the sorting happens once, in the generator, before a code exists.

## The tagged-struct shape

Constructor `c (f₁ : T₁) … (fₙ : Tₙ)` contributes the member

    Ast.struct [("_tag", false, .lit (.str "c")), <fields, sorted>]

so the code is discriminated BY CONSTRUCTION, and the generated
`<T>.schemaDiscriminated` theorem pins that as a fact rather than an
intention. `El` of the code is then the iterated member sum, `toEl` is
the per-constructor match into it, and `ofEl` is tag dispatch.
-/

namespace Cas.Schema.Deriving

open Lean
open Lean.Elab
open Lean.Elab.Command
open Lean.Meta

private def jsonFieldName (field : Name) : String :=
  field.eraseMacroScopes.getString!

private def canonicalFields (indName : Name) : CoreM (Array Name) := do
  let fields := getStructureFieldsFlattened (← getEnv) indName
    (includeSubobjectFields := false)
  return fields.qsort fun a b => jsonFieldName a < jsonFieldName b

private def mkGetter (targetType : Term) (field : Name) : TermElabM Term := do
  let xName ← mkFreshUserName `x
  let x := mkIdent xName
  `(fun ($x:ident : $targetType) => $x.$(mkIdent field))

private def mkFieldSpec (targetType : Term) (field : Name) : TermElabM Term := do
  let name := Syntax.mkStrLit (jsonFieldName field)
  let getter ← mkGetter targetType field
  `(Cas.Schema.Deriving.fieldSpec (ρ := $targetType)
    $name $getter)

private def mkFieldSpecs (targetType : Term)
    (fields : Array Name) : TermElabM (Array Term) :=
  fields.mapM (mkFieldSpec targetType)

private def mkToEl (targetType : Term) (fields : Array Name) : TermElabM Term := do
  let xName ← mkFreshUserName `x
  let x := mkIdent xName
  let mut body ← `(())
  for field in fields.reverse do
    let getter ← mkGetter targetType field
    body ← `(Prod.mk
      (Cas.Schema.Deriving.fieldToEl (ρ := $targetType)
        $getter $x)
      $body)
  `(fun $x:ident => $body)

private def mkTupleProjection (root : Term) (idx : Nat) : TermElabM Term := do
  let mut value := root
  for _ in *...idx do
    value ← `(($value).2)
  `(($value).1)

private def mkOfEl (targetType : Term) (fields : Array Name) : TermElabM Term := do
  let xName ← mkFreshUserName `x
  let x := mkIdent xName
  let mut values := #[]
  for h : i in *...fields.size do
    let projection ← mkTupleProjection x i
    let getter ← mkGetter targetType fields[i]
    values := values.push (←
      `(Cas.Schema.Deriving.fieldOfEl (ρ := $targetType)
        $getter $projection))
  let names := fields.map mkIdent
  let body ← `({ $[$names:ident := $values],* })
  `(fun $x:ident => $body)

private def mkWF (targetType : Term) (fields : Array Name) : TermElabM Term := do
  let mut fieldsWF ← `(True.intro)
  for field in fields.reverse do
    let getter ← mkGetter targetType field
    let head ← `(Cas.Schema.Deriving.fieldWF (ρ := $targetType)
      $getter)
    fieldsWF ← `(And.intro $head $fieldsWF)
  `(And.intro (by
      simp [Cas.Schema.Deriving.fieldSpec]) $fieldsWF)

/-! ## The constructor-alternative path -/

/-- One constructor, read for emission: its tag, and its fields in
CANONICAL (JSON-name) order paired with the position they occupy in the
constructor's own argument list. -/
private structure AltInfo where
  /-- The `_tag` literal — the constructor's short name. -/
  tag : String
  /-- Fully-qualified constructor name, for the match patterns. -/
  ctor : Name
  /-- JSON field names, ascending. -/
  names : Array String
  /-- Field types, in the same canonical order. -/
  types : Array Term
  /-- For constructor argument `j`, its index in the canonical order. -/
  slotOf : Array Nat
  deriving Inhabited

/-- The type of a constructor field, as syntax the generated command
can re-elaborate. Parameter-free inductives only, which is exactly what
this path admits, so the expression is closed. -/
private def typeSyntax (type : Expr) : TermElabM Term :=
  withOptions (fun o => o.setBool `pp.fullNames true) do
    Lean.PrettyPrinter.delab type

private def readAlt (ctorName : Name) :
    TermElabM AltInfo := do
  let ctorInfo ← getConstInfoCtor ctorName
  let tag := ctorName.eraseMacroScopes.getString!
  forallTelescopeReducing ctorInfo.type fun xs _ => do
    let mut rawNames : Array String := #[]
    let mut rawTypes : Array Term := #[]
    for i in *...ctorInfo.numFields do
      let x := xs[ctorInfo.numParams + i]!
      let decl ← x.fvarId!.getDecl
      if decl.userName.hasMacroScopes || decl.userName.isAnonymous then
        throwError "`deriving Described` needs every constructor field named; field {i + 1} of `{.ofConstName ctorName}` is anonymous, and a derived tagged union keys each field by its name"
      let name := decl.userName.eraseMacroScopes.getString!
      if name == Cas.Schema.tagField then
        throwError "`deriving Described` reserves the field name `{Cas.Schema.tagField}` for the discriminant; `{.ofConstName ctorName}` declares a field of that name"
      if name < Cas.Schema.tagField then
        throwError "`deriving Described` needs the discriminant `{Cas.Schema.tagField}` to sort FIRST among a member's fields; `{.ofConstName ctorName}` has a field `{name}` that sorts before it, so the generated union would not be discriminated"
      rawNames := rawNames.push name
      rawTypes := rawTypes.push (← typeSyntax decl.type)
    let order := (Array.range rawNames.size).qsort
      fun a b => rawNames[a]! < rawNames[b]!
    for s in *...order.size do
      if s + 1 < order.size then
        if rawNames[order[s]!]! == rawNames[order[s + 1]!]! then
          throwError "`deriving Described` needs a member's field names distinct; `{.ofConstName ctorName}` declares `{rawNames[order[s]!]!}` twice"
    let mut slotOf := Array.replicate rawNames.size 0
    for s in *...order.size do
      slotOf := slotOf.set! order[s]! s
    return {
      tag := tag
      ctor := ctorName
      names := order.map (rawNames[·]!)
      types := order.map (rawTypes[·]!)
      slotOf := slotOf
      : AltInfo }

/-- `Sum.inr (… (Sum.inl ·))`: the injection into position `idx` of a
`count`-member sum. The LAST member is carried bare — `ElMembers`
does not pad the tail with a dead `Empty` summand. -/
private def mkInj (idx count : Nat) (payload : Term) : TermElabM Term := do
  let mut body := payload
  if idx + 1 < count then
    body ← `(Sum.inl $body)
  for _ in *...idx do
    body ← `(Sum.inr $body)
  return body

private def mkInjFun (idx count : Nat) : TermElabM Term := do
  let zName ← mkFreshUserName `z
  let z := mkIdent zName
  let body ← mkInj idx count z
  `(fun $z:ident => $body)

/-- The member code of one constructor: the discriminant first, then
the fields in canonical order. -/
private def mkAltMember (alt : AltInfo) : TermElabM Term := do
  let mut specs : Array Term := #[
    ← `((Cas.Schema.tagField, false,
        Cas.Schema.Ast.lit (Cas.Schema.LitVal.str
          $(Syntax.mkStrLit alt.tag))))]
  for i in *...alt.names.size do
    specs := specs.push (←
      `(Cas.Schema.Deriving.altSpec $(Syntax.mkStrLit alt.names[i]!)
          $(alt.types[i]!)))
  `(Cas.Schema.Ast.struct [$[$specs],*])

/-- The member's well-formedness: sorted field names, then the
discriminant's own `True` and each field's code well-formed. -/
private def mkAltWF (alt : AltInfo) : TermElabM Term := do
  let mut fieldsWF ← `(True.intro)
  for ty in alt.types.reverse do
    fieldsWF ← `(And.intro (Cas.Schema.Deriving.altWF $ty) $fieldsWF)
  `(And.intro (by decide) (And.intro True.intro $fieldsWF))

/-- Fresh binder names for one constructor's arguments, in the
constructor's own order. -/
private def mkAltBinders (alt : AltInfo) : TermElabM (Array Ident) :=
  alt.slotOf.mapM fun _ => return mkIdent (← mkFreshUserName `a)

private def mkAltToEl (alts : Array AltInfo) : TermElabM Term := do
  let xName ← mkFreshUserName `x
  let x := mkIdent xName
  let mut arms : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
  for i in *...alts.size do
    let alt := alts[i]!
    let binders ← mkAltBinders alt
    -- the canonical-order components, tag first
    let mut body ← `(())
    for s in *...alt.names.size do
      let slot := alt.names.size - 1 - s
      let arg := binders[alt.slotOf.findIdx? (· == slot) |>.getD 0]!
      body ← `(Prod.mk (Cas.Schema.Deriving.altToEl $arg) $body)
    body ← `(Prod.mk () $body)
    let payload ← mkInj i alts.size body
    let pat ← `(@$(mkIdent alt.ctor):ident $binders*)
    arms := arms.push (← `(Lean.Parser.Term.matchAltExpr| | $pat => $payload))
  `(fun $x:ident => match $x:ident with $arms:matchAlt*)

private def mkAltOfEl (alts : Array AltInfo) : TermElabM Term := do
  let xName ← mkFreshUserName `x
  let x := mkIdent xName
  let mut arms : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
  for i in *...alts.size do
    let alt := alts[i]!
    let yName ← mkFreshUserName `y
    let y := mkIdent yName
    let pat ← mkInj i alts.size y
    let mut args : Array Term := #[]
    for j in *...alt.slotOf.size do
      let projection ← mkTupleProjection y (alt.slotOf[j]! + 1)
      args := args.push (← `(Cas.Schema.Deriving.altOfEl $projection))
    let body ← `(@$(mkIdent alt.ctor):ident $args*)
    arms := arms.push (← `(Lean.Parser.Term.matchAltExpr| | $pat => $body))
  `(fun $x:ident => match $x:ident with $arms:matchAlt*)

/-- `toEl ∘ ofEl = id`, one micro-proof per arm over the house simp
set, assembled by the match itself. Nothing here is a tactic
escalation: if an arm resists, the EMISSION is wrong. -/
private def mkAltToElOfEl (alts : Array AltInfo) : TermElabM Term := do
  let xName ← mkFreshUserName `x
  let x := mkIdent xName
  let mut arms : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
  for i in *...alts.size do
    let alt := alts[i]!
    let yName ← mkFreshUserName `y
    let y := mkIdent yName
    let pat ← mkInj i alts.size y
    let member ← mkAltMember alt
    let specs ← `(match $member:term with
      | Cas.Schema.Ast.struct fs => fs
      | _ => [])
    let lhs ← mkInj i alts.size
      (← `(Cas.Schema.Deriving.rebuildFields $specs $y))
    let rhs ← mkInj i alts.size y
    let injFun ← mkInjFun i alts.size
    let proof ← `(by
      simp only [Cas.Schema.Deriving.altToEl, Cas.Schema.Deriving.altOfEl,
        Cas.Schema.Deriving.FieldDescription.toEl_ofEl]
      change $lhs = $rhs
      exact congrArg $injFun (Cas.Schema.Deriving.rebuildFields_eq _ $y))
    arms := arms.push (← `(Lean.Parser.Term.matchAltExpr| | $pat => $proof))
  `(fun $x:ident => match $x:ident with $arms:matchAlt*)

open Lean.Elab.Deriving
open TSyntax.Compat in
private def mkStructureInstance (declName : Name) (indVal : InductiveVal) :
    TermElabM Command := do
  let argNames ← mkInductArgNames indVal
  let binders ← mkImplicitBinders argNames
  let binders := binders ++
    (← mkInstImplicitBinders ``Cas.Schema.Described indVal argNames)
  let targetType ← mkInductiveApp indVal argNames
  let instName ← mkInstName ``Cas.Schema.Described declName
  let fields ← canonicalFields declName
  let specs ← mkFieldSpecs targetType fields
  let code ← `(Cas.Schema.Ast.struct [$[$specs],*])
  let wf ← mkWF targetType fields
  let toEl ← mkToEl targetType fields
  let ofEl ← mkOfEl targetType fields
  let ofElToEl ← `(by
    intro x
    cases x
    simp [Cas.Schema.Deriving.fieldToEl,
      Cas.Schema.Deriving.fieldOfEl,
      Cas.Schema.Deriving.FieldDescription.ofEl_toEl])
  let toElOfEl ← `(by
    intro x
    simp only [Cas.Schema.Deriving.fieldToEl,
      Cas.Schema.Deriving.fieldOfEl,
      Cas.Schema.Deriving.FieldDescription.toEl_ofEl]
    change Cas.Schema.Deriving.rebuildFields [$[$specs],*] x = x
    exact Cas.Schema.Deriving.rebuildFields_eq _ x)

  `(instance $(mkIdent instName):ident $binders:implicitBinder* :
      Cas.Schema.Described $targetType where
    code := $code
    wf := $wf
    toEl := $toEl
    ofEl := $ofEl
    ofEl_toEl := $ofElToEl
    toEl_ofEl := $toElOfEl)

open TSyntax.Compat in
private def mkAlternativesInstance (declName : Name) (indVal : InductiveVal) :
    TermElabM (Array Command) := do
  if indVal.numParams != 0 || indVal.numIndices != 0 then
    throwError "`deriving Described` supports parameter-free inductives on the constructor-alternative path; `{.ofConstName declName}` takes type parameters or indices, and the union code has nowhere to spell them"
  if indVal.ctors.isEmpty then
    throwError "`deriving Described` cannot describe `{.ofConstName declName}`: it has no constructors, and the empty union is `Never`, which the schema `Ast` does not admit"
  let targetType := mkIdent declName
  let instName ← mkInstName ``Cas.Schema.Described declName
  let unsorted ← indVal.ctors.toArray.mapM readAlt
  -- ORDER IS IDENTITY: the generator picks ascending tag, once.
  let alts := unsorted.qsort fun a b => a.tag < b.tag
  let members ← alts.mapM mkAltMember
  let code ← `(Cas.Schema.Ast.union [$[$members],*] Cas.Schema.UnionMode.oneOf)
  let mut membersWF ← `(True.intro)
  for alt in alts.reverse do
    membersWF ← `(And.intro $(← mkAltWF alt) $membersWF)
  let wf ← `(And.intro (List.cons_ne_nil _ _) $membersWF)
  let toEl ← mkAltToEl alts
  let ofEl ← mkAltOfEl alts
  let ofElToEl ← `(by
    intro x
    cases x <;>
      simp [Cas.Schema.Deriving.altToEl,
        Cas.Schema.Deriving.altOfEl,
        Cas.Schema.Deriving.FieldDescription.ofEl_toEl])
  let toElOfEl ← mkAltToElOfEl alts
  let instCmd ←
    `(instance $(mkIdent instName):ident :
        Cas.Schema.Described $targetType where
      code := $code
      wf := $wf
      toEl := $toEl
      ofEl := $ofEl
      ofEl_toEl := $ofElToEl
      toEl_ofEl := $toElOfEl)
  -- The discrimination fact, pinned rather than assumed.
  -- `_root_`-anchored: the handler runs wherever the type was
  -- declared, and the fact belongs beside the type, not beside the
  -- caller's namespace.
  let discrimName := mkIdent (`_root_ ++ declName ++ `schemaDiscriminated)
  let discrimCmd ←
    `(/-- The derived code is a DISCRIMINATED union: every member is a
      struct whose first field is the required `_tag` literal, and the
      tags are pairwise distinct. This is what makes `El` of the code
      the member sum rather than `Empty`, so it is pinned here and not
      left to inspection. -/
      theorem $discrimName :
        Cas.Schema.Ast.discriminated
          (Cas.Schema.Described.code (α := $targetType)) = true := by
        rfl)
  return #[instCmd, discrimCmd]

private def mkDescribedCommands (declName : Name) :
    TermElabM (Array Command) := do
  let indVal ← getConstInfoInduct declName
  if indVal.isRec || indVal.isNested || indVal.all.length != 1 then
    throwError "`deriving Described` supports only non-recursive, non-mutual types; `{.ofConstName declName}` is recursive, nested, or mutual"
  if isStructure (← getEnv) declName then
    return #[← mkStructureInstance declName indVal]
  else
    mkAlternativesInstance declName indVal

open Lean.Elab.Deriving in
private def mkDescribedInstanceHandler
    (declNames : Array Name) : CommandElabM Bool := do
  if declNames.isEmpty then
    return false
  for declName in declNames do
    withoutExposeFromCtors declName do
      let cmds ← liftTermElabM <| mkDescribedCommands declName
      for cmd in cmds do
        elabCommand cmd
  return true

initialize
  Lean.Elab.registerDerivingHandler ``Cas.Schema.Described
    mkDescribedInstanceHandler

end Cas.Schema.Deriving
