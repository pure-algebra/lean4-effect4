import Effect4.Laws.Auto.Traversals

/-!
# Laws.Auto.Exhaustive — which matches break when a constructor is added

`#exhaustive_gate Effect4.Program.Ty` lists every definition of the imported `Effect4.*`
modules whose `match` reads a value of the named inductive, and says whether that match has a
**catch-all** at the discriminant it reads. A definition with no catch-all is one the compiler
will refuse the day a constructor is appended; the list of them, printed before the append, is
what that append costs.

## Why this is an inventory and not a second gate

The compiled-LCNF case-site policy (`tools/Conform/Lcnf/Cases.lean`, `make check-cases`) is the
gate: it sees the default arms the compiler created, which were never in the source, and it
carries a signed pin. This command reads the *source*'s matchers instead, and it is deliberately
a printed report: nothing is written into the tree (a `Test` module must not, decisions row 49)
and nothing fails (the census stays an instrument, decisions row 34). Its use is
`lake env lean Test/Audit/TraversalCensus.lean` before a constructor is added, to read the bill.

## How a catch-all is decided

Exactly, from the matcher's own type. The match compiler builds each alternative's type as
`∀ fields, notAltHs → ∀ eqs, motive p₁ … pₙ` (`mkMinorType`, Lean's `Meta/Match/Match.lean`), so
the pattern of alternative `i` at discriminant `d` is literally the `d`-th argument of `motive`
in that alternative's body, and the alternative catches every constructor — present and future —
exactly when that argument is a bound variable of the fields telescope rather than a constructor
application. `MatcherInfo.altNumParams` gives the telescope's length, counting the artificial
`Unit` binder a field-less alternative carries (`mkSimpleThunkType`), the splitter's overlap
assumptions and the discriminant equations, so nothing is guessed. Patterns are annotated:
`Pattern.toExpr (annotate := true)` wraps an inaccessible pattern in `mkInaccessible` and an
`x@p` pattern in `namedPattern x p h`, both of which are stripped before the decision.

`matchMatcherApp? (alsoCasesOn := true)` also recognises a `casesOn` application, whose
alternatives are one per constructor and never a catch-all — which is the honest answer for it.

## What it does not see

Proofs. A `cases t <;> aesop` compiles to `Ty.casesOn` with one alternative per constructor and
no catch-all, while the tactic that was written handles a new constructor fine; and a
`first | … | …` alternative list leaves no residue in the term at all. So the walk is over
definitions only (`Traversals.definitionsUnder`, which already filters theorems, matchers,
recursors and compiler helpers), and the instrument for proof shape is the counted token list of
the trust gate, not this one.
-/

open Lean Elab Meta Command

namespace Effect4.Laws.Auto.Exhaustive

/-- One match on the family: who holds it, where, and at which discriminant. The matcher's
own parameter structure travels with it, because a `casesOn` application's is synthesised by
`matchMatcherApp?` and cannot be read back out of the environment. -/
structure Hit where
  holder : Name
  mod : Name
  matcher : Name
  info : Match.MatcherInfo
  discr : Nat
deriving Inhabited

/-- A `Hit` with the question answered. -/
structure Row where
  holder : Name
  mod : Name
  matcher : Name
  discr : Nat
  alts : Nat
  catchAll : Bool
deriving Inhabited, BEq

/-- Strip the annotations `Pattern.toExpr (annotate := true)` puts on a pattern: the
`_inaccessible` mdata of `.(t)` and `_`, and the `namedPattern x p h` of `x@p`, whose third
explicit argument (`args[2]`) is the pattern itself. Bounded; a pattern nests shallowly. -/
def stripPattern : Nat → Expr → Expr
  | 0, e => e
  | fuel + 1, e =>
    let e := e.consumeMData
    match inaccessible? e with
    | some inner => stripPattern fuel inner
    | none =>
      if e.getAppNumArgs == 4 && e.getAppFn.consumeMData.isConstOf ``namedPattern then
        stripPattern fuel e.getAppArgs[2]!
      else
        e

/-- Is alternative `i` of `matcher` a catch-all at discriminant `d`? -/
def altIsCatchAll (matcher : Name) (info : Match.MatcherInfo) (i d : Nat) : MetaM Bool := do
  let cinfo ← getConstInfo matcher
  forallBoundedTelescope cinfo.type (some (info.getFirstAltPos + i + 1)) fun xs _ => do
    let some alt := xs.back? | return false
    let altTy ← inferType alt
    let some params := info.altNumParams[i]? | return false
    forallBoundedTelescope altTy (some params) fun _ body => do
      let pats := body.getAppArgs
      let some p := pats[d]? | return false
      return (stripPattern 16 p).isFVar

/-- Does any alternative of `matcher` catch every constructor at discriminant `d`? -/
def matcherCatchAll (matcher : Name) (info : Match.MatcherInfo) (d : Nat) : MetaM Bool := do
  for i in [:info.numAlts] do
    if ← altIsCatchAll matcher info i d then return true
  return false

/-- Every matcher application in `e` whose discriminant `d` has a type headed by a member of
`family`, with whether it has a catch-all there. Fuel-bounded, and running out is a loud
refusal rather than a silent short answer (the pattern of `Positions.walkType`).

A binder's body is instantiated with a real local before it is walked, so every subterm the
walk hands to `inferType` is closed; reading a loose bound variable's type is the error this
costs one `withLocalDecl` per binder to avoid. -/
def matchesOn (family : Array Name) (holder mod : Name) :
    Nat → Expr → Array Hit → MetaM (Array Hit)
  | 0, _, acc => do
    logWarning m!"REFUSED {holder}: the term walk ran out of depth"
    return acc
  | fuel + 1, e, acc => do
    let mut rows := acc
    if let some app ← matchMatcherApp? e (alsoCasesOn := true) then
      let info := app.toMatcherInfo
      for d in [:app.discrs.size] do
        let dty ← whnf (← inferType app.discrs[d]!)
        if let some head := dty.getAppFn.constName? then
          if family.contains head then
            rows := rows.push { holder, mod, matcher := app.matcherName, info, discr := d }
    match e with
    | .app f a => matchesOn family holder mod fuel a (← matchesOn family holder mod fuel f rows)
    | .lam n t b bi => do
      let inner ← matchesOn family holder mod fuel t rows
      withLocalDecl n bi t fun x => matchesOn family holder mod fuel (b.instantiate1 x) inner
    | .forallE n t b bi => do
      let inner ← matchesOn family holder mod fuel t rows
      withLocalDecl n bi t fun x => matchesOn family holder mod fuel (b.instantiate1 x) inner
    | .letE n t v b _ => do
      let inner ← matchesOn family holder mod fuel t rows
      let inner ← matchesOn family holder mod fuel v inner
      withLetDecl n t v fun x => matchesOn family holder mod fuel (b.instantiate1 x) inner
    | .mdata _ b | .proj _ _ b => matchesOn family holder mod fuel b rows
    | _ => return rows

/-- The eliminators through which a definition can read a member of `family`: the family's own
recursors and `casesOn`s, and every matcher whose type mentions a family member. Collected in
one pass so the walk skips the definitions that cannot hold such a match at all. -/
def eliminatorsOf (env : Environment) (family : Array Name) : NameSet :=
  let seed : NameSet := family.foldl (init := {}) fun s t =>
    (((s.insert (t ++ `rec)).insert (t ++ `casesOn)).insert (t ++ `recOn)).insert (t ++ `brecOn)
  env.constants.map₁.fold (init := seed) fun acc name info =>
    if isMatcherCore env name && info.type.getUsedConstants.any family.contains then
      acc.insert name
    else acc

/-- The authored definition a helper belongs to: the nearest ancestor of `name` that the
census owns. -/
def ownerOf (owners : NameSet) : Nat → Name → Option Name
  | 0, _ => none
  | _, .anonymous => none
  | fuel + 1, name => if owners.contains name then some name else ownerOf owners fuel name.getPrefix

/-- The bodies to walk: every authored definition of `scope`, plus the helper each recursive
definition's body was moved into, attributed to the definition a person wrote.

`Traversals.definitionsUnder` drops internal details on purpose — it is a census of authored
traversals — but a structural recursion keeps nothing in the authored constant:
`Ty.closed = fun x => Ty.brecOn x Ty.closed._f`, and the `match` over the twenty constructors
is inside `Ty.closed._f`. Without the helpers the inventory would miss every recursive
definition, which is most of the ones a constructor costs. -/
def bodiesUnder (env : Environment) (scope : Name) : Array (Name × Name × Expr) :=
  let defs := definitionsUnder env scope
  let owners : NameSet := defs.foldl (init := {}) fun s (n, _, _, _) => s.insert n
  let authored := defs.map fun (n, m, _, v) => (n, m, v)
  env.constants.map₁.fold (init := authored) fun acc name info =>
    match info with
    | .defnInfo d =>
      if owners.contains name || isMatcherCore env name || isAuxRecursor env name ||
          isCompilerHelper name then acc
      else
        match moduleOf env name, ownerOf owners 32 name.getPrefix with
        | some m, some owner => if scope.isPrefixOf m then acc.push (owner, m, d.value) else acc
        | _, _ => acc
    | _ => acc

syntax (name := exhaustiveGate) "#exhaustive_gate " ident (" under " ident)? : command

@[command_elab exhaustiveGate] def elabExhaustiveGate : CommandElab := fun stx => do
  let root ← liftCoreM (realizeGlobalConstNoOverload stx[1])
  let scope := if stx[2].isNone then `Effect4 else stx[2][1].getId
  let family ← liftCoreM (familyOf root)
  let env ← getEnv
  let eliminators := eliminatorsOf env family
  let mut hits : Array Hit := #[]
  for (name, mod, value) in bodiesUnder env scope do
    unless value.getUsedConstants.any eliminators.contains do continue
    hits := hits ++ (← liftTermElabM (matchesOn family name mod 200 value #[]))
  let sorted := hits.qsort fun a b =>
    a.mod.toString < b.mod.toString ||
      (a.mod == b.mod && (a.holder.toString < b.holder.toString ||
        (a.holder == b.holder && (a.matcher.toString < b.matcher.toString ||
          (a.matcher == b.matcher && a.discr < b.discr)))))
  -- One row per (holder, matcher, discriminant): a term holds the same application many
  -- times over, and having a catch-all is a property of the matcher, not of the copy. The
  -- question is asked once per surviving row, which is what keeps the walk cheap.
  let unique := sorted.foldl (init := #[]) fun (acc : Array Hit) r =>
    match acc.back? with
    | some p => if p.holder == r.holder && p.matcher == r.matcher && p.discr == r.discr
        then acc else acc.push r
    | none => acc.push r
  let mut distinct : Array Row := #[]
  for h in unique do
    let catchAll ← liftTermElabM (matcherCatchAll h.matcher h.info h.discr)
    distinct := distinct.push { holder := h.holder, mod := h.mod, matcher := h.matcher,
                                discr := h.discr, alts := h.info.numAlts, catchAll }
  let exposed := distinct.filter (!·.catchAll)
  let mut report := m!"#exhaustive_gate {root} (family {family.toList}) under {scope}: \
    {distinct.size} match(es) read it, {exposed.size} with no catch-all — \
    appending a constructor refuses exactly those"
  for r in distinct do
    report := report ++ m!"\n  {r.holder}\t{r.mod}\t{r.matcher}\tdiscr {r.discr}\t\
      alts {r.alts}\tcatchAll {r.catchAll}"
  logInfo report

end Effect4.Laws.Auto.Exhaustive
