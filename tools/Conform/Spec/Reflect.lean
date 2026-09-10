import Lean
import Std.Tactic.Do

/-!
# Conform.Spec.Reflect — the leaf specifications a checker needs, generated

**What it is.** Two commands that write the one-line reflection specifications `mvcgen` needs
for the leaves of an `Option`-valued checker, so nobody writes them by hand:

* `reflect_spec f₁ f₂ …` — for each constant `fᵢ : ∀ xs, Option α`, declares
  `fᵢ_reflect : ∀ xs, ⦃⌜True⌝⦄ fᵢ xs ⦃(fun a => ⌜fᵢ xs = some a⌝, fun _ => ⌜fᵢ xs = none⌝, ())⦄`
  and registers it with `@[spec]`, keyed on `fᵢ`'s head, so the generator finds it with no list.
* `harvest_specs d` — reads the *equation lemmas* of the definition `d` (its surface arms, not
  its compiled recursor body), collects every constant applied in them whose type ends in
  `Option _` — the leaves the do-blocks call — and runs `reflect_spec` on those that do not have
  a reflection specification yet. Constructors, `bind`/`pure` and the `Option` combinators the
  library already specifies are skipped by name; internal names are skipped.

**Why this shape.** `Conform.Spec.Probe1` established (runs 1–3, 2026-09-09) that (a) the
specification database is keyed on the program's head symbol, so a generic "any `Option`
program" specification matches the whole do-block and blocks decomposition, while one
specification per leaf head lets the generator split every bind; and (b) the residue is then a
pure goal whose hypotheses are exactly the leaf equations. The reflection specification is the
*weakest useful* one — it says nothing about the leaf but "if it answered, it answered that" —
which is precisely what an *inversion* proof needs. A stronger, hand-proved `@[spec]` for the
same head with a higher priority wins when a proof needs more.

**Depends on.** `Lean` (elaboration), `Std.Tactic.Do`. Nothing from this repository: the commands
work on any constant of any project.

**Properties.**
* **Sound by construction.** Every generated theorem's proof term is `Option.spec_reflect (f xs)`
  and its statement is that term's inferred type — nothing is restated, so a wrong statement is
  impossible; `Option.spec_reflect` is proved here from the library's `WP.pure` and
  `WP.throw_Option` at `[propext, Quot.sound]`.
* **The telescope is `f`'s own.** The theorem abstracts over exactly `f`'s parameters, with
  their names, binder kinds and universes, by `mkForallFVars` over the telescope of `f`'s type.
* **Idempotent.** A name that already exists is skipped with a note, so `harvest_specs` may be
  re-run after a checker grows a leaf.
* **Refuses what it cannot state.** A constant whose type does not end in `Option α` with
  `α : Type`, or that has no equation lemmas and no body, is reported by name and skipped;
  nothing is guessed.
-/

namespace Conform.Spec

open Std.Do

/-- Running an `Option` value as a program: if it answers, it was `some` of the answer; if it
fails, it was `none`. The failure clause is permitted, not `False`. The one lemma every
generated reflection specification is an instance of. -/
theorem Option.spec_reflect {α : Type} (o : Option α) :
    ⦃⌜True⌝⦄ o ⦃(fun a => ⌜o = some a⌝, fun _ => ⌜o = none⌝, ())⦄ := by
  cases o with
  | none =>
    simp only [Triple]
    rw [show (Option.none : Option α) = (MonadExceptOf.throw () : Option α) from rfl,
      WP.throw_Option]
  | some a =>
    simp only [Triple]
    rw [show (some a : Option α) = (pure a : Option α) from rfl, WP.pure]
    simp

/-- `some a` is `pure a`: the library's `Spec.pure`, keyed on the constructor the generator
otherwise does not recognise. -/
@[spec] theorem Spec.some {α : Type} {a : α} {Q : PostCond α (.except PUnit .pure)} :
    ⦃Q.1 a⦄ (some a : Option α) ⦃Q⦄ := Std.Do.Spec.pure (m := Option)

/-- `none` is `throw ()`: the library's `Spec.throw_Option`, keyed on the constructor. -/
@[spec] theorem Spec.none {α : Type} {Q : PostCond α (.except PUnit .pure)} :
    ⦃Q.2.1 ()⦄ (Option.none : Option α) ⦃Q⦄ := by
  simp only [Triple]
  rw [show (Option.none : Option α) = (MonadExceptOf.throw () : Option α) from rfl,
    WP.throw_Option]

/-- `Option.map f x` is `f <$> x`: the library's `Spec.map`, keyed on the `Option` head an arm
written as `(… ).map g` has. -/
@[spec] theorem Spec.map_Option {α β : Type} {f : α → β} {x : Option α}
    {Q : PostCond β (.except PUnit .pure)} :
    ⦃wp⟦x⟧ (fun a => Q.1 (f a), Q.2)⦄ Option.map f x ⦃Q⦄ := by
  exact Std.Do.Spec.map (m := Option) (f := f) (x := x)

/-- `Option.bind x f` is `x >>= f`: the library's `Spec.bind`, keyed on the `Option` head. -/
@[spec] theorem Spec.bind_Option {α β : Type} {x : Option α} {f : α → Option β}
    {Q : PostCond β (.except PUnit .pure)} :
    ⦃wp⟦x⟧ (fun a => wp⟦f a⟧ Q, Q.2)⦄ Option.bind x f ⦃Q⦄ := by
  exact Std.Do.Spec.bind (m := Option) (f := f) (x := x)

/-- From `⦃True⦄ o ⦃⇓ a => Inv a | failure permitted⦄` back to `o = some a → Inv a`: the bridge
a declarative rule consumes, so no `wp` appears in a soundness statement. -/
theorem Option.of_triple {α : Type} {o : Option α} {Inv : α → Prop}
    (h : ⦃⌜True⌝⦄ o ⦃(fun a => ⌜Inv a⌝, fun _ => ⌜True⌝, ())⦄) :
    ∀ a, o = some a → Inv a := by
  intro a ha
  subst ha
  simp only [Triple] at h
  rw [show (some a : Option α) = (pure a : Option α) from rfl, WP.pure] at h
  simpa using h

open Lean Elab Command Meta

/-- The name of the generated specification for `f`. -/
def reflectName (f : Name) : Name := f.appendAfter "_reflect"

/-- Why a constant cannot be given a reflection specification. -/
inductive Refusal
  | notOption (f : Name)
  | notType0 (f : Name)
  | exists_ (target : Name)
  | noBody (f : Name)

def Refusal.render : Refusal → String
  | .notOption f => s!"`{f}` does not end in `Option _`"
  | .notType0 f => s!"`{f}` answers an `Option α` with `α` not in `Type`"
  | .exists_ t => s!"`{t}` exists"
  | .noBody f => s!"`{f}` has neither equation lemmas nor a body"

/-- Declare `f_reflect` for one constant: statement and proof built as terms from
`Option.spec_reflect (f xs)` over the telescope of `f`'s type, then `@[spec]`. -/
def declareReflect (f : Name) : TermElabM (Except Refusal Name) := do
  let target := reflectName f
  if (← getEnv).contains target then return .error (.exists_ target)
  let info ← getConstInfo f
  let us := info.levelParams.map Level.param
  let result ← forallTelescope info.type fun xs body => do
    let body ← whnfR body
    unless body.isAppOfArity ``Option 1 do return .error (Refusal.notOption f)
    let α := body.appArg!
    unless (← isDefEq (← inferType α) (mkSort Level.one)) do return .error (Refusal.notType0 f)
    let app := mkAppN (mkConst f us) xs
    let proofBody := mkApp2 (mkConst ``Conform.Spec.Option.spec_reflect) α app
    let stmt ← mkForallFVars xs (← inferType proofBody)
    let proof ← mkLambdaFVars xs proofBody
    addDecl (.thmDecl { name := target, levelParams := info.levelParams, type := stmt, value := proof })
    return .ok target
  if let .ok t := result then
    Term.applyAttributes t #[{ name := `spec }]
  return result

/-- `reflect_spec f₁ f₂ …`: one reflection specification per named constant, registered `@[spec]`. -/
syntax (name := reflectSpec) "reflect_spec " ident+ : command

@[command_elab reflectSpec] def elabReflectSpec : CommandElab
  | `(reflect_spec $fs:ident*) => do
    for f in fs do
      let r ← liftTermElabM do
        let c ← realizeGlobalConstNoOverloadWithInfo f
        declareReflect c
      match r with
      | .ok t => logInfo m!"reflect_spec: declared `{t}`"
      | .error e => logWarning m!"reflect_spec: skipped, {e.render}"
  | _ => throwUnsupportedSyntax

/-- The constant heads applied inside an expression whose type ends in `Option _`, excluding the
`Option` API itself and internal names. -/
private def optionLeaves (es : Array Expr) : MetaM (Array Name) := do
  let skip : List Name := [``Option.some, ``Option.none, ``Option.bind, ``Option.map,
    ``Option.getD, ``Option.get!, ``Option.isSome, ``Option.isNone, ``Bind.bind, ``Pure.pure,
    ``Functor.map, ``ite, ``dite, ``Option.elim, ``Option.orElse, ``Option.filter, ``Option.join]
  let mut acc : Array Name := #[]
  for e in es do
    for c in e.getUsedConstants do
      if skip.contains c || c.isInternal || acc.contains c then continue
      let info ← getConstInfo c
      let isOption ← forallTelescope info.type fun _ body => do
        let body ← whnfR body
        return body.isAppOfArity ``Option 1
      if isOption then acc := acc.push c
  return acc.qsort (fun a b => a.toString < b.toString)

/-- `harvest_specs d`: reflection specifications for every `Option`-valued constant the equation
lemmas of `d` apply (falling back to `d`'s body when it has none), those not yet declared. -/
syntax (name := harvestSpecs) "harvest_specs " ident : command

@[command_elab harvestSpecs] def elabHarvestSpecs : CommandElab
  | `(harvest_specs $d:ident) => do
    let (c, leaves, results) ← liftTermElabM do
      let c ← realizeGlobalConstNoOverloadWithInfo d
      let info ← getConstInfo c
      let sources : Array Expr ← match ← getEqnsFor? c with
        | some eqns => eqns.mapM fun e => do return (← getConstInfo e).type
        | none => match info.value? with
          | some v => pure #[v]
          | none => throwError "harvest_specs: {(Refusal.noBody c).render}"
      let leaves ← optionLeaves sources
      let results ← leaves.mapM declareReflect
      pure (c, leaves, results)
    let mut made : Array Name := #[]
    for r in results do
      match r with
      | .ok t => made := made.push t
      | .error (.exists_ _) => pure ()
      | .error e => logWarning m!"harvest_specs: skipped, {e.render}"
    logInfo m!"harvest_specs `{c}`: {leaves.size} Option-valued leaves {leaves.toList}; declared {made.size}: {made.toList}"
  | _ => throwUnsupportedSyntax

end Conform.Spec
