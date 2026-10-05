import Effect4.Laws.Program.Template

/-! Measurement for seat T3a's design note (phase 1): the anchored completeness of the row match.

`checkRow` matches the normal request against the normal template (`Program/Typing/Rules.lean`).
`Ty.normalize` distributes a product over a union member (`Program/Ty.lean`), so the normal
request of `Ref.set(cell, x)` with `x` a union is a union of products. `Ty.infer` has no arm for a
request union against a product template, so it binds nothing there, the parameter instantiates at
`never`, and the guard refuses, although a substitution exists. The probe:

1. evaluates the counterexample under today's `matchTemplate`;
2. evaluates it under a scratch repair, `infer'`, which distributes over a request union;
3. evaluates the guard with the instance normalized (the 2026-09-18 plan §2d).

Replay: `lake env lean docs/research/2026-10-04-seat-T3a/Anchored.lean` under the shared lock. -/

open Effect4.Program

namespace T3aAnchored

/-- `Ref.set`'s T3a template: `[Ref<A>, A]`. -/
def setT : Ty := .prod (.refOf (.var 0)) (.var 0)

/-- `pair(cell, x)` with `cell : Ref<string>` and `x : "a" | "b"`. -/
def setR : Ty := .prod (.refOf .string) (.union (.lit "a") (.lit "b"))

/-- A substitution under which the request is below the instance. -/
def τ : Ty.Subst := [(0, .string)]

-- The request's normal form is a union of two products.
#guard setR.normalize ==
  .union (.prod (.refOf .string) (.lit "a")) (.prod (.refOf .string) (.lit "b"))
-- τ puts the normal request under the instance.
#guard Ty.sub setR.normalize (setT.instantiate τ) = true
#guard Ty.sub setR.normalize (setT.instantiate τ).normalize = true
-- Today's match finds no substitution: `infer` binds nothing against the union.
#guard Ty.infer [] setT.normalize setR.normalize = []
#guard Ty.matchTemplate [] setT.normalize setR.normalize = none

/-- A scratch repair: a request union against a template that is neither a parameter nor a
union is inferred member by member, from the left; every other arm is `Ty.infer`'s. -/
def infer' (σ : Ty.Subst) (template request : Ty) : Ty.Subst :=
  match template, request with
  | .var _, _ | .union _ _, _ => Ty.infer σ template request
  | t, .union c d => infer' (infer' σ t c) t d
  | t, r => Ty.infer σ t r

def matchTemplate' (σ : Ty.Subst) (template request : Ty) : Option Ty.Subst :=
  let σ' := infer' σ template request
  if Ty.sub request (Ty.instantiate σ' template).normalize then some σ' else none

-- The repair finds τ.
#guard matchTemplate' [] setT.normalize setR.normalize = some [(0, .string)]

/-- `Deferred.fail`'s T3a template: `[Deferred<A, E>, E]`. -/
def failT : Ty := .prod (.deferredOf (.var 0) (.var 1)) (.var 1)

/-- `pair(d, e)` with `d : Deferred<number, string>` and `e : "x" | "y"`. -/
def failR : Ty := .prod (.deferredOf .nat .string) (.union (.lit "x") (.lit "y"))

#guard Ty.matchTemplate [] failT.normalize failR.normalize = none
#guard matchTemplate' [] failT.normalize failR.normalize = some [(0, .nat), (1, .string)]

-- An invariant handle with no witness stays refused by the repair: `Ref<number> | Ref<string>`
-- against `Ref<A>`.
def getR : Ty := .union (.refOf .nat) (.refOf .string)
#guard matchTemplate' [] (Ty.refOf (.var 0)) getR.normalize = none
#guard Ty.matchTemplate [] (Ty.refOf (.var 0)) getR.normalize = none

-- On a closed template the repair is subsumption, as `matchTemplate_closed` says of today's.
#guard matchTemplate' [] (.prod (.refOf .nat) .nat) (.prod (.refOf .nat) .nat) = some []

-- p5's shape: an `Entry` cell (`Deposit | Withdraw`, two tagged records) written with an
-- `Entry`-typed value. The normal request is a union of two products, so today's match refuses.
def entryTy : Ty :=
  .union (.record [("_tag", false, .lit "Deposit"), ("amount", false, .nat)])
    (.record [("_tag", false, .lit "Withdraw"), ("amount", false, .nat)])
def entrySetR : Ty := .prod (.refOf entryTy) entryTy
#guard Ty.matchTemplate [] setT.normalize entrySetR.normalize = none
#guard (matchTemplate' [] setT.normalize entrySetR.normalize).isSome
-- A `never` request (a dead branch) binds nothing and still matches: the parameter is `never`.
#guard Ty.matchTemplate [] (Ty.refOf (.var 0)) Ty.never = some []

end T3aAnchored
