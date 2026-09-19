/-! ## Acceptance guards for the generated relational view of `Ty`

Appended verbatim by `--append tools/Effect4Gen/guards/tyview.lean` into
`src/Effect4/Laws/Program/TyView.lean`.

The variance probes above are emitted per head from `tools/Effect4Gen/variances.json`; these
guards are the view's own contract, and they do not depend on which constructors exist:

1. `sub_eq_args` holds at named pairs that exercise each variance, so the law is exercised as a
   computation and not only as a theorem.
2. The four hypotheses are each necessary: dropping any one of them makes the two sides differ
   at a named counterexample (`never`, `union`, the literal rule, the top).
3. `sameHead` is an equivalence on members, and `union` is outside it.
4. `eq_of_sameHead` and `args_congr` at a pair the printer's corpus actually carries.
-/

namespace TyViewAcceptance

open Effect4.Program Effect4.Program.Ty

/-! ### 1. The law, computed -/

private def lhs (a b : Ty) : Bool := Ty.sub a b
private def rhs (a b : Ty) : Bool := Ty.sameHead a b && Ty.argsBelow Ty.sub a b

-- covariant: `option`, `list`, `causeOf`, and the two-argument covariant heads
#guard lhs (.option (.lit "a")) (.option .string) = rhs (.option (.lit "a")) (.option .string)
#guard lhs (.list .nat) (.list .string) = rhs (.list .nat) (.list .string)
#guard lhs (.fiberOf (.lit "a") .never) (.fiberOf .string .string)
  = rhs (.fiberOf (.lit "a") .never) (.fiberOf .string .string)
-- invariant: the cell and promise handles (decisions row 55)
#guard lhs (.refOf (.lit "a")) (.refOf .string) = rhs (.refOf (.lit "a")) (.refOf .string)
#guard lhs (.refOf .string) (.refOf .string) = rhs (.refOf .string) (.refOf .string)
#guard lhs (.deferredOf .nat .string) (.deferredOf .nat .string)
  = rhs (.deferredOf .nat .string) (.deferredOf .nat .string)
-- different heads, and different payloads at the same head
#guard lhs (.option .nat) (.list .nat) = rhs (.option .nat) (.list .nat)
#guard lhs (.handle "A") (.handle "B") = rhs (.handle "A") (.handle "B")
#guard lhs (.lit "a") (.lit "b") = rhs (.lit "a") (.lit "b")
#guard lhs (.var 0) (.var 1) = rhs (.var 0) (.var 1)

/-! ### 2. Each hypothesis is necessary

Every line below is a pair where the two sides of `sub_eq_args` DISAGREE, and the hypothesis
that excludes it. Without them the law would be false, so these are what the four arguments
are for. -/

-- `isMember a`: `never` is below everything, and has no head
#guard Ty.isMember .never = false
#guard lhs .never .nat != rhs .never .nat
-- `isMember b`: a union on the right is a choice, not a congruence
#guard Ty.isMember (.union .nat .string) = false
#guard lhs .nat (.union .nat .string) != rhs .nat (.union .nat .string)
-- `litRule`: a literal is below `string` with no head in common
#guard Ty.litRule (.lit "a") .string = true
#guard lhs (.lit "a") .string != rhs (.lit "a") .string
-- `topRule`: everything is below the top (decisions row 46)
#guard Ty.topRule .nat .unknown = true
#guard lhs .nat .unknown != rhs .nat .unknown

/-! ### 3. `sameHead` on members, and `union` outside it -/

#guard Ty.sameHead (.prod .nat .string) (.prod .string .nat)
#guard !Ty.sameHead (.union .nat .string) (.union .nat .string)
#guard !Ty.sameHead (.prod .nat .string) (.except .nat .string)
#guard Ty.sameHead (.handle "Scope.Scope") (.handle "Scope.Scope")

example (t : Ty) (h : Ty.isMember t = true) : Ty.sameHead t t = true := Ty.sameHead_refl t h
example {a b : Ty} (h : Ty.sameHead a b = true) : Ty.sameHead b a = true := Ty.sameHead_symm h
example {a b c : Ty} (h : Ty.sameHead a b = true) (h' : Ty.sameHead b c = true) :
    Ty.sameHead a c = true := Ty.sameHead_trans h h'

/-! ### 4. The node is its head and its children -/

example {a b : Ty} (h : Ty.sameHead a b = true)
    (hx : a.args.map Prod.snd = b.args.map Prod.snd) : a = b := Ty.eq_of_sameHead h hx
example {a b : Ty} (h : Ty.sameHead a b = true) :
    a.args.length = b.args.length ∧ a.args.map Prod.fst = b.args.map Prod.fst := Ty.args_congr h
example {t : Ty} {v : Ty.Variance} {x : Ty} (h : (v, x) ∈ t.args) : sizeOf x < sizeOf t :=
  Ty.sizeOf_args h

#guard (Ty.prod .nat .string).args.map Prod.snd = [.nat, .string]
#guard (Ty.refOf .nat).args = [(.inv, .nat)]
#guard (Ty.fiberOf .nat .string).args.map Prod.fst = [.co, .co]
#guard (Ty.unknown).args = []

end TyViewAcceptance
