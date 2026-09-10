import Conform.Effect4.TargetX2

/-!
# Conform.Effect4.TargetX2Fixed — the corrected TypeScript layout, as a delta of the X2 one

**What it is.** The layout the follow-up review's F1 recommends, stated as exactly the three
rules that change:

1. **`Option` is tagged for internal values.** `{ _tag: "none" }` / `{ _tag: "some", val: … }`,
   so `none` and `some none` are different objects at every nesting.
2. **`nullable` survives where the payload excludes the null.** The rule for the *instantiation*
   `Option Nat` stays `nullable`, because `Nat`'s layout is a JavaScript number and never the
   null; `Target.ruleFor?` prefers the instantiation-specific rule, and `layout.injective`
   passes it under `Laws.nullable_injective`. That is the review's "permit an unboxed nullable
   layout only when a checked payload-domain condition rules out collision", with the condition
   checked rather than asserted.
3. **`Nat` declares the source restriction its target scalar assumes.** A JavaScript number is
   exact only below `2 ^ 53`; the rule says so, the check passes it under
   `Laws.boundedNat_injective`, and an obligation of kind `representation.scalar-domain` records
   that nothing here inspects the use sites.

Everything else — structures as bare objects, other inductives as `{_tag, …}`, `List` as an
array — is the X2 table unchanged, so a reader can see that the repair is three rules and not
a new representation.

**Depends on.** `Conform.Effect4.TargetX2`.
-/

namespace Conform.Effect4

open Lean (Name)
open Conform.Layout

/-- The corrected table. -/
def targetX2Fixed (W : World) : Target :=
  let base := targetX2 W
  { base with
    name := "x2-typescript-corrected"
    note := "the X2 table with F1's three repairs: Option tagged in general, nullable kept only \
at an instantiation whose payload excludes the null, and Nat's source restriction declared"
    rules :=
      -- the instantiation-specific rule comes first so `ruleFor?` finds it
      #[ Build.nullableOption ``Option "none" "some" (some [.con ``Nat []])
           "Nat's layout is a number and never the null, so the bare nullable spelling stays \
injective here (Laws.nullable_injective)"
       , { type := ``Option, discrimination := .tagField "_tag", container := .objectC
           note := "tagged options for internal values (wave-1 follow-up F1)"
           ctors :=
             [ { ctor := "none", tag := "none", intTag := 0, payload := .erased }
             , { ctor := "some", tag := "some", intTag := 1, payload := .named ["val"] } ] }
       , Build.scalar ``Nat .numK (.bounded 53) (some "n < 2^53")
           "a JavaScript number is exact below 2^53; the restriction is declared, and the \
obligation records that the use sites are not inspected here" ]
      ++ base.rules.filter fun r => r.type != ``Option && r.type != ``Nat }

end Conform.Effect4
