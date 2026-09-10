import Conform.Effect4.LayoutWorld
import Conform.Layout.Build

/-!
# Conform.Effect4.TargetX2 — the X2 emitter's TypeScript layout, as a `Target`

**What it is.** The layout the LCNF→TypeScript emitter of
`docs/research/2026-09-09-seat-types-tooling-x2.lean` actually writes, transcribed rule by rule
from its own source. It is the *red control*: run `layout.injective` over it and the nested
option collides.

| source line | rule here |
| --- | --- |
| `x2.lean:152` `` | `` `Option.none => "null"` `` | `Option` is `nullable "none"` |
| `x2.lean:153` `` | `` `Option.some => vals[0]` `` | `some`'s payload is `single` |
| `x2.lean:147-148` `List.nil => "([] as any[])"`, `List.cons => "[h, ...t]"` | `List` is `nativeSeq` |
| `x2.lean:159-161` a structure is `{ f: v, … }` with **no tag** | a Lean structure is `record` |
| `x2.lean:163-165` everything else is `{ _tag: "c", f: v, … }` | every other inductive is `tagField "_tag"` |
| `x2.lean:119-127` `litValue` writes `Nat` as a decimal | `Nat` is `nativeScalar number` |
| `x2.lean:149-150` `Bool.true/false`, `Unit.unit => "undefined"` | `Bool`, `Unit` are native |

Its destruction side is the same table read backwards (`x2.lean:245-262`: `x === null` for
`Option`, `x.length === 0` for `List`, field access for a single-constructor type,
`switch (x._tag)` otherwise), which is why the *coherence* check passes on it and only the
*injectivity* check fails: the three bugs of `2026-09-09-seat-types-tooling.md` §5.5 were
coherence failures and were repaired; F1 is an injectivity failure and was not.

**Depends on.** `Conform.Effect4.LayoutWorld`, `Conform.Layout.Build`.

**Properties.**
* **`Nat` is `bounded 53` with no declared restriction.** The emitter writes a decimal literal
  into a JavaScript `number`, which is exact only below `2 ^ 53`, and nothing in the emitter
  states a source restriction — so `layout.injective` refuses the `Nat` subject rather than
  passing it — *by construction* (`admissible`, `.nativeScalar` arm).
-/

namespace Conform.Effect4

open Lean (Name)
open Conform.Layout

/-- The X2 emitter's table, materialised over a world: one explicit rule per type. -/
def targetX2 (W : World) : Target :=
  { name := "x2-typescript"
    note := "the LCNF→TypeScript emitter of docs/research/2026-09-09-seat-types-tooling-x2.lean, \
transcribed from ctorApp (construction, lines 145-186) and code.cases (destruction, 245-262)"
    rules :=
      #[ Build.scalar ``Nat .numK (.bounded 53) none
           "litValue writes a decimal into a JavaScript number (x2.lean:120)"
       , Build.scalar ``String .strK .unitsUtf16 none "Json.str (x2.lean:121)"
       , Build.scalar ``Bool .boolK .exact none "true/false (x2.lean:149-150)"
       , Build.unitScalar ``Unit "unit" "undefined (x2.lean:151)"
       , Build.unitScalar ``PUnit "unit" "undefined (x2.lean:151)"
       , Build.nullableOption ``Option "none" "some" none
           "null / the value itself (x2.lean:152-153) — the representation table of \
tools/Tools/TsGen.lean restated"
       , Build.nativeSeq ``List "nil" "cons"
           "([] as any[]) / [h, ...t] (x2.lean:147-148)" ]
      ++ W.types.filterMap familyRule
    usages :=
      #[ { site := "Effect4.Program.GenTy.joinAnswer result"
           type := .con ``Option [.con ``Option [.con `Effect4.Program.Ty []]] }
       , { site := "the brief's minimal nesting"
           type := .con ``Option [.con ``Option [.con ``Nat []]] }
       , { site := "Effect4.Program.GenTy.merge result"
           type := .con ``Option [.con `Effect4.Program.GenTy []] } ] }
where
  familyRule (tv : TypeView) : Option Rule :=
    -- `Option` and `List` have their own builtin rules; `Prod` and `Effect4.Row` are Lean
    -- structures and the emitter treats them as such (`x2.lean:159-161`), so they go through
    -- the ordinary structure rule.
    if tv.name == ``Option || tv.name == ``List then none
    else if tv.isStructure then
      some (Build.record tv Build.verbatim "a Lean structure is a bare object (x2.lean:159-161)")
    else
      some (Build.tagField tv "_tag" Build.verbatim Build.verbatim
        "every other inductive is { _tag, fields } (x2.lean:163-165)")

end Conform.Effect4
