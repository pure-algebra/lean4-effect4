import Conform.Effect4.LayoutWorld
import Conform.Layout.Build

/-!
# Conform.Effect4.TargetWire — the canonical wire's layout, as a `Target`

**What it is.** The representation `Effect4.Store.Canonical` fixes and `tools/Effect4Gen/Main.lean`
emits, transcribed rule by rule from its own sources:

| source | rule here |
| --- | --- |
| `Effect4Gen/Main.lean:17-21` "a structure is constructor 0 with its fields in declaration order; an inductive's constructors are numbered in declaration order" | every family is `indexed`, payload positional |
| `Store/Canonical.lean:522-557` the `Option` instance: `Val.none` / `Val.some v` | `Option` is `nativeOption "Val.none" "Val.some"` |
| `Store/Canonical.lean:497-520` the `List` instance: `Val.list (xs.map toVal)` | `List` is `nativeSeq` |
| `Store/Canonical.lean:569-600` the `Prod` instance: `Val.pair a b` | `Prod` is `nativeTuple` |
| `Store/Canonical.lean:319`, `336` the `Nat`/`String` instances: `Val.nat`, `Val.str` | `Nat` is an exact number, `String` is UTF-8 bytes |

**What it deliberately does not have.** There is no rule for `Effect4.Row`: the tree has no
`Canonical (Row α)` instance (`tools/Effect4Gen/manifest.json` does not request one and
`src/Effect4/Program/Derived.lean` does not emit one), so `layout.covers` reports the type
`unresolved` rather than inventing a spelling. That absence is the reason `EffTy`, whose
`requires` field is a `Row ServiceKey`, has no canonical instance either.

**Depends on.** `Conform.Effect4.LayoutWorld`, `Conform.Layout.Build`.

**Properties.**
* **`Nat` is exact.** `Val.nat` carries a Lean `Nat`, so the wire narrows nothing and the
  scalar arm of `admissible` passes with no obligation — the one target of the four with no
  scalar caveat — *by construction*.
* **Nesting is safe by a theorem, not by a bound.** `Option` is two distinct frames, so
  `Laws.nativeOption_nested_distinct` applies and `Option (Option α)` is injective for every
  `α` — the wire's half of `canonical_nested_distinct` — *proved* (in `Laws`).
-/

namespace Conform.Effect4

open Lean (Name)
open Conform.Layout

/-- The canonical wire's table. -/
def targetWire (W : World) : Target :=
  { name := "canonical-wire"
    note := "Effect4.Store.Canonical's frames and tools/Effect4Gen/Main.lean's declaration-order \
constructor indices"
    rules :=
      #[ Build.scalar ``Nat .numK .exact none "Val.nat (Store/Canonical.lean:319)"
       , Build.scalar ``String .strK .bytesUtf8 none "Val.str (Store/Canonical.lean:336)"
       , Build.scalar ``Bool .boolK .exact none "Val.bool (Store/Canonical.lean:302)"
       , Build.unitScalar ``Unit "unit" "Val.unit (Store/Canonical.lean:288)"
       , Build.unitScalar ``PUnit "unit" "Val.unit (Store/Canonical.lean:288)"
       , Build.nativeOption ``Option "none" "some" "Val.none" "Val.some"
           "the Option instance (Store/Canonical.lean:522)"
       , Build.nativeSeq ``List "nil" "cons" "the List instance (Store/Canonical.lean:497)"
       , Build.nativeTuple ``Prod "mk" "the Prod instance (Store/Canonical.lean:569)" ]
      ++ W.types.filterMap familyRule
    usages :=
      #[ { site := "Effect4.Program.GenTy.joinAnswer result"
           type := .con ``Option [.con ``Option [.con `Effect4.Program.Ty []]] }
       , { site := "the brief's minimal nesting"
           type := .con ``Option [.con ``Option [.con ``Nat []]] } ] }
where
  familyRule (tv : TypeView) : Option Rule :=
    if containerNames.contains tv.name then none
    else some (Build.indexed tv
      "Val.ctor <declaration index> [fields in order] (Effect4Gen/Main.lean:17-21)")

end Conform.Effect4
