import Conform.Effect4.LayoutWorld
import Conform.Layout.Build

/-!
# Conform.Effect4.TargetOCamlEff — the OCaml `eff/` layout, as a `Target`

**What it is.** The carrier alphabet `src/OCaml5/Eff/World.lean` fixes and
`src/OCaml5/Eff/Emit.lean` writes into `ocaml/eff/eff_types.ml`:

| source | rule here |
| --- | --- |
| `World.lean:58-60` `octor oname short = oname.capitalize ++ "_" ++ short` | a family is `variant`, frames spelled `Ty_option` |
| `World.lean:62-63` `ofield oname field = oname ++ "_" ++ field` | a Lean structure is a `record`, fields spelled `fork_options_daemon` |
| `Emit.lean:82-92` a struct is a record, an inductive a variant with positional arguments | the payloads |
| `World.lean:130-135` `Nat → int`, `Bool → bool`, `String → string`, `Option → option`, `List → list`, `Prod → *` | the builtins |
| `World.lean:116-117, 136` "`Effect4.Row α` is carried as `α list`: the one non-structural rule" | `Effect4.Row` is `unboxed` into its `elems` field |
| `eff_types.ml:3` "Lean Nat is OCaml int: values above max_int (2^62 - 1) have no carrier here" | `Nat` is `bounded 62` with that restriction declared |

**The point of this target.** OCaml's `option` is a two-frame variant, not a null, so
`Option (Option Ty)` is injective here with *no* condition on the payload
(`Laws.nativeOption_injective`, `Laws.nativeOption_nested_distinct`). The X2 collision cannot
be stated in this layout, and the check says so rather than a reader having to.

`World.lean`'s one non-structural rule is not an exception in this vocabulary: a `Row α` is a
structure with one computationally relevant field (`elems : List α`; `ascending` is a `Prop`),
and `unboxed` is exactly "a single-constructor single-field type is its field". The Lean side
of the same fact is `Store.Image.subtype`.

**Depends on.** `Conform.Effect4.LayoutWorld`, `Conform.Layout.Build`.
-/

namespace Conform.Effect4

open Lean (Name)
open Conform.Layout

/-- The OCaml name of a family, from `OCaml5.Eff.World.blocks`. -/
def onameOf (n : Name) : Option String := (OCaml5.Eff.allSpecs.find? (·.leanName == n)).map (·.oname)

/-- The `eff/` library's table. -/
def targetOCamlEff (W : World) : Target :=
  { name := "ocaml-eff"
    note := "OCaml5.Eff.World's carrier alphabet as OCaml5.Eff.Emit writes it into \
ocaml/eff/eff_types.ml"
    rules :=
      #[ Build.scalar ``Nat .numK (.bounded 62)
           (some "n ≤ max_int = 2^62 - 1")
           "eff_types.ml:3 states the caveat; an OCaml int is 63 bits, so above max_int the \
carrier is a different value (a wrapping reading would be ScalarDomain.wrapping 63, which is \
refused outright)"
       , Build.scalar ``String .strK .bytesUtf8 none "OCaml strings are byte strings"
       , Build.scalar ``Bool .boolK .exact none "bool"
       , Build.unitScalar ``Unit "unit" "unit"
       , Build.unitScalar ``PUnit "unit" "unit"
       , Build.nativeOption ``Option "none" "some" "None" "Some"
           "OCaml's own option: two frames, never a null (World.lean:133)"
       , Build.nativeSeq ``List "nil" "cons" "'a list (World.lean:134)"
       , Build.nativeTuple ``Prod "mk" "'a * 'b (World.lean:135)"
       , Build.unboxed `Effect4.Row "mk"
           "Effect4.Row α is carried as α list (World.lean:116-117, 136): a one-relevant-field \
structure erased to its field" ]
      ++ W.types.filterMap familyRule
    usages :=
      #[ { site := "Effect4.Program.GenTy.joinAnswer result"
           type := .con ``Option [.con ``Option [.con `Effect4.Program.Ty []]] }
       , { site := "the brief's minimal nesting"
           type := .con ``Option [.con ``Option [.con ``Nat []]] } ] }
where
  familyRule (tv : TypeView) : Option Rule :=
    if containerNames.contains tv.name then none
    else match onameOf tv.name with
      | none => none
      | some oname =>
        if tv.isStructure then
          some (Build.record tv (fun f => OCaml5.Eff.ofield oname f)
            s!"record fields {oname}_<field> (World.lean:62-63)")
        else
          some (Build.variant tv (fun c => OCaml5.Eff.octor oname c)
            s!"variant {oname.capitalize}_<ctor> (World.lean:58-60)")

end Conform.Effect4
