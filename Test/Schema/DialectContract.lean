import Effect4.Schema.Bridge
import Effect4.Schema.OfShape
import Effect4.Codegen.Read

/-!
# Dialect contract — the store's shapes against the program's types, through the schema

Two descriptions of data land in one schema `Representation`: the store's `Shape`
(`Effect4.Store.render`) and the program's `Ty` (`Bridge.schema`, read back by `Bridge.ofSchema`).
No theorem relates them. This battery pins what the composite `Bridge.ofSchema ∘ Store.render`
answers today on every shape former, so that an edit to either rendering is a red row and not a
silent change (scout C, 2026-09-17, §2.2a; the findings ledger, C-1).

Three rows DISAGREE with what the former means, and are pinned as they are, not blessed:
`unit` and `option` are lost; `nat` reads back as `int`, the reserved type admission refuses as
uninhabited. `bytes` and `digest` are refused since decisions row 6 landed (2026-09-18): their
pattern check is one `Ty` cannot represent, and `ofSchema` no longer widens it to `string`.
`anyRef`, a named reference, a sum and a structure have no `Ty` at all, which is the gap a
nominal `Ty.data` would close (ledger, C-P10).
-/

set_option autoImplicit false

namespace Test.Schema.DialectContract

open Effect4 Effect4.Schema Effect4.Store Effect4.Program

def shapeTy (s : Shape) : Option Ty := Bridge.ofSchema (Effect4.Store.render s)

-- agree
#guard shapeTy .bool = some .bool
#guard shapeTy .string = some .string
#guard shapeTy (.list .string) = some (.list .string)

-- disagree: pinned, not blessed
#guard shapeTy .unit = none
#guard shapeTy (.option .bool) = none
#guard shapeTy .nat = some .int
#guard shapeTy (.pair .nat .string) = some (.prod .int .string)

-- refused (row 6): a pattern check `Ty` cannot represent
#guard shapeTy .bytes = none
#guard shapeTy .digest = none

-- no program type exists for these today
#guard shapeTy .anyRef = none
#guard shapeTy (.named "Tree") = none
#guard shapeTy (.sum "Tree" [("leaf", 0, [("value", .nat)])]) = none
#guard shapeTy (.struct "P" [("x", .nat)]) = none

/-! ## A requirement's key in an effect document (decisions row 8)

`EffTy.document` files each requirement under the whole `ServiceKey` (`Bridge.requirementKey`),
spelled as the printer and the reader spell a service key's runtime identity (`keyText`,
`Codegen/Read.lean`). Until 2026-10-01 it was filed under the name alone, `service_{name}`, so two
keys that share a name and differ in service were filed under one key. -/

/-- The schema's key is the printer's key. -/
theorem requirementKey_eq_keyText (k : ServiceKey) : Bridge.requirementKey k = keyText k := rfl

/-- The key determines the service key: the reader recovers both fields from it
(`keyFromText_print`), so distinct requirements are distinct references. -/
theorem requirementKey_injective {k k' : ServiceKey}
    (h : Bridge.requirementKey k = Bridge.requirementKey k') : k = k' :=
  (keyFromText_print k.name.value k.service.value).symm.trans
    ((congrArg keyFromText h).trans (keyFromText_print k'.name.value k'.service.value))

/-- Red control: the old key, the name alone, files two services that share a name together. -/
def nameOnlyKey (k : ServiceKey) : String := s!"service_{k.name.value}"
#guard nameOnlyKey ⟨⟨3⟩, ⟨7⟩⟩ = nameOnlyKey ⟨⟨3⟩, ⟨8⟩⟩

/-- An effect that needs two services sharing name 3: two references, `k3_7` and `k3_8`, each
with a placeholder declaration of its own key. -/
def twoServices : EffTy :=
  ⟨.nat, .never, Machine.Env.Requirement.ofList [⟨⟨3⟩, ⟨8⟩⟩, ⟨⟨3⟩, ⟨7⟩⟩]⟩
#guard (EffTy.document twoServices).references.map (·.key) = ["answer", "error", "k3_7", "k3_8"]
#guard ((EffTy.document twoServices).references.drop 2).map (·.representation) =
  [Bridge.schema (.handle "k3_7"), Bridge.schema (.handle "k3_8")]

end Test.Schema.DialectContract
