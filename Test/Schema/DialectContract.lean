import Effect4.Laws.Codegen.ReadLeaf
import Effect4.Schema.Bridge
import Effect4.Schema.OfShape
import Effect4.Codegen.Read
import Effect4.Laws.Codegen.ReadLeaf

/-!
# Store shapes and program types through Schema

`Store.render` and `Bridge.schema` produce the same Schema representation sort.
This finite battery checks `Bridge.ofSchema ∘ Store.render` on each store shape constructor.
It establishes no general agreement theorem between the two descriptions.

The unit and option faces still refuse.
The natural-number shape reads as `Ty.int`; the program admission rule still refuses that type.
The byte and digest faces retain pattern checks that `Ty` does not represent, so they refuse.
Structures read as structural records, retaining field names without nominal identity.
Unrestricted references, named references, and sums still refuse.
These results concern Schema reading, not value membership or program admission.
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

-- These shape faces remain outside the Schema reader profile.
#guard shapeTy .anyRef = none
#guard shapeTy (.named "Tree") = none
#guard shapeTy (.sum "Tree" [("leaf", 0, [("value", .nat)])]) = none
-- A structure reads as a record; the natural-number field retains the existing int face.
#guard shapeTy (.struct "P" [("x", .nat)]) = some (.record [("x", false, .int)])

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
