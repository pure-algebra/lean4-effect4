import Effect4.Program.Typed
import Effect4.Arch.JsonNumber
import Effect4.Schema.Codec

/-! E4-SCHEMA-CE-056 through 059: retained S-3 contract falsifiers.
The owner approved value admission and layout-compatible coercions on 2026-09-11.
The counterexample proofs are independent of the corrected codec implementation.
The final guards exercise its public normalization boundary. -/
namespace Test.Counterexamples.Schema.Codec
open Effect4 Effect4.Program
open Effect4.Machine (Val)

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem natural_collision :
    Arch.Json.ofNat (2 ^ 53) = Arch.Json.ofNat (2 ^ 53 + 1) := by decide

theorem natural_roundTrip_impossible (decode : Json → Option Val)
    (roundTrip : ∀ n, decode (Arch.Json.ofNat n) = some (.nat n)) : False := by
  have h := roundTrip (2 ^ 53)
  rw [natural_collision, roundTrip (2 ^ 53 + 1)] at h
  have bad : (2 ^ 53 + 1 : Nat) = 2 ^ 53 := by
    injection h with hv
    injection hv
  omega

def resultTy : Ty := .except .bool .bool
def exitTy : Ty := .exitOf .bool .never
def shared : Val := .ctor 0 [.bool true]
def resultJson : Json := .obj [("_tag", .str "Failure"), ("failure", .bool true)]
def exitJson : Json := .obj [("_tag", .str "Success"), ("value", .bool true)]

theorem shared_result : Val.hasTy shared resultTy = true := by decide
theorem shared_exit : Val.hasTy shared exitTy = true := by decide
theorem result_sub_union : Ty.sub resultTy (.union resultTy exitTy) = true := by
  rw [Ty.sub_union_right _ _ _ rfl, Ty.sub_refl]
  rfl
theorem exit_sub_union : Ty.sub exitTy (.union resultTy exitTy) = true := by
  rw [Ty.sub_union_right _ _ _ rfl, Ty.sub_refl, Bool.or_true]

theorem subtype_encoding_impossible (encode : Ty → Val → Option Json)
    (resultShape : encode resultTy shared = some resultJson)
    (exitShape : encode exitTy shared = some exitJson)
    (encodeSub : ∀ {s t v}, Ty.sub s t = true → Val.hasTy v s = true →
      encode t v = encode s v) : False := by
  have hr := encodeSub result_sub_union shared_result
  have he := encodeSub exit_sub_union shared_exit
  have bad : (some resultJson : Option Json) = some exitJson :=
    resultShape.symm.trans (hr.symm.trans (he.trans exitShape))
  exact (by decide : (some resultJson : Option Json) ≠ some exitJson) bad

theorem snapshot_has_list_bool :
    Val.hasTy (Effect4.Machine.Val.fibers []) (.list .bool) = true := by decide

theorem snapshot_not_list :
    ∀ xs, Effect4.Machine.Val.fibers [] ≠ Effect4.Store.Val.list xs := by
  intro xs h
  cases h

theorem list_totality_impossible (encode : Val → Option Json)
    (onlyLists : ∀ v, (∀ xs, v ≠ Effect4.Store.Val.list xs) → encode v = none)
    (total : ∀ v, Val.hasTy v (.list .bool) = true → (encode v).isSome = true) : False := by
  have h := total _ snapshot_has_list_bool
  rw [onlyLists _ snapshot_not_list] at h
  cases h

/-! Under the literal spec's common Success/value form, a Result success that fails
the first Exit branch still decodes there, changing ctor 1 to ctor 0. -/
def resultSuccessTy : Ty := .except .never .bool
def resultSuccess : Val := .ctor 1 [.bool true]
def ambiguousTy : Ty := .union exitTy resultSuccessTy

theorem result_success_admitted : Val.hasTy resultSuccess ambiguousTy = true := by decide
theorem result_success_not_exit : Val.hasTy resultSuccess exitTy = false := by decide

theorem left_biased_roundTrip_impossible (encode : Ty → Val → Option Json)
    (decode : Ty → Json → Option Val)
    (encoded : encode ambiguousTy resultSuccess = some exitJson)
    (leftDecoded : decode ambiguousTy exitJson = some shared)
    (roundTrip : ∀ {v j}, encode ambiguousTy v = some j →
      Val.hasTy v ambiguousTy = true → decode ambiguousTy j = some v) : False := by
  have h := roundTrip encoded result_success_admitted
  rw [leftDecoded] at h
  exact (by decide : (some shared : Option Val) ≠ some resultSuccess) h

-- Normalization at each public entry point removes raw union-order dependence.
-- The canonical order selects an empty list when decoding [], so exact admission
-- refuses an empty cause under either spelling of this union.
#guard Schema.encode (.union (.causeOf .never) (.list .bool)) (.exitErr ⟨[]⟩) =
  Schema.encode (Ty.normalize (.union (.causeOf .never) (.list .bool))) (.exitErr ⟨[]⟩)
#guard Schema.decode (.union (.causeOf .never) (.list .bool)) (.arr []) =
  Schema.decode (Ty.normalize (.union (.causeOf .never) (.list .bool))) (.arr [])
#guard Schema.Codec.isValue (.union (.causeOf .never) (.list .bool)) (.exitErr ⟨[]⟩) =
  Schema.Codec.isValue (Ty.normalize (.union (.causeOf .never) (.list .bool))) (.exitErr ⟨[]⟩)
#guard Schema.encode (.union (.causeOf .never) (.list .bool)) (.exitErr ⟨[]⟩) = none
#guard Schema.decode (.union (.causeOf .never) (.list .bool)) (.arr []) = some (.list [])
#guard !Schema.Codec.isValue (.union (.causeOf .never) (.list .bool)) (.exitErr ⟨[]⟩)

-- A redundant literal and a distributed product cross the normalized boundary.
#guard Schema.encode (.union (.lit "A") .string) (.str "A") = some (.str "A")
#guard Schema.decode (.union .string (.lit "A")) (.str "B") = some (.str "B")
#guard Schema.Codec.isValue (.union (.lit "A") .string) (.str "B")
#guard Schema.encode (.prod (.union .nat .string) .bool) (.list [.nat 3, .bool true]) =
  some (.arr [Arch.Json.ofNat 3, .bool true])
#guard Schema.decode (.prod (.union .string .nat) .bool) (.arr [Arch.Json.ofNat 3, .bool true]) =
  some (.list [.nat 3, .bool true])
#guard Schema.Codec.isValue (.prod (.union .nat .string) .bool) (.list [.nat 3, .bool true])

#print axioms natural_collision
#print axioms natural_roundTrip_impossible
#print axioms subtype_encoding_impossible
#print axioms snapshot_has_list_bool
#print axioms snapshot_not_list
#print axioms list_totality_impossible
#print axioms left_biased_roundTrip_impossible

end Test.Counterexamples.Schema.Codec
