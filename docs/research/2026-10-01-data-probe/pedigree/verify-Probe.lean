import Effect4.Api
import Effect4.Schema.Bridge
import Effect4.Schema.Codec
import Effect4.Store.Domain.Shape
import Effect4.Laws.Program.Typed.Membership

/-!
# Verifier probe for seat PEDIGREE (data probe, 2026-10-01)

Checks the verifier ran beyond the seat's own `PedigreeProbe.lean`. `#guard` lines are finite
checks (tested); theorems are kernel proofs (proved), axioms printed at the foot. Nothing here
edits the tree. RED CONTROLS for the claims below are in `verify-Red.lean`.
-/

set_option autoImplicit false

namespace DataProbe.PedigreeVerify

open Effect4 Effect4.Program Effect4.Machine

/-! ## V1. `ofSchema` exactness fails in more ways than T6 (PED-05)

`checkId` (`Schema/Bridge.lean:62-65`) reads one id per check, so besides a check's payload it
also drops a filter group's inner checks and the `aborted` flag. None of these is an annotation
(`Check.filter rep annotations aborted`, `Schema/Representation.lean:773`). -/

-- V1a: a filter group whose own id is `isInt`, holding a `>= 5` check, reads back as `int`.
def groupedInt : Representation :=
  .number none [Effect4.Schema.Check.group
    (Effect4.Schema.Check.named "effect/schema/isGreaterThanOrEqualTo"
      (.obj [("minimum", Effect4.Arch.Json.ofNat 5)])) []
    none (some ⟨"effect/schema/isInt", .null, none⟩)]

#guard Effect4.Schema.Bridge.ofSchema groupedInt = some .int
#guard Effect4.Schema.Bridge.schema .int ≠ groupedInt

-- V1b: an aborted `isInt` filter reads back as `int`.
def abortedInt : Representation :=
  .number none [Effect4.Schema.Check.named "effect/schema/isInt" (aborted := true)]

#guard Effect4.Schema.Bridge.ofSchema abortedInt = some .int
#guard Effect4.Schema.Bridge.schema .int ≠ abortedInt

-- V1c: an `isInt` filter with a non-null payload reads back as `int`.
def payloadInt : Representation :=
  .number none [Effect4.Schema.Check.named "effect/schema/isInt" (.str "anything")]

#guard Effect4.Schema.Bridge.ofSchema payloadInt = some .int
#guard Effect4.Schema.Bridge.schema .int ≠ payloadInt

-- V1d: the comment at `Bridge.lean:57` says a template parameter's node is one "`ofSchema` does
-- not read back"; it reads back as a handle, and `schema` sends every `var i` and that handle to
-- one node (so `schema` is not injective off the closed types; the retraction is stated on closed
-- types only, which is why `ofSchema_schema` is not contradicted).
#guard Effect4.Schema.Bridge.ofSchema (Effect4.Schema.Bridge.schema (.var 0)) =
  some (.handle "effect/schema/TypeParameter")
#guard Effect4.Schema.Bridge.schema (.var 3) =
  Effect4.Schema.Bridge.schema (.handle "effect/schema/TypeParameter")

/-! ## V2. The JSON codec's exactness fails beyond field order (PED-06)

`Val` is untyped: `Exit.success v` and `Result.failure v` are both `ctor 0 [v]`
(`Machine/Value.lean:199`, `:203`). A union of the two types admits that value under two
different wire layouts, and `decodeRaw`'s union arm accepts the second branch's encoding
(`Schema/Codec.lean:209-212`). So two JSON values with different key sets decode to one value;
no object-entry-order normaliser identifies them. -/

def overlap : Ty := .union (.except .nat .nat) (.exitOf .nat .nat)
def jFailure : Json := .obj [("_tag", .str "Failure"), ("failure", Effect4.Arch.Json.ofNat 1)]
def jSuccess : Json := .obj [("_tag", .str "Success"), ("value", Effect4.Arch.Json.ofNat 1)]

#guard Effect4.Schema.Codec.isSupported overlap.normalize = true
#guard Effect4.Schema.decode overlap jFailure = some (.ctor 0 [.nat 1])
#guard Effect4.Schema.decode overlap jSuccess = some (.ctor 0 [.nat 1])
#guard jFailure ≠ jSuccess
-- the encoder answers exactly one of the two images
#guard Effect4.Schema.encode overlap (.ctor 0 [.nat 1]) = some jFailure ∨
  Effect4.Schema.encode overlap (.ctor 0 [.nat 1]) = some jSuccess
#guard (Effect4.Schema.encode overlap (.ctor 0 [.nat 1]) = some jFailure) !=
  (Effect4.Schema.encode overlap (.ctor 0 [.nat 1]) = some jSuccess)
-- control: at either member alone, the other member's image is refused
#guard Effect4.Schema.decode (.except .nat .nat) jSuccess = none
#guard Effect4.Schema.decode (.exitOf .nat .nat) jFailure = none

/-! ## V3. DI-67's gap is wider than never-products (PED-10)

Uninhabited, non-`never`, and admitted at HEAD: `except never never` at a host-row answer, and a
host-row request column `prod never nat` that a program supplies from a dead binding. -/

def hostRow (request answer : Ty) : Effect4.Program.Row :=
  { name := "query", spelling := "Host.query", request, answer, error := .never,
    kind := .async, registration := .external, cite := "" }

def pHostNat : Api.Program := .perform (.external 0) (.lit (.nat 1))

#guard Ty.normalize (.except .never .never) = .except .never .never
#guard (match Effect4.Program.admitProgram pHostNat [hostRow .nat (.except .never .never)] with
  | .ok _ => true | .error _ => false)

-- the request column: a program supplies `pair (var 0) 1` with `var 0 : never`
def pHostNeverRequest : Api.Program :=
  .bind (.fail (.lit (.nat 1)))
    (.perform (.external 0) (.app "pair" (.cons (.var 0) (.cons (.lit (.nat 1)) .nil))))

#guard (Api.typeOf pHostNeverRequest [hostRow (.prod .never .nat) .nat]).isSome
#guard (match Effect4.Program.admitProgram pHostNeverRequest [hostRow (.prod .never .nat) .nat] with
  | .ok _ => true | .error _ => false)

-- A host row whose answer is a template parameter that no request position binds is admitted
-- (run 1 printed "admitted"); the use site instantiates the parameter at `never` (run 2 printed
-- `some never`), so the program's own answer column is `never`, which DI-67 permits. The table
-- column itself is `var 0`, which `normalize` keeps and no value fits (`fits_var_empty`).
#guard (match Effect4.Program.admitProgram pHostNat [hostRow .nat (.var 0)] with
  | .ok _ => true | .error _ => false)
#guard (Api.typeOf pHostNat [hostRow .nat (.var 0)]).map (·.answer) = some .never
#guard Ty.normalize (.var 0) = .var 0
-- The encoder answers the `except` image (run 1 printed "Failure"; pinned here), so the
-- `exitOf` image `jSuccess` decodes to a value whose encoding is `jFailure`: exactness fails.
#guard Effect4.Schema.encode overlap (.ctor 0 [.nat 1]) = some jFailure

/-- Proved: no value fits `except never never`. -/
theorem fits_except_never_never_empty (w : Typed.World) (v : Val) :
    ¬ Typed.Fits w v (.except .never .never) := by
  intro h
  unfold Typed.Fits at h
  split at h
  · exact h
  · exact h
  · exact h

/-- Proved: the executable check agrees (DI-67 is stated over `Val.hasTy`). -/
theorem hasTy_except_never_never_false (v : Val) (allocated : List String) :
    Val.hasTy v (.except .never .never) allocated = false := by
  unfold Val.hasTy
  split
  · unfold Val.hasTy
    rfl
  · unfold Val.hasTy
    rfl
  · rfl

/-- Proved: no value fits a template parameter. -/
theorem fits_var_empty (w : Typed.World) (v : Val) (i : Nat) : ¬ Typed.Fits w v (.var i) := by
  intro h
  exact h

/-! ## V4. DI-95's fourth constructor (PED-18): the seat checked three of four. -/

#guard Effect4.Schema.Codec.isSupported (.deferredOf .nat .nat) = false
#guard Effect4.Schema.Codec.isSupported .int = false

/-! ## V5. The store's `nat` reads back as the reserved `int` (PED-19, as the Dialect battery
pins it), and the canonical SQL row's published answer is string pairs (PED-21). -/

#guard Effect4.Schema.Bridge.ofSchema (Effect4.Store.render .nat) = some .int
#guard Effect4.Schema.Bridge.schema Effect4.Program.Packages.sqlRows =
  Effect4.Schema.array (Effect4.Schema.array (Effect4.Schema.tuple
    [Effect4.Schema.element Effect4.Schema.string, Effect4.Schema.element Effect4.Schema.string]))

end DataProbe.PedigreeVerify

#print axioms DataProbe.PedigreeVerify.fits_except_never_never_empty
#print axioms DataProbe.PedigreeVerify.hasTy_except_never_never_false
#print axioms DataProbe.PedigreeVerify.fits_var_empty
