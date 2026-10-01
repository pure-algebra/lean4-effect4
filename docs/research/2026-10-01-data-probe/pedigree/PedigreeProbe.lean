import Effect4.Api
import Effect4.Schema.Bridge
import Effect4.Schema.Codec
import Effect4.Store.Domain.Shape
import Effect4.Laws.Program.Typed.Membership

/-!
# Data probe, seat PEDIGREE: what the tree at `bc77e97f` already says about typed data

Each block below re-checks, at this commit, one fact the note's ledger relies on. `#guard`
lines are finite checks (evidence word: tested). The theorems are kernel proofs (proved), with
their axioms printed at the foot. Blocks marked RED CONTROL show the boundary of a claim.
Nothing here edits the tree; the file lives under `docs/research/` only.
-/

set_option autoImplicit false

namespace DataProbe.Pedigree

open Effect4 Effect4.Program Effect4.Machine

/-! ## T1. Records: `Ty` has no image for a schema struct (`objects`). -/

-- `Schema.Struct({ id: String })` as a persisted node: the reader refuses it.
#guard Effect4.Schema.Bridge.ofSchema
    (Effect4.Schema.struct [Effect4.Schema.property "id" Effect4.Schema.string]) = none
-- RED CONTROL: the binary tuple, which `prod` lowers to, reads back.
#guard Effect4.Schema.Bridge.ofSchema
    (Effect4.Schema.tuple [Effect4.Schema.element Effect4.Schema.string,
      Effect4.Schema.element Effect4.Schema.boolean]) = some (.prod .string .bool)

/-! ## T2. The store's own description language has named records; `Ty` cannot read them. -/

#guard Effect4.Schema.Bridge.ofSchema
    (Effect4.Store.render (.struct "User" [("id", .string)])) = none

/-! ## T3. A foreign nullary declaration (a data class) reads back as a host handle type. -/

#guard Effect4.Schema.Bridge.ofSchema (.declaration ⟨"User", .null⟩ none [] []) =
  some (.handle "User")

/-! ## T4. The positional record encoding publishes arrays, not objects.

`userTy` is the shape the deleted `Ty.record` sugar (`Schema/Endpoint.lean`, cut at
`b08f3b58`) built: nested pairs whose first components are field-name literals. -/

def userTy : Ty := .prod (.prod (.lit "id") .nat) (.prod (.lit "name") .string)
def userVal : Val := .list [.list [.str "id", .nat 7], .list [.str "name", .str "ada"]]

#guard Effect4.Schema.encode userTy userVal =
  some (.arr [.arr [.str "id", Effect4.Arch.Json.ofNat 7], .arr [.str "name", .str "ada"]])

/-! ## T5. The JSON codec's read is not exact without a named normaliser.

`decode` accepts an object whose entries are in another order; the value it answers encodes to
different JSON. The third law of an exact embedding (`read j = some v → j ≡ write v`) therefore
needs an object-order normaliser that no theorem names. -/

def someReordered : Json := .obj [("value", Effect4.Arch.Json.ofNat 1), ("_tag", .str "Some")]

#guard Effect4.Schema.decode (.option .nat) someReordered = some (.some (.nat 1))
#guard Effect4.Schema.encode (.option .nat) (.some (.nat 1)) =
  some (.obj [("_tag", .str "Some"), ("value", Effect4.Arch.Json.ofNat 1)])
#guard Effect4.Schema.encode (.option .nat) (.some (.nat 1)) ≠ some someReordered

/-! ## T6. `ofSchema` reads a check by its id only: a "number at least 5" reads back as `nat`.

So `ofSchema r = some t → r = schema t` fails even modulo annotations (decisions rows 6, 35, 41
call that exactness theorem open; this is a counterexample to its unqualified statement). -/

def atLeastFive : Representation :=
  .number none [Effect4.Schema.Bridge.isIntCheck,
    Effect4.Schema.Check.named "effect/schema/isGreaterThanOrEqualTo"
      (.obj [("minimum", Effect4.Arch.Json.ofNat 5)])]

#guard Effect4.Schema.Bridge.ofSchema atLeastFive = some .nat
#guard Effect4.Schema.Bridge.schema .nat ≠ atLeastFive

/-! ## T7. `int` is in `Ty`, its schema reads back, and admission refuses it (DI-67, DI-92). -/

#guard Effect4.Schema.Bridge.ofSchema (.number none [Effect4.Schema.Bridge.isIntCheck]) = some .int

/-! ## T8. Equality is admitted one type at a time (DI-35): not at a product. -/

#guard Effect4.Program.NativeAtom.typeOf Effect4.Program.NativeAtom.eq [.string, .string] =
  some .bool
#guard Effect4.Program.NativeAtom.typeOf Effect4.Program.NativeAtom.eq
  [.prod .nat .nat, .prod .nat .nat] = none

/-! ## T9. DI-95's classifier repair is in the code (the register row still says open). -/

#guard Effect4.Schema.Codec.isSupported .unknown = false
#guard Effect4.Schema.Codec.isSupported (.refOf .nat) = false
#guard Effect4.Schema.Codec.isSupported (.var 0) = false

/-! ## T10. A structured error payload is refused at introduction (DI-62); a tagged text is not. -/

def pFailRecord : Api.Program :=
  .fail (.app "pair" (.cons (.lit (.str "NotFound")) (.cons (.lit (.nat 7)) .nil)))
def pFailTagged : Api.Program :=
  .fail (.app "pair" (.cons (.lit (.str "NotFound")) (.cons (.lit (.str "user 7")) .nil)))

#guard Api.typeOf pFailRecord = none
#guard (Api.typeOf pFailTagged).isSome

/-! ## T11. Admission enforces inhabitance for `int` only: an uninhabited product is admitted.

DI-67 rules that every admitted column normalizes to `never` or has a value. `prod never nat`
does neither (P1 below), and a well-typed program answers at it. -/

def pNeverPair : Api.Program :=
  .bind (.fail (.lit (.nat 1)))
    (.succeed (.app "pair" (.cons (.var 0) (.cons (.lit (.nat 1)) .nil))))

#guard (Api.typeOf pNeverPair).map (·.answer) = some (.prod .never .nat)
#guard Ty.normalize (.prod .never .nat) = .prod .never .nat
#guard (match Effect4.Program.admitProgram pNeverPair with | .ok _ => true | .error _ => false)

-- A declared host-row column, which DI-67 names explicitly: `prod never nat` is admitted.
def hostRow (answer : Ty) : Effect4.Program.Row :=
  { name := "query", spelling := "Host.query", request := .nat, answer, error := .never,
    kind := .async, registration := .external, cite := "" }
def pHost : Api.Program := .perform (.external 0) (.lit (.nat 1))

#guard (match Effect4.Program.admitProgram pHost [hostRow (.prod .never .nat)] with
  | .ok _ => true | .error _ => false)
-- RED CONTROL: the same row at `int` is refused at admission, with its path.
#guard (match Effect4.Program.admitProgram pHost [hostRow .int] with
  | .ok _ => false | .error why => why == .uninhabited ["table", "0", "answer"])

/-! ## P1. Proved: nothing fits `int`, nothing fits `prod never b`. -/

theorem fits_int_empty (w : Typed.World) (v : Val) : ¬ Typed.Fits w v .int := by
  intro h
  exact h

theorem fits_prod_never_empty (w : Typed.World) (v : Val) (b : Ty) :
    ¬ Typed.Fits w v (.prod .never b) := by
  intro h
  unfold Typed.Fits at h
  split at h
  · exact h.1
  · exact h

/-! ## P2. Proved: R3's inhabitance clause is false without an admission premise.

The clause of `docs/core/system-map.md` §8 R3 quantifies over admitted types; dropping the
premise makes it false at `int`, so every uninhabited constructor (today `int`; under the type
algebra note's design also `Ty.foreign`) needs an admission refusal to keep it. -/

theorem inhabitance_needs_admission :
    ¬ (∀ τ : Ty, τ.normalize = .never ∨ ∃ (w : Typed.World) (v : Val), Typed.Fits w v τ) := by
  intro h
  rcases h .int with hn | ⟨w, v, hv⟩
  · cases hn
  · exact fits_int_empty w v hv

/-! ## P3. Proved: DI-67's invariant, stated over `Val.hasTy` as DI-67 states it, has no value
at `prod never b`. With T11 (`normalize` keeps `prod never nat`; admission admits it, at a program
answer and at a host-row column), the ruled invariant is false at HEAD for admitted columns. -/

theorem hasTy_prod_never_false (v : Val) (b : Ty) (allocated : List String) :
    Val.hasTy v (.prod .never b) allocated = false := by
  unfold Val.hasTy
  split
  · unfold Val.hasTy
    rfl
  · rfl

theorem di67_no_value_at_prod_never_nat :
    ¬ ∃ (allocated : List String) (v : Val), Val.hasTy v (.prod .never .nat) allocated = true := by
  rintro ⟨allocated, v, h⟩
  rw [hasTy_prod_never_false] at h
  cases h

end DataProbe.Pedigree

#print axioms DataProbe.Pedigree.hasTy_prod_never_false
#print axioms DataProbe.Pedigree.di67_no_value_at_prod_never_nat
#print axioms DataProbe.Pedigree.fits_int_empty
#print axioms DataProbe.Pedigree.fits_prod_never_empty
#print axioms DataProbe.Pedigree.inhabitance_needs_admission
