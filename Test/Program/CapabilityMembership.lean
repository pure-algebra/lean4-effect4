import Effect4.Laws.Program.Typed.Adequacy

/-!
# Capability membership (finding F-WF; `E4-TYPED-CE-040` repaired)

Controls for the restated `Live` (`Typed/Membership.lean`): membership at `unknown` reads every raw
handle frame, registered and present in its column, so a member of any type is valid in a typed
store (`fits_validIn`, `Typed/Adequacy.lean`). Concept 1, serving concept 4's store clauses.

- red: the raw byte `255` fits no type, so `refMake (.handle 255 7)` is admitted at no certificate
  (`E4-TYPED-CE-040`'s input refused);
- red: a memo map handle fits only where the map is present (row 187, amended);
- green: scalars fit `unknown` everywhere; a present memo map fits its type and is valid.
-/

set_option autoImplicit false
namespace Test.Program.CapabilityMembership
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed

abbrev W := Effect4.Program.Typed.World

/-- **The raw byte fits no type**: its frame's kind is unregistered, so capability membership
(`fits_live`) fails at every world. -/
theorem raw_byte_refused (w : W) (ty : Ty) : ¬ Fits w (.handle 255 7) ty := by
  intro h
  exact fits_live w ty _ h (255, 7) List.mem_cons_self

/-- **`E4-TYPED-CE-040`'s input is refused**: `refMake`'s pre is membership at the certificate. -/
theorem refMake_raw_refused (root : ProgramSource) (w : W) (cert : Ty) :
    ¬ storePre root w (.refMake (.handle 255 7)) cert :=
  raw_byte_refused w cert

/-- The empty world, and one holding memo map `0`. -/
def empty : W := initialWorld (EffTy.pure .unit)

def withMemo : W :=
  { empty with state := { empty.state with memo := [⟨⟨0⟩, none, []⟩] } }

/-- **An absent memo map's handle fits nowhere** (row 187, amended by F-WF). -/
theorem absent_memo_refused (ty : Ty) : ¬ Fits empty (Val.memoMap ⟨0⟩) ty := by
  intro h
  have absent := fits_live empty ty _ h (5, 0) List.mem_cons_self
  change false = true at absent
  cases absent

/-- A present memo map's handle fits the memo map type. -/
theorem present_memo_fits : Fits withMemo (Val.memoMap ⟨0⟩) Ty.memoMap :=
  ⟨rfl, rfl⟩

/-- A scalar fits `unknown` at every world. -/
theorem scalar_unknown (w : W) : Fits w (Val.nat 3) .unknown :=
  live_of_handles_nil rfl

/-- …and is valid in every store. -/
theorem scalar_valid (s : Stores) : Val.validIn s (Val.nat 3) = true := rfl

/-- A present memo map's handle is valid in its world's store (`live_validIn`; no cell or deferred
is read, so the forward bounds hold vacuously). -/
theorem present_memo_valid : Val.validIn withMemo.state (Val.memoMap ⟨0⟩) = true :=
  live_validIn (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fits_live withMemo Ty.memoMap _ present_memo_fits)

end Test.Program.CapabilityMembership
