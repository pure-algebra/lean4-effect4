import Effect4.Run.Preview
import Effect4.Laws.Run.Tree

/-!
# Laws.Api.Preview — the preview profile's reply-admission and non-allocation laws

Slice P of `docs/research/2026-10-17-proof-scout/README.md` (§7.6).

## Placement

* **Concept**: `host-session-protocol`, property `reply-at-call-instance` at the row's columns.
* **Question**: the preview interface's proposed obligation of the authoring review (role
  compatibility), serving `live-session-total` (`Effect4.Live.reached`).
* **Reach**: `Preview.checkedTape`, `Preview.hasHandle`, `externalValue`, and `Preview.rejected`.
* **What it does not establish**: agreement of the call tree with the machine
  (`Tree.ofProgram_eq_denoteRowsB` is a planned goal), or reply admission at generic rows or handle
  answers (which `Preview.admit` refuses).
* **Consumer**: `Tools.Session.answer` (`settle`, `frames`, `explore`) and
  `Test.Program.PreviewControls`.
* **Requirement**: R12.
-/

set_option autoImplicit false

namespace Effect4.Run.Preview

open Effect4 Effect4.Machine Effect4.Program Effect4.Store

/-- **Every reply the checked tape gives passes reply admission at its row (E2).**

Placement:
1. Concept: `host-session-protocol`, property `reply-at-call-instance` at the row's columns.
2. Question: the preview interface's proposed obligation (role compatibility).
3. Reach: `checkedTape` and `Kit.replyFault`.
4. What it does not establish: agreement with the machine or checked instances at generic rows.
5. Consumer: `checkedTape_success_externalValue` and `Tools.Session.answer` (`settle`, `frames`).
   Requirement R12. -/
theorem checkedTape_admits {app : SigApp} {row : Nat} {v : Store.Val} {tape rest : List ExitV}
    {ex : ExitV} (h : checkedTape app row v tape = some (ex, rest)) :
    Kit.replyFault app row ex = none := by
  unfold checkedTape at h
  split at h
  · cases h
  · split at h
    · rename_i hok
      cases h
      exact Option.isNone_iff_eq_none.mp hok
    · cases h

/-- A type with `hasHandle ty = false` is not a host handle at the root.

Placement:
1. Concept: `host-session-protocol`, property `reply-at-call-instance`.
2. Question: helper step for `externalValue_unchanged_of_hasHandle_false`.
3. Reach: `hasHandle` and `Ty.handle`.
4. What it does not establish: membership or allocation.
5. Consumer: `externalValue_of_hasHandle_false`. Requirement R12. -/
theorem not_handle_of_hasHandle_false {ty : Ty} (h : hasHandle ty = false) (target : String) :
    ty ≠ .handle target := by
  intro heq
  subst heq
  cases h

/-- At an answer type that is not a host handle at its head, `externalValue` takes its
non-allocating membership branch.

Placement:
1. Concept: `host-session-protocol`, property `reply-at-call-instance`.
2. Question: helper step for `externalValue_unchanged_of_hasHandle_false`.
3. Reach: `externalValue` at `∀ target, ty ≠ .handle target`.
4. What it does not establish: membership when `externalValue` returns `none`.
5. Consumer: `externalValue_of_hasHandle_false`. Requirement R12. -/
theorem externalValue_of_not_handle {decls : TyDecls} {ty : Ty} {allocated : List String}
    {value : Store.Val} (h : ∀ target, ty ≠ .handle target) :
    externalValue decls ty allocated value =
      if Program.Val.memberIn decls value ty allocated && (Store.Val.handles value).isEmpty then
        some (allocated, value)
      else none := by
  unfold externalValue
  split
  · next target _ => exact False.elim (h target rfl)
  · rfl

/-- At an answer type with `hasHandle ty = false`, `externalValue` takes its non-allocating
membership branch.

Placement:
1. Concept: `host-session-protocol`, property `reply-at-call-instance`.
2. Question: helper step for `externalValue_unchanged_of_hasHandle_false`.
3. Reach: `externalValue` under `hasHandle ty = false`.
4. What it does not establish: membership when `externalValue` returns `none`.
5. Consumer: `externalValue_unchanged_of_hasHandle_false`. Requirement R12. -/
theorem externalValue_of_hasHandle_false {decls : TyDecls} {ty : Ty} {allocated : List String}
    {value : Store.Val} (h : hasHandle ty = false) :
    externalValue decls ty allocated value =
      if Program.Val.memberIn decls value ty allocated && (Store.Val.handles value).isEmpty then
        some (allocated, value)
      else none :=
  externalValue_of_not_handle (not_handle_of_hasHandle_false h)

/-- **At an answer type without a handle, a successful `externalValue` returns the reply and the
allocation list unchanged.**

Placement:
1. Concept: `host-session-protocol`, property `reply-at-call-instance`.
2. Question: the preview profile's non-allocation law of §7.6 (role compatibility).
3. Reach: `externalValue` on any type with `hasHandle ty = false`.
4. What it does not establish: allocation at handle types (`Preview.admit` refuses those).
5. Consumer: `checkedTape_success_externalValue` and `Test.Program.PreviewControls`.
   Requirement R12. -/
theorem externalValue_unchanged_of_hasHandle_false {decls : TyDecls} {ty : Ty}
    {allocated allocated' : List String} {value value' : Store.Val}
    (h : hasHandle ty = false)
    (hext : externalValue decls ty allocated value = some (allocated', value')) :
    allocated' = allocated ∧ value' = value := by
  rw [externalValue_of_hasHandle_false h] at hext
  cases hcond : (Program.Val.memberIn decls value ty allocated && (Store.Val.handles value).isEmpty)
  · rw [hcond] at hext
    cases hext
  · rw [hcond] at hext
    cases hext
    exact ⟨rfl, rfl⟩

/-- **On a profile row (`hasHandle r.answer = false`), a success reply accepted by `checkedTape`
is returned unchanged by `externalValue` with no allocation.**

Placement:
1. Concept: `host-session-protocol`, property `reply-at-call-instance`.
2. Question: the preview profile's value-agreement law of §7.6 (role compatibility).
3. Reach: `checkedTape` and `externalValue` at a row with `hasHandle r.answer = false`.
4. What it does not establish: generic rows or handle-allocating rows (refused by `Preview.admit`).
5. Consumer: `Tools.Session.answer` (`settle`, `frames`) and `Test.Program.PreviewControls`.
   Requirement R12. -/
theorem checkedTape_success_externalValue {app : SigApp} {row : Nat} {r : Program.Row}
    {req value : Store.Val} {tape rest : List ExitV}
    (hrow : (app.rows[row]?).map Program.Row.normalizeTypes = some r)
    (hno : hasHandle r.answer = false)
    (htape : checkedTape app row req tape = some (.success value, rest)) :
    externalValue app.types r.answer [] value = some ([], value) := by
  have hfault := checkedTape_admits htape
  unfold Kit.replyFault Kit.replyFault.columns at hfault
  dsimp only at hfault
  rw [hrow] at hfault
  dsimp only at hfault
  cases hext : externalValue app.types r.answer [] value with
  | none =>
    rw [hext] at hfault
    cases hfault
  | some p =>
    rcases p with ⟨allocated', value'⟩
    obtain ⟨ha, hv⟩ := externalValue_unchanged_of_hasHandle_false hno hext
    rw [ha, hv]

/-- When the remaining tape is empty, `Preview.rejected` reports nothing.

Placement:
1. Concept: `host-session-protocol`, property `reply-at-call-instance`.
2. Question: helper step for `Preview.rejected`'s boundary.
3. Reach: `Preview.rejected` at `o.state = []`.
4. What it does not establish: why the run stopped.
5. Consumer: `Test.Program.PreviewControls`. Requirement R12. -/
theorem rejected_empty (app : SigApp) (o : Tree.Outcome (List ExitV)) (h : o.state = []) :
    rejected app o = none := by
  unfold rejected
  rw [h]
  cases o.stop <;> rfl

/-- `Preview.rejected` reports a fault if and only if the run stopped waiting on a call with a
leading tape entry that `Kit.replyFault` refuses.

Placement:
1. Concept: `host-session-protocol`, property `reply-at-call-instance`.
2. Question: characterization of `Preview.rejected` (role compatibility).
3. Reach: `Preview.rejected`, `Tree.Stop.waiting`, and `Kit.replyFault`.
4. What it does not establish: whether subsequent tape entries fit.
5. Consumer: `Tools.Session.answer` (`settle`, `frames`) and `Test.Program.PreviewControls`.
   Requirement R12. -/
theorem rejected_iff {app : SigApp} {o : Tree.Outcome (List ExitV)} {r : Rejected} :
    rejected app o = some r ↔
      ∃ req rest, o.stop = .waiting r.row req ∧ o.state = r.exit :: rest ∧
        Kit.replyFault app r.row r.exit = some r.fault := by
  constructor
  · intro h
    unfold rejected at h
    cases hstop : o.stop with
    | finished _ =>
      rw [hstop] at h
      cases h
    | cut =>
      rw [hstop] at h
      cases h
    | waiting row req =>
      rw [hstop] at h
      cases hstate : o.state with
      | nil =>
        rw [hstate] at h
        cases h
      | cons ex rest =>
        rw [hstate] at h
        dsimp only at h
        obtain ⟨fault, hfault, heq⟩ := Option.map_eq_some_iff.mp h
        cases heq
        exact ⟨req, rest, rfl, rfl, hfault⟩
  · rintro ⟨req, rest, hstop, hstate, hfault⟩
    unfold rejected
    rw [hstop, hstate]
    dsimp only
    rw [hfault]
    cases r
    rfl

end Effect4.Run.Preview
