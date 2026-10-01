import Effect4.Laws.Run
import Effect4.Laws.Program.CheckedTyping
import Effect4.Laws.Program.Signature
import Effect4.Laws.Program.Typed.Membership

/-!
# Admission's table check and column check (TY-05, rows 127 and 149)

**TY-05.** `Table.lawful` and `Table.checkLawful` decide one condition
(`Table.checkLawful_eq_none_iff`, proved in `Program/Admission.lean`), so admission takes its
refusal from the located check alone and no key is invented for a failure it does not explain.
The certificate theorems that unfold `admitProgram` (`admitProgram_eq_ok`,
`admitProgram_certificate`) read the same fact.

**Rows 127 and 149 (E4-TYPED-CE-015).** `inhabited` is a `TyAlgebra` fold that agrees with `Fits`
on every type (`inhabited_iff_fits`, `Laws/Program/Typed/Membership.lean`); the column check
`admitColumn` refuses exactly the empty columns that are not the designed bottom
(`admitColumn_iff`). The located scans (`findEmptyColumnInTable`, `findEmptyColumnInEffTy`,
`Program/Admission.lean`) name each refused column's position; the signature check refuses a row
with an empty column (`RowReason.emptyColumn`, `Laws/Program/Signature.lean`). Runner admission
(`admitProgram`) does not call the scans yet: its refusal needs an `AdmitRefusal` constructor, an
input of the generated runner group, and the brief runs no generator. The tripwire below fails
when that wiring lands.

Red controls: a pair naming one cell twice fits `prod (refOf nat) (refOf string)` in no world
(`shared_key_not_fits`, proved), which is why completeness declares each handle position at its
own fresh key; and the column scan no longer admits CE-015's host table (`#guard_msgs (error)`).
-/

set_option autoImplicit false

namespace Test.Program.AdmissionColumns

open Effect4 Effect4.Machine Effect4.Program

/-- A host row: `Host.<name>`, a `nat` request, the given answer and error columns. -/
def row (name : String) (answer : Ty) (error : Ty := .never) (request : Ty := .nat) : Row :=
  { name, spelling := "Host." ++ name, kind := .async, registration := .external,
    request, answer, error, cite := "" }

/-- Two rows under one key. -/
def dupTable : RowTable := [row "query" .nat, row "query" .string]

-- tested: the located refusal names the repeated key, and admission reports it
#guard Table.lawful dupTable == false
#guard Table.checkLawful dupTable == some (.duplicateKey (rowKey (row "query" .nat)))
#guard match admitProgram (.succeed (.lit (.nat 0))) dupTable with
  | .error (.duplicateKey k) => k == rowKey (row "query" .nat)
  | _ => false

/-- TY-05 on a table: `lawful` refuses and `checkLawful` locates (proved, by the theorem). -/
theorem dupTable_located : Table.checkLawful dupTable ≠ none :=
  Table.checkLawful_of_not_lawful dupTable (by decide)

#print axioms Effect4.Program.Table.findDup_eq_none_iff
#print axioms Effect4.Program.Table.lawful_eq_true_iff
#print axioms Effect4.Program.Table.checkLawful_eq_none_iff
#print axioms Effect4.Program.Table.checkLawful_of_not_lawful
#print axioms Effect4.Program.admitProgram
#print axioms Effect4.Program.admitProgram_eq_ok
#print axioms Effect4.Run.admitProgram_certificate
#print axioms dupTable_located

/-! ## Rows 127 and 149: the column check -/

/-- A host row at the given request and answer columns (the data probe's `hostRow`). -/
def hostRow (request answer : Ty) : Row :=
  { name := "query", spelling := "Host.query", request, answer, error := .never,
    kind := .async, registration := .external, cite := "" }

/-- The data probe's program: one host call. -/
def pHostNat : NativeEff := .perform (.external 0) (.lit (.nat 1))

-- tested: the scans locate CE-015's columns (a host-row answer, a host-row request, a program
-- answer), and leave the designed bottom and inhabited columns alone
#guard findEmptyColumnInTable [hostRow .nat (.except .never .never)] = some ["table", "0", "answer"]
#guard findEmptyColumnInTable [hostRow (.prod .never .nat) .nat] = some ["table", "0", "request"]
#guard findEmptyColumnInTable [hostRow .nat .nat, hostRow .nat (.prod .nat .never)] =
  some ["table", "1", "answer"]
#guard findEmptyColumnInTable [hostRow .nat .nat, hostRow (.list .never) (.option .never)] = none
#guard findEmptyColumnInEffTy ⟨.prod .never .nat, .never, .empty⟩ = some ["program", "answer"]
#guard findEmptyColumnInEffTy ⟨.never, .except .never .never, .empty⟩ = some ["program", "error"]
#guard findEmptyColumnInEffTy ⟨.never, .never, .empty⟩ = none
-- tested: two refusals, not one (TY-13): the `int` scan refuses `list int`, which has a member,
-- and misses `prod never nat`, which has none
#guard admitColumn (.list .int) && (findInt [] (.list .int)).isSome
#guard !admitColumn (.prod .never .nat) && (findInt [] (.prod .never .nat)).isNone
-- tested: the signature check refuses the same rows, at the row and the column
#guard admitSig (SigApp.mk [hostRow .nat (.except .never .never)] []) =
  .error (.row 0 (.emptyColumn "answer"))
#guard admitSig (SigApp.mk [hostRow (.prod .never .nat) .nat] []) =
  .error (.row 0 (.emptyColumn "request"))
-- tested (the tripwire): runner admission still admits CE-015's host table until the wiring in
-- seat A's receipt lands; this guard fails then and is deleted with it
#guard (match admitProgram pHostNat [hostRow .nat (.except .never .never)] with
  | .ok _ => true | .error _ => false)

/-- The located scan refuses the CE-015 table (proved). -/
theorem ce015_table_refused :
    findEmptyColumnInTable [hostRow .nat (.except .never .never)] ≠ none := by
  decide +kernel

/-- The located scan refuses CE-015's program answer column (proved). -/
theorem ce015_program_refused : findEmptyColumnInEffTy ⟨.prod .never .nat, .never, .empty⟩ ≠ none := by
  decide +kernel

/-- **Red control (proved).** Two handle positions cannot share a key: a pair naming cell 0
twice fits `prod (refOf nat) (refOf string)` in no world, since one key has one declaration and
`nat`, `string` are not equal normal forms. -/
theorem shared_key_not_fits (w : Typed.World) :
    ¬ Typed.Fits w (.list [Val.cell ⟨0⟩, Val.cell ⟨0⟩]) (.prod (.refOf .nat) (.refOf .string)) := by
  rintro ⟨⟨t1, h1, hnat, _⟩, ⟨t2, h2, _, hstr⟩⟩
  rw [h1] at h2
  cases h2
  have hbad : Ty.subN .string .nat = true := Ty.subN_trans hstr hnat
  exact absurd hbad (by decide +kernel)

/-- The same type has a member once each position has its own key (proved, by the agreement). -/
theorem two_cells_inhabited :
    ∃ (w : Typed.World) (v : Val), Typed.Fits w v (.prod (.refOf .nat) (.refOf .string)) :=
  (Typed.inhabited_iff_fits (.prod (.refOf .nat) (.refOf .string))).mp rfl

-- **Red control.** The old acceptance of CE-015's host table does not close against the
-- column scan.
/--
error: Tactic `decide` proved that the proposition
  findEmptyColumnInTable [hostRow Ty.nat (Ty.never.except Ty.never)] = none
is false
-/
#guard_msgs (error) in
example : findEmptyColumnInTable [hostRow .nat (.except .never .never)] = none := by
  decide +kernel

#print axioms Effect4.Program.emptyColumnAt_eq_none_iff
#print axioms Effect4.Program.findEmptyColumnInTable_go_eq_none_iff
#print axioms Effect4.Program.findEmptyColumnInTable_eq_none_iff
#print axioms Effect4.Program.findEmptyColumnInEffTy_eq_none_iff
#print axioms Effect4.Program.Typed.inhabited_of_fits
#print axioms Effect4.Program.Typed.inhabited_of_hasTy
#print axioms Effect4.Program.Typed.fits_of_inhabited_handleFree
#print axioms Effect4.Program.Typed.Grows.refl
#print axioms Effect4.Program.Typed.Grows.trans
#print axioms Effect4.Program.Typed.Grows.fits
#print axioms Effect4.Program.Typed.FreshFrom.addFiber
#print axioms Effect4.Program.Typed.FreshFrom.addRef
#print axioms Effect4.Program.Typed.FreshFrom.addPromise
#print axioms Effect4.Program.Typed.FreshFrom.allocExternal
#print axioms Effect4.Program.Typed.fits_handle_fresh
#print axioms Effect4.Program.Typed.fits_of_inhabited_fresh
#print axioms Effect4.Program.Typed.initialWorld_freshFrom
#print axioms Effect4.Program.Typed.inhabited_iff_fits
#print axioms Effect4.Program.Typed.inhabited_iff_handleFree
#print axioms Effect4.Program.Typed.fiber_inhabited
#print axioms Effect4.Program.Typed.cell_inhabited
#print axioms Effect4.Program.Typed.promise_inhabited
#print axioms Effect4.Program.Typed.handle_inhabited
#print axioms Effect4.Program.Typed.inhabited_sub
#print axioms Effect4.Program.Typed.inhabited_subN
#print axioms Effect4.Program.Typed.inhabited_normalize
#print axioms Effect4.Program.Typed.inhabited_join
#print axioms Effect4.Program.Typed.admitColumn_iff
#print axioms Effect4.Program.Typed.admitColumn_normalize
#print axioms Effect4.Program.Typed.prod_never_nat_empty
#print axioms Effect4.Program.Typed.except_never_never_empty
#print axioms Effect4.Program.Typed.prod_never_nat_no_hasTy
#print axioms Effect4.Program.Typed.except_never_never_no_hasTy
#print axioms Effect4.Program.Typed.admitColumn_prod_never_nat
#print axioms Effect4.Program.Typed.admitColumn_except_never_never
#print axioms ce015_table_refused
#print axioms ce015_program_refused
#print axioms shared_key_not_fits
#print axioms two_cells_inhabited

end Test.Program.AdmissionColumns
