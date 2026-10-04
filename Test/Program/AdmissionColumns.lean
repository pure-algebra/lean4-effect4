import Effect4.Laws.Run
import Effect4.Laws.Program.CheckedTyping
import Effect4.Laws.Program.Signature
import Effect4.Laws.Program.Typed.Membership

/-!
# Admission's table check and column check (TY-05, rows 127 and 149)

**TY-05.** `Table.lawful` and the signature's located refusal (`admitSig`,
`Program/SigApp.lean`) decide one condition on a table's keys: `LawfulSig.tableLawful` reads
`Table.lawful` off a lawful signature, and `admitSig_ok_iff` makes the refusal complete. Program
admission runs `admitSig` (decisions row 21), so it takes its refusal from the located check alone
and no key is invented for a failure it does not explain. The certificate theorems that unfold
`admitProgram` (`admitProgram_eq_ok`, `admitProgram_certificate`) read the certificate's
`signature` field.

**Rows 127 and 149 (E4-TYPED-CE-015).** `inhabited` is a `TyAlgebra` fold that agrees with `Fits`
on every type (`inhabited_iff_fits`, `Laws/Program/Typed/Membership.lean`); the column check
`admitColumn` refuses exactly the empty columns that are not the designed bottom
(`admitColumn_iff`). The signature check refuses a row with an empty column, at the row and the
column (`RowReason.emptyColumn`, `Program/SigApp.lean`), and program admission reports it as
`AdmitRefusal.signature`. The program's own columns are admission's located scan
(`findEmptyColumnInEffTy`, `Program/Admission.lean`), refused as `AdmitRefusal.emptyColumn at`
after every other check (decision D-A1 (a), integration seat I2). The refusal `#guard`s below
replace seat A's tripwire, which pinned the old acceptance.

Red controls: a pair naming one cell twice fits `prod (refOf nat) (refOf string)` in no world
(`shared_key_not_fits`, proved), which is why completeness declares each handle position at its
own fresh key; and the signature check no longer admits CE-015's host table
(`#guard_msgs (error)`).
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
#guard admitSig ⟨dupTable, []⟩ == .error (.duplicateRow (rowKey (row "query" .nat)))
#guard match admitProgram (.succeed (.lit (.nat 0))) ⟨dupTable, []⟩ with
  | .error (.signature (.duplicateRow k)) => k == rowKey (row "query" .nat)
  | _ => false

/-- TY-05 on a table: `lawful` refuses and the signature's refusal locates (proved, by the
theorems: a table `Table.lawful` refuses is no lawful signature). -/
theorem dupTable_located : admitSig ⟨dupTable, []⟩ ≠ .ok () := fun h =>
  absurd ((admitSig_ok_iff _).mp h).tableLawful (by decide)

/-! ## Rows 127 and 149: the column check -/

/-- A host row at the given request and answer columns (the data probe's `hostRow`). -/
def hostRow (request answer : Ty) : Row :=
  { name := "query", spelling := "Host.query", request, answer, error := .never,
    kind := .async, registration := .external, cite := "" }

/-- The data probe's program: one host call. -/
def pHostNat : NativeEff := .perform (.external 0) (.lit (.nat 1))

/-- A program whose answer column is `prod never nat`: the pair of a failed bind's value and a
number. -/
def pNeverPair : NativeEff :=
  .bind (.fail (.lit (.nat 1))) (.succeed (.app "pair" (.cons (.var 0) (.cons (.lit (.nat 1)) .nil))))

-- tested: the checker types it at `prod never nat`, the column admission refuses
#guard (Api.typeOf pNeverPair).map (·.answer) == some (.prod .never .nat)

-- tested: the checks locate CE-015's columns (a host-row answer, a host-row request, a program
-- answer), and leave the designed bottom and inhabited columns alone
#guard admitSig ⟨[hostRow .nat (.except .never .never)], []⟩ = .error (.row 0 (.emptyColumn "answer"))
#guard admitSig ⟨[hostRow (.prod .never .nat) .nat], []⟩ = .error (.row 0 (.emptyColumn "request"))
#guard admitSig ⟨[hostRow .nat .nat, { hostRow .nat (.prod .nat .never) with spelling := "Host.b" }],
  []⟩ = .error (.row 1 (.emptyColumn "answer"))
#guard admitSig ⟨[hostRow .nat .nat, { hostRow (.list .never) (.option .never) with spelling := "Host.b" }],
  []⟩ = .ok ()
#guard findEmptyColumnInEffTy ⟨.prod .never .nat, .never, .empty⟩ = some ["program", "answer"]
#guard findEmptyColumnInEffTy ⟨.never, .except .never .never, .empty⟩ = some ["program", "error"]
#guard findEmptyColumnInEffTy ⟨.never, .never, .empty⟩ = none
-- tested: two refusals, not one (TY-13): the `int` scan refuses `list int`, which has a member,
-- and misses `prod never nat`, which has none
#guard admitColumn (.list .int) && (findInt [] (.list .int)).isSome
#guard !admitColumn (.prod .never .nat) && (findInt [] (.prod .never .nat)).isNone
-- tested: runner admission refuses CE-015's columns, each at its position (a host-row answer and
-- a host-row request at the signature, a program answer after every other check has passed),
-- and still admits the inhabited table
#guard (match admitProgram pHostNat ⟨[hostRow .nat (.except .never .never)], []⟩ with
  | .error (.signature why) => why == .row 0 (.emptyColumn "answer")
  | _ => false)
#guard (match admitProgram (.succeed (.lit (.nat 0))) ⟨[hostRow (.prod .never .nat) .nat], []⟩ with
  | .error (.signature why) => why == .row 0 (.emptyColumn "request")
  | _ => false)
#guard (match admitProgram pNeverPair with
  | .error (.emptyColumn pos) => pos == ["program", "answer"]
  | _ => false)
#guard (match admitProgram pHostNat ⟨[hostRow .nat .nat], []⟩ with
  | .ok _ => true
  | .error _ => false)

/-- The signature check refuses the CE-015 table (proved). -/
theorem ce015_table_refused :
    admitSig ⟨[hostRow .nat (.except .never .never)], []⟩ = .error (.row 0 (.emptyColumn "answer")) := by
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
-- signature check.
/--
error: Tactic `decide` proved that the proposition
  admitSig { rows := [hostRow Ty.nat (Ty.never.except Ty.never)] } = Except.ok ()
is false
-/
#guard_msgs (error) in
example : admitSig ⟨[hostRow .nat (.except .never .never)], []⟩ = .ok () := by
  decide +kernel

end Test.Program.AdmissionColumns
