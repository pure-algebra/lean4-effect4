import Effect4.Laws.Program.Typed.Residual
import Effect4.Laws.Program.Signature

/-!
# Row 116: the host-row entry's domain bit, and `TypedProg` monotone in the table (TY-12)

Before row 116 landed, `asyncPre`'s external arm (`Laws/Program/Typed/Residual.lean`) read the row
`(nativeSignature root.table).rowOf op` without its domain bit (`AsyncRowOnly`). Outside the table
that row is the placeholder, whose columns are `never`, which is below every certificate: the entry
held at every certificate at a short table and constrained at a longer one, so `TypedProg` was not
monotone in the table (the TREE verifier's `typedProg_not_table_monotone`, restated here as
`typedProg_not_table_monotone_of` over that entry, kept as history).

Row 116 (integration seat I2, step 6): the arm is `bitEntry`, the bit then the columns
(`asyncDomainBit_now`; the old reading is refuted, `asyncRowOnly_false`, and the tripwire's proof
is pinned failing below). Its transport along an appended table (`bitEntry_rows_append`) proves
the hypothesis seat A's positive control took (`asyncEntryRows`), and `TypedProg` is monotone
along an appended table outright (`typedProg_rows_append`, moved to `Residual.lean` beside
`typedProg_mono`); at the red control's own sources the flip is `typedProg_table_monotone`.
-/

set_option autoImplicit false

namespace Test.Program.TypedProgRows

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed Effect4.Program.Sched

/-- Row 116's entry: an external registration's precondition includes its row's domain bit. -/
def AsyncDomainBit : Prop :=
  ∀ (root : ProgramSource) (w : Typed.World) (op : NativeOp) (req : Val) (cert : EffTy),
    asyncPre root w (.external op req) cert → (nativeSignature root.table).dom op = true

/-- **Row 116 holds (proved).** The external arm is `bitEntry`, whose first clause is the bit
(`root.signature`'s domain is `nativeSignature root.table`'s). It replaces the tripwire
`asyncRowOnly_now`. -/
theorem asyncDomainBit_now : AsyncDomainBit := fun _ _ _ _ _ h => h.1

/-- The entry as it read before row 116 landed: the row's columns below the certificate, and
nothing about the domain (history). -/
def AsyncRowOnly : Prop :=
  ∀ (root : ProgramSource) (w : Typed.World) (op : NativeOp) (req : Val) (cert : EffTy),
    asyncPre root w (.external op req) cert ↔
      (((nativeSignature root.table).rowOf op).answer.sub cert.answer = true ∧
        ((nativeSignature root.table).rowOf op).error.sub cert.error = true)

/-! ## The red control (history) and its flip -/

/-- A host row answering a string. -/
def rowB : Effect4.Program.Row :=
  { name := "b", spelling := "B.b", shape := .value, kind := .async, request := .unit,
    answer := .string, cite := "probe", registration := .external }

/-- A reference program parked on host row 0, whose continuation hands the exit back. -/
def hostCall : RProgram :=
  .vis (.inr (.async (.external (.external 0) Val.unit) Val.unit)) (fun ex => .pure ex)

def srcShort (p : NativeEff) : ProgramSource := { program := p, table := [] }

/-- The row is lawful, so the longer source carries its evidence. -/
theorem rowB_lawful : LawfulSig ⟨[] ++ [rowB], []⟩ := by decide +kernel

def srcLong (p : NativeEff) : ProgramSource :=
  { program := p, table := [] ++ [rowB], lawful := rowB_lawful }

/-- **Historical red control (proved).** Over the entry as it read before row 116, `TypedProg` was
not monotone along an appended table: the call is typed at `nat` under the empty table (index 0
is the placeholder, whose `never` columns are below every certificate) and refused under
`[rowB]` (whatever the certificate, it is above `string`, so the continuation must accept a
string exit at `nat`). Its unconditional instance, `typedProg_not_table_monotone` at the tripwire,
is false since row 116 (`typedProg_table_monotone`). -/
theorem typedProg_not_table_monotone_of (hold : AsyncRowOnly) :
    ¬ ∀ (p : NativeEff) (w : Typed.World) (ty : EffTy) (prog : RProgram),
        TypedProg (srcShort p) w ty prog → TypedProg (srcLong p) w ty prog := by
  intro hmono
  let w0 : Typed.World := initialWorld (EffTy.pure .unit)
  have hshort : TypedProg (srcShort (.succeed (.lit .unit))) w0 (EffTy.pure .nat) hostCall :=
    TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ _ _ h => nomatch h) (EffTy.pure .nat : EffTy)
      ((hold (srcShort (.succeed (.lit .unit))) w0 (.external 0) Val.unit (EffTy.pure .nat)).mpr
        ⟨Ty.OrderProof.sub_never _, Ty.OrderProof.sub_never _⟩)
      (fun _ _ _ hpost => TypedProg.pure hpost)
  have hlong := hmono _ w0 _ hostCall hshort
  cases hlong with
  | fiber _ _ _ _ cert pre next =>
    have hsub : Ty.sub .string cert.answer = true :=
      ((hold (srcLong (.succeed (.lit .unit))) w0 (.external 0) Val.unit cert).mp pre).1
    have hk := next w0 (leHost_refl w0) (.success (Val.str "x"))
      ⟨fits_sub w0 hsub (Val.str "x") trivial, trivial⟩
    have hex := TypedProg.pure_inv hk
    exact hex.1

/-- **The old reading is refuted (proved).** At the empty table host row 0 is outside the domain,
so the entry refuses it at every certificate, while the old reading admitted it at `nat`. -/
theorem asyncRowOnly_false : ¬ AsyncRowOnly := by
  intro hold
  have entry := (hold (srcShort (.succeed (.lit .unit))) (initialWorld (EffTy.pure .unit))
    (.external 0) Val.unit (EffTy.pure .nat)).mpr
      ⟨Ty.OrderProof.sub_never _, Ty.OrderProof.sub_never _⟩
  have hdom : (nativeSignature []).dom (.external 0) = true := entry.1
  exact absurd hdom (by decide)

-- Red control: the tripwire's proof no longer elaborates against the entry with the bit.
/--
error: Type mismatch
  Iff.rfl
has type
  ?m.6 ↔ ?m.6
but is expected to have type
  asyncPre x✝⁴ x✝³ (EffName.external x✝² x✝¹) x✝ ↔
    ((nativeSignature x✝⁴.table).rowOf x✝²).answer.sub x✝.answer = true ∧
      ((nativeSignature x✝⁴.table).rowOf x✝²).error.sub x✝.error = true
-/
#guard_msgs (error) in
example : AsyncRowOnly := fun _ _ _ _ _ => Iff.rfl

/-- **The flip of the red control (proved).** With the bit, `TypedProg` is monotone from the
short source to the long one, at every program, world and type (`typedProg_rows_append`). -/
theorem typedProg_table_monotone :
    ∀ (p : NativeEff) (w : Typed.World) (ty : EffTy) (prog : RProgram),
      TypedProg (srcShort p) w ty prog → TypedProg (srcLong p) w ty prog :=
  fun p _ _ _ h => typedProg_rows_append (srcShort p) (srcLong p) [rowB] rfl rfl rfl h

/-! ## The entry's transport, the hypothesis seat A's positive control took -/

/-- The external entry transports along an appended table. -/
def AsyncEntryRows : Prop :=
  ∀ (src src' : ProgramSource) (t' : RowTable), src'.table = src.table ++ t' →
    ∀ (w : Typed.World) (op : NativeOp) (req : Val) (cert : EffTy),
      asyncPre src w (.external op req) cert → asyncPre src' w (.external op req) cert

/-- **It holds (proved), from `bitEntry_rows_append`.** -/
theorem asyncEntryRows : AsyncEntryRows :=
  fun src src' t' htab _ op _ cert h => bitEntry_rows_append src src' t' htab op cert h

#print axioms asyncDomainBit_now
#print axioms rowB_lawful
#print axioms typedProg_not_table_monotone_of
#print axioms asyncRowOnly_false
#print axioms typedProg_table_monotone
#print axioms asyncEntryRows
#print axioms Effect4.Program.Typed.bitEntry_rows_append
#print axioms Effect4.Program.Typed.signature_rows_append
#print axioms Effect4.Program.Typed.pointTyped_rows_append
#print axioms Effect4.Program.Typed.bodyTyped_rows_append
#print axioms Effect4.Program.Typed.storePre_rows_append
#print axioms Effect4.Program.Typed.asyncPre_rows_append
#print axioms Effect4.Program.Typed.fiberPre_rows_append
#print axioms Effect4.Program.Typed.typedProg_rows_append

end Test.Program.TypedProgRows
