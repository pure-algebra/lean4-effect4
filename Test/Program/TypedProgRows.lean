import Effect4.Laws.Program.Typed.Residual
import Effect4.Laws.Program.Signature

/-!
# Row 116: the host-row entry's domain bit, and `TypedProg` monotone in the table (TY-12)

`asyncPre`'s external arm (`Laws/Program/Typed/Residual.lean`) reads the row
`(nativeSignature root.table).rowOf op` without its domain bit. Outside the table that row is the
placeholder, whose columns are `never`, which is below every certificate: the entry holds at
every certificate at a short table and constrains at a longer one, so `TypedProg` is not
monotone in the table (the TREE verifier's `typedProg_not_table_monotone`, restated here as
`typedProg_not_table_monotone_of` over the entry as it reads today, `AsyncRowOnly`). Row 116
requires the bit (`AsyncDomainBit`); with it, `TypedProg` is monotone along an appended table
(`typedProg_rows_append`, the positive control TY-12 asks for).

Both are stated against an explicit hypothesis about the entry, because the entry is seat B's to
amend: `asyncRowOnly_now` holds at this commit and is the tripwire the bit flips (seat B
replaces it with `asyncDomainBit_now`, `docs/research/2026-10-01-landing/receipt-A.md`).
-/

set_option autoImplicit false

namespace Test.Program.TypedProgRows

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed Effect4.Program.Sched

/-- Row 116's entry: an external registration's precondition includes its row's domain bit. -/
def AsyncDomainBit : Prop :=
  ∀ (root : ProgramSource) (w : Typed.World) (op : NativeOp) (req : Val) (cert : EffTy),
    asyncPre root w (.external op req) cert → (nativeSignature root.table).dom op = true

/-- The entry as it reads at this commit: the row's columns below the certificate, and nothing
about the domain. -/
def AsyncRowOnly : Prop :=
  ∀ (root : ProgramSource) (w : Typed.World) (op : NativeOp) (req : Val) (cert : EffTy),
    asyncPre root w (.external op req) cert ↔
      (((nativeSignature root.table).rowOf op).answer.sub cert.answer = true ∧
        ((nativeSignature root.table).rowOf op).error.sub cert.error = true)

/-- **Tripwire (proved at this commit).** The entry reads no domain bit. Row 116's amendment
(seat B) makes this false; it is then replaced by `AsyncDomainBit`'s proof. -/
theorem asyncRowOnly_now : AsyncRowOnly := fun _ _ _ _ _ => Iff.rfl

/-! ## The red control -/

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

/-- **Red control (proved).** Over the entry as it reads today, `TypedProg` is not monotone along
an appended table: the call is typed at `nat` under the empty table (index 0 is the placeholder,
whose `never` columns are below every certificate) and refused under `[rowB]` (whatever the
certificate, it is above `string`, so the continuation must accept a string exit at `nat`). -/
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

/-- The red control at this commit. -/
theorem typedProg_not_table_monotone :
    ¬ ∀ (p : NativeEff) (w : Typed.World) (ty : EffTy) (prog : RProgram),
        TypedProg (srcShort p) w ty prog → TypedProg (srcLong p) w ty prog :=
  typedProg_not_table_monotone_of asyncRowOnly_now

/-! ## The positive control: with the bit, `TypedProg` is monotone in the table

`AsyncEntryRows` is what the induction needs of the external entry: it transports along an
appended table. Row 116's entry has that property whatever else it reads (`bitEntry_rows_append`:
the bit puts the operation in the shorter domain, where the longer table's row is the same,
`rows_append`), and the entry as it reads today does not (`typedProg_not_table_monotone`). -/

/-- The external entry transports along an appended table. -/
def AsyncEntryRows : Prop :=
  ∀ (src src' : ProgramSource) (t' : RowTable), src'.table = src.table ++ t' →
    ∀ (w : Typed.World) (op : NativeOp) (req : Val) (cert : EffTy),
      asyncPre src w (.external op req) cert → asyncPre src' w (.external op req) cert

/-- Row 116's entry, as ruled: the domain bit, then the row's columns below the certificate. -/
def bitEntry (root : ProgramSource) (op : NativeOp) (cert : EffTy) : Prop :=
  (nativeSignature root.table).dom op = true ∧
    ((nativeSignature root.table).rowOf op).answer.sub cert.answer = true ∧
    ((nativeSignature root.table).rowOf op).error.sub cert.error = true

/-- **Row 116's entry transports (proved).** -/
theorem bitEntry_rows_append (src src' : ProgramSource) (t' : RowTable)
    (htab : src'.table = src.table ++ t') (op : NativeOp) (cert : EffTy)
    (h : bitEntry src op cert) : bitEntry src' op cert := by
  obtain ⟨hdom, ha, he⟩ := h
  have hrow := (rows_append src.table t').row op hdom
  unfold bitEntry
  rw [htab, hrow.2]
  exact ⟨hrow.1, ha, he⟩

section Transport

variable (src src' : ProgramSource) (t' : RowTable)
  (hprog : src'.program = src.program) (htab : src'.table = src.table ++ t')
include hprog htab

theorem pointTyped_rows_append {w : Typed.World} {point : Point} {ty : EffTy}
    (h : PointTyped src w point ty) : PointTyped src' w point ty := by
  obtain ⟨e, env, hat, hcheck, henv⟩ := h
  refine ⟨e, env, ?_, ?_, henv⟩
  · rw [hprog]
    exact hat
  · rw [htab]
    exact check_ext (rows_append src.table t') hcheck

theorem bodyTyped_rows_append {w : Typed.World} {body : Body} {ty : EffTy}
    (h : BodyTyped src w body ty) : BodyTyped src' w body ty := by
  cases h with
  | at_ p ty hp => exact .at_ p ty (pointTyped_rows_append src src' t' hprog htab hp)
  | fin name ex ty hex => exact .fin name ex ty hex
  | raceCleanup race => exact .raceCleanup race
  | acquireIn p ctx ty hp =>
    exact .acquireIn p ctx ty (pointTyped_rows_append src src' t' hprog htab hp)
  | release p prev ty hp =>
    exact .release p prev ty (pointTyped_rows_append src src' t' hprog htab hp)
  | layerBuild p m scope ty hp =>
    exact .layerBuild p m scope ty (pointTyped_rows_append src src' t' hprog htab hp)

theorem storePre_rows_append {w : Typed.World} {op : SyncOp} {cert : StoreCert op}
    (h : storePre src w op cert) : storePre src' w op cert := by
  cases op with
  | memoGet layer m =>
    obtain ⟨l, lt, hat, hcheck, herr⟩ := h
    refine ⟨l, lt, ?_, ?_, herr⟩
    · rw [hprog]
      exact hat
    · rw [htab]
      exact checkLayer_ext (rows_append src.table t') hcheck
  | _ => exact h

omit hprog in
theorem asyncPre_rows_append (hentry : AsyncEntryRows) {w : Typed.World} {register : EffName}
    {cert : EffTy} (h : asyncPre src w register cert) : asyncPre src' w register cert := by
  cases register with
  | external op req => exact hentry src src' t' htab w op req cert h
  | store name => cases name <;> exact h
  | _ => exact h

theorem fiberPre_rows_append (hentry : AsyncEntryRows) {w : Typed.World} {op : FiberOp}
    {cert : FiberCert op} (h : fiberPre src w op cert) : fiberPre src' w op cert := by
  cases op with
  | raceAll entrants race =>
    intro p hp
    obtain ⟨ty, hpt, ha, he⟩ := h p hp
    exact ⟨ty, pointTyped_rows_append src src' t' hprog htab hpt, ha, he⟩
  | async register token => exact asyncPre_rows_append src src' t' htab hentry h
  | «scoped» body => exact pointTyped_rows_append src src' t' hprog htab h
  | mask flag body => exact bodyTyped_rows_append src src' t' hprog htab h
  | forkScoped child options path => exact pointTyped_rows_append src src' t' hprog htab h
  | fork body options path => exact bodyTyped_rows_append src src' t' hprog htab h
  | forkIn child options scope path => exact ⟨pointTyped_rows_append src src' t' hprog htab h.1, h.2⟩
  | gen p => exact pointTyped_rows_append src src' t' hprog htab h
  | loop p name => exact pointTyped_rows_append src src' t' hprog htab h
  | _ => exact h

/-- **TY-12's positive control (proved, under the entry's transport).** With row 116's entry,
`TypedProg` is monotone along an appended table: every precondition that reads the source
transports (`check_ext` for the checked points, `checkLayer_ext` for the memo layer, the entry
for host rows), and no postcondition reads it. -/
theorem typedProg_rows_append (hentry : AsyncEntryRows) :
    ∀ {w : Typed.World} {ty : EffTy} {p : RProgram}, TypedProg src w ty p → TypedProg src' w ty p := by
  intro w ty p h
  induction h with
  | pure exit => exact .pure exit
  | store cert pre next ih =>
    exact .store cert (storePre_rows_append src src' t' hprog htab pre)
      fun w' hle ans hpost => ih w' hle ans hpost
  | fiber notGuard notUnguard notFinish notScopeExit cert pre next ih =>
    exact .fiber notGuard notUnguard notFinish notScopeExit cert
      (fiberPre_rows_append src src' t' hprog htab hentry pre)
      fun w' hle ans hpost => ih w' hle ans hpost
  | guard mid body run skip ihbody ihrun =>
    exact .guard mid ihbody (fun w' hle ex hpost => ihrun w' hle ex hpost) skip
  | unguard payload => exact .unguard payload
  | finishFinalizer payload => exact .finishFinalizer payload
  | scopeExit payload next ih => exact .scopeExit payload fun w' hle ans => ih w' hle ans

end Transport

#print axioms asyncRowOnly_now
#print axioms rowB_lawful
#print axioms typedProg_not_table_monotone_of
#print axioms typedProg_not_table_monotone
#print axioms bitEntry_rows_append
#print axioms pointTyped_rows_append
#print axioms bodyTyped_rows_append
#print axioms storePre_rows_append
#print axioms asyncPre_rows_append
#print axioms fiberPre_rows_append
#print axioms typedProg_rows_append

end Test.Program.TypedProgRows
