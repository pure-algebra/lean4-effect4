import Effect4.Api.Object
import Effect4.Laws.Api.Built
import Effect4.Laws.Program.SourceTable
import Effect4.Laws.Program.Sketch

/-! Program objects: admission and exact stored bytes.
Placement: exact-codecs, object-exact/object-bytes-exact/object-load-exact, compatibility, R13.
The table helpers instantiate source-annotation-agrees, initial-algebras-folds, R14.
Admission helpers instantiate built-admission-exact; the digest helper instantiates program-digest-exact.
Consumers: file loading, saved-session restoration and compiler inspection.
Byte retraction requires the canonical value's WF. Hash injectivity is never assumed.
No host execution, persistence, progress or cross-layout migration property follows. -/

set_option autoImplicit false
namespace Effect4.Program.Object
open Effect4 Effect4.Program Effect4.Store

/-- Helper of object-exact: successful admission retains exactly the input data. -/
theorem ofBuilt_of_open {o : Object} {b : Api.Built} (h : o.open = .ok b) : ofBuilt b = o := by
  unfold Object.open Api.Built.ofProgram at h
  split at h
  · cases h
  · cases h
    rfl

/-- object-exact: every admitted program reopens to itself, including its certificate. -/
@[semantics "exact-codecs" (requirement := R13)]
theorem open_ofBuilt (b : Api.Built) : (ofBuilt b).open = .ok b := by
  unfold Object.open ofBuilt
  rw [Api.Built.ofProgram_of_admitted b.app b.program b.admitted]

/-- built-admission-exact at objects: opening succeeds exactly when an admission certificate exists. -/
theorem open_ok_iff (o : Object) :
    (∃ b, o.open = .ok b) ↔ Nonempty (AdmittedProgram o.program o.app) := by
  constructor
  · rintro ⟨b, h⟩
    have e := ofBuilt_of_open h
    subst e
    exact ⟨b.admitted⟩
  · rintro ⟨a⟩
    exact ⟨_, Api.Built.ofProgram_of_admitted o.app o.program a⟩

/-- built-admission-exact at objects: opening retains the admission procedure's exact refusal. -/
theorem open_error_iff (o : Object) (why : AdmitRefusal) :
    o.open = .error why ↔ admitProgram o.program o.app = .error why :=
  Api.Built.ofProgram_error_iff o.app o.program why

/-- Helper of object-load-exact: well-formed node bytes read back to the object. -/
theorem read_bytes (o : Object) (h : (toVal o).WF) : read (bytes o) = .ok o := by
  unfold read bytes
  rw [(Node.read_ok_iff).mpr (Node.decode_encode (nodeOf o) h rfl)]
  dsimp only
  rw [Node.readContent_nodeOf]
  rfl

/-- object-bytes-exact: accepted bytes are exactly the returned object's node encoding. -/
@[semantics "exact-codecs" (requirement := R13)]
theorem read_exact {bs : Bytes} {o : Object} (h : read bs = .ok o) :
    bs = bytes o ∧ (toVal o).WF := by
  unfold read at h
  split at h
  · cases h
  · next n hn =>
    obtain ⟨hb, hwf, -⟩ := Node.read_exact hn
    have hc : Node.readContent (α := Object) n = .ok o := by
      cases hr : Node.readContent (α := Object) n with
      | error e =>
        rw [hr] at h
        cases h
      | ok a =>
        rw [hr] at h
        cases h
        rfl
    have hn' := Node.readContent_exact hc
    subst hn'
    exact ⟨hb, hwf⟩

/-- object-load-exact: the saved bytes recover the original admitted program. -/
@[semantics "exact-codecs" (requirement := R13)]
theorem load_bytes (b : Api.Built) (hwf : (toVal (ofBuilt b)).WF) :
    load (bytes (ofBuilt b)) = .ok b := by
  unfold load
  rw [read_bytes _ hwf]
  dsimp only
  rw [open_ofBuilt]
  rfl

/-- Helper of object-load-exact: successful loading accepts only that program's exact object bytes. -/
theorem load_exact {bs : Bytes} {b : Api.Built} (h : load bs = .ok b) :
    bs = bytes (ofBuilt b) := by
  unfold load at h
  split at h
  · cases h
  · next o ho =>
    have hopen : o.open = .ok b := by
      cases hr : o.open with
      | error e =>
        rw [hr] at h
        cases h
      | ok c =>
        rw [hr] at h
        cases h
        rfl
    rw [ofBuilt_of_open hopen]
    exact (read_exact ho).1

/-- program-digest-exact at objects: equal references give equality or an exhibited collision. -/
theorem ref_eq_or_collision {o p : Object} (ho : (toVal o).WF) (hp : (toVal p).WF)
    (h : o.ref = p.ref) :
    o = p ∨ ((nodeOf o).encode ≠ (nodeOf p).encode ∧
      sha256 (nodeOf o).encode = sha256 (nodeOf p).encode) :=
  address_eq_or_collision ho hp h

/-- Helper of source-annotation-agrees: the address table is the existing source annotation. -/
theorem table_eq (o : Object) :
    o.table = Sketch.sourceAnnotate { program := o.program } o.app := rfl

/-- Helper of source-annotation-agrees: the first entry holds the source check at the root. -/
theorem table_head (o : Object) :
    ∃ rest, o.table = ⟨[], some (.env []), some (Sketch.sourceCheck { program := o.program } o.app)⟩
      :: rest := by
  rw [table_eq, Sketch.sourceAnnotate_eq_sourceTable]
  exact Sketch.sourceTable_head _ _

/-- Helper of source-annotation-agrees: the source check agrees with the admission typing function. -/
theorem table_root_toOption (o : Object) :
    (Sketch.sourceCheck { program := o.program } o.app).toOption = Api.typeOf o.program o.app := by
  rw [Sketch.sourceCheck_toOption]
  show typeOfProgram (o.app.withHoles []).signature o.program = _
  rw [SigApp.withHoles_nil]
  rfl

/-- source-annotation-agrees at objects: admitted objects carry their certified type at the table root. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem table_root_of_open {o : Object} {b : Api.Built} (h : o.open = .ok b) :
    Sketch.sourceCheck { program := o.program } o.app = .ok b.ty := by
  have e := ofBuilt_of_open h
  subst e
  have hty : (Sketch.sourceCheck { program := b.program } b.app).toOption = some b.ty :=
    (table_root_toOption (ofBuilt b)).trans b.admitted.typed
  show Sketch.sourceCheck { program := b.program } b.app = .ok b.ty
  cases hc : Sketch.sourceCheck { program := b.program } b.app with
  | error why =>
    rw [hc] at hty
    cases hty
  | ok t =>
    rw [hc] at hty
    cases hty
    rfl

/-- source-annotation-agrees at objects: no source refusal exactly when the root typing succeeds. -/
theorem refusals_nil_iff (o : Object) :
    Sketch.sourceRefusals { program := o.program } o.app = [] ↔
      (Api.typeOf o.program o.app).isSome = true := by
  rw [Sketch.sourceRefusals_nil_iff, table_root_toOption]

end Effect4.Program.Object
