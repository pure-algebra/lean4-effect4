import Effect4.Api.Author
import Effect4.Laws.Program.CheckedTyping
import Effect4.Laws.Api.Built

/-!
# Probe: the admission certificate is a proposition in all but name

Question: what does `Built` hold beyond its data? `AdmittedProgram program app` has one data
field, the type `ty`, and four proof fields. The checker's equation fixes `ty`
(`TypedProgram.type_unique`), so any two certificates at one index are equal. The decision
procedure answers the certificate it is given (`admitProgram_eq_ok`,
`src/Effect4/Laws/Program/CheckedTyping.lean`), and that law alone gives uniqueness.

Consequence: a `Built` is determined by its application, its program and its row names. The
certificate adds no information; it is the evidence that admission holds at that index.
-/

set_option autoImplicit false

namespace Probe.Certificate

open Effect4 Effect4.Program Effect4.Api

/-- **One certificate per index**: two admission certificates at one program and one application
are equal. The decision procedure answers each of them (`admitProgram_eq_ok`). -/
theorem admitted_unique {program : Program} {app : SigApp}
    (a b : AdmittedProgram program app) : a = b := by
  have h := (admitProgram_eq_ok a).symm.trans (admitProgram_eq_ok b)
  exact Except.ok.inj h

instance {program : Program} {app : SigApp} : Subsingleton (AdmittedProgram program app) :=
  ⟨admitted_unique⟩

/-- **A built program is its data**: two values of `Built` with equal application, program and row
names are equal. -/
theorem built_ext {b c : Built} (happ : b.app = c.app) (hprogram : b.program = c.program)
    (hnames : b.rowNames = c.rowNames) : b = c := by
  cases b with
  | mk app program admitted rowNames =>
    cases c with
    | mk app' program' admitted' rowNames' =>
      dsimp only at happ hprogram hnames
      subst happ hprogram hnames
      rw [admitted_unique admitted admitted']

/-- **Admission is decided exactly**: the procedure answers `ok` at an index exactly when a
certificate exists there. The forward direction is the answer itself; the converse is
`admitProgram_eq_ok`. -/
theorem admitProgram_ok_iff (program : Program) (app : SigApp) :
    (∃ a, admitProgram program app = .ok a) ↔ Nonempty (AdmittedProgram program app) :=
  ⟨fun ⟨a, _⟩ => ⟨a⟩, fun ⟨a⟩ => ⟨a, admitProgram_eq_ok a⟩⟩

-- control: the type is data, so `AdmittedProgram` is no `Prop` and a `Subtype` cannot carry it;
-- uniqueness is a theorem about the index, not a property of the universe
/-- error: Type mismatch
  AdmittedProgram
has type
  NativeEff → SigApp → Type
of sort `Type 1` but is expected to have type
  NativeEff → SigApp → Prop
of sort `Type` -/
#guard_msgs in
example : NativeEff → SigApp → Prop := AdmittedProgram

end Probe.Certificate
