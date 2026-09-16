import Effect4.Api
import Effect4.Laws.Program.Typing.Blame

/-! The facade's refusal is the checker's (DI-86): `Api.explain` answers `none` exactly when
`Api.wellTyped` answers `true`, the layer references resolved the same way on both sides. -/
set_option autoImplicit false
namespace Effect4.Api
open Effect4 Effect4.Program

theorem explain_none_iff (program : Program) (table : RowTable) :
    explain program table = none ↔ wellTyped program table = true := by
  unfold explain wellTyped typeOf Program.typeOfProgram Program.typeOf
  split
  · split <;> simp_all [Program.explain_none_iff]
  · simp_all

theorem blame_none_iff (program : Program) (table : RowTable) :
    blame program table = none ↔ wellTyped program table = true := by
  simp [blame, ← explain_none_iff]

end Effect4.Api
