import Effect4.Library.Stream.Steps
import Effect4.Laws.Step.Checking

set_option autoImplicit false

namespace Effect4.Stream

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Modules

variable {Op : Type} {sig : Signature Op} {env : Env} {path : List Nat} {types : List Ty}
variable (atoms : sig.atomOf = nativeAtomTy)
include atoms

/-- **The end step types at the cursor's type**, for an accumulator at `A` and a leftover at `D`. -/
theorem types_endStep {acc leftover : TermSrc} {A D : Ty}
    (hacc : TypesEach sig acc env path types A) (hl : TypesEach sig leftover env path types D) :
    TypesEach sig (endStep acc leftover) env path types (.prod A (.option D)) :=
  types_pair atoms hacc (types_some atoms hl)

/-- **The chunk step types below the cursor's type**: the option of nothing is below every
option, so the loop's stated cursor type takes it by subsumption. -/
theorem types_chunkStep {next : TermSrc} {A : Ty}
    (hn : TypesEach sig next env path types A) :
    TypesEach sig (chunkStep next) env path types (.prod A (.option .never)) :=
  types_pair atoms hn (types_noneT atoms)

end Effect4.Stream
