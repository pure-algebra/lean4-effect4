import Effect4.Laws.Program.DenoteRowsB
import Effect4.Laws.Api.SessionMeaningLoop

/-! Review adapter: all semantics below are aliases of the landed definitions.
The original research interpretation is not imported. -/
set_option autoImplicit false

deriving instance DecidableEq for Effect4.Program.Denote.RowsObservation

namespace Test.HostMeaningWidening
abbrev LoopedDataRows := Effect4.Program.Denote.LoopedDataRows
abbrev denoteRowsB := Effect4.Program.Denote.denoteRowsB
abbrev meaningUnderB := @Effect4.Program.Denote.meaningUnderB
abbrev coarseRowsB := Effect4.Program.Denote.coarseRowsB
abbrev End := Effect4.Program.Denote.RowsStop
abbrev Observation := Effect4.Program.Denote.RowsObservation
abbrev observeTree := @Effect4.Program.Denote.observeRows
end Test.HostMeaningWidening
