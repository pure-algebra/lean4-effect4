/-! ## Acceptance guards for the generated row lemmas

Appended verbatim by `--append tools/Effect4Gen/guards/rowslaws.lean` into
`src/Effect4/Laws/Program/Authoring/Rows.lean`. -/

namespace Effect4.Program.AuthoringRowsLawsGuards

open Effect4.Program Effect4.Program.Authoring

example : Src.Scoped (bind "r" (Ref.make (nat 0)) (Ref.set (var "r") (nat 1))) := by
  authoring_scoped

example : Src.Scoped (bind "d" Deferred.make (Deferred.succeed (var "d") (nat 7))) := by
  authoring_scoped

end Effect4.Program.AuthoringRowsLawsGuards
