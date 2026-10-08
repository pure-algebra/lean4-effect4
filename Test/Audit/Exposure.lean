import Tools.Exposure

/-!
Controls of the exposure table (`tools/Tools/ArchitectureRoles.lean`, decisions row 332): the
longest declared prefix decides a path's class, and the class decides what a user's file may
import. Each line is a finite evaluation of the table.
-/

open Tools.Architecture Tools.Exposure

-- An entry module is a file, and it wins over its directory's class.
#guard exposureOf "src/Effect4/Run.lean" == some .entry
#guard exposureOf "src/Effect4/Run/Tape.lean" == some .internal
-- An entry module inside the proof graph wins over the graph's class.
#guard exposureOf "src/Effect4/Laws/Author.lean" == some .entry
-- A composed module's directory is the module library; the shared step language is internal.
#guard exposureOf "src/Effect4/Modules/Queue/Ops.lean" == some .library
#guard exposureOf "src/Effect4/Modules/Step.lean" == some .internal
-- The proof graph, the tools, the batteries.
#guard exposureOf "src/Effect4/Laws/Modules/Step.lean" == some .proof
#guard exposureOf "tools/Tools/Explain.lean" == some .tool
#guard exposureOf "Test/Dogfood/P1HttpCache.lean" == some .test
-- A path outside every declared prefix has no class.
#guard exposureOf "vendor/effect-4.0.1/src/Queue.ts" == none
-- What a user may import by name.
#guard Exposure.entry.userImportable && Exposure.library.userImportable
#guard !Exposure.internal.userImportable && !Exposure.proof.userImportable
-- A module's source path, from its name.
#guard pathOf `Effect4.Program.Authoring.Loops == some "src/Effect4/Program/Authoring/Loops.lean"
#guard pathOf `Tools.Explain == some "tools/Tools/Explain.lean"
#guard pathOf `Lean.Elab == none
