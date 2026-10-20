import Compiler.GeneratedStamp

/-!
# Tools.GeneratedStamp — the stamp's former module, kept for one importer

The stamp moved under the compiler on 2026-10-20 (`tools/Compiler/GeneratedStamp.lean`, the entry
point's second slice), and its declarations kept the namespace `Tools.GeneratedStamp`. One
importer still names this module: `tools/Drivers/TsGen.lean`, which a parallel seat edits. This
module re-exports the stamp and declares nothing. When that import names
`Compiler.GeneratedStamp`, this module is deleted.
-/
