import Test.Program.SourceDocumentControls
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000
open Effect4.Program Check
open Test.Program.SeamsS1.DocControls
-- The two inverse items each ask once; prior document actions must not run again.
#guard reverted.trace.length = 2
-- A missing undo entry performs no earlier document checks.
#guard (run d0 (.revert 5)).trace.isEmpty
-- A no-op's empty inverse changes history without replaying the original open.
#guard (run noopDoc (.revert 0)).trace.isEmpty
