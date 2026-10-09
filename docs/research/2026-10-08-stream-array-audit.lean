import Test.Program.StreamArray
import Tools.LoadPaths

/-! Narrow proof receipt. The load report sees only this imported environment.
This file reports dependencies; the production axiom gate remains the coordinator's integration check. -/

#print axioms Effect4.Stream.arrayStep_eval
#print axioms Effect4.Stream.arrayStep_agrees
#print axioms Effect4.Stream.arrayBatch_answers
#print axioms Effect4.Stream.arrayOpen
#print axioms Effect4.Stream.arrayBatch
#print axioms Effect4.Stream.arrayPull
#print axioms Effect4.Stream.fromArray
#print axioms Effect4.Stream.ArrayDefinitions.make
#load_report Effect4.Laws.Library.Stream.Array
