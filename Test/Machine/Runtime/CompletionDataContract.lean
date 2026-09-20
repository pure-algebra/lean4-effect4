import Effect4.Laws.Machine.CompletionData

namespace Test.Machine.CompletionDataContract
open Effect4 Effect4.Machine

/--
error: Tactic `aesop` failed, made no progress
Initial goal:
  s : DeferredStore
  k : DeferredKey
  c : DeferredCell
  h : s.cellAt k = some c
  ⊢ s.poll k = some (c.completion (Completion Val Err Defect FiberId Ann))
-/
#guard_msgs (error) in
example (s : DeferredStore) (k : DeferredKey) (c : DeferredCell)
    (h : s.cellAt k = some c) : s.poll k = some c.completion := by
  aesop

#print axioms Effect4.Machine.poll_reads_cell
end Test.Machine.CompletionDataContract
