import Effect4.Laws.Modules.Semaphore.Model

/-! Finite controls for a proposed reuse of Semaphore's model in PartitionedSemaphore.
Latest host observations appear in host-waits.ts. These guards establish no module law. -/

open Effect4.Semaphore.Model

-- A waiter needing two permits does not reserve the free one in this model.
#guard let occupied := (take (initial 2) 0 1).1
       let waiting := (take occupied 1 2).1
       free waiting = 1

-- A visit selects A1 before B1, unlike latest's first per-key release round.
#guard let occupied := (take (initial 3) 0 3).1
       let a1 := (take occupied 1 2).1
       let a2 := (take a1 2 1).1
       let b1 := (take a2 3 1).1
       let released := (release b1 2).1
       ((visit released 0).2.map Waiter.id) = some 1

#eval "Existing Semaphore keeps one free permit; its first visit selects A1."
