def M1Origin.withFiberOf_forkLayer (q : Point) (m : MemoMapId) (scope : Nat) :
    ProofGraph.Obligation ((interpOf root).withFiberOf (.forkLayer q m scope) =
      some (.fork (resolveLayer root q m scope) ⟨true, true, .inherit⟩ q.path)) := ⟨⟩
#proof_wanted M1Origin.withFiberOf_forkLayer

