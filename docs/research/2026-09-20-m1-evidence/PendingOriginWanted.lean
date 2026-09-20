def M1Origin.pendingOk_make (id : FiberId) (c : NCode) (flag : Bool) (budget : Nat × Bool) (ctx : Ctx)
    (origin : Origin := .root) :
    ProofGraph.Obligation (PendingOk (RunFiber.make id c flag budget ctx origin : FRun)) := ⟨⟩
#proof_wanted M1Origin.pendingOk_make

