def M1Origin.make_keys_subset (id : FiberId) (program : Prim ν σ Val Err Defect FiberId Ann) (flag : Bool)
    (budget : Nat × Bool) (ctx : Ctx) (origin : Origin := .root) : ProofGraph.Obligation ((RunFiber.make id program flag budget ctx origin : RunFiber ν σ Val Err Defect FiberId Ann Ctx).keys nk sk ⊆
      primKeys nk sk program ++ ctx.keys) := ⟨⟩
#proof_wanted M1Origin.make_keys_subset

def M1Origin.spawnChild_keys_subset (interp : RunInterp ν σ Val Err Defect FiberId Ann Ctx Stores)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (parent : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (program : Prim ν σ Val Err Defect FiberId Ann)
    (options : Supervision.ForkOptions) (site : List Nat := []) : ProofGraph.Obligation ((spawnChild interp m parent program options site).keys nk sk ⊆
      Handle.fiber parent.id :: primKeys nk sk program ++ parent.context.keys) := ⟨⟩
#proof_wanted M1Origin.spawnChild_keys_subset

def M1Origin.spawn_minted (interp : RunInterp ν σ Val Err Defect FiberId Ann Ctx Stores)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (parent : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (program : Prim ν σ Val Err Defect FiberId Ann)
    (options : Supervision.ForkOptions)
    (_hm : MintedIn m (Handle.fiber parent.id :: m.keys nk sk ++ parent.keys nk sk ++ primKeys nk sk program)) (site : List Nat := []) : ProofGraph.Obligation (m.world.le (spawn interp m parent program options site).1.world ∧
      MintedIn (spawn interp m parent program options site).1
        (Handle.fiber (spawn interp m parent program options site).2.2 ::
          (spawn interp m parent program options site).1.keys nk sk ++
          (spawn interp m parent program options site).2.1.keys nk sk)) := ⟨⟩
#proof_wanted M1Origin.spawn_minted

def M1Origin.launchEntrant_minted (interp : RunInterp ν σ Val Err Defect FiberId Ann Ctx Stores) (raceId : Nat)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (host : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (program : Prim ν σ Val Err Defect FiberId Ann)
    (_hm : MintedIn m (Handle.fiber host.id :: m.keys nk sk ++ host.keys nk sk ++ primKeys nk sk program)) (site : List Nat := []) : ProofGraph.Obligation (m.world.le (launchEntrant interp raceId m host program site).1.world ∧
      MintedIn (launchEntrant interp raceId m host program site).1
        (Handle.fiber (launchEntrant interp raceId m host program site).2 ::
          (launchEntrant interp raceId m host program site).1.keys nk sk)) := ⟨⟩
#proof_wanted M1Origin.launchEntrant_minted

def M1Origin.fork_arm_minted (_hb : KeyBounded nk sk interp ambient)
    (m M : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores) (_hMw : M.world = m.world)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx)
    (program : Prim ν σ Val Err Defect FiberId Ann) (options : Supervision.ForkOptions)
    {site : List Nat}
    (S : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores × RunFiber ν σ Val Err Defect FiberId Ann Ctx × FiberId)
    (T : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores × RunFiber ν σ Val Err Defect FiberId Ann Ctx ×
      List (Cmd ν σ Val Err Defect FiberId Ann))
    (_hS : spawn interp M f program options site = S) (_hT : start S.1 S.2.1 S.2.2 options.startImmediately = T)
    (_hm : MintedIn M (Handle.fiber f.id :: M.keys nk sk ++ f.keys nk sk ++ primKeys nk sk program))
    (it : Iter ν σ Val Err Defect FiberId Ann Ctx Stores) (_hmach : it.machine = T.1)
    (_hfib : it.fiber.keys nk sk ⊆ T.2.1.keys nk sk ++ (interp.fiberValue S.2.2).keys)
    (_hnest : cmdsKeys nk sk it.nested ⊆
      cmdsKeys nk sk T.2.2 ++ [Handle.fiber f.id, Handle.fiber S.2.2])
    (_hout : it.outcome.keys = []) : ProofGraph.Obligation (IterMinted nk sk m it) := ⟨⟩
#proof_wanted M1Origin.fork_arm_minted

def M1Origin.withFiber_fork_minted (_hb : KeyBounded nk sk interp ambient)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (program : Prim ν σ Val Err Defect FiberId Ann) (options : Supervision.ForkOptions)
    {site : List Nat}
    (_hm : MintedIn m (Handle.fiber f.id :: m.keys nk sk ++ f.keys nk sk ++
      (WithFiberAction.fork program options site).keys nk sk)) : ProofGraph.Obligation (IterMinted nk sk m (evaluatePrim.withFiber interp m f yielding (WithFiberAction.fork program options site))) := ⟨⟩
#proof_wanted M1Origin.withFiber_fork_minted

def M1Origin.withFiber_forkIn_minted (_hb : KeyBounded nk sk interp ambient)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (program : Prim ν σ Val Err Defect FiberId Ann) (options : Supervision.ForkOptions) (scope : Nat)
    {site : List Nat}
    (_hm : MintedIn m (Handle.fiber f.id :: m.keys nk sk ++ f.keys nk sk ++
      (WithFiberAction.forkIn program options scope site).keys nk sk)) : ProofGraph.Obligation (IterMinted nk sk m
      (evaluatePrim.withFiber interp m f yielding (WithFiberAction.forkIn program options scope site))) := ⟨⟩
#proof_wanted M1Origin.withFiber_forkIn_minted

def M1Origin.withFiber_forkScoped_minted (_hb : KeyBounded nk sk interp ambient)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (program : Prim ν σ Val Err Defect FiberId Ann) (options : Supervision.ForkOptions)
    {site : List Nat}
    (_hm : MintedIn m (Handle.fiber f.id :: m.keys nk sk ++ f.keys nk sk ++
      (WithFiberAction.forkScoped program options site).keys nk sk)) : ProofGraph.Obligation (IterMinted nk sk m
      (evaluatePrim.withFiber interp m f yielding (WithFiberAction.forkScoped program options site))) := ⟨⟩
#proof_wanted M1Origin.withFiber_forkScoped_minted

def M1Origin.withFiber_raceAll_minted (_hb : KeyBounded nk sk interp ambient)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (entrants : List (Prim ν σ Val Err Defect FiberId Ann))
    {site : Option (List Nat)}
    (_hm : MintedIn m (Handle.fiber f.id :: m.keys nk sk ++ f.keys nk sk ++
      (WithFiberAction.raceAll entrants site).keys nk sk)) : ProofGraph.Obligation (IterMinted nk sk m (evaluatePrim.withFiber interp m f yielding (WithFiberAction.raceAll entrants site))) := ⟨⟩
#proof_wanted M1Origin.withFiber_raceAll_minted

