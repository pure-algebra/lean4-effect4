-- Proposed F forward goals; translation-simulation, rows-block-host/R6.
-- Consumers: CompilesBlk and hosted/session agreement. No progress claim.
@[semantics "translation-simulation" (requirement := R6)]
proof_goal externalValue_data {ty : Ty} (hty : ∀ t, ty ≠ .handle t) {alloc : List String}
    {value : Val} {av : List String × Val} (hv : externalValue ty alloc value = some av) :
    av = (alloc, value)

@[semantics "translation-simulation" (requirement := R6)]
proof_goal prepareExternalAnswer_data {j : Nat} (hrow : dataRow table j = true) (v : Val)
    (w : List Nat) (ex : ExitV) (s : Stores) :
    prepareExternalAnswer table (some (Prim.async (EffName.external (.external j) v w) false none))
      (.ofExit ex) s = (s, Prim.ofExit ex)

@[semantics "translation-simulation" (requirement := R6)]
proof_goal RunsTo.pre {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {K : List NCode} {i : Bool} {c : Nat} {fr fr₁ : NFiber} {s s₁ : Stores} {r r₁ : σ}
    {ctx ctx₁ postCtx : Ctx} (h : ReachesC host root c fr s r fr₁ s₁ r₁ ctx ctx₁) :
    ∀ {o : Option (ExitV × (Stores × σ))},
      RunsTo host root K i fr₁ s₁ r₁ o ctx₁ postCtx → RunsTo host root K i fr s r o ctx postCtx

@[semantics "translation-simulation" (requirement := R6)]
proof_goal RunsTo.frontier {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {K K' : List NCode} {i i' : Bool} {fr : NFiber} {s : Stores} {r : σ}
    {ctx postCtx postCtx' : Ctx}
    (h : RunsTo host root K i fr s r none ctx postCtx) :
    RunsTo host root K' i' fr s r none ctx postCtx'

@[semantics "translation-simulation" (requirement := R6)]
proof_goal Diverges.pre {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {c : Nat} {fr fr₁ : NFiber} {s s₁ : Stores} {r r₁ : σ} {ctx ctx₁ : Ctx}
    (hd : Diverges host root fr₁ s₁ r₁ ctx₁)
    (h : ReachesC host root c fr s r fr₁ s₁ r₁ ctx ctx₁) : Diverges host root fr s r ctx

@[semantics "translation-simulation" (requirement := R6)]
proof_goal RunsToD.pre {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {K : List NCode} {i : Bool} {c : Nat} {fr fr₁ : NFiber} {s s₁ : Stores} {r r₁ : σ}
    {ctx ctx₁ postCtx : Ctx} (h : ReachesC host root c fr s r fr₁ s₁ r₁ ctx ctx₁)
    {o : Option (ExitV × (Stores × σ))} :
    RunsToD host root K i fr₁ s₁ r₁ o ctx₁ postCtx → RunsToD host root K i fr s r o ctx postCtx

@[semantics "translation-simulation" (requirement := R6)]
proof_goal RunsToD.frontier {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {K K' : List NCode} {i i' : Bool} {fr : NFiber} {s : Stores} {r : σ}
    {ctx postCtx postCtx' : Ctx}
    (h : RunsToD host root K i fr s r none ctx postCtx) :
    RunsToD host root K' i' fr s r none ctx postCtx'

@[semantics "translation-simulation" (requirement := R6)]
proof_goal RunsToD.of_zero {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root e : NativeEff}
    {p : Point} {K : List NCode} {i : Bool} {s : Stores} {r : σ} {o : Option (ExitV × (Stores × σ))}
    {ctx postCtx : Ctx} (hf : p.fuel = 0) :
    RunsToD host root K i (fiberOf (compileEff e p) K i) s r o ctx postCtx

@[semantics "translation-simulation" (requirement := R6)]
proof_goal hostRun_of_asExit {σ : Type} (host : Effects.Comodel (RowSig table) σ) (b : NativeEff)
    (q : Point) (s : Stores) (r : σ) {ex : ExitV} (hpl : StraightRows table b = true)
    (h : (compileEff b q).asExit? = some ex) : hostRun host b q.env s r = some (ex, (s, r))

@[semantics "translation-simulation" (requirement := R6)]
proof_goal hostAnswer_call {σ : Type} (host : Effects.Comodel (RowSig table) σ) {j : Nat}
    (hj : j < table.length) (v : Val) (w : List Nat) (r : σ) :
    hostAnswer host (Prim.async (EffName.external (.external j) v w) false none) r =
      host.answer ⟨⟨j, hj⟩, v⟩ r

@[semantics "translation-simulation" (requirement := R6)]
proof_goal eq_external_of_index {op : NativeOp} {j : Nat} (h : externalIndex? op = some j) :
    op = .external j

@[semantics "translation-simulation" (requirement := R6)]
proof_goal ne_external_of_index {op : NativeOp} (h : externalIndex? op = none) : ∀ j, op ≠ .external j

@[semantics "translation-simulation" (requirement := R6)]
proof_goal straight_of_performRows {table : RowTable} {op : NativeOp} {r : Term}
    (h : StraightRows table (.perform op r) = true) (hop : ∀ i, op ≠ .external i) :
    Straight (.perform op r) = true

@[semantics "translation-simulation" (requirement := R6)]
proof_goal compilesD_succeed {σ : Type} (host : Effects.Comodel (RowSig table) σ) (root : NativeEff)
    (v : Term) : CompilesD host root (.succeed v)

@[semantics "translation-simulation" (requirement := R6)]
proof_goal compilesD_fail {σ : Type} (host : Effects.Comodel (RowSig table) σ) (root : NativeEff)
    (e : Term) : CompilesD host root (.fail e)

@[semantics "translation-simulation" (requirement := R6)]
proof_goal compilesD_failCause {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (c : CauseTerm) : CompilesD host root (.failCause c)

@[semantics "translation-simulation" (requirement := R6)]
proof_goal compilesD_sync {σ : Type} (host : Effects.Comodel (RowSig table) σ) (root : NativeEff)
    (t : Term) : CompilesD host root (.sync t)

@[semantics "translation-simulation" (requirement := R6)]
proof_goal compilesD_perform {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) {op : NativeOp} {q : Term} (hpl : StraightRows table (.perform op q) = true) :
    CompilesD host root (.perform op q)

