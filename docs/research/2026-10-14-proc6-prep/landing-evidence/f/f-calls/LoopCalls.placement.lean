-- Proposed F forward goals; translation-simulation, rows-block-host/R6.
-- Consumers: CompilesBlk and hosted/session agreement. No progress claim.
@[semantics "translation-simulation" (requirement := R6)]
proof_goal hostRunB_of_straightRows {σ : Type} (host : Effects.Comodel (RowSig table) σ) (k : Nat)
    (e : NativeEff) (env : List Val) (s : Stores) (st : σ) (h : StraightRows table e = true) :
    hostRunB host k e env s st = (hostRun host e env s st).map fun x => (some x.1, x.2)

@[semantics "translation-simulation" (requirement := R6)]
proof_goal straightRows_of_asExit : ∀ (b : NativeEff) (q : Point) {exit : ExitV},
    LoopedDataRows table b = true → (compileEff b q).asExit? = some exit →
      StraightRows table b = true

@[semantics "translation-simulation" (requirement := R6)]
proof_goal hostRunB_of_asExit {σ : Type} (host : Effects.Comodel (RowSig table) σ) (k : Nat)
    (b : NativeEff) (q : Point) (s : Stores) (r : σ) {ex : ExitV}
    (hl : LoopedDataRows table b = true) (h : (compileEff b q).asExit? = some ex) :
    hostRunB host k b q.env s r = some (some ex, (s, r))

@[semantics "translation-simulation" (requirement := R6)]
proof_goal RunsToDO.pre {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {K : List NCode} {i : Bool} {k c : Nat} {fr fr₁ : NFiber} {s s₁ : Stores} {r r₁ : σ}
    {ctx ctx₁ postCtx : Ctx} (h : ReachesC host root c fr s r fr₁ s₁ r₁ ctx ctx₁) :
    ∀ {o : RowsEnd (Option ExitV) σ},
      RunsToDO host root K i k fr₁ s₁ r₁ o ctx₁ postCtx → RunsToDO host root K i k fr s r o ctx postCtx

@[semantics "translation-simulation" (requirement := R6)]
proof_goal RunsToDO.of_zero {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root e : NativeEff}
    {p : Point} {K : List NCode} {i : Bool} {k : Nat} {s : Stores} {r : σ}
    {ctx postCtx : Ctx} (hf : p.fuel = 0) :
    ∀ {o : RowsEnd (Option ExitV) σ},
      RunsToDO host root K i k (fiberOf (compileEff e p) K i) s r o ctx postCtx

@[semantics "translation-simulation" (requirement := R6)]
proof_goal RunsToDO.of_diverges {σ : Type} {host : Effects.Comodel (RowSig table) σ}
    {root : NativeEff} {K : List NCode} {i : Bool} {k : Nat} {fr : NFiber} {s : Stores} {r : σ}
    {ctx postCtx : Ctx} (hd : Diverges host root fr s r ctx) :
    ∀ {o : RowsEnd (Option ExitV) σ}, RunsToDO host root K i k fr s r o ctx postCtx

@[semantics "translation-simulation" (requirement := R6)]
proof_goal RunsToDO.mono {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {K : List NCode} {i : Bool} {j j' : Nat} {fr : NFiber} {s : Stores} {r : σ}
    {ctx postCtx : Ctx} (hj : j ≤ j') :
    ∀ {o : RowsEnd (Option ExitV) σ},
      RunsToDO host root K i j' fr s r o ctx postCtx → RunsToDO host root K i j fr s r o ctx postCtx

@[semantics "translation-simulation" (requirement := R6)]
proof_goal RunsToDO.pre_add {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {K : List NCode} {i : Bool} {j c : Nat} {fr fr₁ : NFiber} {s s₁ : Stores} {r r₁ : σ}
    {ctx ctx₁ postCtx : Ctx} (h : ReachesC host root c fr s r fr₁ s₁ r₁ ctx ctx₁) :
    ∀ {o : RowsEnd (Option ExitV) σ},
      RunsToDO host root K i j fr₁ s₁ r₁ o ctx₁ postCtx →
      RunsToDO host root K i (j + c) fr s r o ctx postCtx

@[semantics "translation-simulation" (requirement := R6)]
proof_goal RunsToDO.project {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {K : List NCode} {i : Bool} {k : Nat} {fr : NFiber} {s : Stores} {r : σ} {ctx postCtx : Ctx} :
    ∀ {o : RowsEnd (Option ExitV) σ},
      RunsToDO host root K i k fr s r o ctx postCtx → RunsToDB host root K i k fr s r o.project ctx postCtx

@[semantics "translation-simulation" (requirement := R6)]
proof_goal runRowsO_thenOpt {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (p : Effects.Program (RowsSig table) (Option ExitV))
    (f : ExitV → Effects.Program (RowsSig table) (Option ExitV)) (s : Stores) (st : σ) :
    runRowsO host (thenOpt p f) s st =
      (runRowsO host p s st).andThen fun o s st => match o with
        | none => .done none s st
        | some ex => runRowsO host (f ex) s st

@[semantics "translation-simulation" (requirement := R6)]
proof_goal runRowsOB_thenOpt {σ : Type} (host : Effects.Comodel (RowSig table) σ) (k : Nat)
    {e : NativeEff} {env : List Val} (a : NativeEff)
    (F : ExitV → Effects.Program (RowsSig table) (Option ExitV)) (s : Stores) (st : σ)
    (h : denoteRowsB table k e env = thenOpt (denoteRowsB table k a env) F) :
    runRowsO host (denoteRowsB table k e env) s st =
      (runRowsO host (denoteRowsB table k a env) s st).andThen fun o s st => match o with
        | none => .done none s st
        | some ex => runRowsO host (F ex) s st

@[semantics "translation-simulation" (requirement := R6)]
proof_goal runRowsO_iter_succ {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (f : Val → Effects.Program (RowsSig table) (Option ExitV ⊕ Val)) (j : Nat) (c : Val)
    (s : Stores) (r : σ) :
    runRowsO host (Option.join <$> iter f (j + 1) c) s r =
      (runRowsO host (f c) s r).andThen fun x s r => match x with
        | .inl y => .done y s r
        | .inr c' => runRowsO host (Option.join <$> iter f j c') s r

@[semantics "translation-simulation" (requirement := R6)]
proof_goal runRowsO_of_runRowsH {σ : Type} (host : Effects.Comodel (RowSig table) σ) {A : Type}
    {p : Effects.Program (RowsSig table) A} {s s' : Stores} {st st' : σ} {a : A}
    (h : runRowsH host p s st = some (a, (s', st'))) : runRowsO host p s st = .done a s' st'

@[semantics "translation-simulation" (requirement := R6)]
proof_goal runRowsO_of_asExit {σ : Type} (host : Effects.Comodel (RowSig table) σ) (k : Nat)
    (b : NativeEff) (q : Point) (s : Stores) (r : σ) {ex : ExitV}
    (hl : LoopedDataRows table b = true) (h : (compileEff b q).asExit? = some ex) :
    runRowsO host (denoteRowsB table k b q.env) s r = .done (some ex) s r

@[semantics "translation-simulation" (requirement := R6)]
proof_goal compilesBO_of_finishes {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {e : NativeEff} (h : StraightRows table e = true)
    (hc : CompilesD host root e)
    (hfin : ∀ (env : List Val) (s : Stores) (r : σ), ∃ x, hostRun host e env s r = some x) :
    CompilesBO host root k e

@[semantics "translation-simulation" (requirement := R6)]
proof_goal finishes_of_pure {σ : Type} (host : Effects.Comodel (RowSig table) σ) {e : NativeEff}
    (h : ∀ env, ∃ ex, denoteRows table e env = Effects.Program.pure ex) :
    ∀ (env : List Val) (s : Stores) (r : σ), ∃ x, hostRun host e env s r = some x

@[semantics "translation-simulation" (requirement := R6)]
proof_goal compilesBO_perform {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {op : NativeOp} {q : Term}
    (h : StraightRows table (.perform op q) = true) :
    CompilesBO host root k (.perform op q)

@[semantics "translation-simulation" (requirement := R6)]
proof_goal loop_reachesCO {σ : Type} (host : Effects.Comodel (RowSig table) σ) (root : NativeEff)
    (k : Nat) (q : Point) (hq : loopPoint q = q) {cty : Option Ty} {init test step result : Term}
    {body : NativeEff}
    (h : Node.at_ (Node.eff root) q.path =
      some (Node.eff (.iterate cty init test step result body)))
    (K : List NCode) (i : Bool) (ctx : Ctx) (hbody : CompilesBO host root k body) :
    ∀ (j : Nat), j ≤ k → ∀ (c : Val) (s : Stores) (r : σ),
      RunsToDO host root K i j (enter q K i (loopNextAt root q c)) s r
        (runRowsO host (Option.join <$>
          iter (loopStep (denoteRowsB table k body) q.env test step result) j c) s r) ctx ctx

@[semantics "translation-simulation" (requirement := R6)]
proof_goal compilesBO_suspend {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {b : NativeEff} (hb : CompilesBO host root k b) :
    CompilesBO host root k (.suspend b)

@[semantics "translation-simulation" (requirement := R6)]
proof_goal compilesBO_bind {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {a b : NativeEff} (ha : CompilesBO host root k a)
    (hb : CompilesBO host root k b) : CompilesBO host root k (.bind a b)

@[semantics "translation-simulation" (requirement := R6)]
proof_goal compilesBO_select {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {t : Term} {d : Decision} {a b : NativeEff}
    (ha : CompilesBO host root k a) (hb : CompilesBO host root k b) :
    CompilesBO host root k (.select t d a b)

@[semantics "translation-simulation" (requirement := R6)]
proof_goal compilesBO_exit {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {b : NativeEff} (hfrag : LoopedDataRows table b = true)
    (hb : CompilesBO host root k b) : CompilesBO host root k (.exit b)

@[semantics "translation-simulation" (requirement := R6)]
proof_goal compilesBO_catchCause {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {b h : NativeEff} (hb : CompilesBO host root k b)
    (hh : CompilesBO host root k h) : CompilesBO host root k (.catchCause b h)

@[semantics "translation-simulation" (requirement := R6)]
proof_goal compilesBO_catchIf {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {test : Term} {b h : NativeEff} (hb : CompilesBO host root k b)
    (hh : CompilesBO host root k h) : CompilesBO host root k (.catchIf test b h)

@[semantics "translation-simulation" (requirement := R6)]
proof_goal compilesBO_matchCause {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {b v c : NativeEff} (hb : CompilesBO host root k b)
    (hv : CompilesBO host root k v) (hc : CompilesBO host root k c) :
    CompilesBO host root k (.matchCause b v c)

@[semantics "translation-simulation" (requirement := R6)]
proof_goal compilesBO_onExit {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {b f : NativeEff} (hb : CompilesBO host root k b)
    (hf : CompilesBO host root k f) : CompilesBO host root k (.onExit b f)

@[semantics "translation-simulation" (requirement := R6)]
proof_goal compilesBO_iterate {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {cty : Option Ty} {init test step result : Term}
    {body : NativeEff} (hb : CompilesBO host root k body) :
    CompilesBO host root k (.iterate cty init test step result body)

@[semantics "translation-simulation" (requirement := R6)]
proof_goal compilesBO {σ : Type} (host : Effects.Comodel (RowSig table) σ) (root : NativeEff)
    (k : Nat) : ∀ (e : NativeEff), LoopedDataRows table e = true → CompilesBO host root k e

@[semantics "translation-simulation" (requirement := R6)]
proof_goal localRunC_compileBO {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) (e : NativeEff) (p : Point) (K : List NCode) (i : Bool)
    (s : Stores) (r : σ) (hfrag : LoopedDataRows table e = true)
    (hat : Node.at_ (Node.eff root) p.path = some (Node.eff e)) (ctx : Ctx

@[semantics "translation-simulation" (requirement := R6)]
proof_goal localRunC_compileB {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) (e : NativeEff) (p : Point) (K : List NCode) (i : Bool)
    (s : Stores) (r : σ) (hfrag : LoopedDataRows table e = true)
    (hat : Node.at_ (Node.eff root) p.path = some (Node.eff e)) (ctx : Ctx

@[semantics "translation-simulation" (requirement := R6)]
proof_goal loopedDataRows_of_straightRows :
    ∀ (e : NativeEff), StraightRows table e = true → LoopedDataRows table e = true

@[semantics "translation-simulation" (requirement := R6)]
proof_goal localRunC_compile {σ : Type} (host : Effects.Comodel (RowSig table) σ) (root : NativeEff) :
    ∀ (e : NativeEff) (p : Point) (K : List NCode) (i : Bool) (s : Stores) (r : σ) (ctx : Ctx),
      StraightRows table e = true → Node.at_ (Node.eff root) p.path = some (Node.eff e) →
      RunsToD host root K i (fiberOf (compileEff e p) K i) s r (hostRun host e p.env s r) ctx ctx

