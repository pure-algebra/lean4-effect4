import Effect4.Laws.Program.Agreement.BlockPlain
import Effect4.Laws.Program.Agreement.LoopCalls
import Effect4.Laws.Program.BlockMeaning
import Effect4.Laws.Program.FragmentBlock
import Effect4.Laws.Program.ParamRows
import Effect4.Laws.Auto.Semantics

set_option autoImplicit false
namespace Effect4.Program.Agreement
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote
variable {table : RowTable}

/-- A passed tree agrees with its argument site at the empty context.
Consumer: `CompilesBlk`. Reach: every host, request, continuation, and completed view.
This relation establishes no scheduler progress. -/
def ParamsAgree {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) : List (ParamTreeB table) → List (List ArgSite) → Prop
  | params, [] => params = []
  | params, top :: rest => params.length = top.length ∧
      ∀ (j : Nat) (f : ParamTreeB table) (site : ArgSite), params[j]? = some f → top[j]? = some site →
        ∀ (w : Val) (q : Point) (K : List NCode) (i : Bool) (s : Stores) (r : σ),
          q.path = site.path → q.env = site.env ++ [w] → q.params = rest →
          RunsToDO host root K i k (fiberOf (resolve root q) K i) s r
            (runRowsO host (f emptyCtx w) s r)

/-- A body's compile reaches its budgeted observation under related parameters.
Consumer: `compilesBlk_root`. Compile exhaustion remains a live frontier. -/
def CompilesBlk {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) (e : NativeEff) : Prop :=
  ∀ (p : Point) (K : List NCode) (i : Bool) (s : Stores) (r : σ)
      (params : List (ParamTreeB table)),
    Node.at_ (Node.eff root) p.path = some (Node.eff e) →
    ParamsAgree host root k params p.params →
    RunsToDO host root K i k (fiberOf (compileEff e p) K i) s r
      (runRowsO host (denoteBlockB table (bodiesOf root) k params e emptyCtx p.env) s r)

/-- Step of `rows-block-host`, R6. Consumer: `compilesBlk` at a definition hop.
Reach: a leading block's actual body lookup. No typing or progress claim. -/
@[semantics "translation-simulation" (requirement := R6)]
proof_goal defBodyPath_body {root : NativeEff} {j : Nat} {path : List Nat} {body : NativeEff}
    (hpath : defBodyPath root j = some path) (hbody : (bodiesOf root)[j]? = some body) :
    Node.at_ (Node.eff root) path = some (Node.eff body)

/-- Step of `rows-block-host`, R6. Consumer: `compilesBlk` at an invocation.
Reach: actual argument positions and captured environments. No execution claim. -/
@[semantics "translation-simulation" (requirement := R6)]
proof_goal argSitesAt_body {root : NativeEff} {p : Point} {index j : Nat} {request : Term}
    {args : Effs NativeOp} {arg : NativeEff} {site : ArgSite}
    (hat : Node.at_ (Node.eff root) p.path = some (Node.eff (.invoke index request args)))
    (harg : args.toList[j]? = some arg)
    (hsite : (argSitesAt (p.path ++ [0]) p.env args)[j]? = some site) :
    Node.at_ (Node.eff root) site.path = some (Node.eff arg) ∧ site.env = p.env

/-- Step of `rows-block-host`, R6. Consumer: `compilesBlk_root`.
Reach: `BodyRows` inside a `BlockRows` root at every meaning budget.
The local relation uses empty context. No machine progress or host conformance follows. -/
@[semantics "translation-simulation" (requirement := R6)]
proof_goal compilesBlk {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (hroot : BlockRows table root = true) :
    ∀ k e, BodyRows table e = true → CompilesBlk host root k e

/-- Step of `rows-block-host`, R6. Consumer: `localRunC_to_blockB`.
Reach: a block root at the empty parameter stack, including exhausted compile fuel.
This forward relation establishes no progress. -/
@[semantics "translation-simulation" (requirement := R6)]
proof_goal compilesBlk_root {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (hroot : BlockRows table root = true) (k : Nat) (p : Point)
    (K : List NCode) (i : Bool) (s : Stores) (r : σ)
    (hp : p.path = []) (hpar : p.params = []) :
    RunsToDO host root K i k (fiberOf (compileEff root p) K i) s r
      (runRowsO host (denoteBlockB table (bodiesOf root) k [] root emptyCtx p.env) s r)
end Effect4.Program.Agreement
