import Effect4.Laws.Program.Agreement.BlockPlain
import Effect4.Laws.Program.Agreement.LoopCalls
import Effect4.Laws.Program.BlockMeaning
import Effect4.Laws.Program.FragmentBlock
import Effect4.Laws.Program.ParamRows
import Effect4.Laws.Auto.Semantics

/-!
# The forward agreement for definition blocks

Concept: translation-simulation. Claim: rows-block-host, a simulation serving R6.
The local run follows the block meaning at the empty context under every host.
Compile exhaustion remains a live frontier. These proofs establish no scheduler progress.
-/

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

/-- Step of rows-block-host/R6; consumer: `compilesBlk` at an invocation.
A parameter's cut bound weakens without changing its tree or captured site. -/
theorem ParamsAgree.mono {σ : Type} {host : Effects.Comodel (RowSig table) σ}
    {root : NativeEff} {k l : Nat} (hkl : k ≤ l)
    {params : List (ParamTreeB table)} {stack : List (List ArgSite)}
    (h : ParamsAgree host root l params stack) : ParamsAgree host root k params stack := by
  cases stack with
  | nil => exact h
  | cons top rest =>
    refine ⟨h.1, ?_⟩
    intro j f site hf hsite w q K i s r hp he hparams
    exact RunsToDO.mono hkl (h.2 j f site hf hsite w q K i s r hp he hparams)

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

/-- Step of rows-block-host/R6; consumer: `defBodyPath_body`.
The body spine's selected entry has its structural address. No execution claim. -/
private theorem bodySpine_at : ∀ (bodies : Effs NativeOp) (j : Nat) (body : NativeEff),
    bodies.toList[j]? = some body →
    Node.at_ (Node.effs bodies) (List.replicate j 1 ++ [0]) = some (Node.eff body)
  | .nil, j, body, h => by
    simp only [Effs.toList, List.getElem?_nil] at h
    cases h
  | .cons head tail, 0, body, h => by
    simp only [Effs.toList, List.getElem?_cons_zero, Option.some.injEq] at h
    subst body
    rfl
  | .cons head tail, j + 1, body, h => by
    simp only [Effs.toList, List.getElem?_cons_succ] at h
    simpa only [List.replicate_succ, List.cons_append, Node.at_, Node.child,
      Option.bind_some] using bodySpine_at tail j body h

/-- Step of `rows-block-host`, R6. Consumer: `compilesBlk` at a definition hop.
Reach: a leading block's actual body lookup. No typing or progress claim. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem defBodyPath_body {root : NativeEff} {j : Nat} {path : List Nat} {body : NativeEff}
    (hpath : defBodyPath root j = some path) (hbody : (bodiesOf root)[j]? = some body) :
    Node.at_ (Node.eff root) path = some (Node.eff body) := by
  cases root <;> simp only [defBodyPath, reduceCtorEq] at hpath
  rename_i declarations bodies main layers
  split at hpath
  · simp only [Option.some.injEq] at hpath
    subst path
    change bodies.toList[j]? = some body at hbody
    simpa only [List.cons_append, Node.at_, Node.child, Option.bind_some] using bodySpine_at bodies j body hbody
  · cases hpath

/-- Step of rows-block-host/R6; consumer: `argSitesAt_body`.
Every argument site retains its body's address and its captured environment. -/
private theorem argSites_spine (root : NativeEff) (env : List Val) :
    ∀ (args : Effs NativeOp) (path : List Nat) (j : Nat) (arg : NativeEff) (site : ArgSite),
      Node.at_ (Node.eff root) path = some (Node.effs args) →
      args.toList[j]? = some arg → (argSitesAt path env args)[j]? = some site →
      Node.at_ (Node.eff root) site.path = some (Node.eff arg) ∧ site.env = env
  | .nil, path, j, arg, site, hat, harg, hsite => by
    simp only [Effs.toList, List.getElem?_nil] at harg
    cases harg
  | .cons head tail, path, 0, arg, site, hat, harg, hsite => by
    simp only [Effs.toList, List.getElem?_cons_zero, Option.some.injEq] at harg
    simp only [argSitesAt, List.getElem?_cons_zero, Option.some.injEq] at hsite
    subst arg
    subst site
    refine ⟨?_, rfl⟩
    rw [Node.at_append, hat]
    rfl
  | .cons head tail, path, j + 1, arg, site, hat, harg, hsite => by
    simp only [Effs.toList, List.getElem?_cons_succ] at harg
    simp only [argSitesAt, List.getElem?_cons_succ] at hsite
    apply argSites_spine root env tail (path ++ [1]) j arg site _ harg hsite
    rw [Node.at_append, hat]
    rfl

/-- Step of `rows-block-host`, R6. Consumer: `compilesBlk` at an invocation.
Reach: actual argument positions and captured environments. No execution claim. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem argSitesAt_body {root : NativeEff} {p : Point} {index j : Nat} {request : Term}
    {args : Effs NativeOp} {arg : NativeEff} {site : ArgSite}
    (hat : Node.at_ (Node.eff root) p.path = some (Node.eff (.invoke index request args)))
    (harg : args.toList[j]? = some arg)
    (hsite : (argSitesAt (p.path ++ [0]) p.env args)[j]? = some site) :
    Node.at_ (Node.eff root) site.path = some (Node.eff arg) ∧ site.env = p.env := by
  apply argSites_spine root p.env args (p.path ++ [0]) j arg site _ harg hsite
  rw [Node.at_append, hat]
  rfl

/-- Step of rows-block-host/R6; consumer: `compilesBlk` on a body without block calls.
The existing loop agreement applies through block-meaning conservativity.
This proof rests on `denoteBlockB_loopedDataRows` while that goal remains open. -/
theorem compilesBlk_of_loopedDataRows {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) (e : NativeEff) (he : LoopedDataRows table e = true) :
    CompilesBlk host root k e := by
  intro p K i s r params hat _
  rw [denoteBlockB_loopedDataRows table (bodiesOf root) k params e emptyCtx p.env he]
  exact compilesBO host root k e he p K i s r hat

/-- Step of rows-block-host/R6; consumer: `compilesBlk` at suspension.
The one local suspension step preserves the child's detailed observation. -/
theorem compilesBlk_suspend {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {b : NativeEff} (hb : CompilesBlk host root k b) :
    CompilesBlk host root k (.suspend b) := by
  intro p K i s r params hat hagree
  cases hfu : p.fuel with
  | zero => exact RunsToDO.of_zero hfu
  | succ fuel =>
    have hb' : Node.at_ (Node.eff root) ({ p with completed := [] }.child 0).path =
        some (Node.eff b) := at_child hat 0
    have ih := hb ({ p with completed := [] }.child 0) K i s r params hb' hagree
    rw [Point.child_env] at ih
    rw [compileEff_suspend b hfu]
    have hs := step_suspend root (EffThunk.body p) K i s
    simp only [interpAt] at hs
    rw [suspendBodyAt_suspend (q := { p with completed := [] }) hfu hat, resolve_of_at hb'] at hs
    have same : denoteBlockB table (bodiesOf root) k params (.suspend b) emptyCtx p.env =
        denoteBlockB table (bodiesOf root) k params b emptyCtx p.env := by
      cases k <;> rfl
    rw [same]
    exact RunsToDO.pre (ReachesC.step (host := host) hs rfl r) ih

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
theorem compilesBlk_root {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (hroot : BlockRows table root = true) (k : Nat) (p : Point)
    (K : List NCode) (i : Bool) (s : Stores) (r : σ)
    (hp : p.path = []) (hpar : p.params = []) :
    RunsToDO host root K i k (fiberOf (compileEff root p) K i) s r
      (runRowsO host (denoteBlockB table (bodiesOf root) k [] root emptyCtx p.env) s r) := by
  cases root <;> simp only [BlockRows, Bool.false_eq_true] at hroot
  rename_i declarations bodies main layers
  cases layers <;> simp only [Bool.false_eq_true] at hroot
  have hmain : BodyRows table main = true := (Bool.and_eq_true_iff.mp hroot).2
  cases hf : p.fuel with
  | zero => exact RunsToDO.of_zero hf
  | succ fuel =>
    rw [compileEff_defs declarations bodies main .nil hf]
    have hat : Node.at_ (Node.eff (.defs declarations bodies main .nil)) (p.child 1).path =
        some (Node.eff main) := by
      simp only [Point.child, hp, List.nil_append, Node.at_, Node.child, Option.bind_some]
    have hagree : ParamsAgree host (.defs declarations bodies main .nil) k [] (p.child 1).params := by
      change ParamsAgree host (.defs declarations bodies main .nil) k [] p.params
      rw [hpar]
      rfl
    have result := compilesBlk host (.defs declarations bodies main .nil) hroot k main hmain
      (p.child 1) K i s r [] hat hagree
    have same : denoteBlockB table (bodiesOf (.defs declarations bodies main .nil)) k []
        (.defs declarations bodies main .nil) emptyCtx p.env =
        denoteBlockB table (bodiesOf (.defs declarations bodies main .nil)) k [] main emptyCtx
          (p.child 1).env := by
      cases k <;> rfl
    rw [same]
    exact result
end Effect4.Program.Agreement
