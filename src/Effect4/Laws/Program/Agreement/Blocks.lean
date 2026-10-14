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

/-- Step of rows-block-host/R6; consumer: the block control arms of `compilesBlk`.
A block tree's sequencing exposes its first detailed observation. -/
private theorem runBlock_thenOpt {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) (params : List (ParamTreeB table))
    {e : NativeEff} {env : List Val} (a : NativeEff)
    (F : ExitV → Effects.Program (RowsSig table) (Option ExitV)) (s : Stores) (st : σ)
    (h : denoteBlockB table (bodiesOf root) k params e emptyCtx env =
      thenOpt (denoteBlockB table (bodiesOf root) k params a emptyCtx env) F) :
    runRowsO host (denoteBlockB table (bodiesOf root) k params e emptyCtx env) s st =
      (runRowsO host (denoteBlockB table (bodiesOf root) k params a emptyCtx env) s st).andThen
        fun o s st => match o with
        | none => .done none s st
        | some ex => runRowsO host (F ex) s st := by
  rw [h]
  exact runRowsO_thenOpt host _ F s st

/-- Step of rows-block-host/R6; consumer: `compilesBlk`.
The bind arm retains its detailed exits, cuts and waits. No machine progress follows. -/
theorem compilesBlk_bind {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {a b : NativeEff} (ha : CompilesBlk host root k a)
    (hb : CompilesBlk host root k b) : CompilesBlk host root k (.bind a b) := by
  intro p K i s r params h hagree
  rcases hfu : p.fuel with _ | n
  · exact RunsToDO.of_zero hfu
  have ha' : Node.at_ (Node.eff root) (p.child 0).path = some (Node.eff a) := at_child h 0
  have hden : denoteBlockB table (bodiesOf root) k params (.bind a b) emptyCtx p.env =
      thenOpt (denoteBlockB table (bodiesOf root) k params a emptyCtx p.env) (fun
      | .success v => denoteBlockB table (bodiesOf root) k params b emptyCtx (p.env ++ [v])
      | .failure cause => pure (some (.failure cause))) := by
    cases k <;> rfl
  rw [compileEff_bind a b hfu, runBlock_thenOpt host root k params a _ s r hden]
  have iha := ha (p.child 0) (Prim.onSuccess (compileEff a (p.child 0)) (EffName.cont p) :: K) i s r params ha' hagree
  rw [Point.child_env] at iha
  have hpush := ReachesC.step (host := host)
    (step_push_onSuccess root (compileEff a (p.child 0)) (EffName.cont p) K i s) rfl r
  rcases hma : runRowsO host (denoteBlockB table (bodiesOf root) k params a emptyCtx p.env) s r with
      ⟨_ | ex, s', r'⟩ | ⟨row, req, s', r'⟩
  rotate_right
  · rw [hma] at iha
    exact RunsToDO.pre hpush iha
  · rw [hma] at iha
    exact RunsToDO.pre hpush iha
  · rw [hma] at iha
    rcases iha with iha | hdiv
    swap
    · exact RunsToDO.of_diverges (hdiv.pre hpush)
    obtain ⟨ca, hra⟩ := iha
    cases ex with
    | success v =>
      have hb' : Node.at_ (Node.eff root) ({ p with completed := [] }.childWith 1 v).path =
          some (Node.eff b) := at_childWith h 1 v
      have ihb := hb ({ p with completed := [] }.childWith 1 v) K i s' r' params hb' hagree
      rw [Point.childWith_env] at ihb
      have hpop := ReachesC.step (host := host)
        (step_success_onSuccess root v (compileEff a (p.child 0)) (EffName.cont p) K i s') rfl r'
      simp only [interpAt] at hpop
      rw [contAOf_cont, resolve_of_at hb'] at hpop
      exact RunsToDO.pre ((hpush.trans hra).trans hpop) ihb
    | failure c =>
      have hpass := ReachesC.same (host := host) s' r' (fun s =>
        step_failure_pass_onSuccess root c (compileEff a (p.child 0)) (EffName.cont p) K i s) rfl rfl
      exact Or.inl ⟨1 + ca + 0, (hpush.trans hra).trans hpass⟩


/-- Step of rows-block-host/R6; consumer: `compilesBlk`.
The select arm retains its detailed exits, cuts and waits. No machine progress follows. -/
theorem compilesBlk_select {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {t : Term} {d : Decision} {a b : NativeEff}
    (ha : CompilesBlk host root k a) (hb : CompilesBlk host root k b) :
    CompilesBlk host root k (.select t d a b) := by
  intro p K i s r params h hagree
  rcases hfu : p.fuel with _ | n
  · exact RunsToDO.of_zero hfu
  rw [compileEff_select t d a b hfu]
  have hs := step_suspend root (EffThunk.body p) K i s
  simp only [interpAt] at hs
  rcases hdec : (evalTerm p.env t).bind d.decide with _ | ⟨first, bound⟩
  · rw [suspendBodyAt_select_bad (q := { p with completed := [] }) hfu h hdec] at hs
    rw [show runRowsO host (denoteBlockB table (bodiesOf root) k params (.select t d a b) emptyCtx p.env) s r =
        .done (some badShapeExit) s r by
      cases k <;> simp only [denoteBlockB, cata_eff, blockAlgB, hdec] <;> rfl]
    rw [badShape_eq] at hs
    exact Or.inl ⟨1, ReachesC.step (host := host) hs rfl r⟩
  · rw [suspendBodyAt_select_of_decide (q := { p with completed := [] }) hfu h hdec] at hs
    cases first with
    | true =>
      rw [show runRowsO host (denoteBlockB table (bodiesOf root) k params (.select t d a b) emptyCtx p.env) s r =
          runRowsO host (denoteBlockB table (bodiesOf root) k params a emptyCtx (p.env ++ bound.toList)) s r by
        cases k <;> simp only [denoteBlockB, cata_eff, blockAlgB, hdec]]
      cases bound with
      | none =>
        have ha' : Node.at_ (Node.eff root) ({ p with completed := [] }.child 0).path =
            some (Node.eff a) := at_child h 0
        have ih := ha ({ p with completed := [] }.child 0) K i s r params ha' hagree
        rw [Point.child_env] at ih
        simp only [Bool.cond_true, Point.childBind] at hs
        rw [resolve_of_at ha'] at hs
        simp only [Option.toList, List.append_nil]
        exact RunsToDO.pre (ReachesC.step (host := host) hs rfl r) ih
      | some v =>
        have ha' : Node.at_ (Node.eff root) ({ p with completed := [] }.childWith 0 v).path =
            some (Node.eff a) := at_childWith h 0 v
        have ih := ha ({ p with completed := [] }.childWith 0 v) K i s r params ha' hagree
        rw [Point.childWith_env] at ih
        simp only [Bool.cond_true, Point.childBind] at hs
        rw [resolve_of_at ha'] at hs
        simp only [Option.toList]
        exact RunsToDO.pre (ReachesC.step (host := host) hs rfl r) ih
    | false =>
      rw [show runRowsO host (denoteBlockB table (bodiesOf root) k params (.select t d a b) emptyCtx p.env) s r =
          runRowsO host (denoteBlockB table (bodiesOf root) k params b emptyCtx (p.env ++ bound.toList)) s r by
        cases k <;> simp only [denoteBlockB, cata_eff, blockAlgB, hdec]]
      cases bound with
      | none =>
        have hb' : Node.at_ (Node.eff root) ({ p with completed := [] }.child 1).path =
            some (Node.eff b) := at_child h 1
        have ih := hb ({ p with completed := [] }.child 1) K i s r params hb' hagree
        rw [Point.child_env] at ih
        simp only [Bool.cond_false, Point.childBind] at hs
        rw [resolve_of_at hb'] at hs
        simp only [Option.toList, List.append_nil]
        exact RunsToDO.pre (ReachesC.step (host := host) hs rfl r) ih
      | some v =>
        have hb' : Node.at_ (Node.eff root) ({ p with completed := [] }.childWith 1 v).path =
            some (Node.eff b) := at_childWith h 1 v
        have ih := hb ({ p with completed := [] }.childWith 1 v) K i s r params hb' hagree
        rw [Point.childWith_env] at ih
        simp only [Bool.cond_false, Point.childBind] at hs
        rw [resolve_of_at hb'] at hs
        simp only [Option.toList]
        exact RunsToDO.pre (ReachesC.step (host := host) hs rfl r) ih


/-- Step of rows-block-host/R6; consumer: `compilesBlk`.
The catchCause arm retains its detailed exits, cuts and waits. No machine progress follows. -/
theorem compilesBlk_catchCause {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {b h : NativeEff} (hb : CompilesBlk host root k b)
    (hh : CompilesBlk host root k h) : CompilesBlk host root k (.catchCause b h) := by
  intro p K i s r params hat hagree
  rcases hfu : p.fuel with _ | n
  · exact RunsToDO.of_zero hfu
  have hb' : Node.at_ (Node.eff root) (p.child 0).path = some (Node.eff b) := at_child hat 0
  have hden : denoteBlockB table (bodiesOf root) k params (.catchCause b h) emptyCtx p.env =
      thenOpt (denoteBlockB table (bodiesOf root) k params b emptyCtx p.env) (fun
      | .success v => pure (some (.success v))
      | .failure cause => denoteBlockB table (bodiesOf root) k params h emptyCtx (p.env ++ [Val.exitErr cause])) := by
    cases k <;> rfl
  rw [compileEff_catchCause b h hfu, runBlock_thenOpt host root k params b _ s r hden]
  have ih := hb (p.child 0) (Prim.onFailure (compileEff b (p.child 0)) (EffName.caught p) :: K) i s r params hb' hagree
  rw [Point.child_env] at ih
  have hpush := ReachesC.step (host := host)
    (step_push_onFailure root (compileEff b (p.child 0)) (EffName.caught p) K i s) rfl r
  rcases hmb : runRowsO host (denoteBlockB table (bodiesOf root) k params b emptyCtx p.env) s r with
      ⟨_ | ex, s', r'⟩ | ⟨row, req, s', r'⟩
  rotate_right
  · rw [hmb] at ih
    exact RunsToDO.pre hpush ih
  · rw [hmb] at ih
    exact RunsToDO.pre hpush ih
  · rw [hmb] at ih
    rcases ih with ih | hdiv
    swap
    · exact RunsToDO.of_diverges (hdiv.pre hpush)
    obtain ⟨cb, hrb⟩ := ih
    cases ex with
    | success v =>
      have hpass := ReachesC.same (host := host) s' r' (fun s =>
        step_success_pass_onFailure root v (compileEff b (p.child 0)) (EffName.caught p) K i s) rfl rfl
      exact Or.inl ⟨1 + cb + 0, (hpush.trans hrb).trans hpass⟩
    | failure c =>
      have hh' : Node.at_ (Node.eff root) ({ p with completed := [] }.childWith 1 (Val.exitErr c)).path =
          some (Node.eff h) := at_childWith hat 1 (Val.exitErr c)
      have ihh := hh ({ p with completed := [] }.childWith 1 (Val.exitErr c)) K i s' r' params hh' hagree
      rw [Point.childWith_env] at ihh
      have hpop := ReachesC.step (host := host)
        (step_failure_onFailure root c (compileEff b (p.child 0)) (EffName.caught p) K i s') rfl r'
      simp only [interpAt] at hpop
      rw [contEOf_caught, resolve_of_at hh'] at hpop
      exact RunsToDO.pre ((hpush.trans hrb).trans hpop) ihh


/-- Step of rows-block-host/R6; consumer: `compilesBlk`.
The catchIf arm retains its detailed exits, cuts and waits. No machine progress follows. -/
theorem compilesBlk_catchIf {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {test : Term} {b h : NativeEff} (hb : CompilesBlk host root k b)
    (hh : CompilesBlk host root k h) : CompilesBlk host root k (.catchIf test b h) := by
  intro p K i s r params hat hagree
  rcases hfu : p.fuel with _ | n
  · exact RunsToDO.of_zero hfu
  have hb' : Node.at_ (Node.eff root) (p.child 0).path = some (Node.eff b) := at_child hat 0
  have hden : denoteBlockB table (bodiesOf root) k params (.catchIf test b h) emptyCtx p.env =
      thenOpt (denoteBlockB table (bodiesOf root) k params b emptyCtx p.env) (fun
      | .success v => pure (some (.success v))
      | .failure cause => match caughtErrorValue? p.env test cause with
        | some value => denoteBlockB table (bodiesOf root) k params h emptyCtx (p.env ++ [value])
        | none => pure (some (.failure cause))) := by
    cases k <;> rfl
  rw [compileEff_catchIf test b h hfu, runBlock_thenOpt host root k params b _ s r hden]
  have ih := hb (p.child 0)
    (Prim.onFailure (compileEff b (p.child 0)) (EffName.caughtError p) :: K) i s r params hb' hagree
  rw [Point.child_env] at ih
  have hpush := ReachesC.step (host := host)
    (step_push_onFailure root (compileEff b (p.child 0)) (EffName.caughtError p) K i s) rfl r
  rcases hmb : runRowsO host (denoteBlockB table (bodiesOf root) k params b emptyCtx p.env) s r with
      ⟨_ | ex, s', r'⟩ | ⟨row, req, s', r'⟩
  rotate_right
  · rw [hmb] at ih
    exact RunsToDO.pre hpush ih
  · rw [hmb] at ih
    exact RunsToDO.pre hpush ih
  · rw [hmb] at ih
    rcases ih with ih | hdiv
    swap
    · exact RunsToDO.of_diverges (hdiv.pre hpush)
    obtain ⟨cb, hrb⟩ := ih
    cases ex with
    | success v =>
      have hpass := ReachesC.same (host := host) s' r' (fun s =>
        step_success_pass_onFailure root v (compileEff b (p.child 0)) (EffName.caughtError p) K i s)
        rfl rfl
      exact Or.inl ⟨1 + cb + 0, (hpush.trans hrb).trans hpass⟩
    | failure c =>
      have hpop := ReachesC.step (host := host)
        (step_failure_onFailure root c (compileEff b (p.child 0)) (EffName.caughtError p) K i s') rfl r'
      simp only [interpAt] at hpop
      have hcont : contEOf root (EffName.caughtError { p with completed := [] }) c =
          (match caughtErrorValue? p.env test c with
            | some value => resolve root ({ p with completed := [] }.childWith 1 value)
            | none => Prim.failure c) := by
        show (match Node.at_ (Node.eff root) p.path with
          | some (.eff (.catchIf test _ _)) =>
            match caughtErrorValue? p.env test c with
            | some value => resolve root ({ p with completed := [] }.childWith 1 value)
            | none => Prim.failure c
          | _ => Prim.failure c) = _
        rw [hat]
      rw [hcont] at hpop
      show RunsToDO host root K i k _ s r (runRowsO host
        (match caughtErrorValue? p.env test c with
          | some value => denoteBlockB table (bodiesOf root) k params h emptyCtx (p.env ++ [value])
          | none => pure (some (Exit.failure c))) s' r')
      rcases hcv : caughtErrorValue? p.env test c with _ | value
      · simp only [hcv] at hpop
        exact Or.inl ⟨1 + cb + 1, (hpush.trans hrb).trans hpop⟩
      · simp only [hcv] at hpop
        have hh' : Node.at_ (Node.eff root) ({ p with completed := [] }.childWith 1 value).path =
            some (Node.eff h) := at_childWith hat 1 value
        have ihh := hh ({ p with completed := [] }.childWith 1 value) K i s' r' params hh' hagree
        rw [Point.childWith_env] at ihh
        rw [resolve_of_at hh'] at hpop
        exact RunsToDO.pre ((hpush.trans hrb).trans hpop) ihh


/-- Step of rows-block-host/R6; consumer: `compilesBlk`.
The matchCause arm retains its detailed exits, cuts and waits. No machine progress follows. -/
theorem compilesBlk_matchCause {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {b v c : NativeEff} (hb : CompilesBlk host root k b)
    (hv : CompilesBlk host root k v) (hc : CompilesBlk host root k c) :
    CompilesBlk host root k (.matchCause b v c) := by
  intro p K i s r params h hagree
  rcases hfu : p.fuel with _ | n
  · exact RunsToDO.of_zero hfu
  have hb' : Node.at_ (Node.eff root) (p.child 0).path = some (Node.eff b) := at_child h 0
  have hden : denoteBlockB table (bodiesOf root) k params (.matchCause b v c) emptyCtx p.env =
      thenOpt (denoteBlockB table (bodiesOf root) k params b emptyCtx p.env) (fun
      | .success x => denoteBlockB table (bodiesOf root) k params v emptyCtx (p.env ++ [x])
      | .failure cause => denoteBlockB table (bodiesOf root) k params c emptyCtx (p.env ++ [Val.exitErr cause])) := by
    cases k <;> rfl
  rw [compileEff_matchCause b v c hfu, runBlock_thenOpt host root k params b _ s r hden]
  have ih := hb (p.child 0)
    (Prim.onSuccessAndFailure (compileEff b (p.child 0)) (EffName.onValue p) (EffName.onCause p) :: K)
    i s r params hb' hagree
  rw [Point.child_env] at ih
  have hpush := ReachesC.step (host := host) (step_push_onSuccessAndFailure root
    (compileEff b (p.child 0)) (EffName.onValue p) (EffName.onCause p) K i s) rfl r
  rcases hmb : runRowsO host (denoteBlockB table (bodiesOf root) k params b emptyCtx p.env) s r with
      ⟨_ | ex, s', r'⟩ | ⟨row, req, s', r'⟩
  rotate_right
  · rw [hmb] at ih
    exact RunsToDO.pre hpush ih
  · rw [hmb] at ih
    exact RunsToDO.pre hpush ih
  · rw [hmb] at ih
    rcases ih with ih | hdiv
    swap
    · exact RunsToDO.of_diverges (hdiv.pre hpush)
    obtain ⟨cb, hrb⟩ := ih
    cases ex with
    | success x =>
      have hv' : Node.at_ (Node.eff root) ({ p with completed := [] }.childWith 1 x).path =
          some (Node.eff v) := at_childWith h 1 x
      have ihv := hv ({ p with completed := [] }.childWith 1 x) K i s' r' params hv' hagree
      rw [Point.childWith_env] at ihv
      have hpop := ReachesC.step (host := host) (step_success_onSuccessAndFailure root x
        (compileEff b (p.child 0)) (EffName.onValue p) (EffName.onCause p) K i s') rfl r'
      simp only [interpAt] at hpop
      rw [contAOf_onValue, resolve_of_at hv'] at hpop
      exact RunsToDO.pre ((hpush.trans hrb).trans hpop) ihv
    | failure cause =>
      have hc' : Node.at_ (Node.eff root)
          ({ p with completed := [] }.childWith 2 (Val.exitErr cause)).path = some (Node.eff c) :=
        at_childWith h 2 (Val.exitErr cause)
      have ihc := hc ({ p with completed := [] }.childWith 2 (Val.exitErr cause)) K i s' r' params hc' hagree
      rw [Point.childWith_env] at ihc
      have hpop := ReachesC.step (host := host) (step_failure_onSuccessAndFailure root cause
        (compileEff b (p.child 0)) (EffName.onValue p) (EffName.onCause p) K i s') rfl r'
      simp only [interpAt] at hpop
      rw [contEOf_onCause, resolve_of_at hc'] at hpop
      exact RunsToDO.pre ((hpush.trans hrb).trans hpop) ihc


/-- Step of rows-block-host/R6; consumer: `compilesBlk`.
The onExit arm retains its detailed exits, cuts and waits. No machine progress follows. -/
theorem compilesBlk_onExit {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {b f : NativeEff} (hb : CompilesBlk host root k b)
    (hf : CompilesBlk host root k f) : CompilesBlk host root k (.onExit b f) := by
  intro p K i s r params h hagree
  rcases hfu : p.fuel with _ | n
  · exact RunsToDO.of_zero hfu
  have hb' : Node.at_ (Node.eff root) (p.child 0).path = some (Node.eff b) := at_child h 0
  have hden : denoteBlockB table (bodiesOf root) k params (.onExit b f) emptyCtx p.env =
      thenOpt (denoteBlockB table (bodiesOf root) k params b emptyCtx p.env) (fun ex =>
      thenOpt (denoteBlockB table (bodiesOf root) k params f emptyCtx (p.env ++ [reifyExitVal ex])) fun fex =>
        pure (some (Exit.restoreAfterFinalizer ex (finVoid fex)))) := by
    cases k <;> rfl
  rw [compileEff_onExit b f hfu, runBlock_thenOpt host root k params b _ s r hden]
  have ih := hb (p.child 0) (Prim.onExit (compileEff b (p.child 0)) (EffName.fin p) false :: K) i s r params hb' hagree
  rw [Point.child_env] at ih
  have hpush := ReachesC.step (host := host)
    (step_push_onExit root (compileEff b (p.child 0)) (EffName.fin p) false K i s) rfl r
  rcases hmb : runRowsO host (denoteBlockB table (bodiesOf root) k params b emptyCtx p.env) s r with
      ⟨_ | ex, s', r'⟩ | ⟨row, req, s', r'⟩
  rotate_right
  · rw [hmb] at ih
    exact RunsToDO.pre hpush ih
  · rw [hmb] at ih
    exact RunsToDO.pre hpush ih
  · rw [hmb] at ih
    rcases ih with ih | hdiv
    swap
    · exact RunsToDO.of_diverges (hdiv.pre hpush)
    obtain ⟨cb, hrb⟩ := ih
    show RunsToDO host root K i k _ s r (runRowsO host
      (thenOpt (denoteBlockB table (bodiesOf root) k params f emptyCtx (p.env ++ [reifyExitVal ex])) fun fex =>
        pure (some (Exit.restoreAfterFinalizer ex (finVoid fex)))) s' r')
    rw [runRowsO_thenOpt]
    -- the body's exit meets the frame: the finalizer runs under the mask
    have hf' : Node.at_ (Node.eff root) ({ p with completed := [] }.childWith 1 (reifyExitVal ex)).path =
        some (Node.eff f) := at_childWith h 1 (reifyExitVal ex)
    have hmeet := ReachesC.step (host := host)
      (step_ofExit_onExit root ex (compileEff b (p.child 0)) p K i s') (isCall_ofExit ex) r'
    rw [resolve_of_at hf'] at hmeet
    have hunmask (result : ExitV) (state : Stores) (rr : σ) : ReachesC host root 0
        (fiberOf (Prim.ofExit result) (maskStack i K) false) state rr
        (fiberOf (Prim.ofExit result) K i) state rr := by
      cases i
      · exact ReachesC.refl host root _ state rr
      · exact ReachesC.same (host := host) state rr
          (fun s => step_ofExit_pass_setInterruptible root _ K false true s)
          (isCall_ofExit result) (isCall_ofExit result)
    cases ex with
    | success value =>
      let program := compileEff f ({ p with completed := [] }.childWith 1
        (reifyExitVal (.success value)))
      let restore := EffName.restore (.success value)
      have hpush₂ := ReachesC.step (host := host)
        (step_push_onSuccess root program restore (maskStack i K) false s') rfl r'
      have ihf := hf ({ p with completed := [] }.childWith 1 (reifyExitVal (.success value)))
        (Prim.onSuccess program restore :: maskStack i K) false s' r' params hf' hagree
      rw [Point.childWith_env] at ihf
      rcases hmf : runRowsO host (denoteBlockB table (bodiesOf root) k params f emptyCtx (p.env ++ [reifyExitVal (.success value)])) s' r' with
          ⟨_ | fex, s'', r''⟩ | ⟨row, req, s'', r''⟩
      rotate_right
      · rw [hmf] at ihf
        exact RunsToDO.pre (((hpush.trans hrb).trans hmeet).trans hpush₂) ihf
      · rw [hmf] at ihf
        exact RunsToDO.pre (((hpush.trans hrb).trans hmeet).trans hpush₂) ihf
      · rw [hmf] at ihf
        rcases ihf with ihf | hdiv
        swap
        · exact RunsToDO.of_diverges (hdiv.pre (((hpush.trans hrb).trans hmeet).trans hpush₂))
        obtain ⟨cf, hrf⟩ := ihf
        cases fex with
        | success finValue =>
          have hfin := ReachesC.step (host := host)
            (step_success_onSuccess root finValue program restore (maskStack i K) false s'') rfl r''
          change ReachesC host root 1 _ s'' r''
            (fiberOf (Prim.success value) (maskStack i K) false) s'' r'' at hfin
          exact Or.inl ⟨1 + cb + 1 + 1 + cf + 1 + 0,
            (((((hpush.trans hrb).trans hmeet).trans hpush₂).trans hrf).trans hfin).trans
              (hunmask (.success value) s'' r'')⟩
        | failure finCause =>
          have hpass := ReachesC.same (host := host) s'' r'' (fun s =>
            step_failure_pass_onSuccess root finCause program restore (maskStack i K) false s) rfl rfl
          exact Or.inl ⟨1 + cb + 1 + 1 + cf + 0 + 0,
            (((((hpush.trans hrb).trans hmeet).trans hpush₂).trans hrf).trans hpass).trans
              (hunmask (.failure finCause) s'' r'')⟩
    | failure cause =>
      let program := compileEff f ({ p with completed := [] }.childWith 1
        (reifyExitVal (.failure cause)))
      let restore := EffName.restore (.failure cause)
      let merge := EffName.merge (.failure cause)
      let outer := Prim.onSuccess (Prim.onFailure program merge) restore
      have hpush₂ := ReachesC.step (host := host)
        (step_push_onSuccess root (Prim.onFailure program merge) restore (maskStack i K) false s') rfl r'
      have hpush₃ := ReachesC.step (host := host)
        (step_push_onFailure root program merge (outer :: maskStack i K) false s') rfl r'
      have ihf := hf ({ p with completed := [] }.childWith 1 (reifyExitVal (.failure cause)))
        (Prim.onFailure program merge :: outer :: maskStack i K) false s' r' params hf' hagree
      rw [Point.childWith_env] at ihf
      rcases hmf : runRowsO host (denoteBlockB table (bodiesOf root) k params f emptyCtx (p.env ++ [reifyExitVal (.failure cause)])) s' r' with
          ⟨_ | fex, s'', r''⟩ | ⟨row, req, s'', r''⟩
      rotate_right
      · rw [hmf] at ihf
        exact RunsToDO.pre ((((hpush.trans hrb).trans hmeet).trans hpush₂).trans hpush₃) ihf
      · rw [hmf] at ihf
        exact RunsToDO.pre ((((hpush.trans hrb).trans hmeet).trans hpush₂).trans hpush₃) ihf
      · rw [hmf] at ihf
        rcases ihf with ihf | hdiv
        swap
        · exact RunsToDO.of_diverges
            (hdiv.pre ((((hpush.trans hrb).trans hmeet).trans hpush₂).trans hpush₃))
        obtain ⟨cf, hrf⟩ := ihf
        cases fex with
        | success finValue =>
          have hpass := ReachesC.same (host := host) s'' r'' (fun s =>
            step_success_pass_onFailure root finValue program merge (outer :: maskStack i K) false s)
            rfl rfl
          have hfin := ReachesC.step (host := host) (step_success_onSuccess root finValue
            (Prim.onFailure program merge) restore (maskStack i K) false s'') rfl r''
          change ReachesC host root 1 _ s'' r''
            (fiberOf (Prim.failure cause) (maskStack i K) false) s'' r'' at hfin
          exact Or.inl ⟨1 + cb + 1 + 1 + 1 + cf + 0 + 1 + 0,
            (((((((hpush.trans hrb).trans hmeet).trans hpush₂).trans hpush₃).trans hrf).trans
              hpass).trans hfin).trans (hunmask (.failure cause) s'' r'')⟩
        | failure finCause =>
          have hmerge := ReachesC.step (host := host)
            (step_failure_onFailure root finCause program merge (outer :: maskStack i K) false s'')
            rfl r''
          change ReachesC host root 1 _ s'' r''
            (fiberOf (Prim.failure (Cause.combine cause finCause)) (outer :: maskStack i K) false)
            s'' r'' at hmerge
          have hpass := ReachesC.same (host := host) s'' r'' (fun s => step_failure_pass_onSuccess root
            (Cause.combine cause finCause) (Prim.onFailure program merge) restore (maskStack i K)
            false s) rfl rfl
          exact Or.inl ⟨1 + cb + 1 + 1 + 1 + cf + 1 + 0 + 0,
            (((((((hpush.trans hrb).trans hmeet).trans hpush₂).trans hpush₃).trans hrf).trans
              hmerge).trans hpass).trans (hunmask (.failure (Cause.combine cause finCause)) s'' r'')⟩


/-- Step of rows-block-host/R6; consumer: `compilesBlk_iterate`.
Each round retains the supplied parameter frame and its detailed observation. -/
theorem loop_reachesBlk {σ : Type} (host : Effects.Comodel (RowSig table) σ) (root : NativeEff)
    (k : Nat) (params : List (ParamTreeB table)) (q : Point) (hq : loopPoint q = q) {cty : Option Ty} {init test step result : Term}
    {body : NativeEff}
    (h : Node.at_ (Node.eff root) q.path =
      some (Node.eff (.iterate cty init test step result body)))
    (K : List NCode) (i : Bool) (hbody : CompilesBlk host root k body)
    (hagree : ParamsAgree host root k params q.params) :
    ∀ (j : Nat), j ≤ k → ∀ (c : Val) (s : Stores) (r : σ),
      RunsToDO host root K i j (enter q K i (loopNextAt root q c)) s r
        (runRowsO host (Option.join <$>
          iter (loopStep (denoteBlockB table (bodiesOf root) k params body emptyCtx) q.env test step result) j c) s r)
  | 0, _, _, s, r => .inl ⟨0, _, s, r, Nat.le_refl 0, ReachesC.refl host root _ s r⟩
  | j + 1, hj, c, s, r => by
    have hNext : ∀ {x : Option Val} {ln : LoopNext Val NCode}, evalTerm (q.env ++ [c]) test = x →
        (match x with
         | some (Val.bool true) => LoopNext.continue c (resolve root (q.childWith 0 c))
         | some (Val.bool false) => .finish (loopFinishAt root q c)
         | _ => .finish badShape) = ln → loopNextAt root q c = ln := by
      intro x ln hx hln
      unfold loopNextAt
      rw [loopAt_iterate root h]
      dsimp only
      rw [hx]
      exact hln
    have hFinish : ∀ {x : Option Val} {code : NCode}, evalTerm (q.env ++ [c]) result = x →
        (match x with
         | some answer => Prim.success answer
         | none => badShape) = code → loopFinishAt root q c = code := by
      intro x code hx hcode
      unfold loopFinishAt
      rw [loopResultAt_iterate root h]
      dsimp only
      rw [hx]
      exact hcode
    rw [runRowsO_iter_succ]
    -- a round that ends the loop at once with the exit `y`, the stores and state untouched
    have hdone : ∀ (y : ExitV) (code : NCode),
        runRowsO host (loopStep (denoteBlockB table (bodiesOf root) k params body emptyCtx) q.env test step result c) s r =
          .done (.inl (some y)) s r →
        loopNextAt root q c = .finish code → code = Prim.ofExit y →
        RunsToDO host root K i (j + 1) (enter q K i (loopNextAt root q c)) s r
          (.done (some y) s r) := by
      intro y code hf hln hcode
      rw [hln]
      show RunsToD host root K i (fiberOf code K i) s r (some (y, (s, r)))
      rw [hcode]
      exact Or.inl ⟨0, ReachesC.refl host root _ s r⟩
    cases ht : evalTerm (q.env ++ [c]) test with
    | none =>
      have hf : runRowsO host (loopStep (denoteBlockB table (bodiesOf root) k params body emptyCtx) q.env test step result c) s r =
          .done (.inl (some badShapeExit)) s r := by
        unfold loopStep
        rw [ht]
        rfl
      rw [hf]
      exact hdone badShapeExit badShape hf (hNext ht rfl) badShape_eq
    | some tv =>
      cases tv with
      | bool flag =>
        cases flag with
        | false =>
          cases hr : evalTerm (q.env ++ [c]) result with
          | none =>
            have hf : runRowsO host (loopStep (denoteBlockB table (bodiesOf root) k params body emptyCtx) q.env test step result c)
                s r = .done (.inl (some badShapeExit)) s r := by
              unfold loopStep
              rw [ht, hr]
              rfl
            rw [hf]
            exact hdone badShapeExit badShape hf (by rw [hNext ht rfl, hFinish hr rfl]) badShape_eq
          | some v =>
            have hf : runRowsO host (loopStep (denoteBlockB table (bodiesOf root) k params body emptyCtx) q.env test step result c)
                s r = .done (.inl (some (Exit.success v))) s r := by
              unfold loopStep
              rw [ht, hr]
              rfl
            rw [hf]
            exact hdone (Exit.success v) (Prim.success v) hf (by rw [hNext ht rfl, hFinish hr rfl]) rfl
        | true =>
          rw [hNext ht rfl]
          have hat : Node.at_ (Node.eff root) (q.childWith 0 c).path = some (Node.eff body) :=
            at_childWith h 0 c
          have hent : enter q K i (LoopNext.continue c (resolve root (q.childWith 0 c))) =
              fiberOf (compileEff body (q.childWith 0 c)) (Prim.whileLoop (EffName.loop q) c :: K) i := by
            rw [resolve_of_at hat]
            rfl
          rw [hent]
          have ihb := hbody (q.childWith 0 c) (Prim.whileLoop (EffName.loop q) c :: K) i s r params hat hagree
          rw [Point.childWith_env] at ihb
          -- the round's run, from the body's run
          have hround : runRowsO host (loopStep (denoteBlockB table (bodiesOf root) k params body emptyCtx) q.env test step result c)
              s r = (runRowsO host (denoteBlockB table (bodiesOf root) k params body emptyCtx (q.env ++ [c])) s r).andThen
                fun x s r => runRowsO host
                (match x with
                 | none => pure (.inl none)
                 | some (Exit.failure cause) => pure (.inl (some (Exit.failure cause)))
                 | some (Exit.success a) =>
                   match evalTerm (q.env ++ [c, a]) step with
                   | some c' => pure (.inr c')
                   | none => pure (.inl (some badShapeExit))) s r := by
            unfold loopStep
            rw [ht]
            exact runRowsO_bind host _ _ s r
          rw [hround]
          rcases hmb : runRowsO host (denoteBlockB table (bodiesOf root) k params body emptyCtx (q.env ++ [c])) s r with
              ⟨_ | exb, s', r'⟩ | ⟨row, req, s', r'⟩
          rotate_right
          · rw [hmb] at ihb
            exact ihb
          · rw [hmb] at ihb
            exact RunsToDO.mono hj ihb
          · rw [hmb] at ihb
            rcases ihb with ihb | hdiv
            swap
            · exact RunsToDO.of_diverges hdiv
            obtain ⟨cb, hrb⟩ := ihb
            cases exb with
            | failure cause =>
              have hpass := ReachesC.same (host := host) s' r' (fun s₀ =>
                step_failure_pass_whileLoop root q c cause K i s₀) rfl rfl
              exact Or.inl ⟨cb + 0, hrb.trans hpass⟩
            | success a =>
              have hstepA := ReachesC.step (host := host) (step_success_enter root q hq c a K i s')
                rfl r'
              have hResume : ∀ {x : Option Val} {ln : LoopNext Val NCode},
                  evalTerm (q.env ++ [c, a]) step = x →
                  (match x with
                   | some next => loopNextAt root q next
                   | none => LoopNext.finish badShape) = ln → loopResumeAt root q c a = ln := by
                intro x ln hx hln
                unfold loopResumeAt
                rw [loopAt_iterate root h]
                dsimp only
                rw [hx]
                exact hln
              dsimp only [RowsEnd.andThen]
              cases hs : evalTerm (q.env ++ [c, a]) step with
              | none =>
                rw [hResume hs rfl] at hstepA
                rw [badShape_eq] at hstepA
                exact Or.inl ⟨cb + 1, hrb.trans hstepA⟩
              | some c' =>
                rw [hResume hs rfl] at hstepA
                have ih := loop_reachesBlk host root k params q hq h K i hbody hagree j (by omega) c' s' r'
                exact RunsToDO.mono (by omega) (RunsToDO.pre_add (hrb.trans hstepA) ih)
      | _ =>
        have hf : runRowsO host (loopStep (denoteBlockB table (bodiesOf root) k params body emptyCtx) q.env test step result c) s r =
            .done (.inl (some badShapeExit)) s r := by
          unfold loopStep
          rw [ht]
          rfl
        rw [hf]
        exact hdone badShapeExit badShape hf (hNext ht rfl) badShape_eq


/-- Step of rows-block-host/R6; consumer: `compilesBlk`.
The loop uses its meaning budget and claims no scheduler progress. -/
theorem compilesBlk_iterate {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {cty : Option Ty} {init test step result : Term}
    {body : NativeEff} (hb : CompilesBlk host root k body) :
    CompilesBlk host root k (.iterate cty init test step result body) := by
  intro p K i s r params h hagree
  rcases hfu : p.fuel with _ | n
  · exact RunsToDO.of_zero hfu
  have hq : Node.at_ (Node.eff root) (loopPoint p).path =
      some (Node.eff (.iterate cty init test step result body)) := h
  rw [compileEff_iterate cty init test step result body hfu]
  have hs := step_suspend root (EffThunk.body p) K i s
  simp only [interpAt] at hs
  rw [Effect4.Program.Sched.suspendBodyAt_iterate (q := loopPoint p) hfu hq] at hs
  have hden : denoteBlockB table (bodiesOf root) k params
      (.iterate cty init test step result body) emptyCtx p.env =
      match evalTerm p.env init with
      | some initialValue => Option.join <$> iter
          (loopStep (denoteBlockB table (bodiesOf root) k params body emptyCtx)
            p.env test step result) k initialValue
      | none => pure (some badShapeExit) := by
    cases k <;> rfl
  rw [hden]
  cases hi : evalTerm p.env init with
  | none =>
    rw [show evalTerm (loopPoint p).env init = none from hi, badShape_eq] at hs
    exact Or.inl ⟨1, ReachesC.step (host := host) hs rfl r⟩
  | some c₀ =>
    rw [show evalTerm (loopPoint p).env init = some c₀ from hi] at hs
    have henter := ReachesC.step (host := host)
      (step_whileLoop_enter root (loopPoint p) rfl c₀ K i s) rfl r
    exact RunsToDO.pre ((ReachesC.step (host := host) hs rfl r).trans henter)
      (loop_reachesBlk host root k params (loopPoint p) rfl hq K i hb hagree k (Nat.le_refl k) c₀ s r)


/-- Step of rows-block-host/R6; consumer: `compilesBlk`.
The exit fold reads the placed block exit law; a cut or wait remains live. -/
theorem compilesBlk_exit {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) {b : NativeEff} (hfrag : BodyRows table b = true)
    (hb : CompilesBlk host root k b) : CompilesBlk host root k (.exit b) := by
  intro p K i s r params h hagree
  rcases hfu : p.fuel with _ | n
  · exact RunsToDO.of_zero hfu
  have hb' : Node.at_ (Node.eff root) (p.child 0).path = some (Node.eff b) := at_child h 0
  have hden : denoteBlockB table (bodiesOf root) k params (.exit b) emptyCtx p.env =
      thenOpt (denoteBlockB table (bodiesOf root) k params b emptyCtx p.env)
        (fun ex => pure (some (.success (reifyExitVal ex)))) := by
    cases k <;> rfl
  rw [runBlock_thenOpt host root k params b _ s r hden]
  rcases hx : (compileEff b (p.child 0)).asExit? with _ | ex
  · rw [compileEff_exit_frame b hfu hx]
    have ih := hb (p.child 0) (Prim.exitFrame (compileEff b (p.child 0)) :: K) i s r params hb' hagree
    rw [Point.child_env] at ih
    have hpush := ReachesC.step (host := host)
      (step_push_exitFrame root (compileEff b (p.child 0)) K i s) rfl r
    rcases hmb : runRowsO host (denoteBlockB table (bodiesOf root) k params b emptyCtx p.env) s r with
        ⟨_ | ex, s', r'⟩ | ⟨row, req, s', r'⟩
    rotate_right
    · rw [hmb] at ih
      exact RunsToDO.pre hpush ih
    · rw [hmb] at ih
      exact RunsToDO.pre hpush ih
    · rw [hmb] at ih
      rcases ih with ih | hdiv
      swap
      · exact RunsToDO.of_diverges (hdiv.pre hpush)
      obtain ⟨cb, hrb⟩ := ih
      have hpop := ReachesC.step (host := host)
        (step_ofExit_exitFrame root ex (compileEff b (p.child 0)) K i s') (isCall_ofExit ex) r'
      exact Or.inl ⟨1 + cb + 1, (hpush.trans hrb).trans hpop⟩
  · -- the fold: the compiled program already is the meaning's exit (row D1)
    have heq := denoteBlockB_of_asExit table (bodiesOf root) b (p.child 0) ex hfrag hx k params emptyCtx
    have hmb : runRowsO host
        (denoteBlockB table (bodiesOf root) k params b emptyCtx (p.child 0).env) s r =
        .done (some ex) s r := by
      rw [heq]
      rfl
    rw [Point.child_env] at hmb
    rw [compileEff_exit_fold b hfu hx, hmb]
    exact Or.inl ⟨0, ReachesC.refl host root _ s r⟩


/-- Step of rows-block-host/R6; consumer: `compilesBlk` at a program parameter.
The related frame supplies the passed tree, including malformed missing-index cases. -/
theorem compilesBlk_param {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k j : Nat) (request : Term) :
    CompilesBlk host root k (.perform (.param j) request) := by
  intro p K i s r params hat hagree
  cases hfu : p.fuel with
  | zero => exact RunsToDO.of_zero hfu
  | succ fuel =>
    rw [compileEff_perform (.param j) request hfu]
    have hs := step_suspend root (EffThunk.body p) K i s
    simp only [interpAt] at hs
    rw [suspendBodyAt_param (q := { p with completed := [] }) hfu hat] at hs
    cases hv : evalTerm p.env request with
    | none =>
      simp only [hv] at hs
      have hden : denoteBlockB table (bodiesOf root) k params (.perform (.param j) request)
          emptyCtx p.env = pure (some badShapeExit) := by
        cases k <;> simp only [denoteBlockB, cata_eff, blockAlgB, hv]
      rw [hden]
      rw [badShape_eq] at hs
      exact Or.inl ⟨1, ReachesC.step (host := host) hs rfl r⟩
    | some w =>
      cases hstack : p.params with
      | nil =>
        have hempty : params = [] := by
          simpa only [hstack, ParamsAgree] using hagree
        subst params
        simp only [hv, hstack] at hs
        have hden : denoteBlockB table (bodiesOf root) k [] (.perform (.param j) request)
            emptyCtx p.env = pure (some badShapeExit) := by
          cases k <;> simp only [denoteBlockB, cata_eff, blockAlgB, hv, List.getElem?_nil]
        rw [hden]
        rw [badShape_eq] at hs
        exact Or.inl ⟨1, ReachesC.step (host := host) hs rfl r⟩
      | cons top rest =>
        have ha : ParamsAgree host root k params (top :: rest) := by
          rw [← hstack]
          exact hagree
        cases hsite : top[j]? with
        | none =>
          have hmissing : params[j]? = none := by
            apply List.getElem?_eq_none_iff.mpr
            have hbound := List.getElem?_eq_none_iff.mp hsite
            have hlen := ha.1
            omega
          simp only [hv, hstack, hsite] at hs
          have hden : denoteBlockB table (bodiesOf root) k params (.perform (.param j) request)
              emptyCtx p.env = pure (some badShapeExit) := by
            cases k <;> simp only [denoteBlockB, cata_eff, blockAlgB, hv, hmissing]
          rw [hden]
          rw [badShape_eq] at hs
          exact Or.inl ⟨1, ReachesC.step (host := host) hs rfl r⟩
        | some site =>
          cases hf : params[j]? with
          | none =>
            have hbound := List.getElem?_eq_none_iff.mp hf
            have hlt := (List.getElem?_eq_some_iff.mp hsite).1
            have hlen := ha.1
            have impossible : False := by omega
            exact impossible.elim
          | some f =>
            simp only [hv, hstack, hsite] at hs
            rw [denoteBlockB_param table (bodiesOf root) k params j request f emptyCtx p.env w hf hv]
            have ih := ha.2 j f site hf hsite w
              { ({ p with completed := [] } : Point).redirect site.path with
                env := site.env ++ [w], params := rest, call := p.call.tail }
              K i s r rfl rfl rfl
            exact RunsToDO.pre (ReachesC.step (host := host) hs rfl r) ih

/-- Step of rows-block-host/R6; consumer: the call and invocation arms of `compilesBlk`.
A definition path exists exactly at the selected body index. -/
private theorem defBodyPath_lookup (root : NativeEff) (j : Nat) :
    defBodyPath root j = ((bodiesOf root)[j]?).map (fun _ => 0 :: List.replicate j 1 ++ [0]) := by
  cases root with
  | defs declarations bodies main layers =>
    change (if j < bodies.toList.length then some (0 :: List.replicate j 1 ++ [0]) else none) =
      (bodies.toList[j]?).map (fun _ => 0 :: List.replicate j 1 ++ [0])
    cases hb : bodies.toList[j]? with
    | none =>
      have hbound := List.getElem?_eq_none_iff.mp hb
      rw [if_neg (Nat.not_lt.mpr hbound)]
      rfl
    | some body =>
      have hlt := (List.getElem?_eq_some_iff.mp hb).1
      rw [if_pos hlt]
      rfl
  | _ => rfl

/-- Step of rows-block-host/R6; consumer: `compilesBlk` at call budget zero.
A valid request reaches the zero-depth cut without a progress claim. -/
theorem compilesBlk_call_zero {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (j : Nat) (request : Term) :
    CompilesBlk host root 0 (.perform (.call j) request) := by
  intro p K i s r params hat _
  cases hfu : p.fuel with
  | zero => exact RunsToDO.of_zero hfu
  | succ fuel =>
    cases hv : evalTerm p.env request with
    | some v =>
      have hden : denoteBlockB table (bodiesOf root) 0 params (.perform (.call j) request)
          emptyCtx p.env = pure none := by
        simp only [denoteBlockB, cata_eff, blockAlgB, hv]
      rw [hden]
      exact Or.inl ⟨0, _, s, r, Nat.le_refl 0, ReachesC.refl host root _ s r⟩
    | none =>
      have hden : denoteBlockB table (bodiesOf root) 0 params (.perform (.call j) request)
          emptyCtx p.env = pure (some badShapeExit) := by
        simp only [denoteBlockB, cata_eff, blockAlgB, hv]
      rw [hden, compileEff_perform (.call j) request hfu]
      have hs := step_suspend root (EffThunk.body p) K i s
      simp only [interpAt] at hs
      rw [suspendBodyAt_call (q := { p with completed := [] }) hfu hat] at hs
      simp only [hv] at hs
      rw [badShape_eq] at hs
      exact Or.inl ⟨1, ReachesC.step (host := host) hs rfl r⟩

/-- Step of rows-block-host/R6; consumer: `compilesBlk` at positive call budget.
A call pushes its empty lexical frame and uses the induction at its actual definition body. -/
theorem compilesBlk_call_succ {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k j : Nat) (request : Term)
    (ih : ∀ body ∈ bodiesOf root, CompilesBlk host root k body) :
    CompilesBlk host root (k + 1) (.perform (.call j) request) := by
  intro p K i s r params hat _
  cases hfu : p.fuel with
  | zero => exact RunsToDO.of_zero hfu
  | succ fuel =>
    rw [compileEff_perform (.call j) request hfu]
    have hs := step_suspend root (EffThunk.body p) K i s
    simp only [interpAt] at hs
    rw [suspendBodyAt_call (q := { p with completed := [] }) hfu hat] at hs
    cases hv : evalTerm p.env request with
    | none =>
      simp only [hv] at hs
      have hden : denoteBlockB table (bodiesOf root) (k + 1) params (.perform (.call j) request)
          emptyCtx p.env = pure (some badShapeExit) := by
        simp only [denoteBlockB, cata_eff, blockAlgB, hv]
      rw [hden]
      rw [badShape_eq] at hs
      exact Or.inl ⟨1, ReachesC.step (host := host) hs rfl r⟩
    | some v =>
      cases hb : (bodiesOf root)[j]? with
      | none =>
        have hpath : defBodyPath root j = none := by
          rw [defBodyPath_lookup, hb]
          rfl
        simp only [hv, hpath] at hs
        have hden : denoteBlockB table (bodiesOf root) (k + 1) params (.perform (.call j) request)
            emptyCtx p.env = pure (some badShapeExit) := by
          simp only [denoteBlockB, cata_eff, blockAlgB, hv, hb]
        rw [hden]
        rw [badShape_eq] at hs
        exact Or.inl ⟨1, ReachesC.step (host := host) hs rfl r⟩
      | some body =>
        let path := 0 :: List.replicate j 1 ++ [0]
        have hpath : defBodyPath root j = some path := by
          rw [defBodyPath_lookup, hb]
          rfl
        have hbody := defBodyPath_body hpath hb
        let q : Point := { ({ p with completed := [] } : Point).redirect path with
          env := [v], params := [] :: p.params, call := p.path :: p.call }
        have hq : Node.at_ (Node.eff root) q.path = some (Node.eff body) := hbody
        have hagree : ParamsAgree host root k [] q.params := by
          refine ⟨rfl, ?_⟩
          intro index f site impossible
          simp only [List.getElem?_nil, reduceCtorEq] at impossible
        have member : body ∈ bodiesOf root := List.mem_of_getElem? hb
        have child := ih body member q K i s r [] hq hagree
        rw [denoteBlockB_call table (bodiesOf root) k params j request body emptyCtx p.env v hb hv]
        simp only [hv, hpath] at hs
        rw [resolve_of_at hq] at hs
        exact RunsToDO.pre_add (ReachesC.step (host := host) hs rfl r) child

/-- Step of rows-block-host/R6; consumer: `invocationParams`.
An invocation retains one site per supplied argument. -/
private theorem argSites_length (path : List Nat) (env : List Val) :
    ∀ args : Effs NativeOp, (argSitesAt path env args).length = args.toList.length
  | .nil => rfl
  | .cons head tail => by
    simp only [argSitesAt, Effs.toList, List.length_cons, argSites_length (path ++ [1]) env tail]

/-- Step of rows-block-host/R6; consumer: `compilesBlk_invoke_succ`.
Captured arguments retain the caller's budget and lexical frame; their cut bound weakens once. -/
private theorem invocationParams {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat) (p : Point) (index : Nat) (request : Term)
    (args : Effs NativeOp) (params : List (ParamTreeB table))
    (hat : Node.at_ (Node.eff root) p.path = some (Node.eff (.invoke index request args)))
    (hagree : ParamsAgree host root (k + 1) params p.params)
    (hargs : ∀ arg ∈ args.toList, CompilesBlk host root (k + 1) arg) :
    ParamsAgree host root k
      (args.toList.map fun arg ctx w =>
        denoteBlockB table (bodiesOf root) (k + 1) params arg ctx (p.env ++ [w]))
      (argSitesAt (p.path ++ [0]) p.env args :: p.params) := by
  refine ⟨?_, ?_⟩
  · rw [List.length_map, argSites_length]
  · intro j f site hf hsite w q K i s r hpath henv hstack
    rw [List.getElem?_map] at hf
    obtain ⟨arg, harg, rfl⟩ := Option.map_eq_some_iff.mp hf
    obtain ⟨hnode, hcaptured⟩ := argSitesAt_body hat harg hsite
    have hq : Node.at_ (Node.eff root) q.path = some (Node.eff arg) := by
      rw [hpath]
      exact hnode
    have hparams : ParamsAgree host root (k + 1) params q.params := by
      rw [hstack]
      exact hagree
    have child := hargs arg (List.mem_of_getElem? harg) q K i s r params hq hparams
    have he : q.env = p.env ++ [w] := by
      rw [henv, hcaptured]
    rw [he] at child
    rw [resolve_of_at hq]
    exact RunsToDO.mono (Nat.le_succ k) child

/-- Step of rows-block-host/R6; consumer: `compilesBlk` at invocation budget zero.
A valid invocation request reaches the zero-depth cut without running its arguments. -/
theorem compilesBlk_invoke_zero {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (index : Nat) (request : Term) (args : Effs NativeOp) :
    CompilesBlk host root 0 (.invoke index request args) := by
  intro p K i s r params hat _
  cases hfu : p.fuel with
  | zero => exact RunsToDO.of_zero hfu
  | succ fuel =>
    cases hv : evalTerm p.env request with
    | some v =>
      have hden : denoteBlockB table (bodiesOf root) 0 params (.invoke index request args)
          emptyCtx p.env = pure none := by
        simp only [denoteBlockB, cata_eff, blockAlgB, hv]
      rw [hden]
      exact Or.inl ⟨0, _, s, r, Nat.le_refl 0, ReachesC.refl host root _ s r⟩
    | none =>
      have hden : denoteBlockB table (bodiesOf root) 0 params (.invoke index request args)
          emptyCtx p.env = pure (some badShapeExit) := by
        simp only [denoteBlockB, cata_eff, blockAlgB, hv]
      rw [hden, compileEff_invoke index request args hfu]
      have hs := step_suspend root (EffThunk.body p) K i s
      simp only [interpAt] at hs
      rw [suspendBodyAt_invoke (q := { p with completed := [] }) hfu hat] at hs
      simp only [hv] at hs
      rw [badShape_eq] at hs
      exact Or.inl ⟨1, ReachesC.step (host := host) hs rfl r⟩

/-- Step of rows-block-host/R6; consumer: `compilesBlk` at positive invocation budget.
A definition receives its captured arguments under the caller's lexical frame. -/
theorem compilesBlk_invoke_succ {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k index : Nat) (request : Term) (args : Effs NativeOp)
    (ih : ∀ body ∈ bodiesOf root, CompilesBlk host root k body)
    (hargs : ∀ arg ∈ args.toList, CompilesBlk host root (k + 1) arg) :
    CompilesBlk host root (k + 1) (.invoke index request args) := by
  intro p K i s r params hat hagree
  cases hfu : p.fuel with
  | zero => exact RunsToDO.of_zero hfu
  | succ fuel =>
    rw [compileEff_invoke index request args hfu]
    have hs := step_suspend root (EffThunk.body p) K i s
    simp only [interpAt] at hs
    rw [suspendBodyAt_invoke (q := { p with completed := [] }) hfu hat] at hs
    cases hv : evalTerm p.env request with
    | none =>
      simp only [hv] at hs
      have hden : denoteBlockB table (bodiesOf root) (k + 1) params (.invoke index request args)
          emptyCtx p.env = pure (some badShapeExit) := by
        simp only [denoteBlockB, cata_eff, blockAlgB, hv]
      rw [hden]
      rw [badShape_eq] at hs
      exact Or.inl ⟨1, ReachesC.step (host := host) hs rfl r⟩
    | some v =>
      cases hb : (bodiesOf root)[index]? with
      | none =>
        have hpath : defBodyPath root index = none := by
          rw [defBodyPath_lookup, hb]
          rfl
        simp only [hv, hpath] at hs
        have hden : denoteBlockB table (bodiesOf root) (k + 1) params (.invoke index request args)
            emptyCtx p.env = pure (some badShapeExit) := by
          simp only [denoteBlockB, cata_eff, blockAlgB, hv, hb]
        rw [hden]
        rw [badShape_eq] at hs
        exact Or.inl ⟨1, ReachesC.step (host := host) hs rfl r⟩
      | some body =>
        let path := 0 :: List.replicate index 1 ++ [0]
        have hpath : defBodyPath root index = some path := by
          rw [defBodyPath_lookup, hb]
          rfl
        have hbody := defBodyPath_body hpath hb
        let q : Point := { ({ p with completed := [] } : Point).redirect path with
          env := [v], params := argSitesAt (p.path ++ [0]) p.env args :: p.params,
          call := p.path :: p.call }
        have hq : Node.at_ (Node.eff root) q.path = some (Node.eff body) := hbody
        let trees := args.toList.map fun arg ctx w =>
          denoteBlockB table (bodiesOf root) (k + 1) params arg ctx (p.env ++ [w])
        have hrelated : ParamsAgree host root k trees q.params :=
          invocationParams host root k p index request args params hat hagree hargs
        have child := ih body (List.mem_of_getElem? hb) q K i s r trees hq hrelated
        rw [denoteBlockB_invoke table (bodiesOf root) k params index request args body emptyCtx p.env v hb hv]
        simp only [hv, hpath] at hs
        rw [resolve_of_at hq] at hs
        exact RunsToDO.pre_add (ReachesC.step (host := host) hs rfl r) child

mutual
/-- Step of rows-block-host/R6; consumer: `compilesBlk` at each fixed budget.
The structural induction delegates calls to the outer budget induction. -/
private theorem compilesBlk_body {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat)
    (hcall : ∀ j request, CompilesBlk host root k (.perform (.call j) request))
    (hinvoke : ∀ index request args,
      (∀ arg ∈ args.toList, CompilesBlk host root k arg) →
      CompilesBlk host root k (.invoke index request args)) :
    ∀ e, BodyRows table e = true → CompilesBlk host root k e
  | .succeed v, _ => compilesBlk_of_loopedDataRows host root k _ rfl
  | .fail e, _ => compilesBlk_of_loopedDataRows host root k _ rfl
  | .failCause cause, _ => compilesBlk_of_loopedDataRows host root k _ rfl
  | .sync t, _ => compilesBlk_of_loopedDataRows host root k _ rfl
  | .perform op request, he => by
    cases op with
    | call j => exact hcall j request
    | param j => exact compilesBlk_param host root k j request
    | _ => exact compilesBlk_of_loopedDataRows host root k _ he
  | .suspend b, he => compilesBlk_suspend host root k
      (compilesBlk_body host root k hcall hinvoke b he)
  | .exit b, he => compilesBlk_exit host root k he
      (compilesBlk_body host root k hcall hinvoke b he)
  | .iterate c initial test step result b, he => compilesBlk_iterate host root k
      (compilesBlk_body host root k hcall hinvoke b he)
  | .bind a b, he => by
    have ha : BodyRows table a = true := (Bool.and_eq_true_iff.mp he).1
    have hb : BodyRows table b = true := (Bool.and_eq_true_iff.mp he).2
    exact compilesBlk_bind host root k (compilesBlk_body host root k hcall hinvoke a ha)
      (compilesBlk_body host root k hcall hinvoke b hb)
  | .select t d a b, he => by
    have ha : BodyRows table a = true := (Bool.and_eq_true_iff.mp he).1
    have hb : BodyRows table b = true := (Bool.and_eq_true_iff.mp he).2
    exact compilesBlk_select host root k (compilesBlk_body host root k hcall hinvoke a ha)
      (compilesBlk_body host root k hcall hinvoke b hb)
  | .catchCause b h, he => by
    have hb : BodyRows table b = true := (Bool.and_eq_true_iff.mp he).1
    have hh : BodyRows table h = true := (Bool.and_eq_true_iff.mp he).2
    exact compilesBlk_catchCause host root k (compilesBlk_body host root k hcall hinvoke b hb)
      (compilesBlk_body host root k hcall hinvoke h hh)
  | .catchIf t b h, he => by
    have hb : BodyRows table b = true := (Bool.and_eq_true_iff.mp he).1
    have hh : BodyRows table h = true := (Bool.and_eq_true_iff.mp he).2
    exact compilesBlk_catchIf host root k (compilesBlk_body host root k hcall hinvoke b hb)
      (compilesBlk_body host root k hcall hinvoke h hh)
  | .matchCause b v c, he => by
    have hb : BodyRows table b = true := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp he).1).1
    have hv : BodyRows table v = true := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp he).1).2
    have hc : BodyRows table c = true := (Bool.and_eq_true_iff.mp he).2
    exact compilesBlk_matchCause host root k (compilesBlk_body host root k hcall hinvoke b hb)
      (compilesBlk_body host root k hcall hinvoke v hv) (compilesBlk_body host root k hcall hinvoke c hc)
  | .onExit b f, he => by
    have hb : BodyRows table b = true := (Bool.and_eq_true_iff.mp he).1
    have hf : BodyRows table f = true := (Bool.and_eq_true_iff.mp he).2
    exact compilesBlk_onExit host root k (compilesBlk_body host root k hcall hinvoke b hb)
      (compilesBlk_body host root k hcall hinvoke f hf)
  | .invoke index request args, he =>
    hinvoke index request args (compilesBlk_args host root k hcall hinvoke args he)
  | .gen _, he | .uninterruptible _, he | .interruptible _, he | .yieldNow _, he
  | .awaitFiber _ _, he | .withFiber _, he | .scoped _, he | .acquireRelease _ _, he
  | .provideLayer _ _ _, he | .service _, he | .provideService _ _ _, he | .restore _ _, he
  | .defs _ _ _ _, he | .provideContext _ _, he => absurd (he : false = true) Bool.false_ne_true

/-- Step of rows-block-host/R6; consumer: `compilesBlk_body` at invocation.
The argument-spine induction supplies each body's structural compilation witness. -/
private theorem compilesBlk_args {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (k : Nat)
    (hcall : ∀ j request, CompilesBlk host root k (.perform (.call j) request))
    (hinvoke : ∀ index request args,
      (∀ arg ∈ args.toList, CompilesBlk host root k arg) →
      CompilesBlk host root k (.invoke index request args)) :
    ∀ args : Effs NativeOp, cata_effs (bodyRowsAlg table) args = true →
      ∀ arg ∈ args.toList, CompilesBlk host root k arg
  | .nil, _, arg, member => by
    simp only [Effs.toList, List.not_mem_nil] at member
  | .cons head tail, he, arg, member => by
    have hhead : BodyRows table head = true := (Bool.and_eq_true_iff.mp he).1
    have htail : cata_effs (bodyRowsAlg table) tail = true := (Bool.and_eq_true_iff.mp he).2
    have hm : arg = head ∨ arg ∈ tail.toList := List.mem_cons.mp member
    cases hm with
    | inl same =>
      subst arg
      exact compilesBlk_body host root k hcall hinvoke head hhead
    | inr rest => exact compilesBlk_args host root k hcall hinvoke tail htail arg rest
end

/-- Step of `rows-block-host`, R6. Consumer: `compilesBlk_root`.
Reach: `BodyRows` inside a `BlockRows` root at every meaning budget.
The local relation uses empty context. No machine progress or host conformance follows. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem compilesBlk {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (hroot : BlockRows table root = true) :
    ∀ k e, BodyRows table e = true → CompilesBlk host root k e := by
  intro k
  induction k with
  | zero =>
    exact compilesBlk_body host root 0 (compilesBlk_call_zero host root)
      (fun index request args _ => compilesBlk_invoke_zero host root index request args)
  | succ k ih =>
    have hbodies : ∀ body ∈ bodiesOf root, CompilesBlk host root k body :=
      fun body member => ih body (bodiesOf_blockRows table root hroot body member)
    exact compilesBlk_body host root (k + 1)
      (fun j request => compilesBlk_call_succ host root k j request hbodies)
      (fun index request args hargs =>
        compilesBlk_invoke_succ host root k index request args hbodies hargs)

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
