import Effect4.Laws.Program.Typed.Assembly
import Effect4.Laws.Program.Handles.Layer
import Effect4.Laws.Program.PathFold
import Effect4.Laws.Program.ExpandFix
import Effect4.Laws.Program.Typed.Commands.Finish

/-!
# The layer family's arm, and M5 unconditional

Concept 2 of `docs/core/semantics.md` (`residual-program-typing`), claim `denote-typed`: the
denotation of a checked program is typed at its certificate by the ambient judgment
(`AmbientProg`, decisions rows 148 and 349): at every world `J` ranges over, at every service row
the fiber's context covers. `childDenotes_upto` (`Typed/Denotation.lean`) assembles every arm of
`denoteR` by induction on fuel except the layer family's, which it takes as the hypothesis
`ProvideLayerArm` (decisions row 176 (b)). This module proves that hypothesis at every source
(`provideLayerArm`), so M5's two goals close without a fragment premise: the fundamental property
(`denotesTyped`) and the load (`loadsTyped`, `load_typed`), through the load connector of
`Typed/Commands/Finish.lean`.

A layer's build answers the context of its output row (`buildTy`, `Typed/Admission.lean`): the
typed context `Context<ROut>` at the layer's checked error type, run at the layer's requirement
row. Each constructor's build keeps that, read through rc.112's layer code line by line:

* **The leaves** (`succeed`, `effect`, `effectDiscard`): one binding at its key's declared
  carrier, or none. An effect's body runs as the installed region `construct` under the layer's
  scope (`construction_typed`, an instance of `ambient_updateContext`); the region's dynamic
  typing is the body bridge's (`Typed/Body.lean`).
* **The memo table** (decisions row 187): a memo cell is declared at the layer's columns, so a
  shared build is typed where it is awaited (`memoize_typed`).
* **The dependency** (`provide`, `provideMerge`): the dependency's context covers its output row,
  so the dependent region runs under it with its requirement row discharged
  (`ambient_updateContext_provide`); `provideMerge` answers both outputs (`combineWith_exit`).
* **The merge** (decisions row 186): the siblings are forked and awaited at the positional
  certificate (`fiberPre`'s tuple of per-target exit columns), so every sibling's context is among
  the awaited ones, and the merged context covers the union of their outputs
  (`mergeContexts_exit`); a failure's reasons fit the joined error column.
* **The protocol** (`provideLayer_arm`): the scope made, the memo map forked, the build, the body
  under `provideContext(built)` at child 1 with the layer's output discharged, the scope closed
  with the exit; the node's error column is the join of the body's and the layer's
  (`Checker.inv_provideLayer`).

Every theorem here is a lemma about the residual judgment over rc.112's layer code; none states a
runtime property beyond what `AmbientProg` means (`Typed/Residual.lean`). It is safety, not
progress. Host boundary: none — the layer family has no external reply.
-/

set_option autoImplicit false

namespace Effect4.Program.Typed

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote

/-! ## Typed contexts

A layer build answers a typed context: a context value whose services fit their keys' carriers,
which holds every key of a row, each key declared. Every way a build makes one — a single
binding, the empty map, the current memo map added, a right-biased merge, `mergeAll` — keeps
it. -/

/-- A typed context's parts: the context read back, its services fitting, the row held, every key
of the row declared. -/
theorem contextOf_parts {w : World} {v : Val} {keys : Env.Requirement}
    (h : Fits w v (.contextOf keys)) :
    ∃ ctx, Val.context? v = some ctx ∧ ServicesFit w ctx.services ∧ ctx.services.Satisfies keys ∧
      ∀ key ∈ keys.elems, (w.serviceTy key).isSome = true := by
  obtain ⟨ctx, decoded, services, coverage, members⟩ := fits_contextOf_inv h
  refine ⟨ctx, decoded, services, coverage, fun key member => ?_⟩
  obtain ⟨carrier, _, declared, _, _⟩ := members key member
  rw [declared]
  rfl

/-- `Context.add(key, v)` at a key the world's table types nothing keeps the services fitting. -/
theorem servicesFit_addV_undeclared {w : World} {s : Env.Ctx} {key : ServiceKey} {v : Val}
    (hs : ServicesFit w s) (hkey : w.serviceTy key = none) (hlive : Live w v) :
    ServicesFit w (s.addV key v) := by
  refine ⟨fun key' sv sty hget hty => ?_, entriesLive_addV hlive hs.2⟩
  by_cases hk : key' = key
  · subst hk
    rw [hkey] at hty
    cases hty
  · rw [Env.Context.getV_addV_other _ _ _ _ hk] at hget
    exact hs.1 key' sv sty hget hty

/-- Adding a binding keeps every row a context holds. -/
theorem satisfies_addV {s : Env.Ctx} {keys : Env.Requirement} (key : ServiceKey) (v : Val)
    (h : s.Satisfies keys) : (s.addV key v).Satisfies keys := by
  intro other member
  show ((s.addV key v).getV other).isSome = true
  by_cases same : other = key
  · subst same
    rw [Env.Context.getV_addV_same]
    rfl
  · rw [Env.Context.getV_addV_other _ _ _ _ same]
    exact h other member

/-- A fold of merges from a context holding a row holds it. -/
theorem satisfies_foldl_keeps (keys : Env.Requirement) :
    ∀ (rest : List Env.Ctx) (acc : Env.Ctx), acc.Satisfies keys →
      (rest.foldl Env.Context.merge acc).Satisfies keys
  | [], _, h => h
  | e :: rest, acc, h => satisfies_foldl_keeps keys rest (acc.merge e)
      (Provision.satisfies_merge_left acc e keys h)

/-- A fold of merges over a context holding a row holds it. -/
theorem satisfies_foldl_gains (keys : Env.Requirement) :
    ∀ (rest : List Env.Ctx) (acc c : Env.Ctx), c ∈ rest → c.Satisfies keys →
      (rest.foldl Env.Context.merge acc).Satisfies keys
  | [], _, _, h, _ => nomatch h
  | e :: rest, acc, c, h, hc => by
    rcases List.mem_cons.mp h with rfl | h
    · exact satisfies_foldl_keeps keys rest (acc.merge c) (Provision.satisfies_merge_right acc c keys hc)
    · exact satisfies_foldl_gains keys rest (acc.merge e) c h hc

/-- **`Context.mergeAll` keeps every merged row** (`Layer.ts:1600`): each context's keys survive the
right-biased merges. -/
theorem satisfies_mergeAll (keys : Env.Requirement) :
    ∀ (cs : List Env.Ctx) (c : Env.Ctx), c ∈ cs → c.Satisfies keys →
      (Env.Context.mergeAll cs).Satisfies keys
  | [], _, h, _ => nomatch h
  | d :: rest, c, h, hc => by
    show (rest.foldl Env.Context.merge d).Satisfies keys
    rcases List.mem_cons.mp h with rfl | h
    · exact satisfies_foldl_keeps keys rest c hc
    · exact satisfies_foldl_gains keys rest d c h hc

/-- `Context.mergeAll` (`Layer.ts:1600`) keeps the services fitting: a left fold of merges. -/
theorem servicesFit_mergeAll {w : World} : ∀ (cs : List Env.Ctx), (∀ c ∈ cs, ServicesFit w c) →
    ServicesFit w (Env.Context.mergeAll cs)
  | [], _ => servicesFit_empty w
  | c :: rest, h => by
    show ServicesFit w (rest.foldl Env.Context.merge c)
    exact foldl_merge rest c (h c (List.mem_cons_self ..)) fun d hd => h d (List.mem_cons_of_mem _ hd)
where
  foldl_merge : ∀ (cs : List Env.Ctx) (acc : Env.Ctx), ServicesFit w acc →
      (∀ c ∈ cs, ServicesFit w c) → ServicesFit w (cs.foldl Env.Context.merge acc)
    | [], _, hacc, _ => hacc
    | d :: rest, acc, hacc, h =>
      foldl_merge rest (acc.merge d) (servicesFit_merge hacc (h d (List.mem_cons_self ..)))
        fun e he => h e (List.mem_cons_of_mem _ he)

/-- A value at an exit type is the image of the exit it reads back as, so that exit fits there. -/
theorem fitsExit_of_exitOfVal {w : World} {v : Val} {a e : Ty} {ex : ExitV}
    (h : Fits w v (.exitOf a e)) (hex : exitOfVal v = some ex) :
    FitsExit w ⟨a, e, Env.Requirement.empty⟩ ex := by
  have hv : v = reifyExitVal ex := by
    rw [reifyExitVal_eq_exitImage]
    exact exitImage.ofVal_exact hex
  subst hv
  exact h

/-- A present memo map's handle is a member of the memo map type (decisions row 187, amended by
F-WF). -/
theorem fits_memoMap (w : World) (o : MemoMapId) (h : MemoLive w o) : Fits w (Val.memoMap o) Ty.memoMap := by
  show HandleFits w HandleKind.memoMap.byte o.index Ty.memoMapTarget
  exact ⟨rfl, h⟩

/-- A member of the memo map type is a memo map's handle. -/
theorem fits_memoMap_inv {w : World} {y : Val} (h : Fits w y Ty.memoMap) :
    ∃ o, y = Val.memoMap o ∧ MemoLive w o := by
  simp only [Fits, FitsAt, Ty.memoMap] at h
  split at h
  · rename_i kind index
    simp only [HandleFits] at h
    split at h
    · exact absurd h.1 (by decide)
    · rename_i hk
      exact ⟨⟨index⟩, by rw [HandleKind.ofByte?_exact hk]; rfl, h.2⟩
    · exact absurd h.1 (by decide)
    · exact h.elim
  · exact absurd h (by decide)
  · exact absurd h.1 (by decide)

section Builds

variable {root : ProgramSource}

/-! ## The build's steps at the ambient judgment

A build reads the context only through its installs (`ambient_updateContext`) and its forks.
Every other step is administrative, typed at the constant-row position of its type: the
continuation runs at the same row. -/

/-- The value sequence at a constant row: the body's success continues, its failure passes below
the result's error column. A step of every build below. -/
theorem ambient_seqGuard {w : World} {available : Env.Requirement} {mid T : EffTy}
    {a : RProgram} {K : ExitV → RProgram}
    (ha : AmbientProg root w available ((mid, available, available) : AmbientPosition) a)
    (herr : Ty.subN mid.error T.error = true)
    (hrun : ∀ later, w.leHost later → ∀ v, Fits later v mid.answer →
      AmbientProg root later available ((T, available, available) : AmbientPosition)
        (K (.success v))) :
    AmbientProg root w available ((T, available, available) : AmbientPosition)
      ((guardR .onSuccess a).bind K) := by
  refine ambient_guardBind root ha (fun later ordered exit arm payload => ?_)
    (fun later ordered exit payload absent => ?_) (Row.subset_refl _)
  · cases exit with
    | success v => exact hrun later ordered v payload.1.1
    | failure c => exact Bool.noConfusion arm
  · cases exit with
    | success v => exact Bool.noConfusion absent
    | failure c => exact ⟨exitOk_failure_of_errorN herr payload.1, Row.subset_refl _⟩

/-- A store step at a constant row: the store row's pre, its post at every later world. -/
theorem ambient_store {w : World} {available : Env.Requirement} {T : EffTy} {op : SyncOp}
    {k : Val → RProgram} (cert : StoreCert op) (pre : storePre root w op cert)
    (notForeign : ∀ scope capture, op ≠ .scopeAdd scope (.foreign capture))
    (next : ∀ later, w.leHost later → ∀ ans, storePost later op cert ans →
      AmbientProg root later available ((T, available, available) : AmbientPosition) (k ans)) :
    AmbientProg root w available ((T, available, available) : AmbientPosition) (.vis (.inl op) k) :=
  .store cert ⟨pre, fun scope capture same => absurd same (notForeign scope capture)⟩ next
    ⟨Row.subset_refl _, Row.subset_refl _⟩

/-- An administrative fiber step at a constant row: the type-only pre and post
(`ambientFiberPre_of_admin`, `fiberPost_of_admin`), the row unchanged. -/
theorem ambient_fiberAdmin {w : World} {available : Env.Requirement} {T : EffTy} {op : FiberOp}
    {k : op.answer → RProgram} (admin : adminOp op = true)
    (notGuard : ∀ kind, op ≠ .guard_ kind) (notUnguard : ∀ exit, op ≠ .unguard exit)
    (notFinish : ∀ exit, op ≠ .finishFinalizer exit)
    (notScopeExit : ∀ previous scope exit, op ≠ .scopeExit previous scope exit)
    (cert : FiberCert op) (pre : fiberPre root w op cert)
    (next : ∀ later, w.leHost later → ∀ ans, fiberPost later op cert ans →
      AmbientProg root later available ((T, available, available) : AmbientPosition) (k ans)) :
    AmbientProg root w available ((T, available, available) : AmbientPosition) (.vis (.inr op) k) := by
  refine .fiber notGuard notUnguard notFinish notScopeExit cert
    (ambientFiberPre_of_admin root available admin pre) (fun later ordered ans post => ?_)
    ⟨Row.subset_refl _, Row.subset_refl _⟩
  show AmbientProg root later (ambientFiberInput available op ans) _ _
  rw [ambientFiberInput_admin available ans admin]
  exact next later ordered ans (fiberPost_of_admin available admin post)

/-- **Every finalizer but a foreign capture's release is administrative code** (`denoteFin`): an
interruption, a scope's close or removal, a release's exit, a park, a children's await, a memo
entry's release and completion. -/
theorem denoteFin_admin (fin : FinName) (notForeign : ∀ capture, fin ≠ .foreign capture)
    (ex : ExitV) : AdminCode (denoteFin fin ex) := by
  cases fin with
  | foreign capture => exact absurd rfl (notForeign capture)
  | interruptFiber fiber skipSelf => cases skipSelf <;> exact AdminCode.fiberVal _ rfl rfl
  | closeChildScope scope => exact .fiber _ _ rfl fun _ => .pure _
  | detachFromParent parent key => exact .store _ _ (fun _ _ h => nomatch h) fun _ => .pure _
  | release label fails => exact .pure _
  | parkThen slot => exact .fiber _ _ rfl fun _ => .pure _
  | awaitNewChildren snapshot => exact AdminCode.fiberVal _ rfl rfl
  | closeChildOnFailure scope =>
    cases ex with
    | success v => exact .pure _
    | failure c => exact .fiber _ _ rfl fun _ => .pure _
  | memoEntry layer memoMap =>
    refine AdminCode.bind (AdminCode.guard _ (.store _ _ (fun _ _ h => nomatch h) fun _ => .pure _))
      fun e => ?_
    cases e with
    | failure c => exact .pure _
    | success v =>
      simp only [seqR]
      split
      · exact .fiber _ _ rfl fun _ => .pure _
      · exact .pure _
  | memoDone layer memoMap => exact .store _ _ (fun _ _ h => nomatch h) fun _ => .pure _

/-- `scopeAddFinalizerExit` is administrative for every finalizer but a foreign capture's release. -/
theorem scopeAddR_admin (scope : Nat) (fin : FinName)
    (notForeign : ∀ capture, fin ≠ .foreign capture) : AdminCode (scopeAddR scope fin) := by
  unfold scopeAddR
  refine AdminCode.bind (AdminCode.guard _ (.store _ _ (fun _ capture same => ?_) fun _ => .pure _))
    fun e => ?_
  · cases same
    exact notForeign capture rfl
  · cases e with
    | failure c => exact .pure _
    | success v =>
      simp only [seqR]
      split
      · exact .pure _
      · split
        · exact (AdminCode.guard _ (denoteFin_admin fin notForeign _)).bind (AdminCode.seq _)
        · exact .pure _

/-- `scopeAddFinalizerExit` (`internal/effect.ts:3847-3858`) at a present scope and an admitted
finalizer: `unit` when it registers, else the closing exit read back and the finalizer run now
(`finalizerTyped_of_admitted`), then `unit`. -/
theorem scopeAdd_typed {w : World} {scope : Nat} {fin : FinName} (hlive : ScopeLive w scope)
    (hadm : FinalizerAdmitted root w fin) :
    TypedProg root w (EffTy.pure .unit) (scopeAddR scope fin) := by
  unfold scopeAddR
  refine seqGuard_typed root
    (mid := ⟨.union .unit (.exitOf .unknown .unknown), .never, Env.Requirement.empty⟩) ?_
    (Bounds.subN_never _) (fun w' o v hv => ?_)
  · refine TypedProg.store (op := .scopeAdd scope fin) (cert := ()) ⟨hlive, hadm⟩
      (fun w'' _ ans post => .pure (strongExit_success w'' _ ans ?_))
    rcases post with rfl | ⟨ex, rfl, hex⟩
    · exact Or.inl trivial
    · exact Or.inr hex
  · simp only [seqR]
    rcases hv with hunit | hexit
    · rw [fits_unit_inv hunit, if_pos rfl]
      exact .pure (strongExit_success w' _ _ trivial)
    · obtain ⟨ex, hexv⟩ := exitOfVal_of_fits hexit
      have hne : v ≠ Val.unit := by
        intro h
        subst h
        exact nomatch hexv
      rw [if_neg hne, hexv]
      exact seqGuard_typed root (mid := ⟨.unknown, .never, Env.Requirement.empty⟩)
        (finalizerTyped_of_admitted root w fin hadm w' o ex (fitsExit_of_exitOfVal hexit hexv))
        (Bounds.subN_never _) (fun w'' _ _ _ => .pure (strongExit_success w'' _ _ trivial))

/-- `fromBuild`'s finalizer (`Layer.ts:343`): the layer scope closed on failure only. -/
theorem closeChildOnFailure_typed {w : World} {child : Nat} (hlive : ScopeLive w child)
    (ex : ExitV) (hex : FitsExit w ⟨.unknown, .unknown, Env.Requirement.empty⟩ ex) :
    TypedProg root w (EffTy.pure .unit) (denoteFin (.closeChildOnFailure child) ex) := by
  cases ex with
  | success v => exact .pure (strongExit_success w _ _ trivial)
  | failure c =>
    exact TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ _ _ h => nomatch h) () ⟨hlive, hex⟩ (fun _ _ _ post => .pure post)

/-- `scopeAddFinalizerExit` at the ambient judgment, at every finalizer but a foreign capture's
release: the type-only proof (`scopeAdd_typed`) lifted (`ambientProg_of_admin`). -/
theorem ambient_scopeAdd {w : World} {available : Env.Requirement} {scope : Nat} {fin : FinName}
    (hlive : ScopeLive w scope) (hadm : FinalizerAdmitted root w fin)
    (notForeign : ∀ capture, fin ≠ .foreign capture) :
    AmbientProg root w available ((EffTy.pure .unit, available, available) : AmbientPosition)
      (scopeAddR scope fin) :=
  ambientProg_of_admin root (scopeAdd_typed hlive hadm) (scopeAddR_admin scope fin notForeign)
    available

/-- **`fromBuild`** (`Layer.ts:333-345`): the layer scope forked from the caller's present one, the
inner build inside it under the finalizer that closes it on failure. -/
theorem fromBuild_typed {w : World} {available : Env.Requirement} {T : EffTy} {scope : Nat}
    {inner : Nat → RProgram} (hlive : ScopeLive w scope)
    (hinner : ∀ later, w.leHost later → ∀ child, ScopeLive later child →
      AmbientProg root later available ((T, available, available) : AmbientPosition) (inner child)) :
    AmbientProg root w available ((T, available, available) : AmbientPosition)
      (fromBuildR scope inner) := by
  unfold fromBuildR
  refine ambient_seqGuard (mid := EffTy.pure Ty.scope)
    (ambient_store (op := .scopeFork scope .sequential) () hlive (fun _ _ h => nomatch h)
      (fun later _ ans post =>
        .pure ⟨strongExit_success later _ ans post, Row.subset_refl _⟩ ⟨Row.subset_refl _, Row.subset_refl _⟩))
    (Bounds.subN_never _) (fun later o v hv => ?_)
  obtain ⟨child, rfl, hchild⟩ := fits_scope_inv hv
  simp only [seqR, Val.scope?_scopeHandle]
  exact ambient_onExit_typed root (cleanupType := EffTy.pure .unit) (Ty.subN_refl _)
    (Ty.subN_refl _) (Bounds.subN_never _) (hinner later o child hchild)
    (fun later' o' ex hok => ambientProg_of_admin root
      (closeChildOnFailure_typed (scopeLive_mono o'.1 hchild) ex (fitsExit_unknown hok.1))
      (denoteFin_admin (.closeChildOnFailure child) (fun _ h => nomatch h) ex) available)

/-- **`getOrElseMemoize`** (`Layer.ts:445-457`) at a checked layer leaf: the counted suspend, the
lookup at the layer's columns; a hit registers the entry finalizer on the caller's present scope
and awaits the entry's deferred, declared at the layer's output context and error (the memo-table
clause, decisions row 187); a miss builds the entry at those columns, registers its finalizer and
runs the construction into the layer scope under the finalizer completing the entry with the
construction's exit. -/
theorem memoize_typed {w : World} {available : Env.Requirement} {q : Point} {m : MemoMapId}
    {scope : Nat} {lt : LayerTy} {l : LayerTerm NativeOp} {construction : Nat → RProgram}
    (hat : Node.at_ (.eff root.program) q.path = some (.layer l))
    (hcheck : Checker.checkLayer (root.scopeSig q.path) q.path (LayerTerm.expandIn root.program l) =
      .ok lt)
    (hlive : ScopeLive w scope)
    (hcons : ∀ later, w.leHost later → ∀ layerScope, ScopeLive later layerScope →
      AmbientProg root later available ((buildTy lt, available, available) : AmbientPosition)
        (construction layerScope)) :
    AmbientProg root w available ((buildTy lt, available, available) : AmbientPosition)
      (memoizeR q m scope construction) := by
  unfold memoizeR
  refine ambient_suspendR_typed root (Row.subset_refl _) (fun w1 o1 => ?_)
  refine ambient_seqGuard
    (mid := ⟨.union .unit (.prod (.deferredOf (.contextOf lt.out) lt.error) Ty.memoMap),
      .never, Env.Requirement.empty⟩) ?_ (Bounds.subN_never _) (fun w2 o2 v hv => ?_)
  · refine ambient_store (op := .memoGet q.layerKey m) (.contextOf lt.out, lt.error)
      ⟨l, lt, hat, hcheck, rfl⟩ (fun _ _ h => nomatch h) (fun w' _ ans post => ?_)
    refine .pure ⟨strongExit_success w' _ ans ?_, Row.subset_refl _⟩ ⟨Row.subset_refl _, Row.subset_refl _⟩
    rcases post with rfl | ⟨cell, owner, hhit, hdecl, hpresent⟩
    · exact Or.inl trivial
    · rw [Val.memoHit?_exact hhit]
      exact Or.inr ⟨⟨_, _, hdecl, ⟨Ty.subN_refl _, Ty.subN_refl _⟩, ⟨Ty.subN_refl _, Ty.subN_refl _⟩⟩,
        fits_memoMap w' owner hpresent⟩
  · have o12 := leHost_trans _ _ _ o1 o2
    simp only [seqR]
    rcases hv with hunit | hhit
    · -- a miss: the entry built at the layer's columns, the construction into its scope
      rw [fits_unit_inv hunit]
      show AmbientProg root w2 available _ (if Val.unit = Val.unit then _ else _)
      rw [if_pos rfl]
      refine ambient_seqGuard (mid := EffTy.pure Ty.scope) ?_ (Bounds.subN_never _)
        (fun w3 o3 u hu => ?_)
      · exact ambient_store (op := .memoBuild q.layerKey m) (.contextOf lt.out, lt.error)
          ⟨l, lt, hat, hcheck, rfl⟩ (fun _ _ h => nomatch h)
          (fun w'' _ ans post =>
            .pure ⟨strongExit_success w'' _ ans post, Row.subset_refl _⟩ ⟨Row.subset_refl _, Row.subset_refl _⟩)
      · obtain ⟨layerScope, rfl, hls⟩ := fits_scope_inv hu
        simp only [seqR, Val.scope?_scopeHandle]
        have o13 := leHost_trans _ _ _ o12 o3
        refine ambient_seqGuard (mid := EffTy.pure .unit)
          (ambient_scopeAdd (scopeLive_mono o13.1 hlive) trivial (fun _ h => nomatch h))
          (Bounds.subN_never _) (fun w4 o4 _ _ => ?_)
        simp only [seqR]
        exact ambient_onExit_typed root (cleanupType := EffTy.pure .unit) (Ty.subN_refl _)
          (Ty.subN_refl _) (Bounds.subN_never _)
          (hcons w4 (leHost_trans _ _ _ o13 o4) layerScope (scopeLive_mono o4.1 hls))
          (fun w5 _ ex hex => ambient_store (op := .memoComplete q.layerKey m ex) ()
            ⟨l, lt, hat, hcheck, exitOk_widen (Ty.subN_refl _) (Ty.subN_refl _) hex⟩
            (fun _ _ h => nomatch h) (fun w6 _ ans post => by
              subst post
              exact .pure ⟨strongExit_success w6 _ _ trivial, Row.subset_refl _⟩ ⟨Row.subset_refl _, Row.subset_refl _⟩))
    · -- a hit: the entry finalizer registered, then the await of the entry's deferred
      obtain ⟨x, y, rfl, hx, hy⟩ := (fits_prod_iff w2 v _ _).mp hhit
      obtain ⟨c, rfl, hdecl⟩ := fits_deferredOf_inv hx
      obtain ⟨o, rfl, _⟩ := fits_memoMap_inv hy
      rw [show Val.memoHit? (.list [Val.promise c, Val.memoMap o]) = some (c, o) from
        Val.memoHit?_memoHit c o]
      refine ambient_seqGuard (mid := EffTy.pure .unit)
        (ambient_scopeAdd (scopeLive_mono o12.1 hlive) trivial (fun _ h => nomatch h))
        (Bounds.subN_never _) (fun w3 o3 _ _ => ?_)
      simp only [seqR]
      obtain ⟨a', e', hpi, ha, he⟩ := promiseDeclared_mono o3 hdecl
      exact ambient_fiberAdmin rfl (fun _ h => nomatch h) (fun _ h => nomatch h)
        (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) (⟨a', e', Env.Requirement.empty⟩ : EffTy)
        ⟨a', e', hpi, Ty.sub_refl _, Ty.sub_refl _⟩
        (fun w4 _ ans post => .pure ⟨exitOk_widen ha.1 he.1 post,
          by cases ans <;> exact Row.subset_refl _⟩ ⟨Row.subset_refl _, Row.subset_refl _⟩)

/-- A present memo map's handle is live (row 187, amended by F-WF). -/
theorem live_memoMap (w : World) (m : MemoMapId) (h : MemoLive w m) : Live w (Val.memoMap m) :=
  live_kind (k := .memoMap) h

/-- The machine's current-memo-map key types nothing (`SigApp.serviceTy`: a reserved name below
`firstFreeName` other than the scope's). -/
theorem serviceTy_currentMemoMapKey (app : SigApp) : app.serviceTy Env.currentMemoMapKey = none :=
  rfl

/-- `Context.make(key, value)` or `Context.empty()` over a leaf's answer (`bindServiceR`): the
context of the construction's output row, its one binding at its key's declared carrier. -/
theorem bindService_exit {w : World} {key : Option ServiceKey} {v : Val}
    (hfit : ∀ k, key = some k → ∃ sty, w.serviceTy k = some sty ∧ FlatFits w v sty)
    (hlive : Live w v) :
    ∃ ctx, bindServiceR key v = .pure (.success (Val.context ctx)) ∧
      Fits w (Val.context ctx) (.contextOf (constructOut key)) := by
  cases key with
  | none =>
    refine ⟨Ctx.withServices Env.Context.empty, rfl,
      fits_contextOf_intro (servicesFit_empty w) ?_ ?_⟩
    · intro key member
      exact absurd member (Row.not_mem_empty key)
    · intro key member
      exact absurd member (Row.not_mem_empty key)
  | some k =>
    obtain ⟨sty, hsty, hflat⟩ := hfit k rfl
    refine ⟨Ctx.withServices (Env.Context.empty.addV k v), rfl,
      fits_contextOf_intro (servicesFit_addV (servicesFit_empty w) hsty hflat hlive)
        (Provision.satisfies_single_addV k v) ?_⟩
    intro other member
    have same : other = k := (Row.mem_singleton k other).mp member
    subst other
    rw [hsty]
    rfl

/-- `Context.add(CurrentMemoMap, memoMap)` over a built context (`addCurrentMemoMapR`): the context
read back, the memo map added under a key that types nothing; the output row stays held. -/
theorem addCurrentMemoMap_exit {w : World} {m : MemoMapId} {v : Val} {out : Env.Requirement}
    (htie : Tied root w) (hm : MemoLive w m) (hv : Fits w v (.contextOf out)) :
    ∃ v', addCurrentMemoMapR m v = .pure (.success v') ∧ Fits w v' (.contextOf out) := by
  obtain ⟨ctx, hctx, hsvc, hcov, hdecl⟩ := contextOf_parts hv
  unfold addCurrentMemoMapR
  rw [hctx]
  refine ⟨_, rfl, fits_contextOf_intro (servicesFit_addV_undeclared hsvc ?_
    (live_memoMap w m hm)) (satisfies_addV _ _ hcov) hdecl⟩
  rw [htie.services]
  exact serviceTy_currentMemoMapKey _

/-- What `provideWith`'s combiner answers: `provide` the dependent's output, `provideMerge` both
outputs (`LayerTy.provide`, `LayerTy.provideMerge`). -/
def combineOut : CombineMode → Env.Requirement → Env.Requirement → Env.Requirement
  | .provide, self, _ => self
  | .provideMerge, self, that => Row.union self that

/-- `f(merged, context)` (`Layer.ts:1923`): `provide` answers the dependent's context as read,
`provideMerge` the dependency's map merged under it, which holds both outputs. -/
theorem combineWith_exit {w : World} (mode : CombineMode) {that : Env.Ctx} {u : Val}
    {thatOut selfOut : Env.Requirement} (thatFit : ServicesFit w that)
    (thatCovers : that.Satisfies thatOut)
    (thatDeclared : ∀ key ∈ thatOut.elems, (w.serviceTy key).isSome = true)
    (hu : Fits w u (.contextOf selfOut)) :
    ∃ v, combineWithR mode that u = .pure (.success v) ∧
      Fits w v (.contextOf (combineOut mode selfOut thatOut)) := by
  obtain ⟨merged, hctx, hsvc, hcov, hdecl⟩ := contextOf_parts hu
  unfold combineWithR
  rw [hctx]
  cases mode with
  | provide =>
    refine ⟨_, rfl, ?_⟩
    rw [← Val.context?_exact hctx]
    exact hu
  | provideMerge =>
    refine ⟨_, rfl, fits_contextOf_intro (servicesFit_merge thatFit hsvc)
      (Provision.satisfies_union_of _ _ _ (Provision.satisfies_merge_right _ _ _ hcov)
        (Provision.satisfies_merge_left _ _ _ thatCovers)) fun key member => ?_⟩
    rcases (Row.mem_union key selfOut thatOut).mp member with mine | theirs
    · exact hdecl key mine
    · exact thatDeclared key theirs

/-- **`provideWith`** (`Layer.ts:1915-1923`): the dependency built, the dependent region under
`provideContext(context)` with the dependency's output discharged from its requirement row
(`ambient_updateContext_provide`), then the combiner; both builds' errors below the result's. -/
theorem provideWith_typed {w : World} {available : Env.Requirement} {dependency : RProgram}
    {dependent : Region} {mode : CombineMode} {T : EffTy} {that self : LayerTy}
    (hdep : AmbientProg root w available ((buildTy that, available, available) : AmbientPosition)
      dependency)
    (hdnt : RegionTyped root w dependent (buildTy self))
    (hstack : RegionStackTyped root w available dependent)
    (needed : Row.Subset (Row.diff self.requires that.out) available)
    (hT : T.answer = .contextOf (combineOut mode self.out that.out))
    (herrd : Ty.subN that.error T.error = true) (herrs : Ty.subN self.error T.error = true) :
    AmbientProg root w available ((T, available, available) : AmbientPosition)
      (provideWithR dependency dependent mode) := by
  unfold provideWithR
  refine ambient_seqGuard hdep herrd (fun w1 o1 v hv => ?_)
  obtain ⟨ctx, hctx, hsvc, hcov, hdecl⟩ := contextOf_parts hv
  have same := Val.context?_exact hctx
  subst same
  simp only [seqR, Val.context?_context]
  refine ambient_seqGuard (mid := buildTy self)
    (ambient_updateContext_provide root available available self.requires that.out ctx hv needed
      (Row.subset_refl _) (buildTy self) dependent (regionTyped_mono o1 hdnt)
      (regionStackTyped_mono o1 hstack) (.provide ctx.services) (fun _ => rfl))
    herrs (fun w2 o2 u hu => ?_)
  simp only [seqR]
  obtain ⟨v', hv', fits'⟩ := combineWith_exit mode (servicesFit_mono o2 hsvc) hcov
    (fun key member => by rw [le_serviceTy o2.1]; exact hdecl key member) hu
  rw [hv']
  refine .pure ⟨strongExit_success w2 _ _ ?_, Row.subset_refl _⟩ ⟨Row.subset_refl _, Row.subset_refl _⟩
  show Fits w2 v' T.answer
  rw [hT]
  exact fits'

/-- **`buildWithMemoMap`** (`Layer.ts:756-765`): the build through the map under
`provideService(CurrentMemoMap)`, the region `buildAdding` adding the map to its answer; the key
types nothing, and the installed context keeps the entry row. -/
theorem buildWithMemoMap_typed {w : World} {available : Env.Requirement} {point : Point}
    {m : MemoMapId} {scope : Nat} {lt : LayerTy} (htie : Tied root w)
    (hpt : LayerPointTyped root w point lt) (hlive : ScopeLive w scope) (hm : MemoLive w m)
    (hreq : Row.Subset lt.requires available)
    (hstack : AmbientStackTyped root w available (scopeParams root.program point.path)
      point.params) :
    AmbientProg root w available ((buildTy lt, available, available) : AmbientPosition)
      (buildWithMemoMapR point m scope) := by
  unfold buildWithMemoMapR
  refine ambient_updateContext root available available lt.requires (Row.subset_refl _)
    (buildTy lt) (.buildAdding point m scope) ⟨lt, rfl, hpt, hlive, hm⟩ hstack _
    (fun later grew previous members => ?_) (fun previous covered => ?_)
  · refine servicesFit_merge members (servicesFit_addV_undeclared (servicesFit_empty later) ?_
      (live_memoMap later m (memoLive_mono grew.1 hm)))
    rw [(Tied.mono grew htie).services]
    exact serviceTy_currentMemoMapKey _
  · show (previous.merge ((Env.Context.empty : Env.Ctx).addV Env.currentMemoMapKey
        (Val.memoMap m))).Satisfies lt.requires ∧
      (previous.merge ((Env.Context.empty : Env.Ctx).addV Env.currentMemoMapKey
        (Val.memoMap m))).Satisfies available
    exact ⟨Provision.satisfies_merge_left _ _ _ (previous.satisfies_weaken covered hreq),
      Provision.satisfies_merge_left _ _ _ covered⟩

/-- Every reason of awaited exits that fit `Exit<a, e>` fits the error column and is no shape
defect. -/
theorem reasonsOfList_fit {w : World} {a e : Ty} : ∀ (xs : List Val),
    (∀ x ∈ xs, Fits w x (.exitOf a e)) → ∀ r ∈ reasonsOfList xs,
      (match r with
        | .fail err _ => ∃ v, valOfErr err = some v ∧ Fits w v e
        | .die _ _ | .interrupt _ _ => True) ∧
      (match r with
        | .die defect _ => defect ≠ .badName ∧ defect ≠ .notImplemented
        | _ => True)
  | [], _, r, hr => by
    simp only [reasonsOfList] at hr
    exact nomatch hr
  | x :: rest, hall, r, hr => by
    simp only [reasonsOfList, List.mem_append] at hr
    rcases hr with hx | hrest
    · have hfx := hall x (List.mem_cons_self ..)
      simp only [Fits, FitsAt] at hfx
      split at hfx
      · simp only [reasonsOfVal] at hx
        exact nomatch hx
      · rename_i written
        split at hfx
        · rename_i c hc
          simp only [reasonsOfVal, hc, Option.map_some, Option.getD_some] at hx
          exact ⟨hfx.1 r hx, hfx.2 r hx⟩
        · exact hfx.elim
      · exact hfx.elim
    · exact reasonsOfList_fit rest (fun y hy => hall y (List.mem_cons_of_mem _ hy)) r hrest

/-- A fiber's declaration persists at every later world. -/
theorem fiberDeclared_mono {w w' : World} (ord : w.leHost w') {id : FiberId} {a e : Ty}
    (h : FiberDeclared w id a e) : FiberDeclared w' id a e := by
  obtain ⟨fty, hΓ, ha, he⟩ := h
  exact ⟨fty, ord.1.2.1 _ _ hΓ, ha, he⟩

/-- A scope forked from a present one, at a constant row (`scopeFork`'s row). -/
theorem ambient_scopeFork {w : World} {available : Env.Requirement} {scope : Nat}
    {strategy : FinalizerStrategy} (hlive : ScopeLive w scope) :
    AmbientProg root w available ((EffTy.pure Ty.scope, available, available) : AmbientPosition)
      (storeR (.scopeFork scope strategy)) :=
  ambient_store (op := .scopeFork scope strategy) () hlive (fun _ _ h => nomatch h)
    (fun later _ ans post =>
      .pure ⟨strongExit_success later _ ans post, Row.subset_refl _⟩ ⟨Row.subset_refl _, Row.subset_refl _⟩)

/-! ### The merge: the positional await and `Context.mergeAll` -/

/-- A tuple's member is a list holding one item per column. -/
theorem fits_tuple_inv {w : World} {v : Val} {ts : List Ty} (h : Fits w v (.tuple ts)) :
    ∃ xs, v = .list xs ∧ ItemsFit (ts.map (fun t x => Fits w x t)) xs := by
  cases v with
  | list xs => exact ⟨xs, rfl, (fits_tuple w xs ts).mp h⟩
  | _ => exact (h : False).elim

/-- Items fitting their columns in order: each item fits some column, and each column has an
item fitting it. -/
theorem itemsFit_members {α : Type} (P : α → Val → Prop) :
    ∀ (targets : List α) (xs : List Val), ItemsFit (targets.map P) xs →
      (∀ x ∈ xs, ∃ t ∈ targets, P t x) ∧ (∀ t ∈ targets, ∃ x ∈ xs, P t x)
  | [], [], _ => ⟨fun _ h => (nomatch h), fun _ h => (nomatch h)⟩
  | [], _ :: _, h => (h : False).elim
  | _ :: _, [], h => (h : False).elim
  | t :: ts, x :: xs, h => by
    obtain ⟨hx, hrest⟩ := h
    obtain ⟨each, every⟩ := itemsFit_members P ts xs hrest
    refine ⟨fun y hy => ?_, fun s hs => ?_⟩
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨t, List.mem_cons_self .., hx⟩
      · obtain ⟨s, hs, hsy⟩ := each y hy
        exact ⟨s, List.mem_cons_of_mem _ hs, hsy⟩
    · rcases List.mem_cons.mp hs with rfl | hs
      · exact ⟨x, List.mem_cons_self .., hx⟩
      · obtain ⟨y, hy, hsy⟩ := every s hs
        exact ⟨y, List.mem_cons_of_mem _ hy, hsy⟩

/-- A member of a tuple of per-target columns: one item per target, at that target's column. -/
theorem tuple_members {w : World} {α : Type} (f : α → Ty) {targets : List α} {v : Val}
    (h : Fits w v (.tuple (targets.map f))) :
    ∃ xs, v = .list xs ∧ (∀ x ∈ xs, ∃ t ∈ targets, Fits w x (f t)) ∧
      (∀ t ∈ targets, ∃ x ∈ xs, Fits w x (f t)) := by
  obtain ⟨xs, rfl, items⟩ := fits_tuple_inv h
  rw [List.map_map] at items
  exact ⟨xs, rfl, itemsFit_members (fun t x => Fits w x (f t)) targets xs items⟩

/-- A fiber's declared exit columns in a world, or `never` for an undeclared one: the positional
certificate's columns at an await of declared fibers. -/
def gammaCols (w : World) (t : FiberId) : Ty × Ty :=
  ((w.Γ t).map fun fty => (fty.answer, fty.error)).getD (.never, .never)

theorem gammaCols_of {w : World} {t : FiberId} {fty : EffTy} (h : w.Γ t = some fty) :
    gammaCols w t = (fty.answer, fty.error) := by
  unfold gammaCols
  rw [h]
  rfl

/-- The positional certificate's pre at declared fibers: each target at its own columns. -/
theorem positional_pre {w : World} {pairs : List (FiberId × (Env.Requirement × Ty))}
    (declared : ∀ p ∈ pairs, FiberDeclared w p.1 (.contextOf p.2.1) p.2.2) :
    ∀ t ∈ pairs.map Prod.fst, ∃ fty, w.Γ t = some fty ∧ fty.answer.sub (gammaCols w t).1 = true ∧
      fty.error.sub (gammaCols w t).2 = true := by
  intro t ht
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ht
  obtain ⟨fty, hΓ, -, -⟩ := declared p hp
  rw [gammaCols_of hΓ]
  exact ⟨fty, hΓ, Ty.sub_refl _, Ty.sub_refl _⟩

/-- **The positional await of declared fibers**: every awaited exit is some fiber's, below that
fiber's declared columns, and every fiber's exit is among the awaited ones. -/
theorem awaited_columns {w w' : World} {pairs : List (FiberId × (Env.Requirement × Ty))} {v : Val}
    (declared : ∀ p ∈ pairs, FiberDeclared w p.1 (.contextOf p.2.1) p.2.2)
    (h : Fits w' v (.tuple ((pairs.map Prod.fst).map fun t =>
      .exitOf (gammaCols w t).1 (gammaCols w t).2))) :
    ∃ xs, v = .list xs ∧
      (∀ x ∈ xs, ∃ c ∈ pairs.map Prod.snd, Fits w' x (.exitOf (.contextOf c.1) c.2)) ∧
      (∀ c ∈ pairs.map Prod.snd, ∃ x ∈ xs, Fits w' x (.exitOf (.contextOf c.1) c.2)) := by
  obtain ⟨xs, rfl, each, every⟩ := tuple_members _ h
  have convert : ∀ p ∈ pairs, ∀ x, Fits w' x (.exitOf (gammaCols w p.1).1 (gammaCols w p.1).2) →
      Fits w' x (.exitOf (.contextOf p.2.1) p.2.2) := by
    intro p hp x hx
    obtain ⟨fty, hΓ, ha, he⟩ := declared p hp
    rw [gammaCols_of hΓ] at hx
    exact fits_subN w' (subN_exitOf ha he) x hx
  refine ⟨xs, rfl, fun x hx => ?_, fun c hc => ?_⟩
  · obtain ⟨t, ht, hfit⟩ := each x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ht
    exact ⟨p.2, List.mem_map.mpr ⟨p, hp, rfl⟩, convert p hp x hfit⟩
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
    obtain ⟨x, hx, hfit⟩ := every p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩)
    exact ⟨x, hx, convert p hp x hfit⟩

/-- A read-back exit of a typed context: its success's context, its row held. -/
theorem exitContext_parts {w : World} {x c : Val} {keys : Env.Requirement} {e : Ty}
    (hx : Fits w x (.exitOf (.contextOf keys) e)) (hex : exitOfVal x = some (.success c)) :
    ∃ ctx, Val.context? c = some ctx ∧ ServicesFit w ctx.services ∧ ctx.services.Satisfies keys ∧
      ∀ key ∈ keys.elems, (w.serviceTy key).isSome = true :=
  contextOf_parts (fitsExit_of_exitOfVal hx hex)

/-- The contexts read back from awaited exits each fit, when every exit is a typed context's. -/
theorem contextsOfList_services {w : World} {cols : List (Env.Requirement × Ty)} :
    ∀ (xs : List Val) (cs : List Env.Ctx), contextsOfList xs = some cs →
    (∀ x ∈ xs, ∃ c ∈ cols, Fits w x (.exitOf (.contextOf c.1) c.2)) → ∀ c ∈ cs, ServicesFit w c
  | [], cs, h, _ => by
    simp only [contextsOfList, Option.some.injEq] at h
    subst h
    intro c hc
    exact nomatch hc
  | x :: rest, cs, h, hall => by
    simp only [contextsOfList] at h
    split at h
    · rename_i c hx
      split at h
      · rename_i ctx ctxs hctx hrest
        simp only [Option.some.injEq] at h
        subst h
        intro d hd
        rcases List.mem_cons.mp hd with rfl | hd'
        · obtain ⟨col, -, hfit⟩ := hall x (List.mem_cons_self ..)
          obtain ⟨ctx', hctx', hsvc, -, -⟩ := exitContext_parts hfit hx
          rw [hctx] at hctx'
          cases hctx'
          exact hsvc
        · exact contextsOfList_services rest ctxs hrest
            (fun y hy => hall y (List.mem_cons_of_mem _ hy)) d hd'
      · cases h
    · cases h

/-- **Every awaited typed context is merged**: an awaited exit of a typed context reads back as a
context the list holds, which holds the row. -/
theorem contextsOfList_member {w : World} {keys : Env.Requirement} {e : Ty} :
    ∀ (xs : List Val) (cs : List Env.Ctx), contextsOfList xs = some cs → ∀ x ∈ xs,
    Fits w x (.exitOf (.contextOf keys) e) →
    ∃ c ∈ cs, c.Satisfies keys ∧ ∀ key ∈ keys.elems, (w.serviceTy key).isSome = true
  | [], _, _, _, hx, _ => nomatch hx
  | x :: rest, cs, h, y, hy, hfit => by
    simp only [contextsOfList] at h
    split at h
    · rename_i c hx
      split at h
      · rename_i ctx ctxs hctx hrest
        simp only [Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hy with rfl | hy'
        · obtain ⟨ctx', hctx', -, hcov, hdecl⟩ := exitContext_parts hfit hx
          rw [hctx] at hctx'
          cases hctx'
          exact ⟨_, List.mem_cons_self .., hcov, hdecl⟩
        · obtain ⟨d, hd, hcov, hdecl⟩ := contextsOfList_member rest ctxs hrest y hy' hfit
          exact ⟨d, List.mem_cons_of_mem _ hd, hcov, hdecl⟩
      · cases h
    · cases h

/-- Awaited exits of typed contexts none of which failed have their contexts read back. -/
theorem contextsOfList_some {w : World} {cols : List (Env.Requirement × Ty)} : ∀ (xs : List Val),
    (∀ x ∈ xs, ∃ c ∈ cols, Fits w x (.exitOf (.contextOf c.1) c.2)) →
    (xs.any fun x => match exitOfVal x with
      | some (Exit.failure _) => true
      | _ => false) = false →
    ∃ cs, contextsOfList xs = some cs
  | [], _, _ => ⟨[], rfl⟩
  | x :: rest, hall, hnone => by
    rw [List.any_cons, Bool.or_eq_false_iff] at hnone
    obtain ⟨hxnot, hrest⟩ := hnone
    obtain ⟨cs, hcs⟩ :=
      contextsOfList_some rest (fun y hy => hall y (List.mem_cons_of_mem _ hy)) hrest
    obtain ⟨col, -, hfx⟩ := hall x (List.mem_cons_self ..)
    obtain ⟨ex, hex⟩ := exitOfVal_of_fits hfx
    cases ex with
    | failure c =>
      rw [hex] at hxnot
      exact nomatch hxnot
    | success c =>
      obtain ⟨ctx, hctx, -, -, -⟩ := exitContext_parts hfx hex
      exact ⟨ctx.services :: cs, by simp only [contextsOfList, hex, hctx, hcs]⟩

/-- **The merge** (`Layer.ts:1600`) over the awaited exits of typed contexts, one per sibling and
every sibling's among them: every build succeeded, and the merged context holds the union of the
siblings' output rows; or one failed, and the merge fails with the failures' reasons, which fit the
error column (decisions row 186). The refusal is unreachable. -/
theorem mergeContexts_exit {w : World} {xs : List Val} {cols : List (Env.Requirement × Ty)}
    {out : Env.Requirement} {T : EffTy} (hT : T.answer = .contextOf out)
    (each : ∀ x ∈ xs, ∃ c ∈ cols, Fits w x (.exitOf (.contextOf c.1) c.2))
    (every : ∀ c ∈ cols, ∃ x ∈ xs, Fits w x (.exitOf (.contextOf c.1) c.2))
    (herr : ∀ c ∈ cols, Ty.subN c.2 T.error = true)
    (hout : ∀ key ∈ out.elems, ∃ c ∈ cols, key ∈ c.1) :
    ∃ ex, mergeContextsR (.list xs) = .pure ex ∧ ExitOk w T ex := by
  have uniform : ∀ x ∈ xs, Fits w x (.exitOf .unknown T.error) := fun x hx => by
    obtain ⟨c, hc, hfit⟩ := each x hx
    exact fits_subN w (subN_exitOf (subN_unknown _) (herr c hc)) x hfit
  have hco : contextsOf (.list xs) = contextsOfList xs := rfl
  unfold mergeContextsR
  rw [hco]
  cases hc : contextsOfList xs with
  | some cs =>
    refine ⟨_, rfl, strongExit_success w T _ ?_⟩
    rw [hT]
    refine fits_contextOf_intro (ctx := Ctx.withServices (Env.Context.mergeAll cs))
      (servicesFit_mergeAll cs (contextsOfList_services xs cs hc each))
      (fun key member => ?_) (fun key member => ?_)
    · obtain ⟨c, hcol, hkey⟩ := hout key member
      obtain ⟨x, hx, hfit⟩ := every c hcol
      obtain ⟨d, hd, hcov, -⟩ := contextsOfList_member xs cs hc x hx hfit
      exact satisfies_mergeAll c.1 cs d hd hcov key hkey
    · obtain ⟨c, hcol, hkey⟩ := hout key member
      obtain ⟨x, hx, hfit⟩ := every c hcol
      obtain ⟨-, -, -, hdecl⟩ := contextsOfList_member xs cs hc x hx hfit
      exact hdecl key hkey
  | none =>
    have hfailed : failedIn (.list xs) = true := by
      cases hf : failedIn (.list xs) with
      | true => rfl
      | false =>
        have hany : (xs.any fun x => match exitOfVal x with
            | some (Exit.failure _) => true
            | _ => false) = false := by
          unfold failedIn at hf
          exact hf
        obtain ⟨cs, hcs⟩ := contextsOfList_some xs each hany
        rw [hc] at hcs
        cases hcs
    simp only [hfailed, if_true]
    have hreasons := reasonsOfList_fit xs uniform
    refine ⟨_, rfl, (fitsExit_failure_iff w T _).mpr ⟨fun r hr => ?_, fun r hr => (hreasons r hr).2⟩,
      fun r hr => (hreasons r hr).2⟩
    have h1 := (hreasons r hr).1
    revert h1
    cases r with
    | fail err ann =>
      intro h1
      exact h1
    | die _ _ => intro _; trivial
    | interrupt _ _ => intro _; trivial

/-- **The merge after the forks** (`Layer.ts:1597-1600`): the fail-fast await of every forked
sibling at the positional certificate, then the merge, at the merged layer's columns. -/
theorem awaitMerge_typed {w : World} {available : Env.Requirement} {T : EffTy}
    {out : Env.Requirement} {pairs : List (FiberId × (Env.Requirement × Ty))}
    (declared : ∀ p ∈ pairs, FiberDeclared w p.1 (.contextOf p.2.1) p.2.2)
    (hT : T.answer = .contextOf out) (herr : ∀ p ∈ pairs, Ty.subN p.2.2 T.error = true)
    (hout : ∀ key ∈ out.elems, ∃ p ∈ pairs, key ∈ p.2.1) :
    AmbientProg root w available ((T, available, available) : AmbientPosition)
      ((guardR .onSuccess (fiberValR (.awaitAllFailFast (pairs.map Prod.fst)) rfl)).bind
        (seqR fun ex => mergeContextsR ex)) := by
  refine ambient_seqGuard (mid := ⟨.tuple ((pairs.map Prod.fst).map fun t =>
      .exitOf (gammaCols w t).1 (gammaCols w t).2), .never, Env.Requirement.empty⟩)
    (ambient_fiberAdmin rfl (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ _ _ h => nomatch h) _ (.inr ⟨gammaCols w, rfl, positional_pre declared⟩)
      (fun w' _ ans post =>
        .pure ⟨strongExit_success w' _ _ post, Row.subset_refl _⟩ ⟨Row.subset_refl _, Row.subset_refl _⟩))
    (Bounds.subN_never _) (fun w' _ v hv => ?_)
  simp only [seqR]
  obtain ⟨xs, rfl, each, every⟩ := awaited_columns declared hv
  obtain ⟨ex, hex, ok⟩ := mergeContexts_exit hT each every
    (fun c hc => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
      exact herr p hp)
    (fun key member => by
      obtain ⟨p, hp, hk⟩ := hout key member
      exact ⟨p.2, List.mem_map.mpr ⟨p, hp, rfl⟩, hk⟩)
  rw [hex]
  exact .pure ⟨ok, by cases ex <;> exact Row.subset_refl _⟩ ⟨Row.subset_refl _, Row.subset_refl _⟩

/-- One sibling's build forked as an immediate daemon (`Layer.ts:1597`): the fork's body is the
build at the sibling's admitted layer point into a present scope (`BodyTyped.layerBuild`, decisions
row 186 (a)), its requirement row within the available one and its parameters typed there
(`BodyCoverage`), its fiber declared at the build's types. -/
theorem forkLayer_typed {w : World} {available : Env.Requirement} {q : Point} {m : MemoMapId}
    {scope : Nat} {lt : LayerTy} (hpt : LayerPointTyped root w q lt) (hlive : ScopeLive w scope)
    (hmemo : MemoLive w m) (hreq : Row.Subset lt.requires available)
    (hstack : AmbientStackTyped root w available (scopeParams root.program q.path) q.params) :
    AmbientProg root w available
      (((⟨.fiberOf (.contextOf lt.out) lt.error, .never, Env.Requirement.empty⟩ : EffTy),
        available, available) : AmbientPosition) (forkLayerR q m scope) := by
  refine .fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) (buildTy lt)
    ⟨BodyTyped.layerBuild q m scope lt hpt hlive hmemo, hreq,
      (fun _ _ impossible => by cases impossible), (fun _ _ _ impossible => by cases impossible),
      (fun _ impossible => by cases impossible), (fun _ _ _ impossible => by cases impossible),
      (fun point role => by
        rcases role with impossible | ⟨ctx, impossible | impossible⟩ <;> cases impossible),
      (fun point memo scope' same => by
        cases same
        exact hstack)⟩
    (fun w' _ ans post => ?_) ⟨Row.subset_refl _, Row.subset_refl _⟩
  obtain ⟨id, rfl, hΓ⟩ := post
  exact .pure ⟨strongExit_success w' _ _ ⟨buildTy lt, hΓ, Ty.subN_refl _, Ty.subN_refl _⟩,
    Row.subset_refl _⟩ ⟨Row.subset_refl _, Row.subset_refl _⟩

/-- **`mergeAllEffect`'s loop for two siblings** (`Layer.ts:1597-1600`): a sequential child of the
present parallel parent per sibling, the sibling's build forked into it, then the positional await
of both and the merge, which holds both outputs. -/
theorem mergeFork_typed {w : World} {available : Env.Requirement} {q : Point} {m : MemoMapId}
    {parent : Nat} {la lb : LayerTy} (hlive : ScopeLive w parent) (hmemo : MemoLive w m)
    (ha : LayerPointTyped root w (q.child 0) la) (hb : LayerPointTyped root w (q.child 1) lb)
    (hra : Row.Subset la.requires available) (hrb : Row.Subset lb.requires available)
    (hsa : AmbientStackTyped root w available (scopeParams root.program (q.child 0).path)
      (q.child 0).params)
    (hsb : AmbientStackTyped root w available (scopeParams root.program (q.child 1).path)
      (q.child 1).params) :
    AmbientProg root w available ((buildTy (la.merge lb), available, available) : AmbientPosition)
      (mergeForkR q m parent) := by
  unfold mergeForkR
  refine ambient_seqGuard (ambient_scopeFork hlive) (Bounds.subN_never _) (fun w1 o1 v hv => ?_)
  obtain ⟨c0, rfl, hc0⟩ := fits_scope_inv hv
  simp only [seqR, Val.scope?_scopeHandle]
  refine ambient_seqGuard (forkLayer_typed (layerPointTyped_mono o1 ha) hc0
      (memoLive_mono o1.1 hmemo) hra (ambientStackTyped_mono o1 hsa))
    (Bounds.subN_never _) (fun w2 o2 f0 hf0 => ?_)
  obtain ⟨i0, rfl, hd0⟩ := fiber_of_fits hf0
  simp only [seqR]
  rw [show Val.fiber? (Value.fiber i0) = some ⟨i0⟩ from rfl]
  dsimp only
  have o12 := leHost_trans _ _ _ o1 o2
  refine ambient_seqGuard (ambient_scopeFork (scopeLive_mono o12.1 hlive)) (Bounds.subN_never _)
    (fun w3 o3 u hu => ?_)
  obtain ⟨c1, rfl, hc1⟩ := fits_scope_inv hu
  simp only [seqR, Val.scope?_scopeHandle]
  have o13 := leHost_trans _ _ _ o12 o3
  refine ambient_seqGuard (forkLayer_typed (layerPointTyped_mono o13 hb) hc1
      (memoLive_mono o13.1 hmemo) hrb (ambientStackTyped_mono o13 hsb))
    (Bounds.subN_never _) (fun w4 o4 f1 hf1 => ?_)
  obtain ⟨i1, rfl, hd1⟩ := fiber_of_fits hf1
  simp only [seqR]
  rw [show Val.fiber? (Value.fiber i1) = some ⟨i1⟩ from rfl]
  dsimp only
  have hd0w := fiberDeclared_mono (leHost_trans _ _ _ o3 o4) hd0
  exact awaitMerge_typed (pairs := [(⟨i0⟩, (la.out, la.error)), (⟨i1⟩, (lb.out, lb.error))])
    (fun p hp => by
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hd0w
      · rw [List.mem_singleton] at hp
        subst hp
        exact hd1)
    rfl
    (fun p hp => by
      rcases List.mem_cons.mp hp with rfl | hp
      · exact Ty.subN_join_left _ _
      · rw [List.mem_singleton] at hp
        subst hp
        exact Ty.subN_join_right _ _)
    (fun key member => by
      rcases (Row.mem_union key la.out lb.out).mp member with left | right
      · exact ⟨_, List.mem_cons_self .., left⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), right⟩)

/-- **`Layer.merge`'s build** after `fromBuild` (`Layer.ts:1587-1602`): the parallel parent forked
from the layer scope, then the two siblings. -/
theorem mergeTwo_typed {w : World} {available : Env.Requirement} {q : Point} {m : MemoMapId}
    {child : Nat} {la lb : LayerTy} (hlive : ScopeLive w child) (hmemo : MemoLive w m)
    (ha : LayerPointTyped root w (q.child 0) la) (hb : LayerPointTyped root w (q.child 1) lb)
    (hra : Row.Subset la.requires available) (hrb : Row.Subset lb.requires available)
    (hsa : AmbientStackTyped root w available (scopeParams root.program (q.child 0).path)
      (q.child 0).params)
    (hsb : AmbientStackTyped root w available (scopeParams root.program (q.child 1).path)
      (q.child 1).params) :
    AmbientProg root w available ((buildTy (la.merge lb), available, available) : AmbientPosition)
      (mergeTwoR q m child) := by
  unfold mergeTwoR
  refine ambient_seqGuard (ambient_scopeFork hlive) (Bounds.subN_never _) (fun w1 o1 v hv => ?_)
  obtain ⟨parent, rfl, hparent⟩ := fits_scope_inv hv
  simp only [seqR, Val.scope?_scopeHandle]
  exact mergeFork_typed hparent (memoLive_mono o1.1 hmemo) (layerPointTyped_mono o1 ha)
    (layerPointTyped_mono o1 hb) hra hrb (ambientStackTyped_mono o1 hsa)
    (ambientStackTyped_mono o1 hsb)

/-- A layer point's check, read at its node. -/
theorem LayerPointTyped.at_layer {w : World} {q : Point} {lt : LayerTy} {l : LayerTerm NativeOp}
    (hpt : LayerPointTyped root w q lt) (hat : Node.at_ (.eff root.program) q.path = some (.layer l)) :
    Checker.checkLayer (root.scopeSig q.path) q.path (LayerTerm.expandIn root.program l) = .ok lt ∧
      q.env = [] ∧ (∀ r ∈ q.completed, ∃ fty, w.Γ r.1 = some fty ∧ ExitOk w fty r.2) ∧
      StackTyped root w (scopeParams root.program q.path) q.params := by
  obtain ⟨l', hat', hcheck, henv, hview, hstack⟩ := hpt
  rw [hat] at hat'
  cases hat'
  exact ⟨hcheck, henv, hview, hstack⟩

/-- A layer point typed at the scope of a path that has its parameters (as `pointTyped_scope`):
its layer checked at that path's signature, and its stack typed at that path's scope. -/
theorem layerPointTyped_scope {w : World} {q : Point} {path : List Nat} {l : LayerTerm NativeOp}
    {lt : LayerTy} (hscope : scopeParams root.program q.path = scopeParams root.program path)
    (hat : Node.at_ (.eff root.program) q.path = some (.layer l))
    (hcheck : Checker.checkLayer (root.scopeSig path) q.path (LayerTerm.expandIn root.program l) =
      .ok lt)
    (henv : q.env = []) (hview : ∀ r ∈ q.completed, ∃ fty, w.Γ r.1 = some fty ∧ ExitOk w fty r.2)
    (hstack : StackTyped root w (scopeParams root.program path) q.params) :
    LayerPointTyped root w q lt := by
  have hsig : root.scopeSig q.path = root.scopeSig path := by
    unfold ProgramSource.scopeSig
    rw [hscope]
  rw [← hsig] at hcheck
  rw [← hscope] at hstack
  exact ⟨l, hat, hcheck, henv, hview, hstack⟩

/-- A layer child's point, admitted by its own check. -/
theorem layerPointTyped_child {w : World} {q : Point} {l c : LayerTerm NativeOp} {i : Nat}
    {lt : LayerTy} (hat : Node.at_ (.eff root.program) q.path = some (.layer l))
    (hc : (Node.layer l).child i = some (.layer c))
    (hcheck : Checker.checkLayer (root.scopeSig q.path) (q.path ++ [i])
      (LayerTerm.expandIn root.program c) = .ok lt)
    (henv : q.env = []) (hview : ∀ r ∈ q.completed, ∃ fty, w.Γ r.1 = some fty ∧ ExitOk w fty r.2)
    (hstack : StackTyped root w (scopeParams root.program q.path) q.params) :
    LayerPointTyped root w (q.child i) lt :=
  layerPointTyped_scope (scopeParams_layer_below hat [i]) (Node.at_child hat hc) hcheck henv hview
    hstack

/-- One more round, applied first, is one more round applied last. -/
private theorem foldl_shift {α β : Type} (g : α → α) : ∀ (L : List β) (x : α),
    L.foldl (fun acc _ => g acc) (g x) = g (L.foldl (fun acc _ => g acc) x) :=
  fun _ _ => List.foldl_hom g (fun _ _ => rfl)

/-- **A reference's check is its target's**: the reference's check reads the target's term after
the expansion's rounds; that term, checked, is fixed by one more round (`ExpandFix`), so the
target's own rounds give the same term, at the same signature and path. A step of
`layerPointTyped_redirect` and `layerPointTyped_redirect_module`. -/
theorem checkLayer_ref_target {S : Signature NativeOp} {p target : List Nat} {lt : LayerTy}
    {l : LayerTerm NativeOp}
    (hcheck : Checker.checkLayer S p (LayerTerm.expandIn root.program (.ref target)) = .ok lt)
    (hlayer : (Node.eff root.program).layerAt target = some l) :
    Checker.checkLayer S p (LayerTerm.expandIn root.program l) = .ok lt := by
  have hsite : LayerTerm.expandIn root.program (.ref target) =
      (List.range (root.program.refSites []).length).foldl
        (fun acc _ => LayerTerm.expandRound (Node.eff root.program) acc) l := by
    unfold LayerTerm.expandIn
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      ← foldl_shift (LayerTerm.expandRound (Node.eff root.program))]
    congr 1
    show ((Node.eff root.program).layerAt target).getD (.ref target) = l
    rw [hlayer]
    rfl
  rw [hsite] at hcheck
  have hfix := checkLayer_expandRound (Node.eff root.program) hcheck
  have htarget : LayerTerm.expandIn root.program l =
      (List.range (root.program.refSites []).length).foldl
        (fun acc _ => LayerTerm.expandRound (Node.eff root.program) acc) l := by
    unfold LayerTerm.expandIn
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, hfix]
  rw [htarget]
  exact hcheck

/-- **The hop's point** (decisions rows 153 (b), 170): the target's term has the reference's
check (`checkLayer_ref_target`), which the checker gives at the target's path as at the site's
(`checkLayer_path`), and the target stands in the reference's scope. -/
theorem layerPointTyped_redirect {w : World} {q : Point} {target : List Nat} {lt : LayerTy}
    {l : LayerTerm NativeOp} (hat : Node.at_ (.eff root.program) q.path = some (.layer (.ref target)))
    (hs : scopeParams root.program target = scopeParams root.program q.path)
    (hpt : LayerPointTyped root w q lt) (hlayer : (Node.eff root.program).layerAt target = some l) :
    LayerPointTyped root w (q.redirect target) lt := by
  obtain ⟨hcheck, henv, hview, hstack⟩ := hpt.at_layer hat
  -- the target stands in the reference's scope, so the reference's stack reads its parameters
  exact layerPointTyped_scope hs ((Node.layerAt_eq_some_iff _ _ _).mp hlayer)
    (checkLayer_path (checkLayer_ref_target hcheck hlayer) target) henv hview hstack

/-- **The hop's point into the module** (decisions row 341, step 2): a module layer has no
parameters in scope (`scopeParams_module`), so every stack is typed there (`stackTyped_nil`).
The module's own check types the target's term at the source's signature
(`ModuleLayersTyped`), which the site's signature extends (`ProgramSource.scopeSig_extends`); the
checker answers one verdict at both (`checkLayer_ext`), so the type is the reference's. A step of
`ref_builds`. -/
theorem layerPointTyped_redirect_module {w : World} {q : Point} {target : List Nat} {lt : LayerTy}
    {l : LayerTerm NativeOp} (hmod : ModuleLayersTyped root)
    (hin : root.program.inModule target = true) (hhead : Path.spineHead target.tail = true)
    (hat : Node.at_ (.eff root.program) q.path = some (.layer (.ref target)))
    (hpt : LayerPointTyped root w q lt) (hlayer : (Node.eff root.program).layerAt target = some l) :
    LayerPointTyped root w (q.redirect target) lt := by
  obtain ⟨hcheck, henv, hview, hstack⟩ := hpt.at_layer hat
  have hsite := checkLayer_path (checkLayer_ref_target hcheck hlayer) target
  obtain ⟨lt', hmodule⟩ := hmod target l hin hhead hlayer
  have hext := checkLayer_ext (root.scopeSig_extends q.path) hmodule
  rw [hsite] at hext
  cases hext
  have hsig : root.scopeSig target = root.signature := by
    unfold ProgramSource.scopeSig
    rw [scopeParams_module hin]
    rfl
  refine ⟨l, (Node.layerAt_eq_some_iff _ _ _).mp hlayer, ?_, henv, hview, ?_⟩
  · show Checker.checkLayer (root.scopeSig target) target _ = _
    rw [hsig]
    exact hmodule
  · show StackTyped root w (scopeParams root.program target) q.params
    rw [scopeParams_module hin]
    exact stackTyped_nil root w q.params

/-- `orDie`'s failure (`internal/effect.ts:3289`, `orDieCause`) fits every error column: the first
typed error becomes a user or error defect, never the shape one, since it read back; with no typed
error the cause had none to fit. -/
theorem orDieCause_exitOk {w : World} {T T' : EffTy} {c : CauseV} (h : ExitOk w T (.failure c)) :
    ExitOk w T' (.failure (orDieCause c)) := by
  have hfit := (fitsExit_failure_iff w T c).mp h.1
  unfold orDieCause
  split
  · rename_i e he
    obtain ⟨r, hr, hre⟩ := List.exists_of_findSome?_eq_some he
    cases r with
    | fail e' ann =>
      simp only [Option.some.injEq] at hre
      subst hre
      obtain ⟨v, hv, -⟩ := hfit.1 _ hr
      have hshape : ShapeFree (Cause.die (Defect.ofError e') : CauseV) := by
        intro r' hr'
        simp only [Cause.die, List.mem_singleton] at hr'
        subst hr'
        exact Defect.ofError_shapeFree hv
      refine ⟨(fitsExit_failure_iff w T' _).mpr ⟨fun r' hr' => ?_, hshape⟩, hshape⟩
      simp only [Cause.die, List.mem_singleton] at hr'
      subst hr'
      trivial
    | die _ _ => exact nomatch hre
    | interrupt _ _ => exact nomatch hre
  · rename_i hnone
    refine ⟨(fitsExit_failure_iff w T' c).mpr ⟨fun r hr => ?_, hfit.2⟩, h.2⟩
    cases r with
    | fail e ann =>
      have := List.findSome?_eq_none_iff.mp hnone _ hr
      exact nomatch this
    | die _ _ => trivial
    | interrupt _ _ => trivial

/-- The scope service's key is typed at the scope type (the one reserved service type). -/
theorem serviceTy_scopeKey (app : SigApp) : app.serviceTy Env.scopeKey = some Ty.scope := rfl

/-- A layer descendant's parameters are the layer's: its path below the layer's, its stack the
layer's. -/
theorem layerStack_below {w : World} {available : Env.Requirement} {q q' : Point}
    {l : LayerTerm NativeOp} (hat : Node.at_ (.eff root.program) q.path = some (.layer l))
    (rest : List Nat) (path : q'.path = q.path ++ rest) (params : q'.params = q.params)
    (h : AmbientStackTyped root w available (scopeParams root.program q.path) q.params) :
    AmbientStackTyped root w available (scopeParams root.program q'.path) q'.params := by
  rw [path, scopeParams_layer_below hat rest, params]
  exact h

/-- A walk down a spine stays below its start and keeps its parameters. -/
theorem spineWalk_below : ∀ (j : Nat) (p : Point),
    ∃ rest, (Point.spineWalk j p).path = p.path ++ rest ∧ (Point.spineWalk j p).params = p.params
  | 0, p => ⟨[], (List.append_nil _).symm, rfl⟩
  | j + 1, p => by
    obtain ⟨rest, hpath, hparams⟩ := spineWalk_below j (p.child 1)
    refine ⟨[1] ++ rest, ?_, hparams⟩
    show (Point.spineWalk j (p.child 1)).path = p.path ++ ([1] ++ rest)
    rw [hpath, ← List.append_assoc]
    rfl

/-- A `mergeAll`'s layer point stays below the merge and keeps its parameters. -/
theorem spineChild_below (q : Point) (j : Nat) :
    ∃ rest, (q.spineChild j).path = q.path ++ rest ∧ (q.spineChild j).params = q.params := by
  obtain ⟨rest, hpath, hparams⟩ := spineWalk_below j (q.child 0)
  rw [Point.spineChild_eq]
  refine ⟨[0] ++ rest ++ [0], ?_, hparams⟩
  show (Point.spineWalk j (q.child 0)).path ++ [0] = q.path ++ ([0] ++ rest ++ [0])
  rw [hpath]
  show q.path ++ [0] ++ rest ++ [0] = _
  simp only [List.append_assoc]

/-- A leaf's construction on its layer scope (`Layer.ts:1482`, `:1440`, `:1515`): the layer scope
provided under the scope key, the body at the leaf's child point as the installed region
`construct`, its answer bound under the key (or the empty context). The installed context holds
the body's row: the scope key from the install, the rest from the layer's requirement row. -/
theorem construction_typed {w : World} {available : Env.Requirement} {q : Point}
    {key : Option ServiceKey} {bodyTy : EffTy} {lt : LayerTy} {layerScope : Nat}
    (htie : Tied root w) (hls : ScopeLive w layerScope)
    (hbody : PointTyped root w (q.child 0) bodyTy)
    (hout : lt.out = constructOut key) (herr : lt.error = bodyTy.error)
    (hreq : Row.Subset (Row.diff bodyTy.requires (Env.Requirement.single Env.scopeKey)) available)
    (hkey : ∀ k, key = some k → ∃ carrier, w.serviceTy k = some carrier ∧
      Ty.subN bodyTy.answer carrier = true ∧ flatCarrier carrier = true)
    (hstack : AmbientStackTyped root w available (scopeParams root.program (q.child 0).path)
      (q.child 0).params) :
    AmbientProg root w available ((buildTy lt, available, available) : AmbientPosition)
      (updateContextR (.provideService Env.scopeKey (Val.scopeHandle layerScope))
        (.construct (q.child 0) key)) := by
  refine ambient_updateContext root available available bodyTy.requires (Row.subset_refl _)
    (buildTy lt) (.construct (q.child 0) key) ⟨bodyTy, hbody, ?_, hkey⟩ hstack _
    (fun later grew previous members => ?_) (fun previous covered => ?_)
  · show (⟨.contextOf lt.out, lt.error, bodyTy.requires⟩ : EffTy) = _
    rw [hout, herr]
  · have live := fits_scopeHandle later layerScope (scopeLive_mono grew.1 hls)
    refine servicesFit_merge members (servicesFit_addV (servicesFit_empty later) ?_
      (fits_flatFits rfl live) (fits_live later _ _ live))
    rw [(Tied.mono grew htie).services]
    exact serviceTy_scopeKey _
  · show (previous.merge ((Env.Context.empty : Env.Ctx).addV Env.scopeKey
        (Val.scopeHandle layerScope))).Satisfies bodyTy.requires ∧
      (previous.merge ((Env.Context.empty : Env.Ctx).addV Env.scopeKey
        (Val.scopeHandle layerScope))).Satisfies available
    refine ⟨fun k member => ?_, Provision.satisfies_merge_left _ _ _ covered⟩
    by_cases isScope : k = Env.scopeKey
    · subst isScope
      exact Provision.satisfies_merge_right _ _ _
        (Provision.satisfies_single_addV Env.scopeKey (Val.scopeHandle layerScope)) Env.scopeKey
        ((Row.mem_singleton Env.scopeKey Env.scopeKey).mpr rfl)
    · exact Provision.satisfies_merge_left _ _ _ covered k
        (hreq k ((Row.mem_diff k _ _).mpr ⟨member, fun h => isScope ((Row.mem_singleton _ _).mp h)⟩))

/-- Every scope's signature keeps the native scope key: the key a layer's own scope answers. -/
theorem scopeSig_scopeKey (root : ProgramSource) (path : List Nat) :
    (root.scopeSig path).scopeKey = Env.scopeKey := by
  unfold ProgramSource.scopeSig
  cases scopeParams root.program path <;> rfl

/-- The recursion's motive: the build of a layer term is typed at every admitted point of it, at a
world whose service table is the source's, into a present scope through a present memo map
(finding F-WF), at every available row holding the layer's requirement row and typing the point's
parameters, within the hop's fuel bound. -/
abbrev BuildsTyped (root : ProgramSource) (K : Nat) (l : LayerTerm NativeOp) : Prop :=
  ∀ (q : Point) (w : World) (lt : LayerTy) (m : MemoMapId) (scope : Nat)
    (available : Env.Requirement), q.fuel ≤ K → Tied root w →
    Node.at_ (.eff root.program) q.path = some (.layer l) → LayerPointTyped root w q lt →
    ScopeLive w scope → MemoLive w m → Row.Subset lt.requires available →
    AmbientStackTyped root w available (scopeParams root.program q.path) q.params →
    AmbientProg root w available ((buildTy lt, available, available) : AmbientPosition)
      (denoteLayer root.program l q m scope)

/-- **`Layer.succeed`** (`Layer.ts:1129`): the literal bound under its key, at the key's carrier. -/
theorem succeed_builds {key : ServiceKey} {value : Lit} {K : Nat} :
    BuildsTyped root K (.succeed key value) := by
  intro q w lt m scope available _ htie hat hpt _ _ _ _
  obtain ⟨hcheck, -, -, -⟩ := hpt.at_layer hat
  rw [LayerTerm.expandIn_succeed] at hcheck
  obtain ⟨v, ty, hlv, hsty, hsub, rfl⟩ := Checker.inv_layer_succeed _ _ _ _ _ hcheck
  rw [root.scopeSig_serviceTy] at hsty
  rw [denoteLayer_succeed]
  have hlit : ∃ x, Lit.toVal value = some x ∧ Fits w x (Lit.ty value) := by
    cases value with
    | unit => exact ⟨_, rfl, trivial⟩
    | nat n => exact ⟨_, rfl, trivial⟩
    | bool b => exact ⟨_, rfl, trivial⟩
    | str s' => exact nomatch hlv
  obtain ⟨x, hx, hfx⟩ := hlit
  rw [hx]
  have hsty' : root.sig.serviceTy key = some ty := hsty
  obtain ⟨ctx, hbind, hfits⟩ := bindService_exit (key := some key) (v := x)
    (fun k hk => by
      cases hk
      exact ⟨ty, by rw [htie.services]; exact hsty',
        fits_flatFits (serviceTy_flat root key ty hsty) (fits_subN w hsub x hfx)⟩)
    (live_of_handles_nil (Effect4.Program.RawHandles.lit_toVal_handles value x hx))
  show AmbientProg root w available _ (bindServiceR (some key) x)
  rw [hbind]
  exact .pure ⟨strongExit_success w _ _ hfits, Row.subset_refl _⟩ ⟨Row.subset_refl _, Row.subset_refl _⟩

/-- **`Layer.fresh`** (`Layer.ts:3851`): the inner layer built through a brand-new memo map. -/
theorem fresh_builds {inner : LayerTerm NativeOp} {K : Nat} (hi : BuildsTyped root K inner) :
    BuildsTyped root K (.fresh inner) := by
  intro q w lt m scope available hK htie hat hpt hlive hmemo hreq hstack
  obtain ⟨hcheck, henv, hview, hstk⟩ := hpt.at_layer hat
  rw [LayerTerm.expandIn_fresh] at hcheck
  have hc := Checker.inv_layer_fresh _ _ _ _ hcheck
  rw [denoteLayer_fresh]
  refine ambient_seqGuard (mid := EffTy.pure Ty.memoMap)
    (ambient_store (op := .memoFork none) () trivial (fun _ _ h => nomatch h)
      (fun w' _ ans post => ?_))
    (Bounds.subN_never _) (fun w' o v hv => ?_)
  · obtain ⟨id, rfl, hid⟩ := post
    exact .pure ⟨strongExit_success w' _ _ (fits_memoMap w' id hid), Row.subset_refl _⟩
      ⟨Row.subset_refl _, Row.subset_refl _⟩
  · obtain ⟨id, rfl, hid⟩ := fits_memoMap_inv hv
    simp only [seqR, Val.memoMap?_memoMap]
    exact hi (q.child 0) w' lt id scope available (Nat.le_trans (Nat.sub_le _ _) hK)
      (Tied.mono o htie) (Node.at_child hat rfl)
      (layerPointTyped_child hat rfl hc henv (completed_mono o hview) (stackTyped_mono o hstk))
      (scopeLive_mono o.1 hlive) hid hreq
      (layerStack_below hat [0] rfl rfl (ambientStackTyped_mono o hstack))

/-- **`Layer.orDie`** (`Layer.ts:3327`): the inner build's failure turned into a defect, which fits
every error column (`orDieCause_exitOk`); the inner layer is built as it resolves (decisions row
185). -/
theorem orDie_builds {inner : LayerTerm NativeOp} {K : Nat} (hi : BuildsTyped root K inner) :
    BuildsTyped root K (.orDie inner) := by
  intro q w lt m scope available hK htie hat hpt hlive hmemo hreq hstack
  obtain ⟨hcheck, henv, hview, hstk⟩ := hpt.at_layer hat
  rw [LayerTerm.expandIn_orDie] at hcheck
  obtain ⟨li, hci, rfl⟩ := Checker.inv_layer_orDie _ _ _ _ hcheck
  rw [denoteLayer_orDie]
  refine ambient_guardBind root
    (hi (q.child 0) w li m scope available (Nat.le_trans (Nat.sub_le _ _) hK) htie
      (Node.at_child hat rfl) (layerPointTyped_child hat rfl hci henv hview hstk) hlive hmemo hreq
      (layerStack_below hat [0] rfl rfl hstack))
    (fun later _ exit arm payload => ?_) (fun later _ exit payload absent => ?_)
    (Row.subset_refl _)
  · cases exit with
    | success v => exact Bool.noConfusion arm
    | failure c =>
      exact .pure ⟨orDieCause_exitOk payload.1, Row.subset_refl _⟩ ⟨Row.subset_refl _, Row.subset_refl _⟩
  · cases exit with
    | success v => exact ⟨exitOk_success_of_answerN (Ty.subN_refl _) payload.1, Row.subset_refl _⟩
    | failure c => exact Bool.noConfusion absent

/-- **`Layer.effect`** and **`Layer.effectDiscard`** (`Layer.ts:1482`, `:1440`): `fromBuild`, the
memoized leaf, its construction on the layer scope, the body's answer bound under the key at the
key's carrier, or discarded for the empty context. -/
theorem leaf_builds {key : Option ServiceKey} {body : NativeEff} {l : LayerTerm NativeOp}
    {K : Nat}
    (shape : ∀ (q : Point) (m : MemoMapId) (scope : Nat), denoteLayer root.program l q m scope =
      fromBuildR scope fun child => memoizeR q m child fun layerScope =>
        updateContextR (.provideService Env.scopeKey (Val.scopeHandle layerScope))
          (.construct (q.child 0) key))
    (checked : ∀ (sig : Signature NativeOp) (p : List Nat) (lt : LayerTy),
      Checker.checkLayer sig p (LayerTerm.expandIn root.program l) = .ok lt →
      ∃ t, Checker.check sig [] (p ++ [0]) (Eff.expandIn root.program body) = .ok t ∧
        lt.out = constructOut key ∧ lt.error = t.error ∧ lt.requires = bodyRequires sig t ∧
        ∀ k, key = some k → ∃ ty, sig.serviceTy k = some ty ∧ Ty.subN t.answer ty = true)
    (below : ∀ q : Point, Node.at_ (.eff root.program) q.path = some (.layer l) →
      Node.at_ (.eff root.program) (q.path ++ [0]) = some (.eff body)) :
    BuildsTyped root K l := by
  intro q w lt m scope available _ htie hat hpt hlive _ hreq hstack
  obtain ⟨hcheck, henv, hview, hstk⟩ := hpt.at_layer hat
  obtain ⟨t, hcb, hout, herr, hrow, hkeys⟩ := checked _ _ _ hcheck
  rw [shape]
  refine fromBuild_typed hlive (fun w1 o1 child hchild => ?_)
  refine memoize_typed hat hcheck hchild (fun w2 o2 layerScope hls => ?_)
  have o12 := leHost_trans _ _ _ o1 o2
  refine construction_typed (Tied.mono o12 htie) hls ?_ hout herr ?_ ?_
    (layerStack_below hat [0] rfl rfl (ambientStackTyped_mono o12 hstack))
  · refine pointTyped_scope (scopeParams_layer_below hat [0]) (below q hat) hcb ?_
      (completed_mono o12 hview) (stackTyped_mono o12 hstk)
    show EnvTyped w2 [] q.env
    rw [henv]
    exact envTyped_nil w2
  · rw [hrow] at hreq
    unfold bodyRequires at hreq
    rw [scopeSig_scopeKey] at hreq
    exact hreq
  · intro k hk
    obtain ⟨ty, hsty, hsub⟩ := hkeys k hk
    rw [root.scopeSig_serviceTy] at hsty
    have hsty' : root.sig.serviceTy k = some ty := hsty
    exact ⟨ty, by rw [(Tied.mono o12 htie).services]; exact hsty', hsub, serviceTy_flat root k ty hsty⟩

/-- **`Layer.effect`** (`Layer.ts:1482`). -/
theorem effect_builds {key : ServiceKey} {body : NativeEff} {K : Nat} :
    BuildsTyped root K (.effect key body) :=
  leaf_builds (key := some key) (body := body) (fun _ _ _ => denoteLayer_effect _ _ _ _ _ _)
    (fun sig p lt hcheck => by
      rw [LayerTerm.expandIn_effect] at hcheck
      obtain ⟨t, ty, hcb, hsty, hsub, rfl⟩ := Checker.inv_layer_effect _ _ _ _ _ hcheck
      exact ⟨t, hcb, rfl, rfl, rfl, fun k hk => by
        cases hk
        exact ⟨ty, hsty, hsub⟩⟩)
    (fun _ hat => Node.at_child hat rfl)

/-- **`Layer.effectDiscard`** (`Layer.ts:1440`). -/
theorem effectDiscard_builds {body : NativeEff} {K : Nat} :
    BuildsTyped root K (.effectDiscard body) :=
  leaf_builds (key := none) (body := body) (fun _ _ _ => denoteLayer_effectDiscard _ _ _ _ _)
    (fun sig p lt hcheck => by
      rw [LayerTerm.expandIn_effectDiscard] at hcheck
      obtain ⟨t, hcb, rfl⟩ := Checker.inv_layer_effectDiscard _ _ _ _ hcheck
      exact ⟨t, hcb, rfl, rfl, rfl, fun k hk => nomatch hk⟩)
    (fun _ hat => Node.at_child hat rfl)

/-- **`Layer.provide`** and **`Layer.provideMerge`** (`Layer.ts:1915`): `fromBuild`, the dependency
built, the dependent region under its context with the dependency's output discharged, the
combiner's answer. -/
theorem dependency_builds {self that : LayerTerm NativeOp} {l : LayerTerm NativeOp}
    {mode : CombineMode} {K : Nat}
    (shape : ∀ (q : Point) (m : MemoMapId) (scope : Nat), denoteLayer root.program l q m scope =
      fromBuildR scope fun child =>
        provideWithR (denoteLayer root.program that (q.child 1) m child) (.build (q.child 0) m child)
          mode)
    (checked : ∀ (sig : Signature NativeOp) (p : List Nat) (lt : LayerTy),
      Checker.checkLayer sig p (LayerTerm.expandIn root.program l) = .ok lt →
      ∃ ls lt', Checker.checkLayer sig (p ++ [0]) (LayerTerm.expandIn root.program self) = .ok ls ∧
        Checker.checkLayer sig (p ++ [1]) (LayerTerm.expandIn root.program that) = .ok lt' ∧
        lt.out = combineOut mode ls.out lt'.out ∧ lt.error = ls.error.join lt'.error ∧
        lt.requires = Row.union (Row.diff ls.requires lt'.out) lt'.requires)
    (children : ∀ q : Point, Node.at_ (.eff root.program) q.path = some (.layer l) →
      (Node.layer l).child 0 = some (.layer self) ∧ (Node.layer l).child 1 = some (.layer that))
    (ht : BuildsTyped root K that) : BuildsTyped root K l := by
  intro q w lt m scope available hK htie hat hpt hlive hmemo hreq hstack
  obtain ⟨hcheck, henv, hview, hstk⟩ := hpt.at_layer hat
  obtain ⟨ls, lt', hcs, hct, hout, herr, hrow⟩ := checked _ _ _ hcheck
  obtain ⟨c0, c1⟩ := children q hat
  rw [shape]
  refine fromBuild_typed hlive (fun w1 o1 child hchild => ?_)
  have hview1 := completed_mono o1 hview
  rw [hrow] at hreq
  refine provideWith_typed (that := lt') (self := ls)
    (ht (q.child 1) w1 lt' m child available (Nat.le_trans (Nat.sub_le _ _) hK)
      (Tied.mono o1 htie) (Node.at_child hat c1)
      (layerPointTyped_child hat c1 hct henv hview1 (stackTyped_mono o1 hstk)) hchild
      (memoLive_mono o1.1 hmemo) (Row.subset_trans (Row.subset_union_right _ _) hreq)
      (layerStack_below hat [1] rfl rfl (ambientStackTyped_mono o1 hstack)))
    ⟨ls, rfl, layerPointTyped_child hat c0 hcs henv hview1 (stackTyped_mono o1 hstk), hchild,
      memoLive_mono o1.1 hmemo⟩
    (layerStack_below hat [0] rfl rfl (ambientStackTyped_mono o1 hstack))
    (Row.subset_trans (Row.subset_union_left _ _) hreq) (by rw [← hout]; rfl) ?_ ?_
  · rw [show (buildTy lt).error = lt.error from rfl, herr]
    exact Ty.subN_join_right _ _
  · rw [show (buildTy lt).error = lt.error from rfl, herr]
    exact Ty.subN_join_left _ _

/-- **`Layer.provide`** (`Layer.ts:1915`). -/
theorem provide_builds {self that : LayerTerm NativeOp} {K : Nat} (ht : BuildsTyped root K that) :
    BuildsTyped root K (.provide self that) :=
  dependency_builds (self := self) (that := that) (mode := .provide)
    (fun _ _ _ => denoteLayer_provide _ _ _ _ _ _)
    (fun sig p lt hcheck => by
      rw [LayerTerm.expandIn_provide] at hcheck
      obtain ⟨ls, lt', hcs, hct, rfl⟩ := Checker.inv_layer_provide _ _ _ _ _ hcheck
      exact ⟨ls, lt', hcs, hct, rfl, rfl, rfl⟩)
    (fun _ _ => ⟨rfl, rfl⟩) ht

/-- **`Layer.provideMerge`** (`Layer.ts:1915-1923`): as `provide`, both outputs answered. -/
theorem provideMerge_builds {self that : LayerTerm NativeOp} {K : Nat}
    (ht : BuildsTyped root K that) : BuildsTyped root K (.provideMerge self that) :=
  dependency_builds (self := self) (that := that) (mode := .provideMerge)
    (fun _ _ _ => denoteLayer_provideMerge _ _ _ _ _ _)
    (fun sig p lt hcheck => by
      rw [LayerTerm.expandIn_provideMerge] at hcheck
      obtain ⟨ls, lt', hcs, hct, rfl⟩ := Checker.inv_layer_provideMerge _ _ _ _ _ hcheck
      exact ⟨ls, lt', hcs, hct, rfl, rfl, rfl⟩)
    (fun _ _ => ⟨rfl, rfl⟩) ht

/-- **`Layer.merge`** (`Layer.ts:1587-1602`): `fromBuild`, then the two siblings forked and merged. -/
theorem merge_builds {left right : LayerTerm NativeOp} {K : Nat} :
    BuildsTyped root K (.merge left right) := by
  intro q w lt m scope available _ _ hat hpt hlive hmemo hreq hstack
  obtain ⟨hcheck, henv, hview, hstk⟩ := hpt.at_layer hat
  rw [LayerTerm.expandIn_merge] at hcheck
  obtain ⟨a, b, ha, hb, rfl⟩ := Checker.inv_layer_merge _ _ _ _ _ hcheck
  rw [denoteLayer_merge]
  exact fromBuild_typed hlive (fun w1 o1 child hchild =>
    mergeTwo_typed hchild (memoLive_mono o1.1 hmemo)
      (layerPointTyped_child hat rfl ha henv (completed_mono o1 hview) (stackTyped_mono o1 hstk))
      (layerPointTyped_child hat rfl hb henv (completed_mono o1 hview) (stackTyped_mono o1 hstk))
      (Row.subset_trans (Row.subset_union_left _ _) hreq)
      (Row.subset_trans (Row.subset_union_right _ _) hreq)
      (layerStack_below hat [0] rfl rfl (ambientStackTyped_mono o1 hstack))
      (layerStack_below hat [1] rfl rfl (ambientStackTyped_mono o1 hstack)))

/-- **A reference and its target have the same parameters in scope** (decisions row 340, ruling
of 2026-10-10, `docs/research/2026-10-10-cx-lexical-scope.md` §11), when the target stands outside
the module's layers: the formation check keeps such a reference in its target's scope
(`layerRefsWF_scopeOf`), and a path's parameters are its scope's (`scopeParams_eq`). So the stack
a reference's hop keeps reads the target's parameters. A step of `denote-typed`; its consumer is
`ref_builds`. -/

@[semantics "residual-program-typing" (requirement := R4)]
theorem scopeParams_ref {program : NativeEff} (hwf : program.layerRefsWF = true)
    {site target : List Nat} (h : Node.at_ (.eff program) site = some (.layer (.ref target)))
    (hm : program.inModule target = false) :
    scopeParams program target = scopeParams program site := by
  rw [scopeParams_eq, scopeParams_eq, layerRefsWF_scopeOf hwf (mem_refSites_of_at h) hm]

/-- Each layer of a nonempty merge errs below the merge (`Layer.ts:1652`, the errors joined). -/
theorem mergeNonempty_error : ∀ (ls : List LayerTy) (lt : LayerTy),
    LayerTy.mergeNonempty ls = some lt → ∀ x ∈ ls, Ty.subN x.error lt.error = true
  | [], _, h, _, _ => nomatch h
  | [l], lt, h, x, hx => by
    simp only [LayerTy.mergeNonempty, Option.some.injEq] at h
    subst h
    rw [List.mem_singleton] at hx
    subst hx
    exact Ty.subN_refl _
  | l :: m :: rest, lt, h, x, hx => by
    simp only [LayerTy.mergeNonempty] at h
    obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.mp h
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact Ty.subN_join_left _ _
    · exact Ty.subN_trans (mergeNonempty_error (m :: rest) t' ht' x hx') (Ty.subN_join_right _ _)

/-- Checking a spine keeps its length. -/
theorem checkLayers_length {sig : Signature NativeOp} :
    ∀ (ts : LayerTerms NativeOp) (p : List Nat) (ls : List LayerTy),
    Checker.checkLayers sig p ts = .ok ls → ls.length = ts.length
  | .nil, p, ls, h => by
    rw [Checker.inv_layers_nil _ _ ls h]
    rfl
  | .cons hd tl, p, ls, h => by
    obtain ⟨hh, tt, -, htl, rfl⟩ := Checker.inv_layers_cons _ _ _ _ _ h
    show tt.length + 1 = tl.length + 1
    rw [checkLayers_length tl _ tt htl]

/-- The expansion keeps a spine's length. -/
theorem expandIn_layers_length : ∀ (ts : LayerTerms NativeOp),
    (LayerTerms.expandIn root.program ts).length = ts.length
  | .nil => by rw [LayerTerms.expandIn_nil]
  | .cons hd tl => by
    rw [LayerTerms.expandIn_cons]
    show (LayerTerms.expandIn root.program tl).length + 1 = tl.length + 1
    rw [expandIn_layers_length tl]

/-- **A spine's layer points are admitted** by the spine's check: the `j`-th layer of a checked
spine, at the spine walked `j` steps in, carries the `j`-th checked type. -/
theorem spine_layerPointTyped {w : World} {base : List Nat} :
    ∀ (j : Nat) (p : Point) (ts : LayerTerms NativeOp)
    (ls : List LayerTy),
    (∀ x, p.path <+: x → scopeParams root.program x = scopeParams root.program base) →
    Node.at_ (.eff root.program) p.path = some (.layers ts) →
    Checker.checkLayers (root.scopeSig base) p.path (LayerTerms.expandIn root.program ts) = .ok ls →
    p.env = [] → (∀ r ∈ p.completed, ∃ fty, w.Γ r.1 = some fty ∧ ExitOk w fty r.2) →
    StackTyped root w (scopeParams root.program base) p.params →
    ∀ (hj : j < ls.length), LayerPointTyped root w ((Point.spineWalk j p).child 0) (ls[j])
  | _, _, .nil, ls, _, _, hcheck, _, _, _, hj => by
    rw [LayerTerms.expandIn_nil, Checker.inv_layers_nil _ _ ls hcheck] at *
    exact absurd hj (Nat.not_lt_zero _)
  | 0, p, .cons hd tl, ls, hscope, hat, hcheck, henv, hview, hstack, hj => by
    rw [LayerTerms.expandIn_cons] at hcheck
    obtain ⟨hh, tt, hhd, -, rfl⟩ := Checker.inv_layers_cons _ _ _ _ _ hcheck
    exact layerPointTyped_scope (hscope _ (List.prefix_append _ _)) (Node.at_child hat rfl) hhd
      henv hview hstack
  | j + 1, p, .cons hd tl, ls, hscope, hat, hcheck, henv, hview, hstack, hj => by
    rw [LayerTerms.expandIn_cons] at hcheck
    obtain ⟨hh, tt, -, htl, rfl⟩ := Checker.inv_layers_cons _ _ _ _ _ hcheck
    exact spine_layerPointTyped j (p.child 1) tl tt
      (fun x hx => hscope x ((List.prefix_append _ _).trans hx)) (Node.at_child hat rfl) htl henv
      hview hstack (Nat.lt_of_succ_lt_succ hj)

/-- **A layer reference** (decisions rows 153, 170, 185, 341): no fuel is the frontier; else the
hop to the target's term at the redirected point, one fuel down, by the hop hypothesis —
well-formedness (`layerRefsWF_at`) gives a target that is a layer and no reference, either in
the reference's scope (`scopeParams_ref`, `layerPointTyped_redirect`) or a whole module layer
(`layerRefsWF_module`, `layerPointTyped_redirect_module`), so the hop's point is typed, its
parameters the reference's or none. -/
theorem ref_builds {target : List Nat} {K : Nat} (hwf : root.program.layerRefsWF = true)
    (hmod : ModuleLayersTyped root)
    (hhop : ∀ (l : LayerTerm NativeOp) (q : Point) (w : World) (lt : LayerTy) (m : MemoMapId)
      (scope : Nat) (available : Env.Requirement), q.fuel < K → Tied root w →
      Node.at_ (.eff root.program) q.path = some (.layer l) → LayerPointTyped root w q lt →
      ScopeLive w scope → MemoLive w m → Row.Subset lt.requires available →
      AmbientStackTyped root w available (scopeParams root.program q.path) q.params →
      AmbientProg root w available ((buildTy lt, available, available) : AmbientPosition)
        (denoteLayer root.program l q m scope)) :
    BuildsTyped root K (.ref target) := by
  intro q w lt m scope available hK htie hat hpt hlive hmemo hreq hstack
  cases hfq : q.fuel with
  | zero =>
    rw [denoteLayer_ref_zero _ _ _ _ _ hfq]
    refine .fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ _ _ h => nomatch h) () True.intro ?_ ⟨Row.subset_refl _, Row.subset_refl _⟩
    intro _ _ _ impossible
    exact impossible.elim
  | succ k =>
    obtain ⟨lt_t, hlayer, hnotref⟩ := layerRefsWF_at hwf hat
    rw [denoteLayer_ref_succ _ _ _ _ _ hfq, (Node.layerAt_eq_some_iff _ _ _).mp hlayer]
    have hredir : LayerPointTyped root w (q.redirect target) lt ∧
        AmbientStackTyped root w available (scopeParams root.program target) q.params := by
      cases hin : root.program.inModule target with
      | false =>
        refine ⟨layerPointTyped_redirect hat (scopeParams_ref hwf hat hin) hpt hlayer, ?_⟩
        rw [scopeParams_ref hwf hat hin]
        exact hstack
      | true =>
        refine ⟨layerPointTyped_redirect_module hmod hin
          (layerRefsWF_module hwf (mem_refSites_of_at hat) hin) hat hpt hlayer, ?_⟩
        rw [scopeParams_module hin]
        exact ambientStackTyped_nil root w available q.params
    have hk : (q.redirect target).fuel = k := by
      show q.fuel - 1 = k
      rw [hfq]
      rfl
    have hKk : (q.redirect target).fuel < K := by rw [hk]; rw [hfq] at hK; omega
    cases lt_t with
    | ref t' => exact absurd rfl (hnotref t')
    | _ =>
      exact hhop _ (q.redirect target) w lt m scope available hKk htie ((Node.layerAt_eq_some_iff _ _ _).mp hlayer)
        hredir.1 hlive hmemo hreq hredir.2

/-- Each layer of a nonempty merge requires within the merge (`Layer.ts:1652`, the rows joined). -/
theorem mergeNonempty_requires : ∀ (ls : List LayerTy) (lt : LayerTy),
    LayerTy.mergeNonempty ls = some lt → ∀ x ∈ ls, Row.Subset x.requires lt.requires
  | [], _, h, _, _ => nomatch h
  | [l], lt, h, x, hx => by
    simp only [LayerTy.mergeNonempty, Option.some.injEq] at h
    subst h
    rw [List.mem_singleton] at hx
    subst hx
    exact Row.subset_refl _
  | l :: m :: rest, lt, h, x, hx => by
    simp only [LayerTy.mergeNonempty] at h
    obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.mp h
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact Row.subset_union_left _ _
    · exact Row.subset_trans (mergeNonempty_requires (m :: rest) t' ht' x hx')
        (Row.subset_union_right _ _)

/-- Every output of a nonempty merge is some layer's (`Layer.ts:1652`, the outputs joined). -/
theorem mergeNonempty_out : ∀ (ls : List LayerTy) (lt : LayerTy),
    LayerTy.mergeNonempty ls = some lt → ∀ key ∈ lt.out.elems, ∃ x ∈ ls, key ∈ x.out
  | [], _, h, _, _ => nomatch h
  | [l], lt, h, key, hk => by
    simp only [LayerTy.mergeNonempty, Option.some.injEq] at h
    subst h
    exact ⟨_, List.mem_singleton_self _, hk⟩
  | l :: m :: rest, lt, h, key, hk => by
    simp only [LayerTy.mergeNonempty] at h
    obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.mp h
    rcases (Row.mem_union key l.out t'.out).mp hk with mine | theirs
    · exact ⟨l, List.mem_cons_self .., mine⟩
    · obtain ⟨x, hx, hkx⟩ := mergeNonempty_out (m :: rest) t' ht' key theirs
      exact ⟨x, List.mem_cons_of_mem _ hx, hkx⟩

/-- **`mergeAllEffect`'s fork loop** (`Layer.ts:1597-1600`) for a `mergeAll`'s spine: with every
fiber forked so far declared below its layer's output context and error, every remaining layer's
point admitted at the spine's checked type within the available row, and every output of the merge
some forked or remaining layer's, each layer forked into a sequential child of the present
parallel parent, then the positional await of all and the merge. -/
theorem mergeAllFork_typed {q : Point} {m : MemoMapId} {parent : Nat}
    {available : Env.Requirement} {ls : List LayerTy} {lt : LayerTy}
    (herr : ∀ x ∈ ls, Ty.subN x.error lt.error = true) :
    ∀ (remaining i : Nat) (pairs : List (FiberId × (Env.Requirement × Ty))) (w : World),
      ScopeLive w parent → MemoLive w m → i + remaining = ls.length →
      (∀ p ∈ pairs, FiberDeclared w p.1 (.contextOf p.2.1) p.2.2 ∧
        Ty.subN p.2.2 lt.error = true) →
      (∀ j (hj : j < ls.length), i ≤ j → LayerPointTyped root w (q.spineChild j) ls[j] ∧
        Row.Subset ls[j].requires available ∧
        AmbientStackTyped root w available (scopeParams root.program (q.spineChild j).path)
          (q.spineChild j).params) →
      (∀ key ∈ lt.out.elems, (∃ p ∈ pairs, key ∈ p.2.1) ∨
        ∃ j, ∃ hj : j < ls.length, i ≤ j ∧ key ∈ ls[j].out) →
      AmbientProg root w available ((buildTy lt, available, available) : AmbientPosition)
        (mergeAllForkR q m parent remaining i (pairs.map Prod.fst))
  | 0, i, pairs, w, _, _, hlen, hpairs, _, hcover =>
    awaitMerge_typed (fun p hp => (hpairs p hp).1) rfl (fun p hp => (hpairs p hp).2)
      (fun key member => by
        rcases hcover key member with inPairs | ⟨j, hj, hij, _⟩
        · exact inPairs
        · omega)
  | remaining + 1, i, pairs, w, hlive, hmemo, hlen, hpairs, hspine, hcover => by
    have hi : i < ls.length := by omega
    obtain ⟨hpti, hreqi, hstacki⟩ := hspine i hi (Nat.le_refl _)
    show AmbientProg root w available _
      ((guardR .onSuccess (storeR (.scopeFork parent .sequential))).bind _)
    refine ambient_seqGuard (ambient_scopeFork hlive) (Bounds.subN_never _) (fun w1 o1 v hv => ?_)
    obtain ⟨c, rfl, hc⟩ := fits_scope_inv hv
    simp only [seqR, Val.scope?_scopeHandle]
    refine ambient_seqGuard (forkLayer_typed (layerPointTyped_mono o1 hpti) hc
        (memoLive_mono o1.1 hmemo) hreqi (ambientStackTyped_mono o1 hstacki))
      (Bounds.subN_never _) (fun w2 o2 f hf => ?_)
    obtain ⟨index, rfl, hd⟩ := fiber_of_fits hf
    simp only [seqR]
    rw [show Val.fiber? (Value.fiber index) = some ⟨index⟩ from rfl]
    dsimp only
    have o12 := leHost_trans _ _ _ o1 o2
    have hpairs' : ∀ p ∈ pairs ++ [(⟨index⟩, (ls[i].out, ls[i].error))],
        FiberDeclared w2 p.1 (.contextOf p.2.1) p.2.2 ∧ Ty.subN p.2.2 lt.error = true := by
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact ⟨fiberDeclared_mono o12 (hpairs p hp).1, (hpairs p hp).2⟩
      · rw [List.mem_singleton] at hp
        subst hp
        exact ⟨hd, herr _ (List.getElem_mem hi)⟩
    have hspine' : ∀ j (hj : j < ls.length), i + 1 ≤ j →
        LayerPointTyped root w2 (q.spineChild j) ls[j] ∧ Row.Subset ls[j].requires available ∧
        AmbientStackTyped root w2 available (scopeParams root.program (q.spineChild j).path)
          (q.spineChild j).params := by
      intro j hj hij
      obtain ⟨hpt, hreq, hstk⟩ := hspine j hj (by omega)
      exact ⟨layerPointTyped_mono o12 hpt, hreq, ambientStackTyped_mono o12 hstk⟩
    have hcover' : ∀ key ∈ lt.out.elems,
        (∃ p ∈ pairs ++ [(⟨index⟩, (ls[i].out, ls[i].error))], key ∈ p.2.1) ∨
        ∃ j, ∃ hj : j < ls.length, i + 1 ≤ j ∧ key ∈ ls[j].out := by
      intro key member
      rcases hcover key member with ⟨p, hp, hk⟩ | ⟨j, hj, hij, hk⟩
      · exact .inl ⟨p, List.mem_append_left _ hp, hk⟩
      · by_cases same : j = i
        · subst same
          exact .inl ⟨_, List.mem_append_right _ (List.mem_singleton_self _), hk⟩
        · exact .inr ⟨j, hj, by omega, hk⟩
    have step := mergeAllFork_typed herr remaining (i + 1)
      (pairs ++ [(⟨index⟩, (ls[i].out, ls[i].error))]) w2 (scopeLive_mono o12.1 hlive)
      (memoLive_mono o12.1 hmemo) (by omega) hpairs' hspine' hcover'
    rw [List.map_append] at step
    exact step

/-- **`Layer.mergeAll`** (`Layer.ts:1587-1600`, the n-ary merge): `fromBuild`, the parallel parent,
then every layer of the spine forked at its admitted point (`spine_layerPointTyped`) and the merge;
each layer errs and requires within the merge (`mergeNonempty_error`, `mergeNonempty_requires`),
and every output of the merge is some layer's (`mergeNonempty_out`). -/
theorem mergeAll_builds {layers : LayerTerms NativeOp} {K : Nat} :
    BuildsTyped root K (.mergeAll layers) := by
  intro q w lt m scope available _ _ hat hpt hlive hmemo hreq hstack
  obtain ⟨hcheck, henv, hview, hstk⟩ := hpt.at_layer hat
  rw [LayerTerm.expandIn_mergeAll] at hcheck
  obtain ⟨ls, hcs, hmerge⟩ := Checker.inv_layer_mergeAll _ _ _ _ hcheck
  have hlen : ls.length = layers.length := by
    rw [checkLayers_length _ _ _ hcs, expandIn_layers_length]
  rw [denoteLayer_mergeAll]
  refine fromBuild_typed hlive (fun w1 o1 child hchild => ?_)
  unfold mergeAllR
  refine ambient_seqGuard (ambient_scopeFork hchild) (Bounds.subN_never _) (fun w2 o2 v hv => ?_)
  obtain ⟨parent, rfl, hparent⟩ := fits_scope_inv hv
  simp only [seqR, Val.scope?_scopeHandle]
  have o12 := leHost_trans _ _ _ o1 o2
  exact mergeAllFork_typed (mergeNonempty_error ls lt hmerge) layers.length 0 [] w2 hparent
    (memoLive_mono o12.1 hmemo) (by omega) (fun _ h => nomatch h)
    (fun j hj _ => by
      refine ⟨?_, Row.subset_trans (mergeNonempty_requires ls lt hmerge _ (List.getElem_mem hj))
        hreq, ?_⟩
      · rw [Point.spineChild_eq]
        exact spine_layerPointTyped j (q.child 0) layers ls
          (fun x hx => scopeParams_layer_prefix hat ((List.prefix_append _ _).trans hx))
          (Node.at_child hat rfl) hcs henv (completed_mono o12 hview) (stackTyped_mono o12 hstk) hj
      · obtain ⟨rest, hpath, hparams⟩ := spineChild_below q j
        exact layerStack_below hat rest hpath hparams (ambientStackTyped_mono o12 hstack))
    (fun key member => by
      obtain ⟨x, hx, hk⟩ := mergeNonempty_out ls lt hmerge key member
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
      exact .inr ⟨j, hj, Nat.zero_le _, hk⟩)

/-- **The layer family's build, structurally** (decisions rows 176 (b), 185–187, 349): at an
admitted layer point, at a world whose service table is the source's, into a present scope, at
every available row holding the layer's requirement row, every constructor's build answers the
context of its output row at the layer's checked error type. The layer children structurally; a
reference's hop, which leaves the term, by `hhop` at the next fuel down. -/
theorem layerTerm_typed (hwf : root.program.layerRefsWF = true) (hmod : ModuleLayersTyped root)
    (K : Nat)
    (hhop : ∀ (l : LayerTerm NativeOp) (q : Point) (w : World) (lt : LayerTy) (m : MemoMapId)
      (scope : Nat) (available : Env.Requirement), q.fuel < K → Tied root w →
      Node.at_ (.eff root.program) q.path = some (.layer l) → LayerPointTyped root w q lt →
      ScopeLive w scope → MemoLive w m → Row.Subset lt.requires available →
      AmbientStackTyped root w available (scopeParams root.program q.path) q.params →
      AmbientProg root w available ((buildTy lt, available, available) : AmbientPosition)
        (denoteLayer root.program l q m scope)) :
    ∀ l, BuildsTyped root K l
  | .succeed _ _ => succeed_builds
  | .fresh inner => fresh_builds (layerTerm_typed hwf hmod K hhop inner)
  | .orDie inner => orDie_builds (layerTerm_typed hwf hmod K hhop inner)
  | .effect _ _ => effect_builds
  | .effectDiscard _ => effectDiscard_builds
  | .provide _ that => provide_builds (layerTerm_typed hwf hmod K hhop that)
  | .provideMerge _ that => provideMerge_builds (layerTerm_typed hwf hmod K hhop that)
  | .merge _ _ => merge_builds
  | .mergeAll _ => mergeAll_builds
  | .ref _ => ref_builds hwf hmod hhop

/-- **The layer family's build** (by induction on the fuel a reference's hop spends). -/
theorem layerBuild_typed (hwf : root.program.layerRefsWF = true) (hmod : ModuleLayersTyped root)
    (l : LayerTerm NativeOp) (q : Point) (w : World) (lt : LayerTy) (m : MemoMapId) (scope : Nat)
    (available : Env.Requirement) (htie : Tied root w)
    (hat : Node.at_ (.eff root.program) q.path = some (.layer l)) (hpt : LayerPointTyped root w q lt)
    (hlive : ScopeLive w scope) (hmemo : MemoLive w m) (hreq : Row.Subset lt.requires available)
    (hstack : AmbientStackTyped root w available (scopeParams root.program q.path) q.params) :
    AmbientProg root w available ((buildTy lt, available, available) : AmbientPosition)
      (denoteLayer root.program l q m scope) := by
  suffices main : ∀ K, BuildsTyped root K l ∧ ∀ l', BuildsTyped root K l' from
    (main q.fuel).1 q w lt m scope available (Nat.le_refl _) htie hat hpt hlive hmemo hreq hstack
  intro K
  induction K with
  | zero =>
    have all := layerTerm_typed hwf hmod 0
      (fun _ _ _ _ _ _ _ hlt => absurd hlt (Nat.not_lt_zero _))
    exact ⟨all l, all⟩
  | succ K ih =>
    have all := layerTerm_typed hwf hmod (K + 1)
      (fun l' q' w' lt' m' scope' available' hlt =>
        ih.2 l' q' w' lt' m' scope' available' (Nat.lt_succ_iff.mp hlt))
    exact ⟨all l, all⟩

/-! ## The join's protocol

`Effect.provide(self, layer)` after its counted step (`provideLayerR`): the scope made, the memo
map forked (a private one when `local`, else the fiber context's current one's child), the layer
built through it at the closed build point (`layerBuild_typed`), the body under
`provideContext(built)` at child 1, the scope closed with the exit. -/

/-- `MemoMap.fork` read back, then the build through the forked map (`buildWithMemoMap`). -/
theorem forkBuild_typed {w : World} {available : Env.Requirement} {parent : Option MemoMapId}
    {point : Point} {scope : Nat} {lt : LayerTy} (htie : Tied root w)
    (hpt : ∀ w', w.leHost w' → LayerPointTyped root w' point lt) (hlive : ScopeLive w scope)
    (hreq : Row.Subset lt.requires available)
    (hstack : AmbientStackTyped root w available (scopeParams root.program point.path)
      point.params) :
    AmbientProg root w available ((buildTy lt, available, available) : AmbientPosition)
      ((guardR .onSuccess (storeR (.memoFork parent))).bind (seqR fun u =>
        match Val.memoMap? u with
        | some id => buildWithMemoMapR point id scope
        | none => .pure badShapeExit)) := by
  refine ambient_seqGuard (mid := EffTy.pure Ty.memoMap)
    (ambient_store (op := .memoFork parent) () trivial (fun _ _ h => nomatch h)
      (fun w' _ ans post => ?_))
    (Bounds.subN_never _) (fun w' o v hv => ?_)
  · obtain ⟨id, rfl, hid⟩ := post
    exact .pure ⟨strongExit_success w' _ _ (fits_memoMap w' id hid), Row.subset_refl _⟩
      ⟨Row.subset_refl _, Row.subset_refl _⟩
  · obtain ⟨id, rfl, hid⟩ := fits_memoMap_inv hv
    simp only [seqR, Val.memoMap?_memoMap]
    exact buildWithMemoMap_typed (Tied.mono o htie) (hpt w' o) (scopeLive_mono o.1 hlive)
      hid hreq (ambientStackTyped_mono o hstack)

/-- **The layer family's arm** (decisions rows 176 (b) and 349): a typed `provideLayer` point
denotes a program typed at every row holding the node's requirement row. The build answers the
context of the layer's output row (`layerBuild_typed`); the body's exit, or its run as the installed
region under the built context with the layer's output discharged
(`ambient_updateContext_provide`), is typed at the body's type, widened to the join of the two
error columns the checker gives the node. -/
theorem provideLayer_arm (f : Nat) {w : World} (htie : Tied root w)
    {p : Point} {ty : EffTy} {l : LayerTerm NativeOp} {i : Bool} {b : NativeEff}
    (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.provideLayer l i b)))
    (hpt : PointTyped root w p ty) {available : Env.Requirement}
    (coverage : Row.Subset ty.requires available)
    (savedParams : AmbientStackTyped root w available (scopeParams root.program p.path) p.params) :
    AmbientProg root w available ((ty, available, available) : AmbientPosition)
      (denoteR root.program (.provideLayer l i b) p) := by
  obtain ⟨env, hcheck, henv, -, hstack⟩ := hpt.at_node hat
  rw [Eff.expandIn_provideLayer] at hcheck
  obtain ⟨lt, tb, hcl, hcb, rfl⟩ := Checker.inv_provideLayer _ _ _ _ _ _ _ hcheck
  have hatl : Node.at_ (.eff root.program) (p.path ++ [0]) = some (.layer l) :=
    Node.at_child hat rfl
  have hatb : Node.at_ (.eff root.program) (p.path ++ [1]) = some (.eff b) :=
    Node.at_child hat rfl
  have hreq : Row.Subset lt.requires available :=
    Row.subset_trans (Row.subset_union_left _ _) coverage
  have needed : Row.Subset (Row.diff tb.requires lt.out) available :=
    Row.subset_trans (Row.subset_union_right _ _) coverage
  rw [denoteR_provideLayer _ _ _ _ (by rw [hfuel]; exact Nat.succ_ne_zero f)]
  refine ambient_suspendR_typed root (Row.subset_refl _) (fun w1 o1 =>
    ambient_constructR_typed root (Row.subset_refl _) (fun w2 o2 completed hview => ?_))
  have o12 := leHost_trans _ _ _ o1 o2
  unfold provideLayerR
  refine ambient_seqGuard (mid := EffTy.pure Ty.scope)
    (ambient_store (op := .scopeMake .sequential) () trivial (fun _ _ h => nomatch h)
      (fun w' _ ans post =>
        .pure ⟨strongExit_success w' _ ans post, Row.subset_refl _⟩ ⟨Row.subset_refl _, Row.subset_refl _⟩))
    (Bounds.subN_never _) (fun w3 o3 v hv => ?_)
  obtain ⟨scope, rfl, hlive⟩ := fits_scope_inv hv
  simp only [seqR, Val.scope?_scopeHandle]
  have o13 := leHost_trans _ _ _ o12 o3
  refine ambient_onExit_typed root (bodyType := ⟨tb.answer, tb.error.join lt.error, tb.requires⟩)
    (cleanupType := EffTy.pure .unit) (Ty.subN_refl _) (Ty.subN_refl _) (Bounds.subN_never _) ?_
    (fun w4 o4 _ hok => ambient_fiberAdmin rfl (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) ()
      ⟨scopeLive_mono o4.1 hlive, fitsExit_unknown hok.1⟩
      (fun _ _ ans post => .pure ⟨post, by cases ans <;> exact Row.subset_refl _⟩
        ⟨Row.subset_refl _, Row.subset_refl _⟩))
  -- the build at the closed layer point, at every later world
  have hlpt : ∀ w', w3.leHost w' → LayerPointTyped root w' ({ p with completed } : Point).layerBuild lt :=
    fun w' o => layerPointTyped_scope (scopeParams_child hat 0) hatl hcl rfl
      (completed_mono (leHost_trans _ _ _ o3 o) hview) (stackTyped_mono (leHost_trans _ _ _ o13 o) hstack)
  have hlstack : AmbientStackTyped root w3 available
      (scopeParams root.program ({ p with completed } : Point).layerBuild.path) p.params := by
    show AmbientStackTyped root w3 available (scopeParams root.program (p.path ++ [0])) p.params
    rw [scopeParams_child hat 0]
    exact ambientStackTyped_mono o13 savedParams
  refine ambient_seqGuard (mid := buildTy lt) ?_ (Ty.subN_join_right _ _) (fun w5 o5 u hu => ?_)
  · cases i with
    | true => exact forkBuild_typed (Tied.mono o13 htie) hlpt hlive hreq hlstack
    | false =>
      refine ambient_seqGuard (mid := ⟨.contextOf Env.Requirement.empty, .never, Env.Requirement.empty⟩)
        (ambient_getContext_typed root w3 Env.Requirement.empty available
          (fun a ha => absurd ha (Row.not_mem_empty a)) (fun a ha => absurd ha (Row.not_mem_empty a)))
        (Bounds.subN_never _) (fun w' o x hx => ?_)
      obtain ⟨ctx, hctx, -, -, -⟩ := contextOf_parts hx
      simp only [seqR]
      rw [hctx]
      exact forkBuild_typed (Tied.mono (leHost_trans _ _ _ o13 o) htie)
        (fun w'' o' => hlpt w'' (leHost_trans _ _ _ o o')) (scopeLive_mono o.1 hlive) hreq
        (ambientStackTyped_mono o hlstack)
  -- the body, under the built context, at child 1 of the constructed point
  obtain ⟨ctx, hctx, -, -, -⟩ := contextOf_parts hu
  have same := Val.context?_exact hctx
  subst same
  simp only [seqR, Val.context?_context]
  have o15 := leHost_trans _ _ _ o13 o5
  have hchild : PointTyped root w5 (({ p with completed } : Point).child 1) tb :=
    pointTyped_child hat rfl rfl hcb (envTyped_mono o15 henv)
      (completed_mono (leHost_trans _ _ _ o3 o5) hview) (stackTyped_mono o15 hstack)
  have hfuel1 : (({ p with completed } : Point).child 1).fuel = f := child_fuel_eq hfuel 1
  cases hsub : inlineYield b (({ p with completed } : Point).child 1) with
  | some ex =>
    refine .pure ⟨exitOk_widen (mid := tb) (Ty.subN_refl _) (Ty.subN_join_left _ _)
      (inlineYield_typed (Tied.mono o15 htie) f _ hfuel1 hatb hchild hsub), ?_⟩ ⟨Row.subset_refl _, Row.subset_refl _⟩
    cases ex <;> exact Row.subset_refl _
  | none =>
    refine ambientProg_widen root (before := (⟨tb.answer, tb.error, tb.requires⟩, available, available))
      (after := (⟨tb.answer, tb.error.join lt.error, tb.requires⟩, available, available))
      (Ty.subN_refl _) (Ty.subN_join_left _ _) (Row.subset_refl _) (Row.subset_refl _) ?_
    refine ambient_updateContext_provide root available available tb.requires lt.out ctx hu needed
      (Row.subset_refl _) ⟨tb.answer, tb.error, tb.requires⟩ (.program (({ p with completed } : Point).child 1))
      hchild ?_ (.provide ctx.services) (fun _ => rfl)
    show AmbientStackTyped root w5 available (scopeParams root.program (p.path ++ [1])) p.params
    rw [scopeParams_child hat 1]
    exact ambientStackTyped_mono o15 savedParams

/-- **`ProvideLayerArm` holds at every source**: the hypothesis the assembly was conditional on. -/
theorem provideLayerArm (root : ProgramSource) : ProvideLayerArm root :=
  fun _ _ f _ _ htie _ _ _ _ _ hfuel hat hpt _ coverage savedParams =>
    provideLayer_arm f htie hfuel hat hpt coverage savedParams

end Builds

/-! ## M5, unconditional -/

/-- **M5's fundamental property** (decisions rows 148 and 349, `denotesTyped`): at every source
whose layer references are well formed, a checked point denotes a program typed by the ambient
judgment at every world whose service table is the source's and every row holding its requirement
row. The arms by induction on fuel (`childDenotes_upto`), the layer family's by
`provideLayerArm`. -/
theorem denotesTyped (root : ProgramSource) : DenotesTyped root :=
  denotesTyped_of_provideLayer root (provideLayerArm root)

/-- **M5** (`loadsTyped`): a lawful, checked, closed source whose requirement row is
empty loads into `J` at the initial world, at every fuel and compile budget. -/
theorem loadsTyped (root : ProgramSource) (rootTy : EffTy) (fuel compileFuel : Nat) :
    LoadsTyped root rootTy fuel compileFuel :=
  loadsTyped_of_denotesTyped_typed root rootTy fuel compileFuel (denotesTyped root)

/-- **The typed load for a checked closed program**: row 117's empty requirement row applies
at the load. The source's lawful-signature premise is not read here. -/
theorem load_typed (root : ProgramSource) (rootTy : EffTy) (fuel compileFuel : Nat)
    (checked : Program.typeOfProgram root.sig.signature root.program = some rootTy)
    (closedRow : rootTy.requires = Env.Requirement.empty) :
    ∃ w, MachineTyped root rootTy w (loadR root.program fuel compileFuel) :=
  load_typed_of_denotesTyped_typed root rootTy fuel compileFuel (denotesTyped root) checked closedRow

end Effect4.Program.Typed
