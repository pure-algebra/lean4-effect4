import Effect4.Laws.Program.Typed.Assembly
import Effect4.Laws.Program.Handles.Layer
import Effect4.Laws.Program.PathFold
import Effect4.Laws.Program.ExpandFix
import Effect4.Laws.Program.Typed.Commands.Finish

/-!
# The layer family's arm, and M5 unconditional

Concept 2 of `docs/core/semantics.md` (`residual-program-typing`), claim `denote-typed`: the
denotation of a checked program is `TypedProg` at its certificate, at every world `J` ranges over
(decisions row 148, the fundamental property; algebra A3). `childDenotes_upto`
(`Typed/Denotation.lean`) assembles every arm of `denoteR` by induction on fuel except the layer
family's, which it takes as the hypothesis `ProvideLayerArm` (decisions row 176 (b)). This module
proves that hypothesis at every source (`provideLayerArm`), so M5's two goals close without a
fragment premise: the fundamental property (`denotesTyped`, `denotesTyped`) and the
load (`loadsTyped`, `loadsTyped`), through the load connector whose race-marker
premise the root code's typing discharges (`loadsTyped_of_denotesTyped_typed`,
`Typed/Commands/Finish.lean`, which this module imports for it).

The argument is the logical relation's compatibility lemmas, one per construct (the per-construct
sequencing of `Typed/Seq.lean`, since `TypedProg` is not bind-closed: `E4-TYPED-CE-030`), read
through rc.112's layer code line by line:

* **The build** (`layerBuild_typed`): every `LayerTerm` constructor's build at an admitted layer
  point (`LayerPointTyped`, decisions row 186 (a)) answers the built context — the fiber-context
  image of its service map (row 176 (b)) — at the layer's checked error type. By structural
  recursion on the term (`layerTerm_typed`) inside an induction on the fuel a reference's hop
  spends. A leaf's body is the program induction's (`ChildDenotes`); a hop's target is typed at the
  redirected point because expansion fixes checked terms and checking is path-independent
  (`ExpandFix`, `checkLayer_expandRound`, `checkLayer_path`), and well-formedness gives a target
  that is a layer (`PathFold.layerRefsWF_at`).
* **The memo table** (decisions row 187): a lookup's hit is the entry's deferred, declared at the
  built context and the layer's own checked error type (`memoGet`'s post), so a shared build is
  typed where it is awaited (`memoize_typed`) — the asserting type the guard rule keeps.
* **The merge** (decisions row 186): awaited sibling exits are typed at `Exit<Context, e>`; either
  every context reads back and they merge, or a failure's reasons are the merge's
  (`mergeContexts_typed`); the refusal is unreachable at a typed value.
* **The protocol** (`provideLayer_arm`): the scope made, the memo map forked, the build, the body
  under `provideContext(built)` at child 1, the scope closed with the exit; the node's error column
  is the join of the body's and the layer's (`Checker.inv_provideLayer`).

Every theorem here is a lemma about the residual judgment over rc.112's layer code; none states a
runtime property beyond what `TypedProg` means (`Typed/Residual.lean`). Host boundary: none — the
layer family has no external reply.
-/

set_option autoImplicit false

namespace Effect4.Program.Typed

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote

/-! ## Built contexts

A layer build answers a built context, the fiber-context image of a service map (`builtContext`,
decisions row 176 (b)). It fits the context type when its services fit their keys' types and the
handles its values name are declared: `Fits`' context arm. Every way a build makes one — a
single binding, the empty map, the current memo map added, a right-biased merge, `mergeAll` —
keeps both. -/

/-- Membership in the context type from its two parts. -/
theorem fits_builtContext {w : World} {s : Env.Ctx} (hs : ServicesFit w s)
    (hl : Live w (builtContext s)) : Fits w (builtContext s) (.handle Ty.contextTarget) :=
  ⟨rfl, Ctx.withServices s, Val.context?_context _, hs, hl⟩

/-- Capability membership of a built context from its raw frames' sources. -/
theorem live_builtContext_of {w : World} {s : Env.Ctx} {vs : List Val}
    (hsub : Env.Context.rawHandles s ⊆ vs.flatMap Store.Val.handles) (hl : ∀ v ∈ vs, Live w v) :
    Live w (builtContext s) := by
  intro h hm
  rw [Val.handles_builtContext] at hm
  obtain ⟨v, hv, hk⟩ := List.mem_flatMap.mp (hsub hm)
  exact hl v hv h hk

/-- `Context.add(key, v)` keeps the services fitting when `v` fits the key's carrier. -/
theorem servicesFit_addV {w : World} {s : Env.Ctx} {key : ServiceKey} {v : Val}
    (hs : ServicesFit w s) (hv : ∀ sty, w.serviceTy key = some sty → FlatFits w v sty)
    (hlive : Live w v) : ServicesFit w (s.addV key v) := by
  refine ⟨fun key' sv sty hget hty => ?_, entriesLive_addV hlive hs.2⟩
  by_cases hk : key' = key
  · subst hk
    rw [Env.Context.getV_addV_same] at hget
    cases hget
    exact hv sty hty
  · rw [Env.Context.getV_addV_other _ _ _ _ hk] at hget
    exact hs.1 key' sv sty hget hty

/-- The right-biased merge (`Context.merge`, `ContextUpdate.apply_provide_get?`) keeps the services
fitting: every binding is one side's. -/
theorem servicesFit_merge {w : World} {a b : Env.Ctx} (ha : ServicesFit w a)
    (hb : ServicesFit w b) : ServicesFit w (a.merge b) := by
  refine ⟨fun key sv sty hget hty => ?_, entriesLive_of_flatMap fun x hx => ?_⟩
  · rw [Env.Context.getV_merge] at hget
    cases hbk : b.getV key with
    | some x =>
      rw [hbk] at hget
      cases hget
      exact hb.1 key _ sty hbk hty
    | none =>
      rw [hbk] at hget
      exact ha.1 key sv sty hget hty
  · rcases List.mem_append.mp (Env.Context.rawHandles_merge a b hx) with h | h
    · exact flatMap_live ha.2 x h
    · exact flatMap_live hb.2 x h

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

/-- The types a layer's build runs at: the built context, at the layer's checked error type. -/
def buildTy (lt : LayerTy) : EffTy := ⟨.handle Ty.contextTarget, lt.error, Env.Requirement.empty⟩

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
  simp only [Fits, Ty.memoMap] at h
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

/-- **`fromBuild`** (`Layer.ts:333-345`): the layer scope forked from the caller's present one, the
inner build inside it under the finalizer that closes it on failure. -/
theorem fromBuild_typed {w : World} {T : EffTy} {scope : Nat} {inner : Nat → RProgram}
    (hlive : ScopeLive w scope)
    (hinner : ∀ w', w.leHost w' → ∀ child, ScopeLive w' child → TypedProg root w' T (inner child)) :
    TypedProg root w T (fromBuildR scope inner) := by
  unfold fromBuildR
  refine seqGuard_typed root (mid := EffTy.pure Ty.scope) ?_ (Bounds.subN_never _) (fun w' o v hv => ?_)
  · exact TypedProg.store (op := .scopeFork scope .sequential) (cert := ()) hlive
      (fun w'' _ ans post => .pure (strongExit_success w'' _ ans post))
  · obtain ⟨child, rfl, hchild⟩ := fits_scope_inv hv
    simp only [seqR, Val.scope?_scopeHandle]
    exact onExit_typed root (b := T) (f := EffTy.pure .unit) (Ty.subN_refl _) (Ty.subN_refl _)
      (Bounds.subN_never _) (hinner w' o child hchild)
      (fun w'' o' ex hok => closeChildOnFailure_typed (scopeLive_mono o'.1 hchild) ex
        (fitsExit_unknown hok.1))

/-- **`getOrElseMemoize`** (`Layer.ts:445-457`) at a checked layer leaf: the counted suspend, the
lookup at the layer's columns; a hit registers the entry finalizer on the caller's present scope
and awaits the entry's deferred, declared at the built context and the layer's error (the
memo-table clause, decisions row 187); a miss builds the entry at those columns, registers its
finalizer and runs the construction into the layer scope under the finalizer completing the entry
with the construction's exit. -/
theorem memoize_typed {w : World} {q : Point} {m : MemoMapId} {scope : Nat} {lt : LayerTy}
    {l : LayerTerm NativeOp} {construction : Nat → RProgram}
    (hat : Node.at_ (.eff root.program) q.path = some (.layer l))
    (hcheck : Checker.checkLayer (root.scopeSig q.path) q.path (LayerTerm.expandIn root.program l) =
      .ok lt)
    (hlive : ScopeLive w scope)
    (hcons : ∀ w', w.leHost w' → ∀ layerScope, ScopeLive w' layerScope →
      TypedProg root w' (buildTy lt) (construction layerScope)) :
    TypedProg root w (buildTy lt) (memoizeR q m scope construction) := by
  unfold memoizeR
  refine suspendR_typed root (fun w1 o1 => ?_)
  refine seqGuard_typed root
    (mid := ⟨.union .unit (.prod (.deferredOf (.handle Ty.contextTarget) lt.error) Ty.memoMap),
      .never, Env.Requirement.empty⟩) ?_ (Bounds.subN_never _) (fun w2 o2 v hv => ?_)
  · refine TypedProg.store (op := .memoGet q.path m) (cert := lt.error) ⟨l, lt, hat, hcheck, rfl⟩
      (fun w' _ ans post => .pure (strongExit_success w' _ ans ?_))
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
      show TypedProg root w2 (buildTy lt) (if Val.unit = Val.unit then _ else _)
      rw [if_pos rfl]
      refine seqGuard_typed root (mid := EffTy.pure Ty.scope) ?_ (Bounds.subN_never _)
        (fun w3 o3 u hu => ?_)
      · exact TypedProg.store (op := .memoBuild q.path m) (cert := (.handle Ty.contextTarget, lt.error))
          ⟨l, lt, hat, hcheck, rfl⟩ (fun w'' _ ans post => .pure (strongExit_success w'' _ ans post))
      · obtain ⟨layerScope, rfl, hls⟩ := fits_scope_inv hu
        simp only [seqR, Val.scope?_scopeHandle]
        have o13 := leHost_trans _ _ _ o12 o3
        refine seqGuard_typed root (mid := EffTy.pure .unit)
          (scopeAdd_typed (scopeLive_mono o13.1 hlive) trivial) (Bounds.subN_never _)
          (fun w4 o4 _ _ => ?_)
        simp only [seqR]
        exact onExit_typed root (b := buildTy lt) (f := EffTy.pure .unit) (Ty.subN_refl _)
          (Ty.subN_refl _) (Bounds.subN_never _)
          (hcons w4 (leHost_trans _ _ _ o13 o4) layerScope (scopeLive_mono o4.1 hls))
          (fun w5 _ ex hex => TypedProg.store (op := .memoComplete q.path m ex) (cert := ())
            ⟨l, lt, hat, hcheck, hex⟩ (fun w6 _ ans post => by
              subst post
              exact .pure (strongExit_success w6 _ _ trivial)))
    · -- a hit: the entry finalizer registered, then the await of the entry's deferred
      obtain ⟨x, y, rfl, hx, hy⟩ := (fits_prod_iff w2 v _ _).mp hhit
      obtain ⟨c, rfl, hdecl⟩ := fits_deferredOf_inv hx
      obtain ⟨o, rfl, _⟩ := fits_memoMap_inv hy
      rw [show Val.memoHit? (.list [Val.promise c, Val.memoMap o]) = some (c, o) from
        Val.memoHit?_memoHit c o]
      refine seqGuard_typed root (mid := EffTy.pure .unit)
        (scopeAdd_typed (scopeLive_mono o12.1 hlive) trivial) (Bounds.subN_never _)
        (fun w3 o3 _ _ => ?_)
      simp only [seqR]
      obtain ⟨a', e', hpi, ha, he⟩ := promiseDeclared_mono o3 hdecl
      exact TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
        (fun _ _ _ h => nomatch h) (⟨a', e', Env.Requirement.empty⟩ : EffTy)
        ⟨a', e', hpi, Ty.sub_refl _, Ty.sub_refl _⟩
        (fun w4 _ ans post => .pure (exitOk_widen ha.1 he.1 post))

/-- Capability membership through a raw-frame inclusion. -/
theorem live_of_handles_subset {w : World} {v v' : Val}
    (hsub : Store.Val.handles v ⊆ Store.Val.handles v') (h : Live w v') : Live w v :=
  fun x hx => h x (hsub hx)

/-- A present memo map's handle is live (row 187, amended by F-WF). -/
theorem live_memoMap (w : World) (m : MemoMapId) (h : MemoLive w m) : Live w (Val.memoMap m) :=
  live_kind (k := .memoMap) h

/-- The machine's current-memo-map key types nothing (`SigApp.serviceTy`: a reserved name below
`firstFreeName` other than the scope's). -/
theorem serviceTy_currentMemoMapKey (app : SigApp) : app.serviceTy Env.currentMemoMapKey = none :=
  rfl

/-- **`updateContext`** (`internal/effect.ts:2087-2096`) over an update that keeps the services
fitting: the context read; the same map runs the body as is, else the next context set and the
body under the finalizer restoring the previous one. -/
theorem updateContext_typed {w : World} {T : EffTy} {update : Env.ContextUpdate} {body : RProgram}
    (hupd : ∀ w', w.leHost w' → ∀ prev : Env.Ctx, ServicesFit w' prev →
      ServicesFit w' (update.apply prev))
    (hbody : ∀ w', w.leHost w' → TypedProg root w' T body) :
    TypedProg root w T (updateContextR update body) := by
  unfold updateContextR
  refine seqGuard_typed root (getContext_typed root w) (Bounds.subN_never _) (fun w' o u hu => ?_)
  obtain ⟨prev, hprev, hsvc⟩ := fits_context_inv hu
  simp only [seqR]
  rw [hprev]
  dsimp only
  split
  · exact hbody w' o
  · refine seqGuard_typed root (setContext_typed root (hupd w' o prev.services hsvc))
      (Bounds.subN_never _) (fun w'' o' _ _ => ?_)
    simp only [seqR]
    exact onExit_typed root (b := T) (f := EffTy.pure .unit) (Ty.subN_refl _) (Ty.subN_refl _)
      (Bounds.subN_never _) (hbody w'' (leHost_trans _ _ _ o o'))
      (fun w3 o3 _ _ => setContext_typed root (servicesFit_mono (leHost_trans _ _ _ o' o3) hsvc))

/-- `Context.make(key, value)` or `Context.empty()` over a leaf's answer (`bindServiceR`): a built
context whose one binding fits its key's carrier. -/
theorem bindService_typed {w : World} {key : Option ServiceKey} {v : Val} {T : EffTy}
    (hT : T.answer = .handle Ty.contextTarget)
    (hfit : ∀ k, key = some k → ∀ sty, w.serviceTy k = some sty → FlatFits w v sty)
    (hlive : Live w v) : TypedProg root w T (bindServiceR key v) := by
  cases key with
  | none =>
    refine .pure (strongExit_success w T _ ?_)
    rw [hT]
    exact fits_builtContext (servicesFit_empty w) (live_builtContext_of (vs := [])
      (by rw [Env.Context.rawHandles_empty]; exact List.nil_subset _) (fun _ h => nomatch h))
  | some k =>
    refine .pure (strongExit_success w T _ ?_)
    rw [hT]
    refine fits_builtContext (servicesFit_addV (servicesFit_empty w) (hfit k rfl) hlive) ?_
    refine live_builtContext_of (vs := [v]) ?_ (fun x hx => by
      rw [List.mem_singleton] at hx
      subst hx
      exact hlive)
    intro h hh
    rcases List.mem_append.mp (Env.Context.rawHandles_addV _ k v hh) with h' | h'
    · exact List.mem_flatMap.mpr ⟨v, List.mem_singleton_self _, h'⟩
    · rw [Env.Context.rawHandles_empty] at h'
      exact absurd h' List.not_mem_nil

/-- `Context.add(CurrentMemoMap, memoMap)` over a built context (`addCurrentMemoMapR`): the context
read back, the memo map added under a key that types nothing. -/
theorem addCurrentMemoMap_typed {w : World} {m : MemoMapId} {v : Val} {T : EffTy}
    (htie : w.serviceTy = root.sig.serviceTy) (hT : T.answer = .handle Ty.contextTarget)
    (hm : MemoLive w m) (hv : Fits w v (.handle Ty.contextTarget)) :
    TypedProg root w T (addCurrentMemoMapR m v) := by
  obtain ⟨ctx, hctx, hsvc⟩ := fits_context_inv hv
  have hlive := fits_live w _ v hv
  unfold addCurrentMemoMapR
  rw [hctx]
  refine .pure (strongExit_success w T _ ?_)
  rw [hT]
  refine fits_builtContext (servicesFit_addV hsvc (fun sty h => ?_)
    (fits_live w Ty.memoMap _ ⟨rfl, hm⟩)) ?_
  · rw [htie, serviceTy_currentMemoMapKey] at h
    cases h
  · refine live_builtContext_of (vs := [Val.memoMap m, v]) ?_ ?_
    · intro h hh
      rcases List.mem_append.mp (Env.Context.rawHandles_addV _ _ _ hh) with h' | h'
      · exact List.mem_flatMap.mpr ⟨_, List.mem_cons_self .., h'⟩
      · refine List.mem_flatMap.mpr ⟨v, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
        exact Val.context?_handles hctx h'
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact live_memoMap w m hm
      · rw [List.mem_singleton] at hx'
        subst hx'
        exact hlive

/-- `f(merged, context)` (`Layer.ts:1923`): `provide` answers the dependent's context as read,
`provideMerge` the dependency's map merged under it. -/
theorem combineWith_typed {w : World} {mode : CombineMode} {that : Env.Ctx} {v : Val} {T : EffTy}
    (hT : T.answer = .handle Ty.contextTarget)
    (hthat : Fits w (builtContext that) (.handle Ty.contextTarget))
    (hv : Fits w v (.handle Ty.contextTarget)) :
    TypedProg root w T (combineWithR mode that v) := by
  obtain ⟨merged, hctx, hsvc⟩ := fits_context_inv hv
  have hlive := fits_live w _ v hv
  unfold combineWithR
  rw [hctx]
  cases mode with
  | provide =>
    refine .pure (strongExit_success w T _ ?_)
    rw [hT, ← Val.context?_exact hctx]
    exact hv
  | provideMerge =>
    obtain ⟨thatCtx, hthatCtx, hthatSvc⟩ := fits_context_inv hthat
    have hread : Val.context? (builtContext that) = some (Ctx.withServices that) :=
      Val.context?_context _
    rw [hread] at hthatCtx
    cases hthatCtx
    refine .pure (strongExit_success w T _ ?_)
    rw [hT]
    refine fits_builtContext (servicesFit_merge hthatSvc hsvc) ?_
    refine live_builtContext_of (vs := [builtContext that, v]) ?_ ?_
    · intro h hh
      rcases List.mem_append.mp (Env.Context.rawHandles_merge _ _ hh) with h' | h'
      · refine List.mem_flatMap.mpr ⟨builtContext that, List.mem_cons_self .., ?_⟩
        rw [Val.handles_builtContext]
        exact h'
      · exact List.mem_flatMap.mpr ⟨v, List.mem_cons_of_mem _ (List.mem_singleton_self _),
          Val.context?_handles hctx h'⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact fits_live w _ _ hthat
      · rw [List.mem_singleton] at hx'
        subst hx'
        exact hlive

/-- **`provideWith`** (`Layer.ts:1915-1923`): the dependency built, the dependent under
`provideContext(context)`, then the combiner; both builds' errors below the result's. -/
theorem provideWith_typed {w : World} {dependency dependent : RProgram} {mode : CombineMode}
    {T Td Ts : EffTy} (hT : T.answer = .handle Ty.contextTarget)
    (hTd : Td.answer = .handle Ty.contextTarget) (hTs : Ts.answer = .handle Ty.contextTarget)
    (herrd : Ty.subN Td.error T.error = true) (herrs : Ty.subN Ts.error T.error = true)
    (hdep : TypedProg root w Td dependency)
    (hdnt : ∀ w', w.leHost w' → TypedProg root w' Ts dependent) :
    TypedProg root w T (provideWithR dependency dependent mode) := by
  unfold provideWithR
  refine seqGuard_typed root hdep herrd (fun w' o v hv => ?_)
  rw [hTd] at hv
  obtain ⟨ctx, hctx, hsvc⟩ := fits_context_inv hv
  have hbuilt : Fits w' (builtContext ctx.services) (.handle Ty.contextTarget) := by
    refine fits_builtContext hsvc (live_of_handles_subset ?_ (fits_live w' _ v hv))
    intro x hx
    rw [Val.handles_builtContext] at hx
    exact Val.context?_handles hctx hx
  simp only [seqR]
  rw [hctx]
  dsimp only
  refine seqGuard_typed root (mid := Ts)
    (updateContext_typed (fun w'' o' prev hprev => servicesFit_merge hprev (servicesFit_mono o' hsvc))
      (fun w'' o' => hdnt w'' (leHost_trans _ _ _ o o')))
    herrs (fun w'' o' u hu => ?_)
  simp only [seqR]
  rw [hTs] at hu
  exact combineWith_typed hT (fits_mono o' hbuilt) hu

/-- **`buildWithMemoMap`** (`Layer.ts:756-765`): the build through the map under
`provideService(CurrentMemoMap)`, the map added to its answer; the key types nothing. -/
theorem buildWithMemoMap_typed {w : World} {build : MemoMapId → RProgram} {m : MemoMapId}
    {lt : LayerTy} (htie : w.serviceTy = root.sig.serviceTy) (hm : MemoLive w m)
    (hbuild : ∀ w', w.leHost w' → TypedProg root w' (buildTy lt) (build m)) :
    TypedProg root w (buildTy lt) (buildWithMemoMapR build m) := by
  unfold buildWithMemoMapR
  refine updateContext_typed (fun w' o prev hprev => servicesFit_addV hprev (fun sty h => ?_)
    (fits_live w' Ty.memoMap _ ⟨rfl, memoLive_mono o.1 hm⟩)) (fun w' o => ?_)
  · rw [serviceTy_leHost o htie, serviceTy_currentMemoMapKey] at h
    cases h
  · exact seqGuard_typed root (hbuild w' o) (Ty.subN_refl _) (fun w'' o' v hv =>
      addCurrentMemoMap_typed (serviceTy_leHost (leHost_trans _ _ _ o o') htie) rfl
        (memoLive_mono (leHost_trans _ _ _ o o').1 hm) hv)

/-- The contexts read back from awaited exits each fit, when every exit fits `Exit<Context, e>`. -/
theorem contextsOfList_fit {w : World} {e : Ty} : ∀ (xs : List Val) (cs : List Env.Ctx),
    (∀ x ∈ xs, Fits w x (.exitOf (.handle Ty.contextTarget) e)) → contextsOfList xs = some cs →
    ∀ c ∈ cs, ServicesFit w c
  | [], cs, _, h => by
    simp only [contextsOfList, Option.some.injEq] at h
    subst h
    intro c hc
    exact nomatch hc
  | x :: rest, cs, hall, h => by
    simp only [contextsOfList] at h
    split at h
    · rename_i c hx
      split at h
      · rename_i ctx ctxs hctx hrest
        simp only [Option.some.injEq] at h
        subst h
        intro d hd
        rcases List.mem_cons.mp hd with rfl | hd'
        · have hfe := fitsExit_of_exitOfVal (hall x (List.mem_cons_self ..)) hx
          obtain ⟨ctx', hctx', hsvc⟩ := fits_context_inv hfe
          rw [hctx] at hctx'
          cases hctx'
          exact hsvc
        · exact contextsOfList_fit rest ctxs (fun y hy => hall y (List.mem_cons_of_mem _ hy)) hrest
            d hd'
      · cases h
    · cases h

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
      simp only [Fits] at hfx
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

/-- Awaited exits none of which failed have their contexts read back. -/
theorem contextsOfList_some {w : World} {e : Ty} : ∀ (xs : List Val),
    (∀ x ∈ xs, Fits w x (.exitOf (.handle Ty.contextTarget) e)) →
    (xs.any fun x => match exitOfVal x with
      | some (Exit.failure _) => true
      | _ => false) = false →
    ∃ cs, contextsOfList xs = some cs
  | [], _, _ => ⟨[], rfl⟩
  | x :: rest, hall, hnone => by
    rw [List.any_cons, Bool.or_eq_false_iff] at hnone
    obtain ⟨hxnot, hrest⟩ := hnone
    obtain ⟨cs, hcs⟩ := contextsOfList_some rest (fun y hy => hall y (List.mem_cons_of_mem _ hy)) hrest
    have hfx := hall x (List.mem_cons_self ..)
    obtain ⟨ex, hex⟩ := exitOfVal_of_fits hfx
    cases ex with
    | failure c =>
      rw [hex] at hxnot
      exact nomatch hxnot
    | success c =>
      have hfe := fitsExit_of_exitOfVal hfx hex
      obtain ⟨ctx, hctx, _⟩ := fits_context_inv hfe
      exact ⟨ctx.services :: cs, by simp only [contextsOfList, hex, hctx, hcs]⟩

/-- **The merge** (`Layer.ts:1600`) over awaited exits typed at `Exit<Context, e>`: every build
succeeded, and the contexts merge into a built context; or one failed, and the merge fails with
the failures' reasons, which fit the error column (decisions row 186). The refusal is unreachable:
a value the list type admits that holds no failed exit holds every context. -/
theorem mergeContexts_typed {w : World} {v : Val} {e : Ty} {T : EffTy}
    (hT : T.answer = .handle Ty.contextTarget) (he : Ty.subN e T.error = true)
    (hv : Fits w v (.list (.exitOf (.handle Ty.contextTarget) e))) :
    TypedProg root w T (mergeContextsR v) := by
  obtain ⟨xs, hxs, hall⟩ := (fits_list_iff w v _).mp hv
  have hco : contextsOf v = contextsOfList xs := by
    unfold contextsOf
    rw [hxs]
    rfl
  unfold mergeContextsR
  rw [hco]
  cases hc : contextsOfList xs with
  | some cs =>
    refine .pure (strongExit_success w T _ ?_)
    rw [hT]
    refine fits_builtContext (servicesFit_mergeAll cs (contextsOfList_fit xs cs hall hc)) ?_
    exact live_builtContext_of (vs := xs)
      (List.Subset.trans (Env.Context.rawHandles_mergeAll cs) (contextsOfList_handles xs cs hc))
      (fun x hx => fits_live w _ x (hall x hx))
  | none =>
    have hfailed : failedIn v = true := by
      cases hf : failedIn v with
      | true => rfl
      | false =>
        have hany : (xs.any fun x => match exitOfVal x with
            | some (Exit.failure _) => true
            | _ => false) = false := by
          unfold failedIn at hf
          rw [hxs, Option.getD_some] at hf
          exact hf
        obtain ⟨cs, hcs⟩ := contextsOfList_some xs hall hany
        rw [hc] at hcs
        cases hcs
    simp only [hfailed, if_true]
    have hreasons : ∀ r ∈ reasonsOfVal v,
        (match r with
          | .fail err _ => ∃ u, valOfErr err = some u ∧ Fits w u e
          | .die _ _ | .interrupt _ _ => True) ∧
        (match r with
          | .die defect _ => defect ≠ .badName ∧ defect ≠ .notImplemented
          | _ => True) := by
      rcases Val.asList?_exact hxs with rfl | ⟨ids, rfl, -⟩
      · exact reasonsOfList_fit xs hall
      · intro r hr
        simp only [reasonsOfVal] at hr
        exact nomatch hr
    refine .pure ⟨(fitsExit_failure_iff w T _).mpr ⟨fun r hr => ?_, fun r hr => (hreasons r hr).2⟩,
      fun r hr => (hreasons r hr).2⟩
    have h1 := (hreasons r hr).1
    revert h1
    cases r with
    | fail err ann =>
      intro h1
      obtain ⟨u, hu, hfit⟩ := h1
      exact ⟨u, hu, fits_subN w he u hfit⟩
    | die _ _ => intro _; trivial
    | interrupt _ _ => intro _; trivial

/-- One sibling's build forked as an immediate daemon (`Layer.ts:1597`): the fork's body is the
build at the sibling's admitted layer point into a present scope (`BodyTyped.layerBuild`, decisions
row 186 (a)), its fiber declared at the build's types. -/
theorem forkLayer_typed {w : World} {q : Point} {m : MemoMapId} {scope : Nat} {lt : LayerTy}
    (hpt : LayerPointTyped root w q lt) (hlive : ScopeLive w scope) (hmemo : MemoLive w m) :
    TypedProg root w ⟨.fiberOf (.handle Ty.contextTarget) lt.error, .never, Env.Requirement.empty⟩
      (forkLayerR q m scope) :=
  TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) (buildTy lt) (BodyTyped.layerBuild q m scope lt hpt hlive hmemo)
    (fun w' _ ans post => by
      obtain ⟨id, rfl, hΓ⟩ := post
      exact .pure (strongExit_success w' _ _ ⟨buildTy lt, hΓ, Ty.subN_refl _, Ty.subN_refl _⟩))

/-- A forked sibling's fiber, declared below `(Context, e)`, is declared below every wider error. -/
theorem fiberDeclared_widen {w : World} {id : FiberId} {a e e' : Ty}
    (h : FiberDeclared w id a e) (he : Ty.subN e e' = true) : FiberDeclared w id a e' := by
  obtain ⟨fty, hΓ, ha, hfe⟩ := h
  exact ⟨fty, hΓ, ha, Ty.subN_trans hfe he⟩

/-- **`mergeAllEffect`'s loop for two siblings** (`Layer.ts:1597-1600`): a sequential child of the
present parallel parent per sibling, the sibling's build forked into it, then the await of both
and the merge, at the merge's types. -/
theorem mergeFork_typed {w : World} {q : Point} {m : MemoMapId} {parent : Nat} {la lb : LayerTy}
    (hlive : ScopeLive w parent) (hmemo : MemoLive w m) (ha : LayerPointTyped root w (q.child 0) la)
    (hb : LayerPointTyped root w (q.child 1) lb) :
    TypedProg root w (buildTy (la.merge lb)) (mergeForkR q m parent) := by
  unfold mergeForkR
  refine seqGuard_typed root (mid := EffTy.pure Ty.scope)
    (TypedProg.store (op := .scopeFork parent .sequential) (cert := ()) hlive
      (fun w' _ ans post => .pure (strongExit_success w' _ ans post)))
    (Bounds.subN_never _) (fun w1 o1 v hv => ?_)
  obtain ⟨c0, rfl, hc0⟩ := fits_scope_inv hv
  simp only [seqR, Val.scope?_scopeHandle]
  refine seqGuard_typed root (forkLayer_typed (layerPointTyped_mono o1 ha) hc0 (memoLive_mono o1.1 hmemo))
    (Bounds.subN_never _)
    (fun w2 o2 f0 hf0 => ?_)
  obtain ⟨i0, rfl, hd0⟩ := fiber_of_fits hf0
  simp only [seqR]
  rw [show Val.fiber? (Value.fiber i0) = some ⟨i0⟩ from rfl]
  dsimp only
  have o12 := leHost_trans _ _ _ o1 o2
  refine seqGuard_typed root (mid := EffTy.pure Ty.scope)
    (TypedProg.store (op := .scopeFork parent .sequential) (cert := ())
      (scopeLive_mono o12.1 hlive)
      (fun w' _ ans post => .pure (strongExit_success w' _ ans post)))
    (Bounds.subN_never _) (fun w3 o3 u hu => ?_)
  obtain ⟨c1, rfl, hc1⟩ := fits_scope_inv hu
  simp only [seqR, Val.scope?_scopeHandle]
  have o13 := leHost_trans _ _ _ o12 o3
  refine seqGuard_typed root
    (forkLayer_typed (layerPointTyped_mono o13 hb) hc1 (memoLive_mono o13.1 hmemo)) (Bounds.subN_never _)
    (fun w4 o4 f1 hf1 => ?_)
  obtain ⟨i1, rfl, hd1⟩ := fiber_of_fits hf1
  simp only [seqR]
  rw [show Val.fiber? (Value.fiber i1) = some ⟨i1⟩ from rfl]
  dsimp only
  -- the await of both siblings, at their declarations widened to the merge's error
  have hd0w : FiberDeclared w4 ⟨i0⟩ (.handle Ty.contextTarget) la.error := by
    obtain ⟨fty, hΓ, ha', he'⟩ := hd0
    exact ⟨fty, (leHost_trans _ _ _ o3 o4).1.2.1 _ _ hΓ, ha', he'⟩
  have hd0' : FiberDeclared w4 ⟨i0⟩ (.handle Ty.contextTarget) (la.error.join lb.error) :=
    fiberDeclared_widen hd0w (Ty.subN_join_left _ _)
  have hd1' : FiberDeclared w4 ⟨i1⟩ (.handle Ty.contextTarget) (la.error.join lb.error) :=
    fiberDeclared_widen hd1 (Ty.subN_join_right _ _)
  obtain ⟨A, E, hpre, hA, hE⟩ := awaitAllCert (ids := [⟨i0⟩, ⟨i1⟩])
    (a := .handle Ty.contextTarget) (e := la.error.join lb.error) (fun id hid => by
      rcases List.mem_cons.mp hid with rfl | hid'
      · exact hd0'
      · rw [List.mem_singleton] at hid'
        subst hid'
        exact hd1')
  refine seqGuard_typed root (mid := ⟨.list (.exitOf A E), .never, Env.Requirement.empty⟩)
    (TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ _ _ h => nomatch h) (.list (.exitOf A E)) ⟨A, E, rfl, hpre⟩
      (fun w' _ ans post => .pure (strongExit_success w' _ ans post)))
    (Bounds.subN_never _) (fun w5 _ ex hex => ?_)
  simp only [seqR]
  exact mergeContexts_typed rfl (Ty.subN_refl _) (fits_subN w5 (subN_listExitOf hA hE) ex hex)

/-- **`Layer.merge`'s build** after `fromBuild` (`Layer.ts:1587-1602`): the parallel parent forked
from the layer scope, then the two siblings. -/
theorem mergeTwo_typed {w : World} {q : Point} {m : MemoMapId} {child : Nat} {la lb : LayerTy}
    (hlive : ScopeLive w child) (hmemo : MemoLive w m) (ha : LayerPointTyped root w (q.child 0) la)
    (hb : LayerPointTyped root w (q.child 1) lb) :
    TypedProg root w (buildTy (la.merge lb)) (mergeTwoR q m child) := by
  unfold mergeTwoR
  refine seqGuard_typed root (mid := EffTy.pure Ty.scope)
    (TypedProg.store (op := .scopeFork child .parallel) (cert := ()) hlive
      (fun w' _ ans post => .pure (strongExit_success w' _ ans post)))
    (Bounds.subN_never _) (fun w1 o1 v hv => ?_)
  obtain ⟨parent, rfl, hparent⟩ := fits_scope_inv hv
  simp only [seqR, Val.scope?_scopeHandle]
  exact mergeFork_typed hparent (memoLive_mono o1.1 hmemo) (layerPointTyped_mono o1 ha)
    (layerPointTyped_mono o1 hb)

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
  layerPointTyped_scope (scopeParams_layer_below hat [i]) (node_at_child hat hc) hcheck henv hview
    hstack

/-- One more round, applied first, is one more round applied last. -/
private theorem foldl_shift {α β : Type} (g : α → α) : ∀ (L : List β) (x : α),
    L.foldl (fun acc _ => g acc) (g x) = g (L.foldl (fun acc _ => g acc) x) :=
  fun _ _ => List.foldl_hom g (fun _ _ => rfl)

/-- The node a layer lookup reads. -/
theorem at_of_layerAt {n : Node NativeOp} {path : List Nat} {l : LayerTerm NativeOp}
    (h : n.layerAt path = some l) : Node.at_ n path = some (.layer l) := by
  unfold Node.layerAt at h
  split at h
  · rename_i l' hat
    cases h
    exact hat
  · cases h

/-- **The hop's point** (decisions rows 153 (b), 170): a reference's check reads the target's term
after the expansion's rounds; that term, checked, is fixed by one more round (`ExpandFix`), so the
target's own rounds give the same term, which the checker types at the target's path as at the
site's (`checkLayer_path`). -/
theorem layerPointTyped_redirect {w : World} {q : Point} {target : List Nat} {lt : LayerTy}
    {l : LayerTerm NativeOp} (hat : Node.at_ (.eff root.program) q.path = some (.layer (.ref target)))
    (hs : scopeParams root.program target = scopeParams root.program q.path)
    (hpt : LayerPointTyped root w q lt) (hlayer : (Node.eff root.program).layerAt target = some l) :
    LayerPointTyped root w (q.redirect target) lt := by
  obtain ⟨hcheck, henv, hview, hstack⟩ := hpt.at_layer hat
  -- the target stands in the reference's scope, so the reference's stack reads its parameters
  refine layerPointTyped_scope hs (at_of_layerAt hlayer) ?_ henv hview hstack
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
  exact checkLayer_path hcheck target

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

/-- A leaf's construction on its layer scope (`Layer.ts:1482`, `:1440`, `:1515`): the layer scope
provided under the scope key, the body at the leaf's child point, its answer bound under the key
(or the empty context). -/
theorem construction_typed {w : World} {q : Point} {key : Option ServiceKey} {body : NativeEff}
    {t : EffTy} {lt : LayerTy} {layerScope : Nat} (htie : w.serviceTy = root.sig.serviceTy)
    (hls : ScopeLive w layerScope) (herr : lt.error = t.error)
    (hbody : ∀ w', w.leHost w' → TypedProg root w' t (denoteR root.program body (q.child 0)))
    (hkey : ∀ k, key = some k → ∀ w', w.leHost w' → ∀ v, Fits w' v t.answer → ∀ sty,
      w'.serviceTy k = some sty → FlatFits w' v sty) :
    TypedProg root w (buildTy lt)
      (updateContextR (.provideService Env.scopeKey (Val.scopeHandle layerScope))
        ((guardR .onSuccess (denoteR root.program body (q.child 0))).bind (seqR fun v =>
          bindServiceR key v))) := by
  refine updateContext_typed (fun w' o prev hprev => servicesFit_addV hprev (fun sty hst => ?_)
    (fits_live w' Ty.scope _ (fits_scopeHandle w' layerScope (scopeLive_mono o.1 hls))))
    (fun w' o => ?_)
  · rw [serviceTy_leHost o htie, serviceTy_scopeKey] at hst
    cases hst
    exact fits_flatFits rfl (fits_scopeHandle w' layerScope (scopeLive_mono o.1 hls))
  · refine seqGuard_typed root (hbody w' o) (by rw [show (buildTy lt).error = lt.error from rfl, herr]; exact Ty.subN_refl _)
      (fun w'' o' v hv => ?_)
    simp only [seqR]
    exact bindService_typed rfl (fun k hk sty hst => hkey k hk w'' (leHost_trans _ _ _ o o') v hv sty hst)
      (fits_live w'' _ v hv)

/-- The recursion's motive: the build of a layer term is typed at every admitted point of it, at a
world whose service table is the source's, into a present scope through a present memo map
(finding F-WF: the map is installed into the built context), within the fuel bounds. -/
abbrev BuildsTyped (root : ProgramSource) (f K : Nat) (l : LayerTerm NativeOp) : Prop :=
  ∀ (q : Point) (w : World) (lt : LayerTy) (m : MemoMapId) (scope : Nat),
    q.fuel ≤ K → q.fuel ≤ f → w.serviceTy = root.sig.serviceTy →
    Node.at_ (.eff root.program) q.path = some (.layer l) → LayerPointTyped root w q lt →
    ScopeLive w scope → MemoLive w m → TypedProg root w (buildTy lt) (denoteLayer root.program l q m scope)

/-- **`Layer.succeed`** (`Layer.ts:1129`): the literal bound under its key, at the key's carrier. -/
theorem succeed_builds {key : ServiceKey} {value : Lit} {f K : Nat} :
    BuildsTyped root f K (.succeed key value) := by
  intro q w lt m scope _ _ htie hat hpt _ _
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
  refine bindService_typed (key := some key) rfl (fun k hk sty hst => ?_)
    (live_of_handles_nil (Effect4.Program.RawHandles.lit_toVal_handles value x hx))
  cases hk
  rw [htie] at hst
  have hsty' : root.sig.serviceTy key = some ty := hsty
  rw [hsty'] at hst
  cases hst
  exact fits_flatFits (serviceTy_flat root key ty hsty) (fits_subN w hsub x hfx)

/-- **`Layer.fresh`** (`Layer.ts:3851`): the inner layer built through a brand-new memo map. -/
theorem fresh_builds {inner : LayerTerm NativeOp} {f K : Nat} (hi : BuildsTyped root f K inner) :
    BuildsTyped root f K (.fresh inner) := by
  intro q w lt m scope hK hf htie hat hpt hlive hmemo
  obtain ⟨hcheck, henv, hview, hstack⟩ := hpt.at_layer hat
  rw [LayerTerm.expandIn_fresh] at hcheck
  have hc := Checker.inv_layer_fresh _ _ _ _ hcheck
  rw [denoteLayer_fresh]
  refine seqGuard_typed root (mid := EffTy.pure Ty.memoMap)
    (TypedProg.store (op := .memoFork none) (cert := ()) trivial (fun w' _ ans post => by
      obtain ⟨id, rfl, hid⟩ := post
      exact .pure (strongExit_success w' _ _ (fits_memoMap w' id hid))))
    (Bounds.subN_never _) (fun w' o v hv => ?_)
  obtain ⟨id, rfl, hid⟩ := fits_memoMap_inv hv
  simp only [seqR, Val.memoMap?_memoMap]
  exact hi (q.child 0) w' lt id scope
    (Nat.le_trans (Nat.sub_le _ _) hK) (Nat.le_trans (Nat.sub_le _ _) hf)
    (serviceTy_leHost o htie) (node_at_child hat rfl)
    (layerPointTyped_child hat rfl hc henv (completed_mono o hview) (stackTyped_mono o hstack))
    (scopeLive_mono o.1 hlive) hid

/-- **`Layer.orDie`** (`Layer.ts:3327`): the inner build's failure turned into a defect, which fits
every error column (`orDieCause_exitOk`); the inner layer is built as it resolves (decisions row 185). -/
theorem orDie_builds {inner : LayerTerm NativeOp} {f K : Nat} (hi : BuildsTyped root f K inner) :
    BuildsTyped root f K (.orDie inner) := by
  intro q w lt m scope hK hf htie hat hpt hlive hmemo
  obtain ⟨hcheck, henv, hview, hstack⟩ := hpt.at_layer hat
  rw [LayerTerm.expandIn_orDie] at hcheck
  obtain ⟨li, hci, rfl⟩ := Checker.inv_layer_orDie _ _ _ _ hcheck
  rw [denoteLayer_orDie]
  exact catchGuard_typed root
    (hi (q.child 0) w li m scope
      (Nat.le_trans (Nat.sub_le _ _) hK) (Nat.le_trans (Nat.sub_le _ _) hf) htie
      (node_at_child hat rfl) (layerPointTyped_child hat rfl hci henv hview hstack) hlive hmemo)
    (Ty.subN_refl _) (fun w' _ c hc => .pure (orDieCause_exitOk hc))

/-- **`Layer.effect`** (`Layer.ts:1482`): `fromBuild`, the memoized leaf, its construction on the
layer scope, the body's answer bound under the key at the key's carrier. -/
theorem effect_builds {key : ServiceKey} {body : NativeEff} {f K : Nat} (hIH : ∀ f' ≤ f, ∀ (c : NativeEff) (path : List Nat),
      Node.at_ (.eff root.program) path = some (.eff c) → ChildDenotes root f' c path) :
    BuildsTyped root f K (.effect key body) := by
  intro q w lt m scope _ hf htie hat hpt hlive _
  obtain ⟨hcheck0, henv, hview, hstack⟩ := hpt.at_layer hat
  have hcheck := hcheck0
  rw [LayerTerm.expandIn_effect] at hcheck
  obtain ⟨t, ty, hcb, hsty, hsub, rfl⟩ := Checker.inv_layer_effect _ _ _ _ _ hcheck
  rw [root.scopeSig_serviceTy] at hsty
  rw [denoteLayer_effect]
  refine fromBuild_typed hlive (fun w1 o1 child hchild => ?_)
  refine memoize_typed hat hcheck0 hchild (fun w2 o2 layerScope hls => ?_)
  have o12 := leHost_trans _ _ _ o1 o2
  refine construction_typed (serviceTy_leHost o12 htie) hls rfl (fun w3 o3 => ?_) ?_
  · have o13 := leHost_trans _ _ _ o12 o3
    refine hIH _ (Nat.le_trans (Nat.sub_le _ _) hf) body (q.path ++ [0]) (node_at_child hat rfl) w3
      (serviceTy_leHost o13 htie) (q.child 0) t rfl rfl
      (pointTyped_scope (scopeParams_layer_below hat [0]) (node_at_child hat rfl) hcb ?_
        (completed_mono o13 hview) (stackTyped_mono o13 hstack))
    show EnvTyped w3 [] q.env
    rw [henv]
    exact envTyped_nil w3
  · intro k hk w' o' v hv sty hst
    cases hk
    rw [serviceTy_leHost (leHost_trans _ _ _ o12 o') htie] at hst
    have hsty' : root.sig.serviceTy key = some ty := hsty
    rw [hsty'] at hst
    cases hst
    exact fits_flatFits (serviceTy_flat root key ty hsty) (fits_subN w' hsub v hv)

/-- **`Layer.effectDiscard`** (`Layer.ts:1440`): as `effect`, the answer discarded for the empty
context. -/
theorem effectDiscard_builds {body : NativeEff} {f K : Nat} (hIH : ∀ f' ≤ f, ∀ (c : NativeEff) (path : List Nat),
      Node.at_ (.eff root.program) path = some (.eff c) → ChildDenotes root f' c path) :
    BuildsTyped root f K (.effectDiscard body) := by
  intro q w lt m scope _ hf htie hat hpt hlive _
  obtain ⟨hcheck0, henv, hview, hstack⟩ := hpt.at_layer hat
  have hcheck := hcheck0
  rw [LayerTerm.expandIn_effectDiscard] at hcheck
  obtain ⟨t, hcb, rfl⟩ := Checker.inv_layer_effectDiscard _ _ _ _ hcheck
  rw [denoteLayer_effectDiscard]
  refine fromBuild_typed hlive (fun w1 o1 child hchild => ?_)
  refine memoize_typed hat hcheck0 hchild (fun w2 o2 layerScope hls => ?_)
  have o12 := leHost_trans _ _ _ o1 o2
  refine construction_typed (serviceTy_leHost o12 htie) hls rfl (fun w3 o3 => ?_)
    (fun k hk => nomatch hk)
  have o13 := leHost_trans _ _ _ o12 o3
  refine hIH _ (Nat.le_trans (Nat.sub_le _ _) hf) body (q.path ++ [0]) (node_at_child hat rfl) w3
    (serviceTy_leHost o13 htie) (q.child 0) t rfl rfl
    (pointTyped_scope (scopeParams_layer_below hat [0]) (node_at_child hat rfl) hcb ?_
      (completed_mono o13 hview) (stackTyped_mono o13 hstack))
  show EnvTyped w3 [] q.env
  rw [henv]
  exact envTyped_nil w3

/-- **`Layer.provide`** (`Layer.ts:1915`): `fromBuild`, the dependency built, the dependent under its
context; the dependent's context answered. -/
theorem provide_builds {self that : LayerTerm NativeOp} {f K : Nat} (hs : BuildsTyped root f K self) (ht : BuildsTyped root f K that) :
    BuildsTyped root f K (.provide self that) := by
  intro q w lt m scope hK hf htie hat hpt hlive hmemo
  obtain ⟨hcheck, henv, hview, hstack⟩ := hpt.at_layer hat
  rw [LayerTerm.expandIn_provide] at hcheck
  obtain ⟨ls, lt', hcs, hct, rfl⟩ := Checker.inv_layer_provide _ _ _ _ _ hcheck
  rw [denoteLayer_provide]
  refine fromBuild_typed hlive (fun w1 o1 child hchild => ?_)
  have hview1 := completed_mono o1 hview
  have htie1 := serviceTy_leHost o1 htie
  exact provideWith_typed (T := buildTy (ls.provide lt')) (Td := buildTy lt') (Ts := buildTy ls)
    rfl rfl rfl (Ty.subN_join_right ls.error lt'.error) (Ty.subN_join_left ls.error lt'.error)
    (ht (q.child 1) w1 lt' m child
      (Nat.le_trans (Nat.sub_le _ _) hK) (Nat.le_trans (Nat.sub_le _ _) hf) htie1
      (node_at_child hat rfl) (layerPointTyped_child hat rfl hct henv hview1 (stackTyped_mono o1 hstack))
        hchild
      (memoLive_mono o1.1 hmemo))
    (fun w2 o2 => hs (q.child 0) w2 ls m child
      (Nat.le_trans (Nat.sub_le _ _) hK) (Nat.le_trans (Nat.sub_le _ _) hf)
      (serviceTy_leHost o2 htie1) (node_at_child hat rfl)
      (layerPointTyped_child hat rfl hcs henv (completed_mono o2 hview1)
        (stackTyped_mono (leHost_trans _ _ _ o1 o2) hstack)) (scopeLive_mono o2.1 hchild)
      (memoLive_mono (leHost_trans _ _ _ o1 o2).1 hmemo))

/-- **`Layer.provideMerge`** (`Layer.ts:1915-1923`): as `provide`, the dependency's map merged under
the dependent's. -/
theorem provideMerge_builds {self that : LayerTerm NativeOp} {f K : Nat} (hs : BuildsTyped root f K self) (ht : BuildsTyped root f K that) :
    BuildsTyped root f K (.provideMerge self that) := by
  intro q w lt m scope hK hf htie hat hpt hlive hmemo
  obtain ⟨hcheck, henv, hview, hstack⟩ := hpt.at_layer hat
  rw [LayerTerm.expandIn_provideMerge] at hcheck
  obtain ⟨ls, lt', hcs, hct, rfl⟩ := Checker.inv_layer_provideMerge _ _ _ _ _ hcheck
  rw [denoteLayer_provideMerge]
  refine fromBuild_typed hlive (fun w1 o1 child hchild => ?_)
  have hview1 := completed_mono o1 hview
  have htie1 := serviceTy_leHost o1 htie
  exact provideWith_typed (T := buildTy (ls.provideMerge lt')) (Td := buildTy lt')
    (Ts := buildTy ls) rfl rfl rfl (Ty.subN_join_right ls.error lt'.error)
    (Ty.subN_join_left ls.error lt'.error)
    (ht (q.child 1) w1 lt' m child
      (Nat.le_trans (Nat.sub_le _ _) hK) (Nat.le_trans (Nat.sub_le _ _) hf) htie1
      (node_at_child hat rfl) (layerPointTyped_child hat rfl hct henv hview1 (stackTyped_mono o1 hstack))
        hchild
      (memoLive_mono o1.1 hmemo))
    (fun w2 o2 => hs (q.child 0) w2 ls m child
      (Nat.le_trans (Nat.sub_le _ _) hK) (Nat.le_trans (Nat.sub_le _ _) hf)
      (serviceTy_leHost o2 htie1) (node_at_child hat rfl)
      (layerPointTyped_child hat rfl hcs henv (completed_mono o2 hview1)
        (stackTyped_mono (leHost_trans _ _ _ o1 o2) hstack)) (scopeLive_mono o2.1 hchild)
      (memoLive_mono (leHost_trans _ _ _ o1 o2).1 hmemo))

/-- **`Layer.merge`** (`Layer.ts:1587-1602`): `fromBuild`, then the two siblings forked and merged. -/
theorem merge_builds {left right : LayerTerm NativeOp} {f K : Nat} :
    BuildsTyped root f K (.merge left right) := by
  intro q w lt m scope _ _ _ hat hpt hlive hmemo
  obtain ⟨hcheck, henv, hview, hstack⟩ := hpt.at_layer hat
  rw [LayerTerm.expandIn_merge] at hcheck
  obtain ⟨a, b, ha, hb, rfl⟩ := Checker.inv_layer_merge _ _ _ _ _ hcheck
  rw [denoteLayer_merge]
  exact fromBuild_typed hlive (fun w1 o1 child hchild =>
    mergeTwo_typed hchild (memoLive_mono o1.1 hmemo)
      (layerPointTyped_child hat rfl ha henv (completed_mono o1 hview) (stackTyped_mono o1 hstack))
      (layerPointTyped_child hat rfl hb henv (completed_mono o1 hview) (stackTyped_mono o1 hstack)))

/-- **A layer reference whose target stands in another scope** (slice CX1,
`docs/research/2026-10-10-cx-lexical-scope.md` §10). The reference's hop runs the target's term at
the target's path with the reference's stack (`denoteLayer_ref_redirect`), and the memo map keys
the build on the target's path. The checker types the reference at its own scope (the expansion),
and `layerRefsWF` reads no scope, so the checker admits a reference whose target's path reads
other parameters than the stack holds; the hop's point is then no typed point (`LayerPointTyped`
reads its path's scope). Open: whether such a build is typed at the reference's type, or the
checker refuses such a reference (an owner's ruling). M5 and M7 rest on it in place of
`invoke_arm`. Concept `residual-program-typing`, claim `denote-typed`, requirement R4; its
consumer is `ref_builds`. -/
@[semantics "residual-program-typing" (requirement := R4)]
proof_goal crossScopeRef_builds {root : ProgramSource} {f : Nat} {target : List Nat}
    (hwf : root.program.layerRefsWF = true)
    (hIH : ∀ f' ≤ f, ∀ (c : NativeEff) (path : List Nat),
      Node.at_ (.eff root.program) path = some (.eff c) → ChildDenotes root f' c path)
    (q : Point) (w : World) (lt : LayerTy) (m : MemoMapId) (scope : Nat) (hf : q.fuel ≤ f)
    (htie : w.serviceTy = root.sig.serviceTy)
    (hat : Node.at_ (.eff root.program) q.path = some (.layer (.ref target)))
    (hcross : scopeParams root.program target ≠ scopeParams root.program q.path)
    (hpt : LayerPointTyped root w q lt) (hlive : ScopeLive w scope) (hmemo : MemoLive w m) :
    TypedProg root w (buildTy lt) (denoteLayer root.program (.ref target) q m scope)

/-- **A layer reference** (decisions rows 153, 170, 185): no fuel is the frontier; else the hop to the
target's term at the redirected point, one fuel down, by the hop hypothesis — well-formedness
(`layerRefsWF_at`) gives a target that is a layer and no reference. The hop's point is typed when
the target stands in the reference's scope (`layerPointTyped_redirect`); a target in another
scope is the open goal `crossScopeRef_builds`. -/
theorem ref_builds {target : List Nat} {f K : Nat} (hwf : root.program.layerRefsWF = true)
    (hIH : ∀ f' ≤ f, ∀ (c : NativeEff) (path : List Nat),
      Node.at_ (.eff root.program) path = some (.eff c) → ChildDenotes root f' c path)
    (hhop : ∀ (l : LayerTerm NativeOp) (q : Point) (w : World) (lt : LayerTy) (m : MemoMapId)
      (scope : Nat), q.fuel < K → q.fuel ≤ f → w.serviceTy = root.sig.serviceTy →
      Node.at_ (.eff root.program) q.path = some (.layer l) → LayerPointTyped root w q lt →
      ScopeLive w scope → MemoLive w m → TypedProg root w (buildTy lt) (denoteLayer root.program l q m scope)) :
    BuildsTyped root f K (.ref target) := by
  intro q w lt m scope hK hf htie hat hpt hlive hmemo
  cases hs : decide (scopeParams root.program target = scopeParams root.program q.path) with
  | false =>
    exact crossScopeRef_builds hwf hIH q w lt m scope hf htie hat (of_decide_eq_false hs) hpt hlive
      hmemo
  | true =>
    cases hfq : q.fuel with
    | zero =>
      rw [denoteLayer_ref_zero _ _ _ _ _ hfq]
      exact pending_typed root w _ _ q
    | succ k =>
      obtain ⟨lt_t, hlayer, hnotref⟩ := layerRefsWF_at hwf hat
      rw [denoteLayer_ref_succ _ _ _ _ _ hfq, at_of_layerAt hlayer]
      have hredir := layerPointTyped_redirect hat (of_decide_eq_true hs) hpt hlayer
      have hk : (q.redirect target).fuel = k := by
        show q.fuel - 1 = k
        rw [hfq]
        rfl
      have hKk : (q.redirect target).fuel < K := by rw [hk]; rw [hfq] at hK; omega
      have hfk : (q.redirect target).fuel ≤ f := by rw [hk]; rw [hfq] at hf; omega
      cases lt_t with
      | ref t' => exact absurd rfl (hnotref t')
      | _ =>
        exact hhop _ (q.redirect target) w lt m scope hKk hfk htie (at_of_layerAt hlayer) hredir hlive hmemo

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
    exact layerPointTyped_scope (hscope _ (List.prefix_append _ _)) (node_at_child hat rfl) hhd
      henv hview hstack
  | j + 1, p, .cons hd tl, ls, hscope, hat, hcheck, henv, hview, hstack, hj => by
    rw [LayerTerms.expandIn_cons] at hcheck
    obtain ⟨hh, tt, -, htl, rfl⟩ := Checker.inv_layers_cons _ _ _ _ _ hcheck
    exact spine_layerPointTyped j (p.child 1) tl tt
      (fun x hx => hscope x ((List.prefix_append _ _).trans hx)) (node_at_child hat rfl) htl henv
      hview hstack (Nat.lt_of_succ_lt_succ hj)

/-- A fiber's declaration persists at every later world. -/
theorem fiberDeclared_mono {w w' : World} (ord : w.leHost w') {id : FiberId} {a e : Ty}
    (h : FiberDeclared w id a e) : FiberDeclared w' id a e := by
  obtain ⟨fty, hΓ, ha, he⟩ := h
  exact ⟨fty, ord.1.2.1 _ _ hΓ, ha, he⟩

/-- **`mergeAllEffect`'s fork loop** (`Layer.ts:1597-1600`) for a `mergeAll`'s spine: with every
fiber forked so far declared below `(Context, E)` and every remaining layer's point admitted at a
type erring below `E`, each layer forked into a sequential child of the present parallel parent,
then the await of all and the merge. -/
theorem mergeAllFork_typed {q : Point} {m : MemoMapId} {parent : Nat} {E : Ty} :
    ∀ (remaining i : Nat) (forked : List FiberId) (w : World), ScopeLive w parent → MemoLive w m →
      (∀ id ∈ forked, FiberDeclared w id (.handle Ty.contextTarget) E) →
      (∀ j, i ≤ j → j < i + remaining → ∃ ltj, LayerPointTyped root w (q.spineChild j) ltj ∧
        Ty.subN ltj.error E = true) →
      TypedProg root w ⟨.handle Ty.contextTarget, E, Env.Requirement.empty⟩
        (mergeAllForkR q m parent remaining i forked)
  | 0, _, forked, w, _, _, hforked, _ => by
    obtain ⟨A, E', hpre, hA, hE⟩ := awaitAllCert (ids := forked) (a := .handle Ty.contextTarget)
      (e := E) hforked
    refine seqGuard_typed root (mid := ⟨.list (.exitOf A E'), .never, Env.Requirement.empty⟩)
      (TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
        (fun _ _ _ h => nomatch h) (.list (.exitOf A E')) ⟨A, E', rfl, hpre⟩
        (fun w' _ ans post => .pure (strongExit_success w' _ ans post)))
      (Bounds.subN_never _) (fun w' _ ex hex => ?_)
    simp only [seqR]
    exact mergeContexts_typed rfl (Ty.subN_refl _) (fits_subN w' (subN_listExitOf hA hE) ex hex)
  | remaining + 1, i, forked, w, hlive, hmemo, hforked, hspine => by
    obtain ⟨lti, hpti, herri⟩ := hspine i (Nat.le_refl _) (by omega)
    show TypedProg root w _ ((guardR .onSuccess (storeR (.scopeFork parent .sequential))).bind _)
    refine seqGuard_typed root (mid := EffTy.pure Ty.scope)
      (TypedProg.store (op := .scopeFork parent .sequential) (cert := ()) hlive
        (fun w' _ ans post => .pure (strongExit_success w' _ ans post)))
      (Bounds.subN_never _) (fun w1 o1 v hv => ?_)
    obtain ⟨c, rfl, hc⟩ := fits_scope_inv hv
    simp only [seqR, Val.scope?_scopeHandle]
    refine seqGuard_typed root (forkLayer_typed (layerPointTyped_mono o1 hpti) hc (memoLive_mono o1.1 hmemo))
      (Bounds.subN_never _)
      (fun w2 o2 f hf => ?_)
    obtain ⟨index, rfl, hd⟩ := fiber_of_fits hf
    simp only [seqR]
    rw [show Val.fiber? (Value.fiber index) = some ⟨index⟩ from rfl]
    dsimp only
    have o12 := leHost_trans _ _ _ o1 o2
    refine mergeAllFork_typed remaining (i + 1) (forked ++ [⟨index⟩]) w2
      (scopeLive_mono o12.1 hlive) (memoLive_mono o12.1 hmemo) (fun id hid => ?_) (fun j hj1 hj2 => ?_)
    · rcases List.mem_append.mp hid with hid' | hid'
      · exact fiberDeclared_mono o12 (hforked id hid')
      · rw [List.mem_singleton] at hid'
        subst hid'
        exact fiberDeclared_widen hd herri
    · obtain ⟨ltj, hptj, herrj⟩ := hspine j (by omega) (by omega)
      exact ⟨ltj, layerPointTyped_mono o12 hptj, herrj⟩

/-- **`Layer.mergeAll`** (`Layer.ts:1587-1600`, the n-ary merge): `fromBuild`, the parallel parent,
then every layer of the spine forked at its admitted point (`spine_layerPointTyped`) and the merge;
each layer errs below the merge (`mergeNonempty_error`). -/
theorem mergeAll_builds {layers : LayerTerms NativeOp} {f K : Nat} :
    BuildsTyped root f K (.mergeAll layers) := by
  intro q w lt m scope _ _ _ hat hpt hlive hmemo
  obtain ⟨hcheck, henv, hview, hstack⟩ := hpt.at_layer hat
  rw [LayerTerm.expandIn_mergeAll] at hcheck
  obtain ⟨ls, hcs, hmerge⟩ := Checker.inv_layer_mergeAll _ _ _ _ hcheck
  have hlen : ls.length = layers.length := by
    rw [checkLayers_length _ _ _ hcs, expandIn_layers_length]
  rw [denoteLayer_mergeAll]
  refine fromBuild_typed hlive (fun w1 o1 child hchild => ?_)
  unfold mergeAllR
  refine seqGuard_typed root (mid := EffTy.pure Ty.scope)
    (TypedProg.store (op := .scopeFork child .parallel) (cert := ()) hchild
      (fun w' _ ans post => .pure (strongExit_success w' _ ans post)))
    (Bounds.subN_never _) (fun w2 o2 v hv => ?_)
  obtain ⟨parent, rfl, hparent⟩ := fits_scope_inv hv
  simp only [seqR, Val.scope?_scopeHandle]
  have o12 := leHost_trans _ _ _ o1 o2
  refine mergeAllFork_typed layers.length 0 [] w2 hparent (memoLive_mono o12.1 hmemo) (fun _ h => nomatch h)
    (fun j _ hj => ?_)
  have hj' : j < ls.length := by rw [hlen]; omega
  refine ⟨ls[j], ?_, mergeNonempty_error ls lt hmerge _ (List.getElem_mem hj')⟩
  rw [Point.spineChild_eq]
  exact spine_layerPointTyped j (q.child 0) layers ls
    (fun x hx => scopeParams_layer_prefix hat ((List.prefix_append _ _).trans hx))
    (node_at_child hat rfl) hcs henv (completed_mono o12 hview) (stackTyped_mono o12 hstack) hj'

/-- **The layer family's build, structurally** (decisions rows 176 (b), 185–187): at an admitted
layer point, at a world whose service table is the source's, into a present scope, every
constructor's build answers the built context at the layer's checked error type. The leaves'
bodies are typed by the program induction (`hIH`); the layer children structurally; a reference's
hop, which leaves the term, by `hhop` at the next fuel down. -/
theorem layerTerm_typed (hwf : root.program.layerRefsWF = true) (f : Nat)
    (hIH : ∀ f' ≤ f, ∀ (c : NativeEff) (path : List Nat),
      Node.at_ (.eff root.program) path = some (.eff c) → ChildDenotes root f' c path)
    (K : Nat)
    (hhop : ∀ (l : LayerTerm NativeOp) (q : Point) (w : World) (lt : LayerTy) (m : MemoMapId)
      (scope : Nat), q.fuel < K → q.fuel ≤ f → w.serviceTy = root.sig.serviceTy →
      Node.at_ (.eff root.program) q.path = some (.layer l) → LayerPointTyped root w q lt →
      ScopeLive w scope → MemoLive w m → TypedProg root w (buildTy lt) (denoteLayer root.program l q m scope)) :
    ∀ l, BuildsTyped root f K l
  | .succeed _ _ => succeed_builds
  | .fresh inner => fresh_builds (layerTerm_typed hwf f hIH K hhop inner)
  | .orDie inner => orDie_builds (layerTerm_typed hwf f hIH K hhop inner)
  | .effect _ _ => effect_builds hIH
  | .effectDiscard _ => effectDiscard_builds hIH
  | .provide self that =>
    provide_builds (layerTerm_typed hwf f hIH K hhop self) (layerTerm_typed hwf f hIH K hhop that)
  | .provideMerge self that =>
    provideMerge_builds (layerTerm_typed hwf f hIH K hhop self)
      (layerTerm_typed hwf f hIH K hhop that)
  | .merge _ _ => merge_builds
  | .mergeAll _ => mergeAll_builds
  | .ref _ => ref_builds hwf hIH hhop

/-- **The layer family's build** (by induction on the fuel a reference's hop spends). -/
theorem layerBuild_typed (hwf : root.program.layerRefsWF = true) (f : Nat)
    (hIH : ∀ f' ≤ f, ∀ (c : NativeEff) (path : List Nat),
      Node.at_ (.eff root.program) path = some (.eff c) → ChildDenotes root f' c path)
    (l : LayerTerm NativeOp) (q : Point) (w : World) (lt : LayerTy) (m : MemoMapId) (scope : Nat)
    (hf : q.fuel ≤ f) (htie : w.serviceTy = root.sig.serviceTy)
    (hat : Node.at_ (.eff root.program) q.path = some (.layer l)) (hpt : LayerPointTyped root w q lt)
    (hlive : ScopeLive w scope) (hmemo : MemoLive w m) :
    TypedProg root w (buildTy lt) (denoteLayer root.program l q m scope) := by
  suffices main : ∀ K, ∀ (l : LayerTerm NativeOp) (q : Point) (w : World) (lt : LayerTy)
      (m : MemoMapId) (scope : Nat), q.fuel ≤ K → q.fuel ≤ f → w.serviceTy = root.sig.serviceTy →
      Node.at_ (.eff root.program) q.path = some (.layer l) → LayerPointTyped root w q lt →
      ScopeLive w scope → MemoLive w m →
        TypedProg root w (buildTy lt) (denoteLayer root.program l q m scope) from
    main q.fuel l q w lt m scope (Nat.le_refl _) hf htie hat hpt hlive hmemo
  intro K
  induction K with
  | zero =>
    exact fun l => layerTerm_typed hwf f hIH 0 (fun _ _ _ _ _ _ hlt => absurd hlt (Nat.not_lt_zero _)) l
  | succ K ih =>
    exact fun l => layerTerm_typed hwf f hIH (K + 1) (fun l q w lt m scope hlt =>
      ih l q w lt m scope (Nat.lt_succ_iff.mp hlt)) l

/-! ## The join's protocol

`Effect.provide(self, layer)` after its counted step (`provideLayerR`): the scope made, the memo
map forked (a private one when `local`, else the fiber context's current one's child), the layer
built through it at the closed build point (`layerBuild_typed`), the body under
`provideContext(built)` at child 1, the scope closed with the exit. -/

/-- `MemoMap.fork` read back, then the build through the forked map (`buildWithMemoMap`). -/
theorem forkBuild_typed {w : World} {parent : Option MemoMapId} {build : MemoMapId → RProgram}
    {lt : LayerTy} (htie : w.serviceTy = root.sig.serviceTy)
    (hbuild : ∀ w', w.leHost w' → ∀ m, MemoLive w' m → TypedProg root w' (buildTy lt) (build m)) :
    TypedProg root w (buildTy lt) ((guardR .onSuccess (storeR (.memoFork parent))).bind
      (seqR fun u => match Val.memoMap? u with
        | some id => buildWithMemoMapR build id
        | none => .pure badShapeExit)) := by
  refine seqGuard_typed root (mid := EffTy.pure Ty.memoMap)
    (TypedProg.store (op := .memoFork parent) (cert := ()) trivial
      (fun w' _ ans post => ?_)) (Bounds.subN_never _) (fun w' o v hv => ?_)
  · obtain ⟨id, rfl, hid⟩ := post
    exact .pure (strongExit_success w' _ _ (fits_memoMap w' id hid))
  · obtain ⟨id, rfl, hid⟩ := fits_memoMap_inv hv
    simp only [seqR, Val.memoMap?_memoMap]
    exact buildWithMemoMap_typed (serviceTy_leHost o htie) hid
      (fun w'' o' => hbuild w'' (leHost_trans _ _ _ o o') id (memoLive_mono o'.1 hid))

/-- **The layer family's arm** (decisions row 176 (b)): a typed `provideLayer` point denotes a
typed program. The build answers the built context at the layer's checked error type
(`layerBuild_typed`); the body's exit, or its run under the merged context, is typed at the
body's type, widened to the join of the two error columns the checker gives the node. -/
theorem provideLayer_arm (hwf : root.program.layerRefsWF = true) (f : Nat)
    (hIH : ∀ f' ≤ f, ∀ (c : NativeEff) (path : List Nat),
      Node.at_ (.eff root.program) path = some (.eff c) → ChildDenotes root f' c path)
    {w : World} (htie : w.serviceTy = root.sig.serviceTy) {p : Point} {ty : EffTy}
    {l : LayerTerm NativeOp} {i : Bool} {b : NativeEff} (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.provideLayer l i b)))
    (hpt : PointTyped root w p ty) :
    TypedProg root w ty (denoteR root.program (.provideLayer l i b) p) := by
  obtain ⟨env, hcheck, henv, -, hstack⟩ := hpt.at_node hat
  rw [Eff.expandIn_provideLayer] at hcheck
  obtain ⟨lt, tb, hcl, hcb, rfl⟩ := Checker.inv_provideLayer _ _ _ _ _ _ _ hcheck
  have hatl : Node.at_ (.eff root.program) (p.path ++ [0]) = some (.layer l) :=
    node_at_child hat rfl
  have hatb : Node.at_ (.eff root.program) (p.path ++ [1]) = some (.eff b) :=
    node_at_child hat rfl
  rw [denoteR_provideLayer _ _ _ _ (by rw [hfuel]; exact Nat.succ_ne_zero f)]
  refine suspendR_typed root (fun w1 o1 => constructR_typed root (fun w2 o2 completed hview => ?_))
  have o12 := leHost_trans _ _ _ o1 o2
  unfold provideLayerR
  refine seqGuard_typed root (mid := EffTy.pure Ty.scope)
    (TypedProg.store (op := .scopeMake .sequential) (cert := ()) trivial
      (fun w' _ ans post => .pure (strongExit_success w' _ ans post)))
    (Bounds.subN_never _) (fun w3 o3 v hv => ?_)
  obtain ⟨scope, rfl, hlive⟩ := fits_scope_inv hv
  simp only [seqR, Val.scope?_scopeHandle]
  have o13 := leHost_trans _ _ _ o12 o3
  refine onExit_typed root (b := ⟨tb.answer, tb.error.join lt.error, _⟩) (f := EffTy.pure .unit)
    (Ty.subN_refl _) (Ty.subN_refl _) (Bounds.subN_never _) ?_
    (fun w4 o4 _ hok => TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) ()
      ⟨scopeLive_mono o4.1 hlive, fitsExit_unknown hok.1⟩
      (fun _ _ _ post => .pure post))
  -- the build: at every later world, through any map, the layer's build at the closed point
  have hbuild : ∀ w', w3.leHost w' → ∀ m, MemoLive w' m → TypedProg root w' (buildTy lt)
      (denoteLayer root.program l ({ p with completed } : Point).layerBuild m scope) :=
    fun w' o m hm => layerBuild_typed hwf f hIH l _ w' lt m scope
      (by rw [Point.layerBuild_fuel]; show p.fuel - 1 ≤ f; omega)
      (serviceTy_leHost (leHost_trans _ _ _ o13 o) htie) hatl
      (layerPointTyped_scope (scopeParams_child hat 0) hatl hcl rfl
        (completed_mono (leHost_trans _ _ _ o3 o) hview)
        (stackTyped_mono (leHost_trans _ _ _ o13 o) hstack))
      (scopeLive_mono o.1 hlive) hm
  refine seqGuard_typed root (mid := buildTy lt) ?_ (Ty.subN_join_right _ _)
    (fun w5 o5 u hu => ?_)
  · cases i with
    | true => exact forkBuild_typed (serviceTy_leHost o13 htie) hbuild
    | false =>
      refine seqGuard_typed root (getContext_typed root w3) (Bounds.subN_never _) (fun w' o x hx => ?_)
      obtain ⟨ctx, hctx, -⟩ := fits_context_inv hx
      simp only [seqR]
      rw [hctx]
      exact forkBuild_typed (serviceTy_leHost (leHost_trans _ _ _ o13 o) htie)
        (fun w'' o' m hm => hbuild w'' (leHost_trans _ _ _ o o') m hm)
  -- the body, under the built context, at child 1 of the constructed point
  obtain ⟨ctx, hctx, hsvc⟩ := fits_context_inv hu
  simp only [seqR]
  rw [hctx]
  have o15 := leHost_trans _ _ _ o13 o5
  have hchild : ∀ w', w5.leHost w' →
      PointTyped root w' (({ p with completed } : Point).child 1) tb := fun w' o =>
    pointTyped_child hat rfl rfl hcb (envTyped_mono (leHost_trans _ _ _ o15 o) henv)
      (completed_mono (leHost_trans _ _ _ (leHost_trans _ _ _ o3 o5) o) hview)
      (stackTyped_mono (leHost_trans _ _ _ o15 o) hstack)
  have hfuel1 : (({ p with completed } : Point).child 1).fuel = f := child_fuel_eq hfuel 1
  dsimp only
  cases hsub : inlineYield b (({ p with completed } : Point).child 1) with
  | some ex =>
    exact .pure (exitOk_widen (mid := tb) (Ty.subN_refl _) (Ty.subN_join_left _ _)
      (inlineYield_typed f _ hfuel1 hatb (hchild w5 (leHost_refl w5)) hsub))
  | none =>
    exact updateContext_typed
      (fun w' o prev hprev => servicesFit_merge hprev (servicesFit_mono o hsvc))
      (fun w' o => typedProg_widen root (T := tb) (Ty.subN_refl _) (Ty.subN_join_left _ _)
        (hIH f (Nat.le_refl f) b (p.path ++ [1]) hatb w'
          (serviceTy_leHost (leHost_trans _ _ _ o15 o) htie) _ tb hfuel1 rfl (hchild w' o)))

/-- **`ProvideLayerArm` holds at every source**: the hypothesis the assembly was conditional on. -/
theorem provideLayerArm (root : ProgramSource) : ProvideLayerArm root :=
  fun hwf f hIH _ htie _ _ _ _ _ hfuel hat hpt => provideLayer_arm hwf f hIH htie hfuel hat hpt

end Builds

/-! ## M5, unconditional -/

/-- **M5's fundamental property** (decisions row 148, `denotesTyped`): at every source
whose layer references are well formed, a checked point denotes a typed program at every world
whose service table is the source's. The arms by induction on fuel (`childDenotes_upto`), the
layer family's by `provideLayerArm`. -/
theorem denotesTyped (root : ProgramSource) : DenotesTyped root :=
  denotesTyped_of_provideLayer root (provideLayerArm root)

/-- **M5** (`loadsTyped`): a lawful, checked, closed source whose requirement row is
empty loads into `J` at the initial world, at every fuel and compile budget. -/
theorem loadsTyped (root : ProgramSource) (rootTy : EffTy) (fuel compileFuel : Nat) :
    LoadsTyped root rootTy fuel compileFuel :=
  loadsTyped_of_denotesTyped_typed root rootTy fuel compileFuel (denotesTyped root)

/-- **The typed load for every checked program**: M5 without the lawful-signature and closed-row
premises, which its proof does not read. -/
theorem load_typed (root : ProgramSource) (rootTy : EffTy) (fuel compileFuel : Nat)
    (checked : Program.typeOfProgram root.sig.signature root.program = some rootTy) :
    ∃ w, MachineTyped root rootTy w (loadR root.program fuel compileFuel) :=
  load_typed_of_denotesTyped_typed root rootTy fuel compileFuel (denotesTyped root) checked

end Effect4.Program.Typed
