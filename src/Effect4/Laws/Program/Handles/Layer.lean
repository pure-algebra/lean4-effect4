import Effect4.Laws.Program.Handles.Compile

/-!
# The handle invariant at the compiled alphabet — Layer & Actions

The handle bounds for layer compilation, region codes, memo maps, generator loop exits,
and fiber actions.
-/

namespace Effect4.Program

open Effect4 Effect4.Machine
open Agreement

/-! ## The join: a layer's build, a region and the memo protocol name only what their points hold -/

theorem Env.ContextUpdate.apply_keys (u : Env.ContextUpdate) (c : Env.Ctx) :
    Env.Context.handleKeys (u.apply c) ⊆ u.keys ++ Env.Context.handleKeys c := by
  cases u with
  | setTo context => exact List.subset_append_left _ _
  | provide that =>
    intro x hx
    rcases List.mem_append.mp (Env.Context.handleKeys_merge c that hx) with h | h
    · exact List.mem_append_right _ h
    · exact List.mem_append_left _ h
  | provideService key value =>
    show Env.Context.handleKeys (c.add key value) ⊆ Val.keys value ++ Env.Context.handleKeys c
    exact Env.Context.handleKeys_add c key value

theorem compileLayer_keys : ∀ (l : LayerTerm NativeOp) (q : Point) (m : MemoMapId) (scope : Nat),
    nativeKeys (compileLayer l q m scope) ⊆ Handle.scope scope :: Handle.memoMap m.index :: q.keys
  | .succeed key value, q, m, scope => by
    simp only [compileLayer]
    split
    · next v hv =>
      show Val.keys (Env.encode (Env.Context.empty.addV key v)) ⊆ _
      rw [Val.keys_encode]
      intro x hx
      rcases List.mem_append.mp (Env.Context.handleKeys_addV _ key v hx) with h | h
      · rw [Lit.toVal_keys value v hv] at h
        exact absurd h List.not_mem_nil
      · rw [Env.Context.handleKeys_empty] at h
        exact absurd h List.not_mem_nil
    · exact List.nil_subset _
  | .fresh inner, q, m, scope => by simp only [compileLayer]; sub_tac
  | .orDie inner, q, m, scope => by
    simp only [compileLayer]
    sub_tac using (compileLayer_keys inner (q.child 0) m scope)
  | .effect _ _, q, m, scope | .effectDiscard _, q, m, scope | .provide _ _, q, m, scope
  | .provideMerge _ _, q, m, scope | .merge _ _, q, m, scope | .mergeAll _, q, m, scope => by
    simp only [compileLayer]; sub_tac
  | .ref _, _, _, _ => by simp only [compileLayer]; exact List.nil_subset _

/-- A hop keeps the point's handles: only the path and the fuel move. -/
theorem Point.redirect_keys (q : Point) (target : List Nat) : (q.redirect target).keys = q.keys := rfl

theorem resolveLayerTerm_keys (root : NativeEff) (l : LayerTerm NativeOp) (q : Point)
    (m : MemoMapId) (scope : Nat) :
    nativeKeys (resolveLayer.resolveLayerTerm root l q m scope) ⊆
      Handle.scope scope :: Handle.memoMap m.index :: q.keys := by
  cases l with
  | ref target =>
    simp only [resolveLayer.resolveLayerTerm]
    split
    · exact frontier_keys q |>.trans (List.subset_cons_of_subset _ (List.subset_cons_of_subset _ (List.Subset.refl _)))
    · split
      · exact List.nil_subset _
      · rw [← Point.redirect_keys q target]; exact compileLayer_keys _ _ _ _
      · exact List.nil_subset _
  | _ => exact compileLayer_keys _ _ _ _

theorem resolveLayer_keys (root : NativeEff) (q : Point) (m : MemoMapId) (scope : Nat) :
    nativeKeys (resolveLayer root q m scope) ⊆ Handle.scope scope :: Handle.memoMap m.index :: q.keys := by
  unfold resolveLayer
  split
  · exact resolveLayerTerm_keys _ _ _ _ _
  · exact List.nil_subset _

theorem innerLayerAt_keys (root : NativeEff) (q : Point) (m : MemoMapId) (child : Nat) :
    nativeKeys (innerLayerAt root q m child) ⊆ Handle.scope child :: Handle.memoMap m.index :: q.keys := by
  unfold innerLayerAt
  -- the rows of the table in order: the two leaves, the two provides, the two merges, any
  -- other layer, no layer
  split
  · sub_tac
  · sub_tac
  · sub_tac using (resolveLayer_keys root (q.child 1) m child)
  · sub_tac using (resolveLayer_keys root (q.child 1) m child)
  · sub_tac
  · sub_tac
  · exact compileLayer_keys _ _ _ _
  · exact List.nil_subset _

theorem constructionAt_keys (root : NativeEff) (q : Point) (layerScope : Nat) :
    nativeKeys (constructionAt root q layerScope) ⊆ Handle.scope layerScope :: q.keys := by
  unfold constructionAt
  split
  · sub_tac
  · sub_tac
  · exact List.nil_subset _

theorem regionCode_keys (root : NativeEff) (r : Region) : nativeKeys (regionCode root r) ⊆ r.keys := by
  cases r with
  | program q => exact resolve_keys root q
  | build q m scope => exact resolveLayer_keys root q m scope
  | buildAdding q m scope => simp only [regionCode]; sub_tac using (resolveLayer_keys root q m scope)
  | construct q key => simp only [regionCode]; sub_tac using (resolve_keys root q)

theorem updateContextAt_keys (u : Env.ContextUpdate) (r : Region) :
    nativeKeys (updateContextAt u r) ⊆ u.keys ++ r.keys := by
  simp only [updateContextAt]; sub_tac

theorem scopeAddAt_keys (scope : Nat) (fin : FinName) :
    nativeKeys (scopeAddAt scope fin) ⊆ Handle.scope scope :: fin.keys := by
  simp only [scopeAddAt]; sub_tac

theorem contextsOfList_keys : ∀ (vs : List Val) (cs : List Env.Ctx), contextsOfList vs = some cs →
    cs.flatMap Env.Context.handleKeys ⊆ vs.flatMap Val.keys
  | [], cs, h => by
    simp only [contextsOfList, Option.some.injEq] at h
    subst h
    exact List.nil_subset _
  | x :: rest, cs, h => by
    simp only [contextsOfList] at h
    split at h
    · next c hc =>
      split at h
      · next ctx ctxs hctx hrest =>
        simp only [Option.some.injEq] at h
        subst h
        simp only [List.flatMap_cons]
        refine List.append_subset.mpr ⟨?_, ?_⟩
        · have hx := exitOfVal_keys x _ hc
          simp only [exitKeys] at hx
          exact List.Subset.trans (Env.decode_keys hctx) (List.Subset.trans hx (List.subset_append_left _ _))
        · exact List.Subset.trans (contextsOfList_keys rest ctxs hrest) (List.subset_append_right _ _)
      · cases h
    · cases h

theorem contextsOf_keys (v : Val) (cs : List Env.Ctx) (h : contextsOf v = some cs) :
    cs.flatMap Env.Context.handleKeys ⊆ v.keys := by
  unfold contextsOf at h
  split at h
  · rw [Val.keys_list]
    exact contextsOfList_keys _ _ h
  · cases h

theorem mergeContextsK_keys (v : Val) : nativeKeys (mergeContextsK v) ⊆ v.keys := by
  unfold mergeContextsK
  split
  · next ctxs hctxs =>
    show Val.keys (Env.encode (Env.Context.mergeAll ctxs)) ⊆ _
    rw [Val.keys_encode]
    exact List.Subset.trans (Env.Context.handleKeys_mergeAll ctxs) (contextsOf_keys v ctxs hctxs)
  · split <;> exact List.nil_subset _

theorem currentMemoMapOf_keys {c : Env.Ctx} {m : MemoMapId} (h : currentMemoMapOf c = some m) :
    Handle.memoMap m.index ∈ Env.Context.handleKeys c := by
  unfold currentMemoMapOf at h
  split at h
  · rename_i index hv
    simp only [Option.some.injEq] at h
    subst h
    exact Env.Context.getV_keys hv (List.mem_singleton.mpr rfl)
  · cases h

theorem provideLayerWithK_keys (root : NativeEff) (p : Point) (scope : Nat) :
    nativeKeys (provideLayerWithK root p scope) ⊆ Handle.scope scope :: p.keys := by
  unfold provideLayerWithK
  split
  · split <;> sub_tac
  · exact List.nil_subset _

theorem provideLayerBodyK_keys (root : NativeEff) (p : Point) (v : Val) :
    nativeKeys (provideLayerBodyK root p v) ⊆ p.keys ++ v.keys := by
  unfold provideLayerBodyK
  split
  · next built hbuilt =>
    split
    · next exit hexit =>
      have hb := resolve_keys root (p.child 1)
      rw [Prim.asExit?_eq_some _ _ hexit, ← exitKeys_eq_nativeKeys_ofExit] at hb
      rw [← exitKeys_eq_nativeKeys_ofExit]
      exact List.Subset.trans hb (List.subset_append_left _ _)
    · sub_tac using (Env.decode_keys hbuilt)
  · exact List.nil_subset _

theorem updateThenK_keys (root : NativeEff) (u : Env.ContextUpdate) (body : Region) (v : Val) :
    nativeKeys (updateThenK root u body v) ⊆ u.keys ++ body.keys ++ v.keys := by
  unfold updateThenK
  split
  · next prev hprev =>
    rw [Val.context?_exact hprev]
    split
    · sub_tac using (regionCode_keys root body)
    · -- `setContext(next)`'s handles are the update's and the previous map's; the restoring
      -- name carries the region's and the previous map's
      intro x hx
      simp only [nativeKeys, primKeys, EffThunk.keys, EffName.keys,
        Val.keys_context, Ctx.keys_eq_handleKeys, List.mem_append] at hx ⊢
      rcases hx with h | h | h
      · rcases List.mem_append.mp (Env.ContextUpdate.apply_keys u prev.services h) with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  · exact List.nil_subset _

theorem buildWithScopeK_keys (q : Point) (scope : Nat) (v : Val) :
    nativeKeys (buildWithScopeK q scope v) ⊆ Handle.scope scope :: q.keys ++ v.keys := by
  unfold buildWithScopeK
  split
  · next ctx hctx =>
    rw [Val.context?_exact hctx]
    cases hm : currentMemoMapOf ctx.services with
    | none => sub_tac
    | some m =>
      show [Handle.memoMap m.index] ++ (Handle.scope scope :: q.keys) ⊆ _
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · rw [List.mem_singleton.mp h]
        refine List.mem_append_right _ ?_
        rw [Val.keys_context, Ctx.keys_eq_handleKeys]
        exact currentMemoMapOf_keys hm
      · exact List.mem_append_left _ h
  · exact List.nil_subset _

theorem addCurrentMemoMapK_keys (m : MemoMapId) (v : Val) :
    nativeKeys (addCurrentMemoMapK m v) ⊆ Handle.memoMap m.index :: v.keys := by
  unfold addCurrentMemoMapK
  split
  · next ctx hctx =>
    show Val.keys (Env.encode _) ⊆ _
    rw [Val.keys_encode]
    intro x hx
    rcases List.mem_append.mp (Env.Context.handleKeys_addV _ _ _ hx) with h | h
    · rw [Val.keys_memoMap] at h
      exact List.mem_cons.mpr (Or.inl (List.mem_singleton.mp h))
    · exact List.mem_cons_of_mem _ (Env.decode_keys hctx h)
  · exact List.nil_subset _

theorem provideThenK_keys (q : Point) (m : MemoMapId) (scope : Nat) (mode : CombineMode) (v : Val) :
    nativeKeys (provideThenK q m scope mode v) ⊆
      Handle.scope scope :: Handle.memoMap m.index :: q.keys ++ v.keys := by
  unfold provideThenK
  split
  · next ctx hctx => sub_tac using (Env.decode_keys hctx)
  · exact List.nil_subset _

theorem combineWithK_keys (mode : CombineMode) (that : Env.Ctx) (v : Val) :
    nativeKeys (combineWithK mode that v) ⊆ Env.Context.handleKeys that ++ v.keys := by
  unfold combineWithK
  split
  · next merged hm =>
    split
    · show Val.keys (Env.encode merged) ⊆ _
      rw [Val.keys_encode]
      exact List.Subset.trans (Env.decode_keys hm) (List.subset_append_right _ _)
    · show Val.keys (Env.encode (that.merge merged)) ⊆ _
      rw [Val.keys_encode]
      intro x hx
      rcases List.mem_append.mp (Env.Context.handleKeys_merge that merged hx) with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (Env.decode_keys hm h)
  · exact List.nil_subset _

theorem bindServiceK_keys (key : Option ServiceKey) (v : Val) :
    nativeKeys (bindServiceK key v) ⊆ v.keys := by
  cases key with
  | some key =>
    show Val.keys (Env.encode (Env.Context.empty.addV key v)) ⊆ _
    rw [Val.keys_encode]
    intro x hx
    rcases List.mem_append.mp (Env.Context.handleKeys_addV _ key v hx) with h | h
    · exact h
    · rw [Env.Context.handleKeys_empty] at h
      exact absurd h List.not_mem_nil
  | none =>
    show Val.keys (Env.encode Env.Context.empty) ⊆ _
    rw [Val.keys_encode, Env.Context.handleKeys_empty]
    exact List.nil_subset _

theorem serviceLookupK_keys (key : ServiceKey) (v : Val) :
    nativeKeys (serviceLookupK key v) ⊆ v.keys := by
  unfold serviceLookupK
  split
  · next ctx hctx =>
    split
    · next value hval =>
      rw [Val.context?_exact hctx, Val.keys_context, Ctx.keys_eq_handleKeys]
      exact Env.Context.getV_keys hval
    · exact List.nil_subset _
  · exact List.nil_subset _

theorem entrants_keys (root : NativeEff) : ∀ (es : Effs NativeOp) (q : Point),
    (actionAt.entrants es q).flatMap nativeKeys ⊆ q.keys
  | .nil, _ => List.nil_subset _
  | .cons h t, q => by
    simp only [actionAt.entrants, List.flatMap_cons]
    exact List.append_subset.mpr ⟨compileEff_keys h (q.child 0), entrants_keys root t (q.child 1)⟩

/-! ## The generator walker keeps to its captured exits and environment -/

theorem blockEnv_subset (root : NativeEff) (p : Point) (block : List Nat) (k : Nat) (env : List Val) :
    blockEnv root p block k env ⊆ env := by
  unfold blockEnv
  split
  · exact List.take_subset _ _
  · exact List.Subset.refl _

theorem blockExit_env (root : NativeEff) (p : Point) (pc : List Nat) (env : List Val) (pc' : List Nat)
    (env' : List Val) (h : blockExit root p pc env = some (pc', env')) : env' ⊆ env := by
  unfold blockExit at h
  dsimp only at h
  -- the block's split, then the enclosing loop body or not, then no enclosing block
  repeat' split at h
  · cases h; exact blockEnv_subset root p _ _ env
  · cases h; exact blockEnv_subset root p _ _ env
  · cases h

theorem loopExit_env (root : NativeEff) : ∀ (depth : Nat) (p : Point) (pc : List Nat) (env : List Val)
    (pc' : List Nat) (env' : List Val), loopExit root depth p pc env = some (pc', env') → env' ⊆ env
  | 0, _, _, _, _, _, h => by cases h
  | depth + 1, p, pc, env, pc', env', h => by
    unfold loopExit at h
    dsimp only at h
    -- the block's split, then the enclosing loop body, the next block out, no enclosing block
    repeat' split at h
    · cases h; exact blockEnv_subset root p _ _ env
    · exact List.Subset.trans (loopExit_env root depth _ _ _ _ _ h) (blockEnv_subset root p _ _ env)
    · cases h

/-- What a generator step may name, given a bound `E` on its point's handles. -/
def StepKeys (E : List Handle) : IterStep EffName EffThunk Val Err Defect FiberId Ann → Prop
  | IterStep.done r => r.keys ⊆ E
  | IterStep.resume next n' => nativeKeys next ++ EffName.keys n' ⊆ E
  | IterStep.halt _ => True

theorem Point.withEnv_keys_subset (p : Point) (env env' : List Val) (h : env' ⊆ env) :
    ({ p with env := env' } : Point).keys ⊆ ({ p with env := env } : Point).keys := by
  apply List.append_subset.mpr
  exact ⟨List.subset_append_left _ _,
    List.Subset.trans (flatMap_subset_of_subset h) (List.subset_append_right _ _)⟩

mutual
theorem runStmts_keys (root : NativeEff) (p : Point) (E : List Handle) :
    ∀ (fuel : Nat) (pc : List Nat) (env folded : List Val),
      ({ p with env := env } : Point).keys ⊆ E →
      StepKeys E (runStmts root p fuel pc env folded).2
  | 0, pc, env, folded, henv => by
    simp only [runStmts, StepKeys]
    sub_tac using henv
  | fuel + 1, pc, env, folded, henv => by
    simp only [runStmts]
    split
    · split
      · simp only [StepKeys]; exact List.nil_subset _
      · next pc' env' hexit =>
        exact runStmts_keys root p E fuel pc' env' folded
          (List.Subset.trans (p.withEnv_keys_subset env env'
            (blockExit_env root p pc env pc' env' hexit)) henv)
    · next s _ _ =>
      split
      · exact yieldOf_keys root p E fuel _ true pc env folded henv
      · exact yieldOf_keys root p E fuel _ false pc env folded henv
      ·
        split
        · next value hvalue =>
          simp only [StepKeys]
          exact List.Subset.trans (evalTerm_point_keys _ { p with env := env } value hvalue) henv
        · simp only [StepKeys]
      · split
        · exact runStmts_keys root p E fuel _ env folded henv
        · exact runStmts_keys root p E fuel _ env folded henv
        · simp only [StepKeys]
      · exact runStmts_keys root p E fuel _ env folded henv
      · split
        · next pc' env' hexit =>
          exact runStmts_keys root p E fuel pc' env' folded
            (List.Subset.trans (p.withEnv_keys_subset env env'
              (loopExit_env root _ p pc env pc' env' hexit)) henv)
        · simp only [StepKeys]
    · simp only [StepKeys]
termination_by fuel _ _ _ _ => (fuel, 0)

theorem yieldOf_keys (root : NativeEff) (p : Point) (E : List Handle) (fuel : Nat) (e : NativeEff) (bind : Bool)
    (pc : List Nat) (env folded : List Val) (henv : ({ p with env := env } : Point).keys ⊆ E) :
    StepKeys E (runStmts.yieldOf root p e bind fuel pc env folded).2 := by
  simp only [runStmts.yieldOf]
  have hcode := compileEff_keys e { p with path := p.path ++ [0] ++ pc ++ [0, 0], env := env, fuel := fuel + 1 }
  split
  · next value hvalue =>
    rw [hvalue] at hcode
    refine runStmts_keys root p E fuel _ _ _ ?_
    cases bind
    · exact henv
    · change ({ p with env := env ++ [value] } : Point).keys ⊆ E
      have hvalue : value.keys ⊆ E := List.Subset.trans hcode henv
      simpa only [Point.keys, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.append_assoc] using List.append_subset.mpr ⟨henv, hvalue⟩
  · simp only [StepKeys]
  ·
    simp only [StepKeys]
    exact List.append_subset.mpr ⟨List.Subset.trans hcode henv, henv⟩
termination_by (fuel, 1)
end

/-! ## A fiber action names only what its point evaluates -/

theorem evalTerm_fiber_mem (t : Term) (env : List Val) (id : FiberId) (h : evalTerm env t = some (Val.fiber id)) :
    Handle.fiber id ∈ env.flatMap Val.keys :=
  evalTerm_keys t env _ h (by rw [Val.keys_fiber]; exact List.mem_singleton.mpr rfl)

theorem evalTerm_scope_mem (t : Term) (env : List Val) (s : Nat) (h : evalTerm env t = some (Val.scopeHandle s)) :
    Handle.scope s ∈ env.flatMap Val.keys :=
  evalTerm_keys t env _ h (by rw [Val.keys_scopeHandle]; exact List.mem_singleton.mpr rfl)

/-- The fibers a `withFiber` term's value names (`actionAt`'s `handles`): a snapshot or a tuple of
fiber handles. -/
theorem handlesOf_keys (v : Val) (ids : List FiberId)
    (hh : (match v with
           | Value.fiberSnapshot hs => (Store.Image.list Value.fiberHandle).ofVal hs
           | v => (Val.tuple? v).bind fun vs => vs.mapM fun
             | Val.fiber ⟨id⟩ => some ⟨id⟩
             | _ => none) = some ids) :
    ids.map Handle.fiber ⊆ v.keys := by
  have hg : ∀ (w : Val) (id : FiberId),
      (fun x => match x with | Val.fiber ⟨id⟩ => some ⟨id⟩ | _ => none) w = some id →
        Handle.fiber id ∈ w.keys := by
    intro w id hw
    simp only [] at hw
    split at hw
    · injection hw with hw
      subst hw
      simp only [Val.keys, Handle.ofCode_fiber, Option.toList, List.mem_singleton]
    · exact nomatch hw
  split at hh
  · next hs =>
    rw [(Store.Image.list Value.fiberHandle).ofVal_exact hh]
    show ids.map Handle.fiber ⊆ (Val.fibers ids).keys
    rw [Val.keys_fibers]
    exact List.Subset.refl _
  · obtain ⟨vs, hvs, hm⟩ := Option.bind_eq_some_iff.mp hh
    exact List.Subset.trans (mapM_fiber_keys _ hg vs ids hm) (tuple?_keys _ vs hvs)

theorem actionAt_keys (root : NativeEff) (p : Point) (a : NAction) (h : actionAt root p = some a) :
    a.keys EffName.keys EffThunk.keys ⊆ p.keys := by
  unfold actionAt at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact resolve_keys root (p.child 0)
  · simp only [Option.some.injEq] at h
    subst h
    exact resolve_keys root (p.child 0)
  · rename_i a' _
    simp only [Option.some.injEq] at h
    cases a' with
    | fork prog options =>
      simp only [] at h
      subst h
      exact resolve_keys root _
    | forkIn prog options scope =>
      simp only [] at h
      split at h
      · rename_i s hs
        subst h
        have hs' := evalTerm_scope_mem scope p.env s hs
        sub_tac using (resolve_keys root _)
      · subst h; exact List.nil_subset _
    | forkScoped prog options =>
      -- the service read names nothing (§20); `forkScopedAt_keys` bounds the `forkIn` half
      simp only [] at h
      subst h
      exact List.nil_subset _
    | runIn target scope =>
      simp only [] at h
      split at h
      · rename_i id s hid hs
        subst h
        have h1 := evalTerm_fiber_mem target p.env ⟨id⟩ hid
        have h2 := evalTerm_scope_mem scope p.env s hs
        sub_tac
      · subst h; exact List.nil_subset _
    | interrupt target =>
      simp only [] at h
      split at h
      · rename_i id hid
        subst h
        have h1 := evalTerm_fiber_mem target p.env ⟨id⟩ hid
        sub_tac
      · subst h; exact List.nil_subset _
    | interruptScoped target =>
      simp only [] at h
      split at h
      · rename_i id hid
        subst h
        have h1 := evalTerm_fiber_mem target p.env ⟨id⟩ hid
        sub_tac
      · subst h; exact List.nil_subset _
    | interruptAll targets interruptor =>
      simp only [] at h
      split at h
      · rename_i ids hids
        obtain ⟨v, hv, hh⟩ := Option.bind_eq_some_iff.mp hids
        have hids' : ids.map Handle.fiber ⊆ p.keys :=
          List.Subset.trans (handlesOf_keys v ids hh) (evalTerm_point_keys targets p v hv)
        split at h
        · subst h
          sub_tac using hids'
        · rename_i who _
          split at h
          · subst h
            sub_tac using hids'
          · subst h; exact List.nil_subset _
      · subst h; exact List.nil_subset _
    | awaitAll targets =>
      simp only [] at h
      split at h
      · rename_i ids hids
        obtain ⟨v, hv, hh⟩ := Option.bind_eq_some_iff.mp hids
        subst h
        exact List.Subset.trans (handlesOf_keys v ids hh) (evalTerm_point_keys targets p v hv)
      · subst h; exact List.nil_subset _
    | awaitAllFailFast targets =>
      simp only [] at h
      split at h
      · rename_i ids hids
        obtain ⟨v, hv, hh⟩ := Option.bind_eq_some_iff.mp hids
        subst h
        exact List.Subset.trans (handlesOf_keys v ids hh) (evalTerm_point_keys targets p v hv)
      · subst h; exact List.nil_subset _
    | snapshotChildren =>
      simp only [] at h
      subst h
      exact List.nil_subset _
    | awaitNewChildren snapshot =>
      simp only [] at h
      split at h
      · rename_i ids hids
        obtain ⟨v, hv, hh⟩ := Option.bind_eq_some_iff.mp hids
        subst h
        exact List.Subset.trans (handlesOf_keys v ids hh) (evalTerm_point_keys snapshot p v hv)
      · subst h; exact List.nil_subset _
    | raceAll es =>
      simp only [] at h
      subst h
      exact entrants_keys root es _
    | setContext context =>
      simp only [] at h
      split at h
      · rename_i ctx hctx
        subst h
        obtain ⟨w, hw, hctx'⟩ := Option.bind_eq_some_iff.mp hctx
        rw [Val.context?_exact hctx'] at hw
        have hkeys := evalTerm_point_keys context p (Val.context ctx) hw
        rw [Val.keys_context] at hkeys
        exact hkeys
      · subst h; exact List.nil_subset _
    | getContext =>
      simp only [] at h
      subst h
      exact List.nil_subset _
    | getId =>
      simp only [] at h
      subst h
      exact List.nil_subset _
    | closeScope scope exit =>
      simp only [] at h
      split at h
      · rename_i s e hs hexit
        subst h
        have h1 := evalTerm_scope_mem scope p.env s hs
        obtain ⟨v, hv, hev⟩ := Option.bind_eq_some_iff.mp hexit
        have h2 : exitKeys e ⊆ p.keys := List.Subset.trans (exitOfVal_keys v e hev) (evalTerm_point_keys exit p v hv)
        sub_tac using h2
      · subst h; exact List.nil_subset _
  · cases h

end Effect4.Program
