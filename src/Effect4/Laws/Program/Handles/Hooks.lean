import Effect4.Laws.Program.Handles.Layer

/-!
# The handle invariant at the compiled alphabet — Hooks

Key-boundedness of all interpreter callbacks/hooks for `interpOf root`.
-/

namespace Effect4.Program

open Effect4 Effect4.Machine
open Agreement

/-! ## The hooks of `interpOf` are key-bounded -/

/-- `forkScoped`'s `forkIn` half (§20) names the handle the service read answered and the
child's point. -/
theorem forkScopedAt_keys (root : NativeEff) (p : Point) (scope : Nat) (a : NAction)
    (h : forkScopedAt root p scope = some a) :
    a.keys EffName.keys EffThunk.keys ⊆ (EffThunk.forkInAt p scope).keys := by
  unfold forkScopedAt at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    simp only [WithFiberAction.keys, EffThunk.keys]
    sub_tac using (resolve_keys root ((p.child 0).child 0))
  · cases h

-- One table, one budget: the join doubled the arms (`set_option`, as `interpOf_keyBounded`).
set_option maxHeartbeats 800000 in
/-- The compile's continuation table names only what its name and its value name. The join's
names first, each by its continuation's own bound (`Agreement.lean`'s equations select the arm;
a handle-reading name splits on its reader); the rest as one `match` over the name and the
value's shape, one case per name: a handle-reading name splits on its reader, a
value-reading name on its `match`, and every other name answers the value itself. -/
theorem contAOf_native_keys (root : NativeEff) (n : EffName) (v : Val) :
    nativeKeys (Program.contAOf root n v) ⊆ n.keys ++ v.keys := by
  cases n
  case provideLayerWith p =>
    cases hs : Val.scope? v with
    | some s =>
      rw [Val.scope?_exact hs, contAOf_provideLayerWith_scope]
      exact List.Subset.trans (provideLayerWithK_keys root p s) (by sub_tac)
    | none =>
      rw [contAOf_provideLayerWith_other root p v (Val.scope?_none hs)]
      exact List.nil_subset _
  case provideLayerBody p =>
    rw [contAOf_provideLayerBody]
    exact List.Subset.trans (provideLayerBodyK_keys root p v) (by sub_tac)
  case updateThen u body =>
    rw [contAOf_updateThen]
    exact List.Subset.trans (updateThenK_keys root u body v) (by sub_tac)
  case bodyThen body previous =>
    rw [contAOf_bodyThen]
    sub_tac using (regionCode_keys root body)
  case buildWithScopeFromContext q scope =>
    rw [contAOf_buildWithScopeFromContext]
    exact List.Subset.trans (buildWithScopeK_keys q scope v) (by sub_tac)
  case withMemoMapThen q scope =>
    cases hid : Val.memoMap? v with
    | some id =>
      rw [Val.memoMap?_exact hid, contAOf_withMemoMapThen_memoMap]
      exact List.Subset.trans (updateContextAt_keys _ _) (by sub_tac)
    | none =>
      rw [contAOf_withMemoMapThen_other root q scope v (Val.memoMap?_none hid)]
      exact List.nil_subset _
  case addCurrentMemoMap m =>
    rw [contAOf_addCurrentMemoMap]
    exact List.Subset.trans (addCurrentMemoMapK_keys m v) (by sub_tac)
  case fromBuildThen q m =>
    cases hs : Val.scope? v with
    | some child =>
      rw [Val.scope?_exact hs, contAOf_fromBuildThen_scope]
      sub_tac using (innerLayerAt_keys root q m child)
    | none =>
      rw [contAOf_fromBuildThen_other root q m v (Val.scope?_none hs)]
      exact List.nil_subset _
  case memoize q m scope =>
    cases hh : Val.memoHit? v with
    | some co =>
      obtain ⟨cell, owner⟩ := co
      rw [Val.memoHit?_exact hh, contAOf_memoize_hit]
      sub_tac using (scopeAddAt_keys scope _)
    | none =>
      by_cases hu : v = Val.unit
      · subst hu
        rw [contAOf_memoize_unit]
        sub_tac
      · rw [contAOf_memoize_other root q m scope v (Val.memoHit?_none hh) hu]
        exact List.nil_subset _
  case awaitPromise cell =>
    rw [contAOf_awaitPromise]
    sub_tac
  case buildIntoLayerScope q m scope =>
    cases hs : Val.scope? v with
    | some layerScope =>
      rw [Val.scope?_exact hs, contAOf_buildIntoLayerScope_scope]
      sub_tac using (scopeAddAt_keys scope _)
    | none =>
      rw [contAOf_buildIntoLayerScope_other root q m scope v (Val.scope?_none hs)]
      exact List.nil_subset _
  case thenBuildInto q m layerScope =>
    rw [contAOf_thenBuildInto]
    sub_tac using (constructionAt_keys root q layerScope)
  case freshThen q scope =>
    cases hid : Val.memoMap? v with
    | some id =>
      rw [Val.memoMap?_exact hid, contAOf_freshThen_memoMap]
      exact List.Subset.trans (resolveLayer_keys root q id scope) (by sub_tac)
    | none =>
      rw [contAOf_freshThen_other root q scope v (Val.memoMap?_none hid)]
      exact List.nil_subset _
  case provideThen q m scope mode =>
    rw [contAOf_provideThen]
    exact List.Subset.trans (provideThenK_keys q m scope mode v) (by sub_tac)
  case combineWith mode that =>
    rw [contAOf_combineWith]
    exact List.Subset.trans (combineWithK_keys mode that v) (by sub_tac)
  case mergeChildren q m =>
    cases hs : Val.scope? v with
    | some parent =>
      rw [Val.scope?_exact hs, contAOf_mergeChildren_scope]
      sub_tac
    | none =>
      rw [contAOf_mergeChildren_other root q m v (Val.scope?_none hs)]
      exact List.nil_subset _
  case mergeForkOne q i m parent forked =>
    cases hs : Val.scope? v with
    | some child =>
      rw [Val.scope?_exact hs, contAOf_mergeForkOne_scope]
      sub_tac
    | none =>
      rw [contAOf_mergeForkOne_other root q i m parent forked v (Val.scope?_none hs)]
      exact List.nil_subset _
  case mergeForkNext q i m parent forked =>
    cases hf : Val.fiber? v with
    | some id =>
      rw [Val.fiber?_exact hf, contAOf_mergeForkNext_fiber]
      split <;> sub_tac
    | none =>
      rw [contAOf_mergeForkNext_other root q i m parent forked v (Val.fiber?_none hf)]
      exact List.nil_subset _
  case mergeAllChildren q m =>
    cases hs : Val.scope? v with
    | some parent =>
      rw [Val.scope?_exact hs, contAOf_mergeAllChildren_scope]
      split <;> sub_tac
    | none =>
      rw [contAOf_mergeAllChildren_other root q m v (Val.scope?_none hs)]
      exact List.nil_subset _
  case mergeAllForkOne q i m parent forked =>
    cases hs : Val.scope? v with
    | some child =>
      rw [Val.scope?_exact hs, contAOf_mergeAllForkOne_scope, forkLayer_keys_spine]
      sub_tac
    | none =>
      rw [contAOf_mergeAllForkOne_other root q i m parent forked v (Val.scope?_none hs)]
      exact List.nil_subset _
  case mergeAllForkNext q i m parent forked =>
    cases hf : Val.fiber? v with
    | some id =>
      rw [Val.fiber?_exact hf, contAOf_mergeAllForkNext_fiber]
      split <;> sub_tac
    | none =>
      rw [contAOf_mergeAllForkNext_other root q i m parent forked v (Val.fiber?_none hf)]
      exact List.nil_subset _
  case mergeContexts =>
    rw [contAOf_mergeContexts]
    exact List.Subset.trans (mergeContextsK_keys v) (by sub_tac)
  case serviceLookup key =>
    rw [contAOf_serviceLookup]
    exact List.Subset.trans (serviceLookupK_keys key v) (by sub_tac)
  case bindService key =>
    rw [contAOf_bindService]
    exact List.Subset.trans (bindServiceK_keys key v) (by sub_tac)
  case orDie =>
    show nativeKeys (Prim.success v) ⊆ _
    sub_tac
  -- the names of `acquireRelease` and `forkScoped`, each by its equation (`Agreement.lean`)
  case forkScopedIn p =>
    cases hs : Val.scope? v with
    | some s =>
      rw [Val.scope?_exact hs, contAOf_forkScopedIn]
      sub_tac
    | none =>
      rw [contAOf_forkScopedIn_other root v (Val.scope?_none hs)]
      exact List.nil_subset _
  case scopeOpen p =>
    cases hs : Val.scope? v with
    | some s =>
      rw [Val.scope?_exact hs]
      simp only [Program.contAOf]
      sub_tac
    | none =>
      have hne := Val.scope?_none hs
      simp only [Program.contAOf, hne]
      exact List.nil_subset _
  case scopeProvide p s =>
    simp only [Program.contAOf]
    split
    · next previous hprev =>
      rw [Val.context?_exact hprev]
      sub_tac using (Ctx.keys_withScope previous _)
        norm [Point.keys, EffName.keys, EffThunk.keys, Val.keys_context]
    · exact List.nil_subset _
  case scopeBody p previous =>
    simp only [Program.contAOf]
    sub_tac using (resolve_keys root _)
  case acquireCtx p =>
    rw [contAOf_acquireCtx]
    split
    · next ctx hctx =>
      rw [Val.context?_exact hctx]
      sub_tac norm [Point.keys, EffName.keys, EffThunk.keys, Val.keys_context]
    · exact List.nil_subset _
  case acquireIn p ctx =>
    cases hs : Val.scope? v with
    | some s =>
      rw [Val.scope?_exact hs, contAOf_acquireIn_scope]
      sub_tac using (resolve_keys root _)
    | none =>
      rw [contAOf_acquireIn_other root ctx v (Val.scope?_none hs)]
      exact List.nil_subset _
  case acquired p ctx s =>
    -- the capture's handles are the point's, the value's and the context's
    rw [contAOf_acquired]
    sub_tac norm [Point.keys, EffName.keys, EffThunk.keys, SyncOp.keys, FinName.keys, Point.capture,
      Val.keysList_eq_flatMap]
  case afterScopeAdd a fin =>
    -- unit answers `a`; a closed scope's exit, read back, runs the release program under it
    rw [contAOf_afterScopeAdd]
    split
    · sub_tac
    · split
      · next exit hexit =>
        sub_tac using (Machine.finProgram_keys _ exit), (exitOfVal_keys _ exit hexit)
          norm [Point.keys, EffName.keys, EffThunk.keys, embed_keys]
      · exact List.nil_subset _
  case releaseUnder p ctx exit =>
    rw [contAOf_releaseUnder]
    split
    · next previous hprev =>
      rw [Val.context?_exact hprev]
      sub_tac norm [Point.keys, EffName.keys, EffThunk.keys, Val.keys_context]
    · exact List.nil_subset _
  case releaseBody p exit previous =>
    -- the release's point appends the reified exit
    rw [contAOf_releaseBody]
    sub_tac norm [Point.keys, EffName.keys, EffThunk.keys, Point.childWith, Machine.reifyExitVal_keys]
  -- the value-passing names: the continuation is the resolved point or an exit
  case cont p =>
    simp only [Program.contAOf]
    sub_tac using (resolve_keys root _)
  case onValue p =>
    simp only [Program.contAOf]
    sub_tac using (resolve_keys root _)
  case restore exit =>
    simp only [Program.contAOf, primKeys_ofExit]
    sub_tac
  case merge exit =>
    simp only [Program.contAOf, primKeys_ofExit]
    sub_tac
  case reFail cause =>
    simp only [Program.contAOf]
    exact List.nil_subset _
  case constant w =>
    simp only [Program.contAOf]
    sub_tac
  case abort =>
    simp only [Program.contAOf]
    exact List.nil_subset _
  case store name =>
    simp only [Program.contAOf, nativeKeys, embed_keys]
    exact Machine.contAOf_keys _ _
  -- every other name answers the value itself (the table's last row)
  case external op request =>
    show nativeKeys (Prim.success v) ⊆ _
    sub_tac
  case caught p =>
    show nativeKeys (Prim.success v) ⊆ _
    sub_tac
  case caughtError p =>
    show nativeKeys (Prim.success v) ⊆ _
    sub_tac
  case onCause p =>
    show nativeKeys (Prim.success v) ⊆ _
    sub_tac
  case fin p =>
    show nativeKeys (Prim.success v) ⊆ _
    sub_tac
  case gen p pc bind =>
    show nativeKeys (Prim.success v) ⊆ _
    sub_tac
  case loop p =>
    show nativeKeys (Prim.success v) ⊆ _
    sub_tac
  case registerAwait cell =>
    show nativeKeys (Prim.success v) ⊆ _
    sub_tac
  case cancelAwait cell =>
    show nativeKeys (Prim.success v) ⊆ _
    sub_tac
  case withWaiter base waiter token =>
    show nativeKeys (Prim.success v) ⊆ _
    sub_tac
  case scopedExit previous scope =>
    show nativeKeys (Prim.success v) ⊆ _
    sub_tac
  case scopeClose scope =>
    show nativeKeys (Prim.success v) ⊆ _
    sub_tac
  case restoreCtx previous =>
    show nativeKeys (Prim.success v) ⊆ _
    sub_tac

/-- A successful conditional handler binds exactly the once-selected first error. -/
theorem caughtErrorValue?_first {env : List Val} {test : Term} {cause : CauseV} {value : Val}
    (h : caughtErrorValue? env test cause = some value) : firstErrorValue? cause = some value := by
  simp only [caughtErrorValue?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨found, hfound, h⟩ := h
  split at h
  · cases h; exact hfound
  · cases h

/-- The selected error image cannot introduce a handle into the handler environment. -/
theorem caughtErrorValue?_keys {env : List Val} {test : Term} {cause : CauseV} {value : Val}
    (h : caughtErrorValue? env test cause = some value) : value.keys = [] := by
  have hf := caughtErrorValue?_first h
  simp only [firstErrorValue?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hf
  obtain ⟨error, _, he⟩ := hf
  exact valOfErr_keys error value he

theorem contEOf_native_keys (root : NativeEff) (n : EffName) (cause : CauseV) :
    nativeKeys (Program.contEOf root n cause) ⊆ n.keys := by
  cases n with
  | caught p => simp only [Program.contEOf]; sub_tac using (resolve_keys root (p.childWith 1 (Val.exitErr cause)))
  | caughtError p =>
    simp only [Program.contEOf]
    split
    · split
      · rename_i value hvalue
        have hk := caughtErrorValue?_keys hvalue
        simpa only [Point.keys, Point.childWith, List.flatMap_append, List.flatMap_cons,
          List.flatMap_nil, hk, List.append_nil, EffName.keys] using
          (resolve_keys root (p.childWith 1 value))
      · exact List.nil_subset _
    · exact List.nil_subset _
  | onCause p => simp only [Program.contEOf]; sub_tac using (resolve_keys root (p.childWith 2 (Val.exitErr cause)))
  | restore exit =>
    simp only [Program.contEOf, primKeys_ofExit]
    sub_tac using (exitKeys_restoreAfterFinalizer exit _)
  | merge exit =>
    simp only [Program.contEOf, primKeys_ofExit]
    sub_tac using (exitKeys_restoreAfterFinalizer exit _)
  | constant w => simp only [Program.contEOf]; exact List.Subset.refl _
  | store name => simp only [Program.contEOf, nativeKeys, embed_keys]; exact Machine.contEOf_keys name cause
  | orDie => simp only [Program.contEOf]; exact List.nil_subset _
  | cont p | onValue p | fin p | gen p pc bind | loop p | registerAwait cell | cancelAwait cell
  | withWaiter base waiter token | abort | reFail c | scopeOpen p | scopeProvide p s | scopeBody p previous
  | scopedExit previous scope | scopeClose scope | restoreCtx previous | forkScopedIn p
  | acquireCtx p | acquireIn p ctx | acquired p ctx sc | afterScopeAdd a finalizer | releaseUnder p ctx e
  | releaseBody p e previous
  | provideLayerWith p | provideLayerBody p | updateThen u body | bodyThen body previous
  | buildWithScopeFromContext q scope | withMemoMapThen q scope | addCurrentMemoMap m
  | fromBuildThen q m | memoize q m scope | awaitPromise cell | buildIntoLayerScope q m scope
  | thenBuildInto q m layerScope | freshThen q scope | provideThen q m scope mode
  | combineWith mode that | mergeChildren q m | mergeForkOne q i m parent forked
  | mergeForkNext q i m parent forked | mergeAllChildren q m | mergeAllForkOne q i m parent forked
  | mergeAllForkNext q i m parent forked | mergeContexts | serviceLookup key | bindService key
  | external _ _ =>
    simp only [Program.contEOf]; exact List.nil_subset _

theorem cancelProgramOf_keys (n : EffName) : nativeKeys (cancelProgramOf n) ⊆ n.keys := by
  unfold cancelProgramOf
  split
  · sub_tac
  · simp only [nativeKeys, embed_keys]; exact Machine.cancelProgram_keys _
  · simp only [nativeKeys, embed_keys]; exact Machine.cancelProgram_keys _
  · exact List.nil_subset _

theorem syncValueAt_keys (root : NativeEff) (t : EffThunk) : (syncValueAt root t).keys ⊆ t.keys := by
  cases t with
  | pure p =>
    simp only [syncValueAt]
    split
    · rename_i term _
      cases hval : evalTerm p.env term with
      | none => exact List.nil_subset _
      | some val => exact evalTerm_point_keys term p val hval
    · exact List.nil_subset _
  | body _ | op _ | park _ | act _ | forkInAt _ _ | getCtx | setCtx _ | closeScope _ _ | store _
  | acquireMasked _ _ | releaseMasked _ _ | memoLookup _ _ _ | forkLayer _ _ _ | awaitAllFailFast _ =>
    simp only [syncValueAt]; exact List.nil_subset _

theorem Val.tagPayload?_keys {tag : String} {v p : Val} (hp : Val.tagPayload? tag v = some p) :
    Val.keys p ⊆ Val.keys v := by
  obtain rfl : v = Val.list [Val.str tag, p] := by
    unfold Val.tagPayload? at hp
    split at hp
    · rename_i t x
      split at hp
      · rename_i h
        simp only [Option.some.injEq] at hp
        subst hp
        simp only [beq_iff_eq] at h
        subst h
        rfl
      · exact nomatch hp
    · exact nomatch hp
  rw [Val.keys_list]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Val.keys, List.nil_append]
  exact List.Subset.refl _

theorem Decision.decide_bound_keys (d : Decision) (v : Val) (first : Bool) (w : Val)
    (h : d.decide v = some (first, some w)) : Val.keys w ⊆ Val.keys v := by
  cases d with
  | bool =>
    cases v <;>
      simp only [decide, Option.some.injEq, Prod.mk.injEq, reduceCtorEq, and_false] at h
  | option =>
    cases v with
    | some a =>
      simp only [decide, Option.some.injEq, Prod.mk.injEq] at h
      cases h.2
      exact List.Subset.refl _
    | _ =>
      simp only [decide, Option.some.injEq, Prod.mk.injEq, Bool.true_eq, reduceCtorEq,
        and_false] at h
  | tag t =>
    simp only [decide] at h
    rcases hp : Val.tagPayload? t v with _ | payload
    · rw [hp] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      cases h.2
      exact List.Subset.refl _
    · rw [hp] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      cases h.2
      exact Val.tagPayload?_keys hp

theorem Point.childBind_keys_subset (p : Point) (i : Nat) (w : Option Val)
    (hw : ∀ v, w = some v → Val.keys v ⊆ p.keys) : (p.childBind i w).keys ⊆ p.keys := by
  cases w with
  | none => rw [Point.childBind, Point.child_keys]; exact List.Subset.refl _
  | some v =>
    rw [Point.childBind, Point.childWith_keys]
    exact List.append_subset.mpr ⟨List.Subset.refl _, hw v rfl⟩

theorem suspendBodyAt_keys (root : NativeEff) (t : EffThunk) : nativeKeys (suspendBodyAt root t) ⊆ t.keys := by
  cases t with
  | body p =>
    simp only [suspendBodyAt]
    split
    · exact frontier_keys p
    · split
      · exact resolve_keys root (p.child 0)
      · split
        · next first bound heq =>
          apply List.Subset.trans (resolve_keys root _)
          apply Point.childBind_keys_subset
          intro v hv
          obtain ⟨sv, hsv, hd⟩ : ∃ sv, evalTerm p.env _ = some sv ∧ _ = some (first, bound) := by
            simpa [Option.bind_eq_some_iff] using heq
          subst hv
          exact List.Subset.trans (Decision.decide_bound_keys _ _ _ _ hd) (evalTerm_point_keys _ p sv hsv)
        · exact List.nil_subset _
      · sub_tac
      · split
        · next cursor hcursor => sub_tac using (evalTerm_point_keys _ p cursor hcursor)
        · exact List.nil_subset _
      · sub_tac
      · exact compileEff_keys _ p
      · exact List.nil_subset _
  | memoLookup q m scope => simp only [suspendBodyAt]; sub_tac
  | store thunk =>
    cases thunk with
    | body program => simp only [suspendBodyAt, nativeKeys, embed_keys]; exact Machine.progOf_keys program
    | park _ | act _ | op _ => simp only [suspendBodyAt]; exact List.nil_subset _
    | foreign capture exit =>
      simp only [suspendBodyAt]
      sub_tac using (Point.ofCapture_keys capture)
  | pure _ | op _ | park _ | act _ | forkInAt _ _ | getCtx | setCtx _ | closeScope _ _
  | acquireMasked _ _ | releaseMasked _ _ | forkLayer _ _ _ | awaitAllFailFast _ =>
    simp only [suspendBodyAt]; exact List.nil_subset _

theorem env_bind_keys (p : Point) (v : Val) (bind : Bool) :
    (if bind then p.env ++ [v] else p.env).flatMap Val.keys ⊆ p.keys ++ v.keys := by
  cases bind with
  | false =>
    change p.env.flatMap Val.keys ⊆ p.keys ++ v.keys
    exact List.Subset.trans p.env_keys_subset (List.subset_append_left _ _)
  | true =>
    change (p.env ++ [v]).flatMap Val.keys ⊆ p.keys ++ v.keys
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact List.append_subset.mpr
      ⟨List.Subset.trans p.env_keys_subset (List.subset_append_left _ _), List.subset_append_right _ _⟩

theorem point_bind_keys (p : Point) (v : Val) (bind : Bool) :
    ({ p with env := if bind then p.env ++ [v] else p.env } : Point).keys ⊆ p.keys ++ v.keys := by
  cases bind with
  | false => exact List.subset_append_left _ _
  | true =>
    change (p.childWith 0 v).keys ⊆ p.keys ++ v.keys
    rw [Point.childWith_keys]
    exact List.Subset.refl _

/-- A scalar oracle completion contributes no unallocated handle to resumed code. -/
theorem externalAdmits_keys (table : RowTable) (i : Nat)
    (answer : Completion Val Err Defect FiberId Ann) (allocated : List String)
    (h : externalAdmits table i answer allocated = true) :
    answer.keys = [] := by
  cases answer with
  | ofExit exit =>
    cases exit with
    | failure cause => rfl
    | success value =>
      cases hr : externalRow table i with
      | none => simp only [externalAdmits, hr, Bool.false_eq_true] at h
      | some row =>
        simp only [externalAdmits, hr, Bool.and_eq_true_iff, List.isEmpty_iff] at h
        simp only [Completion.keys, exitKeys, Val.keys_eq_handles, h.2, List.filterMap_nil]
  | ofRefGet cell =>
    cases hr : externalRow table i <;> simp only [externalAdmits, hr, Bool.false_eq_true] at h

/-- A converted reply grows only the external allocation list; every returned handle
is either an already valid input or the fresh index just appended. -/
theorem externalValue_minted (ty : Ty) (s : Stores) (ids : List FiberId)
    (value result : Val) (allocated : List String)
    (hc : externalValue ty s.externals.allocated value = some (allocated, result))
    (hok : Ok ⟨ids, s⟩ (value.keys ++ s.keys)) :
    let next := { s with externals := { s.externals with allocated } }
    s.le next ∧ Ok ⟨ids, next⟩ (next.keys ++ result.keys) := by
  unfold externalValue at hc
  split at hc
  · rename_i target index
    split at hc
    · rename_i ha
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hc)
      simp only [Bool.and_eq_true, beq_iff_eq] at ha
      obtain ⟨_, rfl⟩ := ha
      have hle : s.le { s with externals := { s.externals with
          allocated := s.externals.allocated ++ [target] } } :=
        ⟨Nat.le_refl _, Nat.le_refl _, (fun _ h => h), Nat.le_refl _,
          (fun _ h => h), by simp⟩
      refine ⟨hle, Ok_append.mpr ⟨?_, ?_⟩⟩
      · exact Ok_mono (World.le_of_state hle) (Ok_append.mp hok).2
      · simp [Val.keys_eq_handles, Store.Val.handles, Handle.ofCode, HandleKind.ofByte?,
          Ok, Handle.existsIn]
    · cases hc
  · split at hc
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hc)
      exact ⟨Stores.le_refl _, Ok_append.mpr ⟨(Ok_append.mp hok).2, (Ok_append.mp hok).1⟩⟩
    · cases hc

/-- The stateful answer hook meets the generic handle contract for every current
code and table, including refused and nonexternal inputs. -/
theorem prepareExternalAnswer_minted (table : RowTable) (current : Option NCode)
    (answer : Completion Val Err Defect FiberId Ann) (s : Stores) (ids : List FiberId)
    (hok : Ok ⟨ids, s⟩ (answer.keys ++ s.keys)) :
    s.le (prepareExternalAnswer table current answer s).1 ∧
      Ok ⟨ids, (prepareExternalAnswer table current answer s).1⟩
        ((prepareExternalAnswer table current answer s).1.keys ++
          nativeKeys (prepareExternalAnswer table current answer s).2) := by
  have fallback : s.le s ∧ Ok ⟨ids, s⟩ (s.keys ++ nativeKeys (embed (completionPrim answer))) := by
    refine ⟨Stores.le_refl _, ?_⟩
    exact Ok_of_subset (by rw [nativeKeys, embed_keys]; sub_tac using completionPrim_keys answer) hok
  unfold prepareExternalAnswer
  split
  · exact fallback
  · split
    · rename_i i request controller cancel value
      split
      · exact fallback
      · rename_i row hr
        split
        · exact fallback
        · rename_i allocated result hv
          exact externalValue_minted row.answer s ids value result allocated hv hok
    · exact fallback

/-- A loop's end names the point's handles and the cursor's: an `iterate`'s result evaluates
inside that environment. -/
theorem loopFinishAt_keys (root : NativeEff) (q : Point) (cursor : Val) :
    nativeKeys (loopFinishAt root q cursor) ⊆ q.keys ++ cursor.keys := by
  unfold loopFinishAt
  split
  · split
    · next answer hanswer =>
      have hk := evalTerm_keys _ (q.env ++ [cursor]) answer hanswer
      simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hk
      sub_tac using hk
    · exact List.nil_subset _
  · exact List.nil_subset _

/-- A loop's next move names the point's handles and the cursor's: the body is a resolved
child point, the final code an exit or the wrong shape. -/
theorem loopNextAt_keys (root : NativeEff) (q : Point) (cursor : Val) :
    loopNextKeys EffName.keys EffThunk.keys (loopNextAt root q cursor) ⊆ q.keys ++ cursor.keys := by
  unfold loopNextAt
  cases loopAt root q with
  | none => exact List.nil_subset _
  | some loop =>
    obtain ⟨test, step, body⟩ := loop
    dsimp only
    cases evalTerm (q.env ++ [cursor]) test with
    | none => exact List.nil_subset _
    | some v =>
      cases v with
      | bool flag =>
        cases flag with
        | true =>
          simp only [loopNextKeys]
          sub_tac using (resolve_keys root (q.childWith 0 cursor))
        | false => exact loopFinishAt_keys root q cursor
      | _ => exact List.nil_subset _

/-- Resuming a loop names the point's handles, the cursor's and the answer's: the stepped
cursor evaluates inside that environment. -/
theorem loopResumeAt_keys (root : NativeEff) (q : Point) (cursor answer : Val) :
    loopNextKeys EffName.keys EffThunk.keys (loopResumeAt root q cursor answer) ⊆
      q.keys ++ cursor.keys ++ answer.keys := by
  unfold loopResumeAt
  cases loopAt root q with
  | none => exact List.nil_subset _
  | some loop =>
    obtain ⟨test, step, body⟩ := loop
    dsimp only
    cases hnext : evalTerm (q.env ++ [cursor, answer]) step with
    | none => exact List.nil_subset _
    | some next =>
      have hk := evalTerm_keys step (q.env ++ [cursor, answer]) next hnext
      simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hk
      refine List.Subset.trans (loopNextAt_keys root q next) ?_
      sub_tac using hk

set_option maxHeartbeats 800000 in
theorem interpOf_keyBounded (root : NativeEff) (table : RowTable := []) :
    KeyBounded EffName.keys EffThunk.keys (interpOf root table) where
  contA n v := contAOf_native_keys root n v
  contE n c := contEOf_native_keys root n c
  syncValue t := syncValueAt_keys root t
  suspendBody t := suspendBodyAt_keys root t
  reifyExit e := by simp only [interpOf, Machine.reifyExitVal_keys]; exact List.Subset.refl _
  iterNext_done n v r h := by
    cases n with
    | gen p pc bind =>
      simp only [interpOf] at h
      have hs := runStmts_keys root p (p.keys ++ v.keys) p.fuel pc (if bind then p.env ++ [v] else p.env) []
        (point_bind_keys p v bind)
      rw [h] at hs
      exact hs
    | store name =>
      simp only [interpOf] at h
      have hs := stores_keyBounded.iterNext_done name v r (embedStep_done h)
      simpa only [EffName.keys, List.nil_append] using hs
    | cont p | caught p | caughtError p | onValue p | onCause p | fin p | restore e | merge e | loop p | registerAwait cell
    | cancelAwait cell | withWaiter base waiter token | abort | reFail c | scopeOpen p | scopeProvide p s
    | scopeBody p previous | scopedExit previous scope | scopeClose scope | restoreCtx previous | constant w
    | forkScopedIn p | acquireCtx p | acquireIn p ctx | acquired p ctx sc | afterScopeAdd a finalizer
    | releaseUnder p ctx e | releaseBody p e previous
    | provideLayerWith p | provideLayerBody p | updateThen u body | bodyThen body previous
    | buildWithScopeFromContext q scope' | withMemoMapThen q scope' | addCurrentMemoMap mm
    | fromBuildThen q mm | memoize q mm scope' | awaitPromise cell' | buildIntoLayerScope q mm scope'
    | thenBuildInto q mm layerScope | freshThen q scope' | provideThen q mm scope' mode
    | combineWith mode that | mergeChildren q mm | mergeForkOne q i mm parent forked
    | mergeForkNext q i mm parent forked | mergeAllChildren q mm | mergeAllForkOne q i mm parent forked
    | mergeAllForkNext q i mm parent forked | mergeContexts | serviceLookup key | bindService key
    | orDie | external _ _ =>
      simp only [interpOf, IterStep.done.injEq] at h
      subst h
      exact List.subset_append_right _ _
  iterNext_resume n v next n' h := by
    cases n with
    | gen p pc bind =>
      simp only [interpOf] at h
      have hs := runStmts_keys root p (p.keys ++ v.keys) p.fuel pc (if bind then p.env ++ [v] else p.env) []
        (point_bind_keys p v bind)
      rw [h] at hs
      exact hs
    | store name =>
      simp only [interpOf] at h
      obtain ⟨next0, n0, hstep, rfl, rfl⟩ := embedStep_resume h
      have hs := stores_keyBounded.iterNext_resume name v next0 n0 hstep
      simpa only [nativeKeys, embed_keys, EffName.keys, List.nil_append] using hs
    | cont p | caught p | caughtError p | onValue p | onCause p | fin p | restore e | merge e | loop p | registerAwait cell
    | cancelAwait cell | withWaiter base waiter token | abort | reFail c | scopeOpen p | scopeProvide p s
    | scopeBody p previous | scopedExit previous scope | scopeClose scope | restoreCtx previous | constant w
    | forkScopedIn p | acquireCtx p | acquireIn p ctx | acquired p ctx sc | afterScopeAdd a finalizer
    | releaseUnder p ctx e | releaseBody p e previous
    | provideLayerWith p | provideLayerBody p | updateThen u body | bodyThen body previous
    | buildWithScopeFromContext q scope' | withMemoMapThen q scope' | addCurrentMemoMap mm
    | fromBuildThen q mm | memoize q mm scope' | awaitPromise cell' | buildIntoLayerScope q mm scope'
    | thenBuildInto q mm layerScope | freshThen q scope' | provideThen q mm scope' mode
    | combineWith mode that | mergeChildren q mm | mergeForkOne q i mm parent forked
    | mergeForkNext q i mm parent forked | mergeAllChildren q mm | mergeAllForkOne q i mm parent forked
    | mergeAllForkNext q i mm parent forked | mergeContexts | serviceLookup key | bindService key
    | orDie | external _ _ =>
      simp only [interpOf] at h; cases h
  loopEnter n c := by
    cases n with
    | loop p => exact List.Subset.trans (loopNextAt_keys root p c) (by sub_tac)
    | _ => exact List.nil_subset _
  loopResume n c v := by
    cases n with
    | loop p => exact List.Subset.trans (loopResumeAt_keys root p c v) (by sub_tac)
    | _ => exact List.nil_subset _
  cancelThenFail n c := by
    simp only [interpOf]
    sub_tac using (cancelProgramOf_keys n)
  parkOf code target mode h := by
    simp only [interpOf] at h
    split at h
    · rename_i kind
      simp only [Option.some.injEq, Except.ok.injEq] at h
      subst h
      mem_tac [EffThunk.keys, ParkKind.keys]
    · rename_i kind
      simp only [Option.some.injEq, Except.ok.injEq] at h
      subst h
      mem_tac [EffThunk.keys, Thunk.keys, ParkKind.keys]
    · cases h
  parkOfAwaitAll code targets h := by
    simp only [interpOf] at h
    split at h
    · rename_i kind
      simp only [Option.some.injEq, Except.ok.injEq] at h
      subst h
      sub_tac
    · rename_i kind
      simp only [Option.some.injEq, Except.ok.injEq] at h
      subst h
      sub_tac
    · cases h
  withFiberOf t a h := by
    cases t with
    | act p => simp only [interpOf] at h; exact actionAt_keys root p a h
    | forkInAt p scope => simp only [interpOf] at h; exact forkScopedAt_keys root p scope a h
    | getCtx => simp only [interpOf, Option.some.injEq] at h; subst h; exact List.nil_subset _
    | setCtx ctx => simp only [interpOf, Option.some.injEq] at h; subst h; exact List.Subset.refl _
    | closeScope scope exit => simp only [interpOf, Option.some.injEq] at h; subst h; exact List.Subset.refl _
    | acquireMasked p ctx =>
      simp only [interpOf, Option.some.injEq] at h
      subst h
      sub_tac
    | releaseMasked p previous =>
      simp only [interpOf, Option.some.injEq] at h
      subst h
      sub_tac using (resolve_keys root p)
    | forkLayer q m scope =>
      simp only [interpOf, Option.some.injEq] at h
      subst h
      sub_tac using (resolveLayer_keys root q m scope)
    | awaitAllFailFast targets =>
      simp only [interpOf, Option.some.injEq] at h
      subst h
      exact List.Subset.refl _
    | store thunk =>
      cases thunk with
      | act action =>
        simp only [interpOf, Option.some.injEq] at h
        subst h
        rw [embedAction_keys]
        exact Machine.actionOf_keys action
      | park _ | op _ | body _ | foreign _ _ => simp only [interpOf] at h; cases h
    | pure _ | body _ | op _ | park _ | memoLookup _ _ _ => simp only [interpOf] at h; cases h
  syncState t s s' v ids h hok := by
    cases t with
    | op operation =>
      simp only [interpOf] at h
      exact ⟨syncOpStep_le operation s s' v h, syncOpStep_keys operation s s' v ids h hok⟩
    | store thunk =>
      cases thunk with
      | op operation =>
        simp only [interpOf] at h
        exact ⟨syncOpStep_le operation s s' v h, syncOpStep_keys operation s s' v ids h hok⟩
      | park _ | act _ | body _ | foreign _ _ => simp only [interpOf] at h; cases h
    | pure _ | body _ | park _ | act _ | forkInAt _ _ | getCtx | setCtx _ | closeScope _ _
    | acquireMasked _ _ | releaseMasked _ _ | memoLookup _ _ _ | forkLayer _ _ _ | awaitAllFailFast _ =>
      simp only [interpOf] at h; cases h
  registerAsync n fiber token s ids hok := by
    have reg : ∀ cell, Ok ⟨ids, s⟩ ([Handle.promise cell] ++ s.keys) →
        s.le { s with deferreds := (s.deferreds.register cell fiber token).1 } ∧
          Ok ⟨ids, { s with deferreds := (s.deferreds.register cell fiber token).1 }⟩
            ({ s with deferreds := (s.deferreds.register cell fiber token).1 }.keys ++
              (((s.deferreds.register cell fiber token).2.map embed).map nativeKeys).getD []) := by
      intro cell hok
      obtain ⟨hkeys, himm, hlen⟩ := DeferredStore.register_keys s.deferreds cell fiber token
      have hle : s.le { s with deferreds := (s.deferreds.register cell fiber token).1 } :=
        ⟨Nat.le_refl _, hlen, fun _ hh => hh, Nat.le_refl _, (fun _ hm => hm), Nat.le_refl _⟩
      refine ⟨hle, ?_⟩
      have hok' := Ok_mono (World.le_of_state hle) hok
      refine Ok_of_subset ?_ hok'
      refine List.append_subset.mpr ⟨?_, ?_⟩
      · sub_tac using hkeys
      · cases himm' : (s.deferreds.register cell fiber token).2 with
        | none => exact List.nil_subset _
        | some prog =>
          show nativeKeys (embed prog) ⊆ _
          simp only [nativeKeys, embed_keys]
          exact List.Subset.trans (himm prog himm') (by sub_tac)
    cases n with
    | registerAwait cell => simp only [interpOf]; exact reg cell hok
    | store name =>
      cases name with
      | registerAwait cell => simp only [interpOf]; exact reg cell hok
      | registerSleep millis =>
        simp only [interpOf]
        exact ⟨⟨Nat.le_refl _, Nat.le_refl _, fun _ hh => hh, Nat.le_refl _, (fun _ hm => hm), Nat.le_refl _⟩,
          Ok_of_subset (by sub_tac) hok⟩
      | restore _ | merge _ | seq _ | joinOn _ | interruptWith _ | doneInto _ | constant _ | exitOfValue
      | snapshotThen _ | cancelAwait _ | cancelSleep | externalRegister _ | abortController | cancelPark
      | cancelRace _ | withWaiter _ _ _ | reFail _ | finalizerName _ | closeSeq _ _ _ | closeParDone
      | closeIfLast _ =>
        simp only [interpOf]
        exact ⟨Stores.le_refl _, Ok_of_subset (by sub_tac) hok⟩
    | external op request =>
      cases op with
      | external i =>
        simp only [interpOf]
        split
        · exact ⟨Stores.le_refl _, Ok_of_subset (by sub_tac) hok⟩
        · cases hq : s.externals.answers with
          | nil =>
            simp only [hq]
            exact ⟨Stores.le_refl _, Ok_of_subset (by sub_tac) hok⟩
          | cons answer rest =>
            simp only [hq]
            split
            · rename_i ha
              have hinput : Ok ⟨ids, s⟩ (answer.keys ++ s.keys) := by
                rw [externalAdmits_keys table i answer s.externals.allocated ha]
                exact Ok_of_subset (by sub_tac) hok
              exact prepareExternalAnswer_minted table
                (some (.async (.external (.external i) request) false none)) answer s ids hinput
            · exact ⟨Stores.le_refl _, Ok_of_subset (by sub_tac) hok⟩
      | _ =>
        simp only [interpOf]
        exact ⟨Stores.le_refl _, Ok_of_subset (by sub_tac) hok⟩
    | cont p | caught p | caughtError p | onValue p | onCause p | fin p | restore e | merge e | gen p pc bind | loop p
    | cancelAwait cell | withWaiter base waiter token' | abort | reFail c | scopeOpen p | scopeProvide p sc
    | scopeBody p previous | scopedExit previous scope | scopeClose scope | restoreCtx previous | constant w
    | forkScopedIn p | acquireCtx p | acquireIn p ctx | acquired p ctx sc' | afterScopeAdd a finalizer
    | releaseUnder p ctx e | releaseBody p e previous
    | provideLayerWith p | provideLayerBody p | updateThen u body | bodyThen body previous
    | buildWithScopeFromContext q scope' | withMemoMapThen q scope' | addCurrentMemoMap mm
    | fromBuildThen q mm | memoize q mm scope' | awaitPromise cell' | buildIntoLayerScope q mm scope'
    | thenBuildInto q mm layerScope | freshThen q scope' | provideThen q mm scope' mode
    | combineWith mode that | mergeChildren q mm | mergeForkOne q i mm parent forked
    | mergeForkNext q i mm parent forked | mergeAllChildren q mm | mergeAllForkOne q i mm parent forked
    | mergeAllForkNext q i mm parent forked | mergeContexts | serviceLookup key | bindService key
    | orDie =>
      simp only [interpOf]
      exact ⟨Stores.le_refl _, Ok_of_subset (by sub_tac) hok⟩
  answerCode c := by simp only [interpOf]; rw [embed_keys]; exact Machine.completionPrim_keys c
  prepareAnswer := prepareExternalAnswer_minted table
  dueResumes s ids hok := by
    simp only [interpOf]
    obtain ⟨h1, h2⟩ := DeferredStore.drainDue_keys s.deferreds
    have hle : s.le { s with deferreds := (s.deferreds.drainDue).2 } := by
      refine ⟨Nat.le_refl _, ?_, fun _ hh => hh, Nat.le_refl _, (fun _ hm => hm), Nat.le_refl _⟩
      simp only [DeferredStore.drainDue]
      exact Nat.le_refl _
    refine ⟨hle, ?_⟩
    have hok' := Ok_mono (World.le_of_state hle) hok
    refine Ok_of_subset ?_ hok'
    have h2' : (s.deferreds.drainDue.1.map (Owed.mapCode embed)).flatMap
        (Owed.keys (primKeys EffName.keys EffThunk.keys)) ⊆ s.deferreds.keys := by
      rw [List.flatMap_map]
      refine List.Subset.trans ?_ h2
      intro x hx
      obtain ⟨d, hd, hxd⟩ := List.mem_flatMap.mp hx
      refine List.mem_flatMap.mpr ⟨d, hd, ?_⟩
      simpa [Owed.keys, Owed.mapCode, embed_keys, programKeys] using hxd
    sub_tac using h1, h2'
  wakeList key phase s ids hok := by
    simp only [interpOf]
    obtain ⟨hk, hle⟩ := Stores.wakeList_keys key phase s
    exact ⟨hle, Ok_of_subset hk (Ok_mono (World.le_of_state hle) hok)⟩
  clockStep millis s ids hok := by
    simp only [interpOf]
    rcases hc : s.timers.clockStep millis (Prim.success Val.unit) with ⟨o, timers⟩
    have hle : s.le { s with timers := timers } :=
      ⟨Nat.le_refl _, Nat.le_refl _, fun _ hk => hk, Nat.le_refl _, (fun _ hm => hm), Nat.le_refl _⟩
    refine ⟨hle, Ok_of_subset ?_ (Ok_mono (World.le_of_state hle) hok)⟩
    cases o with
    | none => simp only [Option.map_none, Option.getD_none, List.append_nil]; exact fun _ h => h
    | some d =>
      obtain ⟨hcode, hmode⟩ := TimerStore.clockStep_owed s.timers millis (Prim.success Val.unit) d
        (by rw [hc])
      simp only [Option.map_some, Option.getD_some, Owed.keys, Owed.mapCode, hcode, hmode,
        embed_keys, primKeys, Val.keys, List.append_nil]
      exact fun _ h => h
  cancelName base fiber token := by simp only [interpOf]; exact List.Subset.refl _
  abortName := rfl
  parkCancelName := rfl
  raceCancelName race := rfl
  parkCode kind := by simp only [interpOf]; sub_tac
  interruptCode target := by simp only [interpOf]; rw [embed_keys]; sub_tac
  interruptAsCode target who := by simp only [interpOf]; rw [embed_keys]; sub_tac
  interruptAllCode targets := by simp only [interpOf]; rw [embed_keys]; sub_tac
  raceSettle race cleanupNeeded exit := by
    simp only [interpOf]; rw [embed_keys]; exact Machine.raceSettleProgram_keys race cleanupNeeded exit
  finalizerProgram n e p h := by
    simp only [interpOf] at h
    split at h
    · rename_i q
      simp only [Option.some.injEq] at h
      subst h
      refine List.Subset.trans (resolve_keys root _) ?_
      rw [Point.childWith_keys, Machine.reifyExitVal_keys]
      exact List.Subset.refl _
    · rename_i scope
      simp only [Option.some.injEq] at h
      subst h
      sub_tac
    · rename_i previous
      simp only [Option.some.injEq] at h
      subst h
      sub_tac
    · rename_i fin
      simp only [Option.some.injEq] at h
      subst h
      rw [embed_keys]
      exact Machine.finProgram_keys fin e
    · cases h
  restoreName e := List.Subset.refl _
  mergeName e := List.Subset.refl _
  scopeStatus scope s h := stores_keyBounded.scopeStatus scope s h
  scopeLinkFiber mode scope key fiber s s' ids h hok := stores_keyBounded.scopeLinkFiber mode scope key fiber s s' ids h hok
  dropFinalizer scope key s s' ids h hok := stores_keyBounded.dropFinalizer scope key s s' ids h hok
  closeScope scope exit flag closer s s' p ids h hok := by
    simp only [interpOf] at h
    obtain ⟨r, hr, hrp⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hrp
    obtain ⟨rfl, rfl⟩ := hrp
    obtain ⟨hle, hok'⟩ := stores_keyBounded.closeScope scope exit flag closer s r.1 r.2 ids hr hok
    refine ⟨hle, ?_⟩
    show Ok _ (nativeKeys (embed r.2) ++ _)
    simp only [nativeKeys, embed_keys]
    exact hok'
  emptyContext := rfl
  contextValue ctx := by simp only [interpOf, Val.keys_context]; exact List.Subset.refl _
  exitValue e mode := by
    cases mode with
    | awaitValue => simp only [interpOf, primKeys, Machine.reifyExitVal_keys]; exact List.Subset.refl _
    | joinEffect => simp only [interpOf, primKeys_ofExit]; exact List.Subset.refl _
  fiberValue id := by simp only [interpOf, Val.keys_fiber]; exact List.Subset.refl _
  fiberIdValue _ := List.nil_subset _
  fibersValue ids := by simp only [interpOf, Val.keys_fibers]; exact List.Subset.refl _
  exitsValue exits := by simp only [interpOf, Machine.exitsVal_keys]; exact List.Subset.refl _
  voidValue := rfl
  scopeValue scope := by simp only [interpOf]; exact List.Subset.refl _
  closeDoneName := rfl
  ambientScope ctx scope h := by
    simp only [interpOf] at h
    exact Ctx.scope_mem_keys h

end Effect4.Program
