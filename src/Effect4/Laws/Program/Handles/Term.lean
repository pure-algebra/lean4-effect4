import Effect4.Laws.Program.Handles.Alphabet
import Effect4.Laws.Machine.Map

/-!
# The handle invariant at the compiled alphabet — Term

Evaluation of terms within environments and preservation of handle bounds across term evaluations.
-/

namespace Effect4.Program

open Effect4 Effect4.Machine
open Agreement

/-! ## Terms evaluate inside their environment -/

theorem Lit.toVal_keys (l : Lit) (v : Val) (h : l.toVal = some v) : v.keys = [] := by
  cases l with
  | unit => cases h; rfl
  | nat n => cases h; rfl
  | bool b => cases h; rfl
  | str s => cases h; rfl

/-- Cause-tag queries construct only a Boolean, never a new handle. -/
theorem queryTag_keys (tag : ReasonTag) (input output : Val)
    (h : queryTag tag input = some output) : output.keys = [] := by
  obtain ⟨reasons, _, houtput⟩ := Option.map_eq_some_iff.mp h
  cases houtput
  rfl

/-- A cause-error query wraps only S2's closed, handle-free error image. -/
theorem queryError_keys (input output : Val) (h : queryError input = some output) :
    output.keys = [] := by
  obtain ⟨reasons, _, houtput⟩ := Option.bind_eq_some_iff.mp h
  cases hfound : (reasons.findSome? Reason.error?).bind valOfErr with
  | none =>
    simp only [hfound] at houtput
    cases houtput
    rfl
  | some value =>
    simp only [hfound] at houtput
    cases houtput
    change value.keys = []
    obtain ⟨error, _, hvalue⟩ := Option.bind_eq_some_iff.mp hfound
    exact valOfErr_keys error value hvalue

/-- A list read back names only handles its value names: the value is that list, or the
snapshot that carries it (`Val.asList?_exact`). -/
theorem asList?_keys {v : Val} {vs : List Val} (h : Val.asList? v = some vs) :
    vs.flatMap Val.keys ⊆ v.keys := by
  rcases Val.asList?_exact h with rfl | rfl
  · rw [Val.keys_list]
    exact List.Subset.refl _
  · show vs.flatMap Val.keys ⊆ Val.keys (.list vs) ++ []
    rw [List.append_nil, Val.keys_list]
    exact List.Subset.refl _

private theorem native_keys_of_handles {value : Val} {inputs : List Val}
    (h : Store.Val.handles value ⊆ inputs.flatMap Store.Val.handles) :
    value.keys ⊆ inputs.flatMap Val.keys := by
  intro key hk
  rw [Val.keys_eq_handles] at hk
  obtain ⟨code, hc, hk⟩ := List.mem_filterMap.mp hk
  obtain ⟨input, hi, hc⟩ := List.mem_flatMap.mp (h hc)
  refine List.mem_flatMap.mpr ⟨input, hi, ?_⟩
  rw [Val.keys_eq_handles]
  exact List.mem_filterMap.mpr ⟨code, hc, hk⟩

/-- A successful static projection selects an existing member of its plain tuple frame.
The key and raw-handle consumers below use this fact without a typing premise. -/
theorem Val.tupleAt?_mem {value out : Val} {index : Nat}
    (h : Val.tupleAt? value index = some out) :
    ∃ items, value = .list items ∧ out ∈ items := by
  obtain ⟨items, hv, hi⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨items, Val.tuple?_exact hv, List.mem_of_getElem? hi⟩

/-- Static tuple projection introduces no decoded key; consumed by `evalTerm_keys`. -/
theorem tupleAt_keys {value out : Val} {index : Nat}
    (h : Val.tupleAt? value index = some out) : out.keys ⊆ value.keys := by
  obtain ⟨items, rfl, hi⟩ := Val.tupleAt?_mem h
  rw [Val.keys_list]
  exact fun key hk => List.mem_flatMap.mpr ⟨out, hi, hk⟩

/-- Static tuple projection introduces no raw handle; consumed by straight meaning typing. -/
theorem tupleAt_handles {value out : Val} {index : Nat}
    (h : Val.tupleAt? value index = some out) :
    Store.Val.handles out ⊆ Store.Val.handles value := by
  obtain ⟨items, rfl, hi⟩ := Val.tupleAt?_mem h
  change Store.Val.handles out ⊆ Store.Val.handlesList items
  rw [Store.Val.handlesList_eq_flatMap]
  exact fun key hk => List.mem_flatMap.mpr ⟨out, hi, hk⟩

theorem nativeAtom_keys (atom : String) (vs : List Val) (v : Val) (h : nativeAtom atom vs = some v) :
    v.keys ⊆ vs.flatMap Val.keys := by
  unfold nativeAtom at h
  obtain ⟨named, _, h⟩ := Option.bind_eq_some_iff.mp h
  unfold NativeAtom.eval at h
  -- one goal per row of `NativeAtom.eval`, in the table's order: `strings` is row 12, the
  -- four cause queries rows 13–16, `ite` row 24, `some` row 25 and the list atoms rows 29–32;
  -- every other answering row is a scalar or a rearrangement of its arguments, and every
  -- refusing row is `none`
  split at h
  case h_12 =>
    unfold stringsAtom at h
    split at h
    · cases h
      rw [Val.keys_list]
      exact List.Subset.refl _
    · cases h
  case h_13 => rw [queryTag_keys _ _ _ h]; exact List.nil_subset _
  case h_14 => rw [queryError_keys _ _ h]; exact List.nil_subset _
  case h_15 => rw [queryTag_keys _ _ _ h]; exact List.nil_subset _
  case h_16 => rw [queryTag_keys _ _ _ h]; exact List.nil_subset _
  -- the selection answers one of its branches, whole
  case h_24 =>
    cases h
    split
    · exact fun x hx => List.mem_flatMap.mpr ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), hx⟩
    · exact fun x hx => List.mem_flatMap.mpr
        ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), hx⟩
  case h_25 =>
    cases h
    exact fun x hx => List.mem_flatMap.mpr ⟨_, List.mem_cons_self .., hx⟩
  -- the list atoms answer members of their list arguments, or a count
  case h_29 =>
    obtain ⟨elems, hl, rfl⟩ := Option.map_eq_some_iff.mp h
    intro k hk
    simp only [Val.keys_list, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_append] at hk ⊢
    exact hk.imp id (fun hk => asList?_keys hl hk)
  case h_30 =>
    obtain ⟨elems, hl, rfl⟩ := Option.map_eq_some_iff.mp h
    split
    · next e he =>
      intro k hk
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append]
      exact .inl (asList?_keys hl (List.mem_flatMap.mpr ⟨e, List.mem_of_getElem? he, hk⟩))
    · exact List.nil_subset _
  case h_31 =>
    obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp h
    exact List.nil_subset _
  case h_32 =>
    obtain ⟨front, hf, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨back, hb, rfl⟩ := Option.map_eq_some_iff.mp h
    intro k hk
    simp only [Val.keys_list, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.mem_append] at hk ⊢
    exact hk.imp (fun hk => asList?_keys hf hk) (fun hk => asList?_keys hb hk)
  case h_37 => cases h; exact List.nil_subset _
  case h_38 =>
    apply native_keys_of_handles
    simpa only [List.flatMap_cons, List.flatMap_nil, Store.Val.handles,
      List.nil_append, List.append_nil] using Machine.Map.get_handles h
  case h_39 =>
    apply native_keys_of_handles
    intro code hc
    have hm := Machine.Map.set_handles h hc
    simp only [List.flatMap_cons, List.flatMap_nil, Store.Val.handles,
      List.nil_append, List.append_nil, List.mem_append] at hm ⊢
    exact hm.elim Or.inr Or.inl
  case h_40 =>
    rw [Val.keys_eq_handles, Machine.Map.keys_handles h]
    exact List.nil_subset _
  case h_41 =>
    apply native_keys_of_handles
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      using Machine.Map.entries_handles h
  case h_42 =>
    apply native_keys_of_handles
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      using Machine.Map.fromEntries_handles h
  case h_43 =>
    cases h
    rw [Val.keys_list]
    exact List.Subset.refl _
  all_goals cases h
  all_goals sub_tac norm [Val.tuple]

theorem flatMap_subset_of_subset {α : Type} {f : α → List Handle} {l l' : List α} (h : l' ⊆ l) :
    l'.flatMap f ⊆ l.flatMap f := by
  intro x hx
  obtain ⟨a, ha, hx⟩ := List.mem_flatMap.mp hx
  exact List.mem_flatMap.mpr ⟨a, h ha, hx⟩

namespace RecordHandles

private theorem columns_values : ∀ (ns xs : List Val) (es : List (String × Val)),
    Record.readColumns ns xs = some es → es.map Prod.snd = xs
  | [], [], es, h => by cases h; rfl
  | [], _ :: _, _, h => by cases h
  | n :: _, [], _, h => by cases n <;> cases h
  | n :: ns, x :: xs, es, h => by
    cases n with
    | str name =>
      obtain ⟨rest, hr, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [List.map_cons, columns_values ns xs rest hr]
    | _ => cases h

private theorem frame_handles (es : List (String × Val)) :
    Store.Val.handles (Record.frame es) = es.flatMap (fun e => Store.Val.handles e.2) := by
  have hnames : Store.Val.handlesList (es.map (fun e => Val.str e.1)) = [] := by
    induction es with
    | nil => rfl
    | cons e es ih =>
      simp only [List.map_cons, Store.Val.handlesList, Store.Val.handles, List.nil_append, ih]
  simp only [Record.frame, Store.Val.handles, Store.Val.handlesList, hnames,
    List.nil_append, List.append_nil, Store.Val.handlesList_eq_flatMap, List.flatMap_map]


private theorem entries_handles {v : Val} {es : List (String × Val)}
    (h : Record.entries v = some es) :
    es.flatMap (fun e => Store.Val.handles e.2) ⊆ Store.Val.handles v := by
  obtain ⟨parts, hp, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ns, xs⟩ := parts
  obtain ⟨fields, hc, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  next hnd =>
    cases h
    rw [Typed.recordParts?_eq_some hp]
    have hxs := columns_values ns xs es hc
    simp only [Store.Val.handles, Store.Val.handlesList, List.append_nil,
      Store.Val.handlesList_eq_flatMap]
    rw [← hxs, List.flatMap_map]
    exact List.subset_append_right _ _
  next hnd => cases h

private theorem canon_handles (es : List (String × Val)) :
    (Field.canonBy Field.bytesKey es).flatMap (fun e => Store.Val.handles e.2) ⊆
      es.flatMap (fun e => Store.Val.handles e.2) := by
  intro k hk
  obtain ⟨e, he, hk⟩ := List.mem_flatMap.mp hk
  exact List.mem_flatMap.mpr ⟨e, Field.mem_canonBy he, hk⟩

/-- Record construction retains only raw handle frames from its supplied values. -/
theorem build {names : List String} {values : List Val} {v : Val}
    (h : Record.build names values = some v) :
    Store.Val.handles v ⊆ values.flatMap Store.Val.handles := by
  obtain ⟨es, he, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  next hnd =>
    cases h
    rw [frame_handles]
    have hv := (Typed.zipNames_columns names values es he).2
    rw [← hv, List.flatMap_map]
    exact canon_handles es
  next hnd => cases h

/-- Either field-read mode retains only raw handle frames from its input value. -/
theorem read {optional : Bool} {value out : Val} {name : String}
    (h : Record.read optional value name = some out) :
    Store.Val.handles out ⊆ Store.Val.handles value := by
  obtain ⟨result, hl, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨es, he, hr⟩ := Option.map_eq_some_iff.mp hl
  subst result
  have hfield : ∀ x, Field.firstOf name es = some x →
      Store.Val.handles x ⊆ Store.Val.handles value := by
    intro x hx k hk
    exact entries_handles he (List.mem_flatMap.mpr ⟨(name, x), Field.firstOf_mem hx, hk⟩)
  cases optional with
  | true =>
    simp only [↓reduceIte, Option.some.injEq] at h
    subst out
    cases hf : Field.firstOf name es with
    | none => exact List.nil_subset _
    | some x => exact hfield x hf
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    exact hfield out h

/-- Overwrite retains only raw handle frames from the target and replacement. -/
theorem set {value replacement out : Val} {name : String}
    (h : Record.set value name replacement = some out) :
    Store.Val.handles out ⊆ Store.Val.handles replacement ++ Store.Val.handles value := by
  obtain ⟨es, he, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  rw [frame_handles]
  exact List.Subset.trans (canon_handles _) (List.append_subset.mpr
    ⟨List.subset_append_left _ _, List.Subset.trans (entries_handles he) (List.subset_append_right _ _)⟩)

private theorem keys_of_handles {v : Val} {vs : List Val}
    (h : Store.Val.handles v ⊆ vs.flatMap Store.Val.handles) :
    v.keys ⊆ vs.flatMap Val.keys := by
  intro k hk
  rw [Val.keys_eq_handles] at hk
  obtain ⟨code, hc, hk⟩ := List.mem_filterMap.mp hk
  obtain ⟨value, hv, hc⟩ := List.mem_flatMap.mp (h hc)
  refine List.mem_flatMap.mpr ⟨value, hv, ?_⟩
  rw [Val.keys_eq_handles]
  exact List.mem_filterMap.mpr ⟨code, hc, hk⟩

theorem build_keys {names : List String} {values : List Val} {v : Val}
    (h : Record.build names values = some v) : v.keys ⊆ values.flatMap Val.keys :=
  keys_of_handles (build h)

theorem read_keys {optional : Bool} {value out : Val} {name : String}
    (h : Record.read optional value name = some out) : out.keys ⊆ value.keys := by
  have hr : Store.Val.handles out ⊆ [value].flatMap Store.Val.handles := by
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using read h
  simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using keys_of_handles hr

theorem set_keys {value replacement out : Val} {name : String}
    (h : Record.set value name replacement = some out) : out.keys ⊆ replacement.keys ++ value.keys := by
  have hr : Store.Val.handles out ⊆ [replacement, value].flatMap Store.Val.handles := by
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using set h
  simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using keys_of_handles hr

end RecordHandles

mutual
theorem evalTerm_keys (t : Term) (env : List Val) (v : Val) (h : evalTerm env t = some v) :
    v.keys ⊆ env.flatMap Val.keys := by
  cases t with
  | var i =>
    have h' : env[i]? = some v := h
    exact fun x hx => List.mem_flatMap.mpr ⟨v, List.mem_of_getElem? h', hx⟩
  | lit l =>
    have h' : l.toVal = some v := h
    rw [Lit.toVal_keys l v h']
    exact List.nil_subset _
  | app atom args =>
    rw [evalTerm_app] at h
    obtain ⟨vs, hvs, hv⟩ := Option.bind_eq_some_iff.mp h
    exact List.Subset.trans (nativeAtom_keys atom vs v hv) (evalTerms_keys args env vs hvs)
  | record fields names values =>
    have h' : (evalTerms env values).bind (Record.build names) = some v := h
    obtain ⟨vs, hvs, hv⟩ := Option.bind_eq_some_iff.mp h'
    exact List.Subset.trans (RecordHandles.build_keys hv) (evalTerms_keys values env vs hvs)
  | field mode target name =>
    have h' : (evalTerm env target).bind (fun value => Record.read (mode = .optional) value name) = some v := h
    obtain ⟨value, he, hr⟩ := Option.bind_eq_some_iff.mp h'
    exact List.Subset.trans (RecordHandles.read_keys hr) (evalTerm_keys target env value he)
  | recordSet target name replacement =>
    have h' : ((evalTerm env target).bind fun value => (evalTerm env replacement).bind
      fun next => Record.set value name next) = some v := h
    obtain ⟨value, he, hr⟩ := Option.bind_eq_some_iff.mp h'
    obtain ⟨next, hn, hs⟩ := Option.bind_eq_some_iff.mp hr
    exact List.Subset.trans (RecordHandles.set_keys hs) (List.append_subset.mpr
      ⟨evalTerm_keys replacement env next hn, evalTerm_keys target env value he⟩)
  | tupleAt target index =>
    have h' : (evalTerm env target).bind (fun value => Val.tupleAt? value index) = some v := h
    obtain ⟨value, he, hr⟩ := Option.bind_eq_some_iff.mp h'
    exact List.Subset.trans (tupleAt_keys hr) (evalTerm_keys target env value he)
termination_by structural t
theorem evalTerms_keys (ts : Terms) (env : List Val) (vs : List Val) (h : evalTerms env ts = some vs) :
    vs.flatMap Val.keys ⊆ env.flatMap Val.keys := by
  cases ts with
  | nil =>
    have h' : some ([] : List Val) = some vs := h
    cases h'
    exact List.nil_subset _
  | cons head tail =>
    rw [evalTerms_cons] at h
    obtain ⟨v1, hv1, h'⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rest, hrest, hcons⟩ := Option.bind_eq_some_iff.mp h'
    cases hcons
    rw [List.flatMap_cons]
    exact List.append_subset.mpr ⟨evalTerm_keys head env v1 hv1, evalTerms_keys tail env rest hrest⟩
termination_by structural ts
end

theorem evalTerm_point_keys (t : Term) (p : Point) (v : Val) (h : evalTerm p.env t = some v) :
    v.keys ⊆ p.keys :=
  List.Subset.trans (evalTerm_keys t p.env v h) p.env_keys_subset

theorem exitOfVal_keys (v : Val) (e : ExitV) (h : exitOfVal v = some e) : exitKeys e ⊆ v.keys := by
  rw [exitImage.ofVal_exact h]
  cases e with
  | success x =>
    show x.keys ⊆ Val.keys (Val.exitOk x)
    rw [Val.keys_exitOk]
    exact List.Subset.refl _
  | failure c => exact List.nil_subset _

theorem awaitCellOf_keys (v : Val) (cell : DeferredKey) (h : NativeOp.awaitCellOf v = some cell) :
    Handle.promise cell ∈ v.keys := by
  unfold NativeOp.awaitCellOf at h
  split at h
  · injection h with h
    subst h
    simp only [Val.keys, Handle.ofCode_promise, Option.toList, List.mem_singleton]
  · exact nomatch h

theorem syncOpOf_keys (op : NativeOp) (v : Val) (o : SyncOp) (h : NativeOp.syncOpOf op v = some o) :
    o.keys ⊆ v.keys := by
  unfold NativeOp.syncOpOf at h
  split at h <;> cases h <;> sub_tac

theorem tuple?_keys (v : Val) : ∀ vs, Val.tuple? v = some vs → vs.flatMap Val.keys ⊆ v.keys := by
  intro vs h
  rw [Val.tuple?_exact h, Val.tuple, Val.keys_list]
  exact List.Subset.refl _

theorem mapM_fiber_keys (g : Val → Option FiberId) (hg : ∀ v id, g v = some id → Handle.fiber id ∈ v.keys) :
    ∀ (vs : List Val) (ids : List FiberId), vs.mapM g = some ids → ids.map Handle.fiber ⊆ vs.flatMap Val.keys
  | [], ids, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    exact List.nil_subset _
  | v :: vs, ids, h => by
    simp only [List.mapM_cons, bind, pure] at h
    obtain ⟨id, hid, h'⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rest, hrest, hcons⟩ := Option.bind_eq_some_iff.mp h'
    simp only [Option.some.injEq] at hcons
    subst hcons
    simp only [List.map_cons, List.flatMap_cons]
    exact List.cons_subset.mpr ⟨List.mem_append_left _ (hg v id hid),
      List.Subset.trans (mapM_fiber_keys g hg vs rest hrest) (List.subset_append_right _ _)⟩

end Effect4.Program

/-!
## Raw handle frames through native terms

The corresponding isolated candidate was checked on Lean v4.33.1 at
58cccb7a28c4df4d1a73dd6db1c2e3c811455b7a; all ten declarations use at most
[propext, Quot.sound]. These laws retain every raw kind byte and index.

Placement:
1. Concept4 native value invariant; Concept1 identifies the value boundary.
2. Serves the value boundary: `lit_toVal_handles` is read by the layer arm
   (`Typed/LayerArm.lean`), and the subset laws are the register's evidence that terms
   mint no frames (`E4-TYPED-CE-040`). `exitHandles_valid` is proved by the typed route
   (`Typed/Commands/Clauses/All.lean`), which supersedes row 180's native invariant.
3. Actual nativeAtom/evalTerm success, arbitrary values/environments, ALL raw
   Store.Val.handles; no typing or registered-input premise on the subset laws.
4. No machine preservation, reachability, handle existence, progress, host or
   backend claim. The final consequence requires registered environment values.
5. Term-construction closure for raw frames (R4); no M7 goal reads it.

The immediate consumer of evalTerm_handles is evalTerm_registered below. The raw
collector is needed because the existing Val.keys collector drops unregistered
kind bytes; its subset law cannot supply registration of all output frames.
-/
set_option autoImplicit false
namespace Effect4.Program.RawHandles
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.Agreement

theorem lit_toVal_handles (l : Lit) (v : Val) (h : l.toVal = some v) :
    Store.Val.handles v = [] := by
  cases l with
  | unit => cases h; rfl
  | nat n => cases h; rfl
  | bool b => cases h; rfl
  | str s => cases h; rfl

theorem valOfErr_handles (err : Err) (v : Val) (h : valOfErr err = some v) :
    Store.Val.handles v = [] := by
  cases err <;> cases h <;> rfl

theorem queryTag_handles (tag : ReasonTag) (input output : Val)
    (h : queryTag tag input = some output) : Store.Val.handles output = [] := by
  obtain ⟨reasons, _, houtput⟩ := Option.map_eq_some_iff.mp h
  cases houtput
  rfl

theorem queryError_handles (input output : Val) (h : queryError input = some output) :
    Store.Val.handles output = [] := by
  obtain ⟨reasons, _, houtput⟩ := Option.bind_eq_some_iff.mp h
  cases hfound : (reasons.findSome? Reason.error?).bind valOfErr with
  | none =>
    simp only [hfound] at houtput
    cases houtput
    rfl
  | some value =>
    simp only [hfound] at houtput
    cases houtput
    change Store.Val.handles value = []
    obtain ⟨error, _, hvalue⟩ := Option.bind_eq_some_iff.mp hfound
    exact valOfErr_handles error value hvalue

theorem handles_list (vs : List Val) :
    Store.Val.handles (Val.list vs) = vs.flatMap Store.Val.handles :=
  Store.Val.handlesList_eq_flatMap vs

theorem asList_handles {v : Val} {vs : List Val} (h : Val.asList? v = some vs) :
    vs.flatMap Store.Val.handles ⊆ Store.Val.handles v := by
  rcases Val.asList?_exact h with rfl | rfl
  · rw [handles_list]
    exact List.Subset.refl _
  · show vs.flatMap Store.Val.handles ⊆ Store.Val.handles (.list vs) ++ []
    rw [List.append_nil, handles_list]
    exact List.Subset.refl _

/-- Atoms return scalars, preserve/rearrange their arguments, or use the closed error image.
The subset forgets multiplicity and order; it retains unregistered bytes and exact indices. -/
theorem nativeAtom_handles (atom : String) (vs : List Val) (v : Val)
    (h : nativeAtom atom vs = some v) :
    Store.Val.handles v ⊆ vs.flatMap Store.Val.handles := by
  unfold nativeAtom at h
  obtain ⟨named, _, h⟩ := Option.bind_eq_some_iff.mp h
  unfold NativeAtom.eval at h
  split at h
  case h_12 =>
    unfold stringsAtom at h
    split at h
    · cases h
      rw [handles_list]
      exact List.Subset.refl _
    · cases h
  case h_13 => rw [queryTag_handles _ _ _ h]; exact List.nil_subset _
  case h_14 => rw [queryError_handles _ _ h]; exact List.nil_subset _
  case h_15 => rw [queryTag_handles _ _ _ h]; exact List.nil_subset _
  case h_16 => rw [queryTag_handles _ _ _ h]; exact List.nil_subset _
  case h_24 =>
    cases h
    split
    · exact fun x hx => List.mem_flatMap.mpr ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), hx⟩
    · exact fun x hx => List.mem_flatMap.mpr
        ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), hx⟩
  case h_25 =>
    cases h
    exact fun x hx => List.mem_flatMap.mpr ⟨_, List.mem_cons_self .., hx⟩
  case h_29 =>
    obtain ⟨elems, hl, rfl⟩ := Option.map_eq_some_iff.mp h
    intro k hk
    simp only [handles_list, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_append] at hk ⊢
    exact hk.imp id (fun hk => asList_handles hl hk)
  case h_30 =>
    obtain ⟨elems, hl, rfl⟩ := Option.map_eq_some_iff.mp h
    split
    · next e he =>
      intro k hk
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append]
      exact .inl (asList_handles hl (List.mem_flatMap.mpr ⟨e, List.mem_of_getElem? he, hk⟩))
    · exact List.nil_subset _
  case h_31 =>
    obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp h
    exact List.nil_subset _
  case h_32 =>
    obtain ⟨front, hf, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨back, hb, rfl⟩ := Option.map_eq_some_iff.mp h
    intro k hk
    simp only [handles_list, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.mem_append] at hk ⊢
    exact hk.imp (fun hk => asList_handles hf hk) (fun hk => asList_handles hb hk)
  case h_37 => cases h; exact List.nil_subset _
  case h_38 =>
    simpa only [List.flatMap_cons, List.flatMap_nil, Store.Val.handles,
      List.nil_append, List.append_nil] using Machine.Map.get_handles h
  case h_39 =>
    intro code hc
    have hm := Machine.Map.set_handles h hc
    simp only [List.flatMap_cons, List.flatMap_nil, Store.Val.handles,
      List.nil_append, List.append_nil, List.mem_append] at hm ⊢
    exact hm.elim Or.inr Or.inl
  case h_40 => rw [Machine.Map.keys_handles h]; exact List.nil_subset _
  case h_41 =>
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      using Machine.Map.entries_handles h
  case h_42 =>
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      using Machine.Map.fromEntries_handles h
  case h_43 =>
    cases h
    rw [handles_list]
    exact List.Subset.refl _
  all_goals cases h
  all_goals sub_tac norm [Val.tuple, Store.Val.handles, Store.Val.handlesList]

mutual
 theorem evalTerm_handles (t : Term) (env : List Val) (v : Val)
     (h : evalTerm env t = some v) :
     Store.Val.handles v ⊆ env.flatMap Store.Val.handles := by
   cases t with
   | var i =>
     have h' : env[i]? = some v := h
     exact fun x hx => List.mem_flatMap.mpr ⟨v, List.mem_of_getElem? h', hx⟩
   | lit l =>
     have h' : l.toVal = some v := h
     rw [lit_toVal_handles l v h']
     exact List.nil_subset _
   | app atom args =>
     rw [evalTerm_app] at h
     obtain ⟨vs, hvs, hv⟩ := Option.bind_eq_some_iff.mp h
     exact List.Subset.trans (nativeAtom_handles atom vs v hv) (evalTerms_handles args env vs hvs)
   | record fields names values =>
     have h' : (evalTerms env values).bind (Record.build names) = some v := h
     obtain ⟨vs, hvs, hv⟩ := Option.bind_eq_some_iff.mp h'
     exact List.Subset.trans (RecordHandles.build hv) (evalTerms_handles values env vs hvs)
   | field mode target name =>
     have h' : (evalTerm env target).bind (fun value => Record.read (mode = .optional) value name) = some v := h
     obtain ⟨value, he, hr⟩ := Option.bind_eq_some_iff.mp h'
     exact List.Subset.trans (RecordHandles.read hr) (evalTerm_handles target env value he)
   | recordSet target name replacement =>
     have h' : ((evalTerm env target).bind fun value => (evalTerm env replacement).bind
       fun next => Record.set value name next) = some v := h
     obtain ⟨value, he, hr⟩ := Option.bind_eq_some_iff.mp h'
     obtain ⟨next, hn, hs⟩ := Option.bind_eq_some_iff.mp hr
     exact List.Subset.trans (RecordHandles.set hs) (List.append_subset.mpr
       ⟨evalTerm_handles replacement env next hn, evalTerm_handles target env value he⟩)
   | tupleAt target index =>
     have h' : (evalTerm env target).bind (fun value => Val.tupleAt? value index) = some v := h
     obtain ⟨value, he, hr⟩ := Option.bind_eq_some_iff.mp h'
     exact List.Subset.trans (tupleAt_handles hr) (evalTerm_handles target env value he)
 termination_by structural t
 theorem evalTerms_handles (ts : Terms) (env : List Val) (vs : List Val)
     (h : evalTerms env ts = some vs) :
     vs.flatMap Store.Val.handles ⊆ env.flatMap Store.Val.handles := by
   cases ts with
   | nil =>
     have h' : some ([] : List Val) = some vs := h
     cases h'
     exact List.nil_subset _
   | cons head tail =>
     rw [evalTerms_cons] at h
     obtain ⟨v1, hv1, h'⟩ := Option.bind_eq_some_iff.mp h
     obtain ⟨rest, hrest, hcons⟩ := Option.bind_eq_some_iff.mp h'
     cases hcons
     rw [List.flatMap_cons]
     exact List.append_subset.mpr
       ⟨evalTerm_handles head env v1 hv1, evalTerms_handles tail env rest hrest⟩
 termination_by structural ts
end

/-- Registered frames in, registered frames out. -/
theorem evalTerm_registered (t : Term) (env : List Val) (v : Val)
    (registered : ∀ x ∈ env, ∀ code ∈ Store.Val.handles x,
      (HandleKind.ofByte? code.1).isSome = true)
    (h : evalTerm env t = some v) :
    ∀ code ∈ Store.Val.handles v, (HandleKind.ofByte? code.1).isSome = true := by
  intro code member
  obtain ⟨x, hx, hcode⟩ := List.mem_flatMap.mp (evalTerm_handles t env v h member)
  exact registered x hx code hcode

end Effect4.Program.RawHandles
