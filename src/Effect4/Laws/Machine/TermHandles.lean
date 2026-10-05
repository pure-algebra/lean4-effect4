import Effect4.Machine.Term
import Effect4.Laws.Machine.Map
import Effect4.Laws.Auto.SubsetTac

/-!
# Machine.TermHandles — terms mint no handle frames

A term's value carries only the raw handle frames of its environment (`RawHandles.evalTerm_handles`):
atom by atom (`RawHandles.nativeAtom_handles`), record operation by record operation
(`RecordHandles.build`, `read`, `set`), static projection by static projection
(`tupleAt_handles`) and list fold by list fold (`foldlM_keeps`, decisions row 228). Its subject is `src/Effect4/Machine/Term.lean`, so the law sits at Machine
height. The store laws read it once a store step evaluates a term (decisions row 43; the state
plan's T2): `SyncOp.refKernel_handles` (`src/Effect4/Laws/Machine/RefKernel.lean`) bounds what every
heap row answers and writes, and the store's validity (`src/Effect4/Laws/Machine/StoresLaws.lean`)
and the handle invariant (`src/Effect4/Laws/Machine/Handles.lean`) are its corollaries.

Moved unchanged, names kept, by seat T2: the raw block, the record frames and the static projection
from `src/Effect4/Laws/Program/Handles/Term.lean`, and the two record-frame lemmas
`Typed.zipNames_columns` and `Typed.recordParts?_eq_some` from
`src/Effect4/Laws/Program/Typed/RecordValues.lean`. Both modules import this one. The two `rfl`
equations the proofs read (`evalTerm_app`, `evalTerms_cons`, `src/Effect4/Laws/Program/Typed.lean`)
are their unfoldings here.
-/

set_option autoImplicit false

/-! ## The record frame's two columns -/

namespace Effect4.Program.Typed
open Effect4.Machine

/-- Successful pairing retains both original columns. Construction uses the name equation. -/
theorem zipNames_columns {α : Type} :
    ∀ (names : List String) (values : List α) (es : List (String × α)),
      Record.zipNames names values = some es →
      es.map Prod.fst = names ∧ es.map Prod.snd = values
  | [], [], _, h => by cases h; exact ⟨rfl, rfl⟩
  | [], _ :: _, _, h => by cases h
  | _ :: _, [], _, h => by cases h
  | n :: names, value :: values, _, h => by
    obtain ⟨es, hes, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨hn, hv⟩ := zipNames_columns names values es hes
    exact ⟨congrArg (List.cons n) hn, congrArg (List.cons value) hv⟩

/-- A record value's frame, from its parts. -/
theorem recordParts?_eq_some {v : Val} {ns xs : List Val} (h : recordParts? v = some (ns, xs)) :
    v = .ctor 0 [.list ns, .list xs] := by
  match v, h with
  | .ctor 0 [.list _, .list _], rfl => rfl

end Effect4.Program.Typed

/-! ## Records and static projections retain only their inputs' raw frames -/

namespace Effect4.Program
open Effect4 Effect4.Machine

/-- A successful static projection selects an existing member of its plain tuple frame.
The key and raw-handle consumers (`tupleAt_keys`, `tupleAt_handles`) use this fact without a
typing premise. -/
theorem Val.tupleAt?_mem {value out : Val} {index : Nat}
    (h : Val.tupleAt? value index = some out) :
    ∃ items, value = .list items ∧ out ∈ items := by
  obtain ⟨items, hv, hi⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨items, Val.tuple?_exact hv, List.mem_of_getElem? hi⟩

/-- Static tuple projection introduces no raw handle; consumed by `RawHandles.evalTerm_handles`. -/
theorem tupleAt_handles {value out : Val} {index : Nat}
    (h : Val.tupleAt? value index = some out) :
    Store.Val.handles out ⊆ Store.Val.handles value := by
  obtain ⟨items, rfl, hi⟩ := Val.tupleAt?_mem h
  change Store.Val.handles out ⊆ Store.Val.handlesList items
  rw [Store.Val.handlesList_eq_flatMap]
  exact fun key hk => List.mem_flatMap.mpr ⟨out, hi, hk⟩

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

end RecordHandles

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

The immediate consumer of evalTerm_handles is evalTerm_registered
(`Laws/Program/Handles/Term.lean`). The raw collector is needed because the
existing Val.keys collector drops unregistered kind bytes; its subset law cannot
supply registration of all output frames.
-/

/-! ## The list fold's evaluation (decisions row 228)

The fold's clause of `evalTerm` as nested `Option.bind`s, and the two facts every law about it
reads: a fold keeps what each step keeps, and a fold answers where each step answers. They are
stated of any step, so the handle laws below, the two value judgments
(`src/Effect4/Laws/Program/Typed.lean`, `src/Effect4/Laws/Program/Typed/RecordOperations.lean`)
and term progress (`src/Effect4/Laws/Program/Typed/Denotation.lean`) read the same two. Steps of
`fold-typed-atomic-update` and `handle-identity-laws` (R4). -/

namespace Effect4.Program
open Effect4 Effect4.Machine

/-- The fold's evaluation: the list and the initial value once, then the body once for each
element from the head, at the environment extended by the accumulator and the element. -/
theorem evalTerm_fold (env : List Val) (accTy : Option Ty) (list init body : Term) :
    evalTerm env (.fold accTy list init body) =
      (evalTerm env list).bind fun value => (Val.asList? value).bind fun items =>
        (evalTerm env init).bind fun start =>
          items.foldlM (fun acc item => evalTerm (env ++ [acc, item]) body) start := rfl

/-- **A fold keeps what each step keeps**: when a step that answers keeps `P` of its accumulator
on the members `Q` of the list, a fold that answers keeps it. It needs successful evaluation and
no typing. -/
theorem foldlM_keeps {α β : Type} {P : β → Prop} {Q : α → Prop} {step : β → α → Option β}
    (hstep : ∀ acc x v, P acc → Q x → step acc x = some v → P v) :
    ∀ (xs : List α) (acc v : β), (∀ x ∈ xs, Q x) → P acc → xs.foldlM step acc = some v → P v
  | [], acc, v, _, hacc, h => by
    have h' : some acc = some v := h
    cases h'
    exact hacc
  | x :: xs, acc, v, hxs, hacc, h => by
    have h' : (step acc x).bind (fun next => xs.foldlM step next) = some v := h
    obtain ⟨next, hnext, hrest⟩ := Option.bind_eq_some_iff.mp h'
    exact foldlM_keeps hstep xs next v (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
      (hstep acc x next hacc (hxs x List.mem_cons_self) hnext) hrest

/-- **A fold answers where each step answers**: when a step answers and keeps `P` on the members
`Q` of the list, the fold answers and keeps `P`. The empty list answers the initial value, and
no step runs. -/
theorem foldlM_answers {α β : Type} {P : β → Prop} {Q : α → Prop} {step : β → α → Option β}
    (hstep : ∀ acc x, P acc → Q x → ∃ v, step acc x = some v ∧ P v) :
    ∀ (xs : List α) (acc : β), (∀ x ∈ xs, Q x) → P acc → ∃ v, xs.foldlM step acc = some v ∧ P v
  | [], acc, _, hacc => ⟨acc, rfl, hacc⟩
  | x :: xs, acc, hxs, hacc => by
    obtain ⟨next, hnext, hP⟩ := hstep acc x hacc (hxs x List.mem_cons_self)
    obtain ⟨v, hv, hPv⟩ :=
      foldlM_answers hstep xs next (fun y hy => hxs y (List.mem_cons_of_mem _ hy)) hP
    refine ⟨v, ?_, hPv⟩
    show (step acc x).bind (fun next => xs.foldlM step next) = some v
    rw [hnext]
    exact hv

end Effect4.Program

namespace Effect4.Program.RawHandles
open Effect4 Effect4.Machine Effect4.Program

theorem lit_toVal_handles (l : Lit) (v : Val) (h : l.toVal = some v) :
    Store.Val.handles v = [] := by
  cases l with
  | unit => cases h; rfl
  | nat n => cases h; rfl
  | bool b => cases h; rfl
  | str s => cases h; rfl

theorem valOfErr_handles (err : Err) (v : Val) (h : valOfErr err = some v) :
    Store.Val.handles v = [] := by
  cases err with
  -- a record payload holds none by the carrier's own proof (decisions row 120)
  | payload p => cases h; exact handles_of_isPayload p.property
  | _ => cases h <;> rfl

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
  -- a prefix and its rest hold members of the list argument (decisions row 228)
  case h_44 =>
    obtain ⟨elems, hl, rfl⟩ := Option.map_eq_some_iff.mp h
    intro k hk
    rw [handles_list] at hk
    obtain ⟨e, he, hke⟩ := List.mem_flatMap.mp hk
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append]
    exact .inl (asList_handles hl (List.mem_flatMap.mpr ⟨e, List.mem_of_mem_take he, hke⟩))
  case h_45 =>
    obtain ⟨elems, hl, rfl⟩ := Option.map_eq_some_iff.mp h
    intro k hk
    rw [handles_list] at hk
    obtain ⟨e, he, hke⟩ := List.mem_flatMap.mp hk
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append]
    exact .inl (asList_handles hl (List.mem_flatMap.mpr ⟨e, List.mem_of_mem_drop he, hke⟩))
  -- the identity test answers a Boolean, which holds no frame (decisions row 229)
  case h_46 =>
    split at h
    · cases h
      exact List.nil_subset _
    · cases h
  all_goals cases h
  -- the list laws `keys_norm` gains only in `Laws/Machine/Handles.lean`, above this module
  all_goals sub_tac norm [Val.tuple, Store.Val.handles, Store.Val.handlesList, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]

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
     change (evalTerms env args).bind (nativeAtom atom) = some v at h
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
   -- the accumulator's frames stay inside the environment's: the initial value's are, each
   -- element's are (they are the list value's), and a step adds only the frames of the
   -- accumulator and of the element to the environment it runs in
   | fold accTy list init body =>
     rw [evalTerm_fold] at h
     obtain ⟨value, hlist, h⟩ := Option.bind_eq_some_iff.mp h
     obtain ⟨items, hitems, h⟩ := Option.bind_eq_some_iff.mp h
     obtain ⟨start, hstart, h⟩ := Option.bind_eq_some_iff.mp h
     refine foldlM_keeps (P := fun acc => Store.Val.handles acc ⊆ env.flatMap Store.Val.handles)
       (Q := fun item => Store.Val.handles item ⊆ env.flatMap Store.Val.handles) ?_ items start v
       ?_ (evalTerm_handles init env start hstart) h
     · intro acc item next hacc hitem hnext k hk
       have hbody := evalTerm_handles body (env ++ [acc, item]) next hnext hk
       simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
         List.mem_append] at hbody
       rcases hbody with hin | hin | hin
       · exact hin
       · exact hacc hin
       · exact hitem hin
     · intro item hitem k hk
       exact evalTerm_handles list env value hlist
         (asList_handles hitems (List.mem_flatMap.mpr ⟨item, hitem, hk⟩))
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
     change ((evalTerm env head).bind fun v =>
       (evalTerms env tail).bind fun rest => some (v :: rest)) = some vs at h
     obtain ⟨v1, hv1, h'⟩ := Option.bind_eq_some_iff.mp h
     obtain ⟨rest, hrest, hcons⟩ := Option.bind_eq_some_iff.mp h'
     cases hcons
     rw [List.flatMap_cons]
     exact List.append_subset.mpr
       ⟨evalTerm_handles head env v1 hv1, evalTerms_handles tail env rest hrest⟩
 termination_by structural ts
end

end Effect4.Program.RawHandles
