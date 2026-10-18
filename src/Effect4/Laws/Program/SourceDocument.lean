import Effect4.Program.Typing.SourceDocument
import Effect4.Laws.Program.SourceTable
import Effect4.Laws.Auto.Obligations
/-!
Placement: initial-algebras-folds; source-session-coherent and typed-replacement, R14.
Question: checked-edit-atomic and validating document replay.
Reach: sealed documents, exact snapshots, accepted action histories, and the stated policy premises.
Exclusions: admission, progress, native execution, and positive-root conclusions for draft.
Consumers: the tool's atomic wrapper, ordered fill publication, and document replay.
A keepExact edit retains an initially refused root; positivity therefore requires the old positive-root premise.

`Doc.step_coherent`, `Doc.commit_sound`, `Doc.commit_one_keepExact` and `Doc.commit_single_sound`
are proved modulo the feed's planned goals `SourceSession.feed_coherent` and
`SourceSession.feed_keepExact`. Those are false at head
(`FeedCounterexample.feed_coherent_refuted`, `Laws/Program/SourceTable.lean`), and so are these:
a kept-exact commit of the filling `late` at a typed root is accepted, its root is refused and the
edited address loses its typed entry (`FeedCounterexample.commit_sound_refuted`,
`FeedCounterexample.commit_single_sound_refuted`,
`FeedCounterexample.commit_one_keepExact_refuted`). They hold once the feed splices only where
nothing is ill formed.
-/
set_option autoImplicit false
namespace Effect4.Program
open _root_.Effect4.Program.Check

@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Doc.step_replay (origin : DocOrigin) (history : List DocAction) (action : DocAction) :
    replayDoc origin (history ++ [action]) =
      ((DocInternal.replayStep Oracle.uncached
        (DocInternal.replayState origin history) action).value).map (·.session) := by
  unfold replayDoc
  rw [DocInternal.replayState_snoc]

@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Doc.step_refuses {o : Oracle} {d : Doc} {snap : Snap} {action : DocAction}
    {why : DocRefusal} (h : (d.step o snap action).value = .error why) :
    (((d.step o snap action).value.map Prod.fst).toOption.getD d) = d := by
  rw [h]
  rfl

/-! ## What an accepted step keeps -/

/-- **A snapshot that checks is the current snapshot.** A step of `source-document-step`. Its
consumer is `Doc.step_coherent`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Doc.check_ok {d : Doc} {at_ : Snap} (h : d.check at_ = .ok ()) : at_ = d.snap := by
  unfold Doc.check at h
  split at h
  · cases h
  · rename_i hdoc
    split at h
    · cases h
    · rename_i hrev
      obtain ⟨doc, rev⟩ := at_
      simp only [ne_eq, Decidable.not_not] at hdoc hrev
      subst hdoc
      subst hrev
      rfl

namespace DocInternal

/-- A batch keeps the application: each feed does (`SourceSession.feed_keeps`). A step of
`source-document-step`. Its consumer is `apply_app`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem batch_app {o : Oracle} {policy : FeedPolicy} :
    ∀ (items : List (Place × Change)) (s : SourceSession) (idx : Nat) (fresh : Fresh),
      (batch o policy s idx items).value = .ok fresh → fresh.session.app = s.app
  | [], s, idx, fresh, h => by
    simp only [batch, Checked.pure_value] at h
    cases h
    rfl
  | (place, change) :: rest, s, idx, fresh, h => by
    unfold batch at h
    split at h
    · cases h
    · split at h
      · cases h
      · rw [Checked.bind_value] at h
        split at h
        · cases h
        · rename_i next step hf
          rw [Checked.bind_value] at h
          split at h
          · cases h
          · rename_i later hlater
            rw [Checked.pure_value] at h
            cases h
            exact (batch_app rest next (idx + 1) later hlater).trans
              (SourceSession.feed_keeps hf).1

/-- A revert's inverses keep the application. A step of `source-document-step`. Its consumer is
`apply_app`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem undoItems_app {o : Oracle} {policy : FeedPolicy} :
    ∀ (items : List UndoItem) (s : SourceSession) (idx : Nat) (fresh : Fresh),
      (undoItems o policy s idx items).value = .ok fresh → fresh.session.app = s.app
  | [], s, idx, fresh, h => by
    simp only [undoItems, Checked.pure_value] at h
    cases h
    rfl
  | item :: rest, s, idx, fresh, h => by
    unfold undoItems at h
    split at h
    · cases h
    · rw [Checked.bind_value] at h
      split at h
      · cases h
      · rename_i next step hf
        rw [Checked.bind_value] at h
        split at h
        · cases h
        · rename_i later hlater
          rw [Checked.pure_value] at h
          cases h
          exact (undoItems_app rest next (idx + 1) later hlater).trans
            (SourceSession.feed_keeps hf).1

/-- The sole interpreter keeps the application. A step of `source-document-step`. Its consumer
is `Doc.step_coherent`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem apply_app {o : Oracle} {st : State} {a : DocAction} {fresh : Fresh}
    (h : (apply o st a).value = .ok fresh) : fresh.session.app = st.session.app := by
  unfold apply at h
  split at h
  · cases h
  · exact batch_app _ _ _ _ h
  · rw [Checked.bind_value] at h
    split at h
    · cases h
    · rename_i next step hf
      rw [Checked.pure_value] at h
      cases h
      exact (SourceSession.feed_keeps hf).1
  · split at h
    · cases h
    · exact undoItems_app _ _ _ _ h

end DocInternal

/-- **A successful step from a coherent document keeps its origin and application, appends one
action, and stays coherent.** The pointer of `source-document-step`. It is proved modulo
`SourceSession.feed_coherent`; at head a document that drafts `late` is a counterexample
(`FeedCounterexample.doc_coherent_refuted`). -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Doc.step_coherent {o : Oracle} {d next : Doc} {snap : Snap} {action : DocAction}
    {receipt : Receipt} (hc : d.session.Coherent)
    (h : (d.step o snap action).value = .ok (next,receipt)) :
    snap = d.snap ∧ next.origin = d.origin ∧ next.history = d.history ++ [action] ∧
      next.session.Coherent ∧ next.session.app = d.session.app := by
  obtain ⟨hcheck, fresh, happ, horigin, hhist, hsess, -⟩ := Doc.step_ok h
  refine ⟨Doc.check_ok hcheck, horigin, hhist, ?_, ?_⟩
  · rw [hsess]
    exact DocInternal.apply_coherent hc happ
  · rw [hsess]
    exact DocInternal.apply_app happ

/-! ## A commit's root -/

namespace SourceSession

/-- A recheck feed is the recheck route. A step of `source-document-commit`. Its consumer is
`feed_recheck_typed`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem feed_recheck_ok {o : Oracle} {s : SourceSession} {e : Edit} {r : SourceSession × Edit.Step}
    (h : (s.feed o .recheck e).value = .ok r) :
    ∃ old c, s.sketch.edit s.app e = some c ∧ (s.recheck o .recheck c e old).value = .ok r := by
  unfold feed at h
  split at h
  · rename_i old c hat hedit
    refine ⟨old, c, hedit, ?_⟩
    split at h
    · exact h
    · exact h
  · cases h

/-- **An accepted recheck holds a typed, coherent session.** A step of
`source-document-commit`. Its consumer is `DocInternal.batch_recheck_final`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem feed_recheck_typed {o : Oracle} {s next : SourceSession} {e : Edit} {step : Edit.Step}
    (h : (s.feed o .recheck e).value = .ok (next, step)) :
    next.Coherent ∧ ∃ ty, next.sketch.sourceCheck next.app = .ok ty := by
  obtain ⟨old, c, -, hr⟩ := feed_recheck_ok h
  have hr1 := recheck_ok hr
  obtain ⟨rfl, -⟩ := Prod.mk.inj hr1
  refine ⟨recheck_coherent s c, ?_⟩
  unfold recheck at hr
  rw [Checked.bind_value, Checked.pure_value, Checked.ask_value] at hr
  cases hv : (run (.module s.app c.holes c.program)).result with
  | error why =>
    simp only [finish, hv] at hr
    cases hr
  | ok ty =>
    exact ⟨ty, hv⟩

/-- **A kept-exact feed keeps the root's type**, on every route: a splice keeps the root entry
first, and a recheck is checked by `finish`. A step of `source-document-commit`. Its consumer is
`DocInternal.batch_keepExact_viewType`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem feed_keepExact_viewType {o : Oracle} {s next : SourceSession} {e : Edit}
    {step : Edit.Step} (hc : s.Coherent) (h : (s.feed o .keepExact e).value = .ok (next, step)) :
    next.view.type = s.view.type := by
  cases hp : e.path with
  | nil =>
    rcases feed_ok_cases h with ⟨-, hpol, -⟩ | ⟨old, c, -, hedit, -⟩
    · cases hpol
    · rw [feed_root o .keepExact s e c hp hedit] at h
      obtain ⟨hr1, ty, hres, hview, -⟩ := recheck_keepExact_ok h
      obtain ⟨rfl, -⟩ := Prod.mk.inj hr1
      rw [view_type (recheck_coherent s c), hview]
      have hsc : c.sourceCheck s.app = .ok ty := hres
      rw [hsc]
      rfl
  | cons i r =>
    have hne : e.path ≠ [] := by
      rw [hp]
      exact List.cons_ne_nil i r
    obtain ⟨old, c, key, focus, hat, hedit, hfocus, hkey, hres, hspl, hrec⟩ :=
      feed_keepExact_ok hne h
    cases hagree : s.expandedEditAgrees c e with
    | true =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (hspl hagree)
      show (Table.typedAt (Table.splice s.table e.path _) []).map (·.2) =
        (Table.typedAt s.table []).map (·.2)
      obtain ⟨rest, hhead⟩ := Sketch.sourceTable_head s.sketch s.app
      rw [table_eq hc, hhead, Table.typedAt_splice_root rfl hne]
    | false =>
      obtain ⟨hr1, ty, hres', hview, -⟩ := recheck_keepExact_ok (hrec hagree)
      obtain ⟨rfl, -⟩ := Prod.mk.inj hr1
      rw [view_type (recheck_coherent s c), hview]
      have hsc : c.sourceCheck s.app = .ok ty := hres'
      rw [hsc]
      rfl

/-- On a coherent session, the root's entry holds the check through the references. A step of
`source-document-single-transport`. Its consumer is `Doc.commit_single_sound`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem typedAt_root {s : SourceSession} {T : EffTy} (hc : s.Coherent)
    (hT : s.sketch.sourceCheck s.app = .ok T) : Table.typedAt s.table [] = some ([], T) := by
  obtain ⟨rest, hhead⟩ := Sketch.sourceTable_head s.sketch s.app
  rw [table_eq hc, hhead, hT]
  unfold Table.typedAt
  rw [List.find?_cons]
  rfl

end SourceSession

namespace DocInternal

/-- A kept-exact batch keeps coherence and the root's type, given feeds that keep coherence. A
step of `source-document-commit`. Its consumer is `Doc.commit_sound`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem batch_keepExact_viewType {o : Oracle}
    (hfeed : ∀ {s next : SourceSession} {e : Edit} {step : Edit.Step}, s.Coherent →
      (s.feed o .keepExact e).value = .ok (next, step) → next.Coherent) :
    ∀ (items : List (Place × Change)) (s : SourceSession) (idx : Nat) (fresh : Fresh),
      s.Coherent → (batch o .keepExact s idx items).value = .ok fresh →
      fresh.session.Coherent ∧ fresh.session.view.type = s.view.type
  | [], s, idx, fresh, hc, h => by
    simp only [batch, Checked.pure_value] at h
    cases h
    exact ⟨hc, rfl⟩
  | (place, change) :: rest, s, idx, fresh, hc, h => by
    unfold batch at h
    split at h
    · cases h
    · split at h
      · cases h
      · rw [Checked.bind_value] at h
        split at h
        · cases h
        · rename_i next step hf
          rw [Checked.bind_value] at h
          split at h
          · cases h
          · rename_i later hlater
            rw [Checked.pure_value] at h
            cases h
            obtain ⟨hc', hv⟩ := batch_keepExact_viewType hfeed rest next (idx + 1) later
              (hfeed hc hf) hlater
            exact ⟨hc', hv.trans (SourceSession.feed_keepExact_viewType hc hf)⟩

/-- **A nonempty recheck batch ends in a typed, coherent session**: its last feed's recheck. A
step of `source-document-commit`. Its consumer is `Doc.commit_sound`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem batch_recheck_final {o : Oracle} :
    ∀ (items : List (Place × Change)) (s : SourceSession) (idx : Nat) (fresh : Fresh),
      items ≠ [] → (batch o .recheck s idx items).value = .ok fresh →
      fresh.session.Coherent ∧ ∃ ty, fresh.session.sketch.sourceCheck fresh.session.app = .ok ty
  | [], _, _, _, hne, _ => absurd rfl hne
  | (place, change) :: rest, s, idx, fresh, _, h => by
    unfold batch at h
    split at h
    · cases h
    · split at h
      · cases h
      · rw [Checked.bind_value] at h
        split at h
        · cases h
        · rename_i next step hf
          rw [Checked.bind_value] at h
          split at h
          · cases h
          · rename_i later hlater
            rw [Checked.pure_value] at h
            cases h
            cases rest with
            | nil =>
              simp only [batch, Checked.pure_value] at hlater
              cases hlater
              exact SourceSession.feed_recheck_typed hf
            | cons it more =>
              exact batch_recheck_final (it :: more) next (idx + 1) later (List.cons_ne_nil _ _)
                hlater

/-- The edit a change makes stands at the resolved address. A step of
`source-document-local-keep`. Its consumers are `Doc.commit_one_keepExact` and
`Doc.commit_single_sound`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem editOf_path {s : SourceSession} {path : List Nat} {change : Change} {e : Edit}
    (h : editOf s path change = .ok e) : e.path = path := by
  cases change with
  | fill q =>
    cases h
    rfl
  | omitHole name =>
    simp only [editOf] at h
    cases hf : s.focusAt path with
    | none =>
      rw [hf] at h
      cases h
    | some focus =>
      rw [hf] at h
      cases h
      rfl

/-- **A single-item commit is one feed**: the place resolves, the change makes its edit, the feed
answers, and the commit's session is the feed's. A step of `source-document-local-keep`. Its
consumers are `Doc.commit_one_keepExact` and `Doc.commit_single_sound`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem batch_single {o : Oracle} {policy : FeedPolicy} {s : SourceSession}
    {place : Place} {change : Change} {fresh : Fresh}
    (h : (batch o policy s 0 [(place, change)]).value = .ok fresh) :
    ∃ path q e step, place.resolve s.app s.sketch = .ok (path, q) ∧
      editOf s path change = .ok e ∧ (s.feed o policy e).value = .ok (fresh.session, step) := by
  unfold batch at h
  split at h
  · cases h
  · rename_i path q hres
    split at h
    · cases h
    · rename_i e hed
      rw [Checked.bind_value] at h
      split at h
      · cases h
      · rename_i next step hf
        rw [Checked.bind_value] at h
        simp only [batch, Checked.pure_value] at h
        cases h
        exact ⟨path, q, e, step, hres, hed, hf⟩

end DocInternal

/-- **A successful keepExact or recheck commit is positive**, with initial positivity required
for keepExact: a kept-exact batch keeps the root's type, and a recheck batch ends in a typed
recheck. The pointer of `source-document-commit`. It is proved modulo
`SourceSession.feed_coherent`, and it is false at head with it
(`FeedCounterexample.commit_sound_refuted`). -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Doc.commit_sound {o : Oracle} {d next : Doc} {snap : Snap}
    {items : List (Place × Change)} {policy : FeedPolicy} {receipt : Receipt}
    (hc : d.session.Coherent)
    (hpolicy : policy = .keepExact ∨ policy = .recheck)
    (hpositive : policy = .keepExact → ∃ T, d.session.sketch.sourceCheck d.session.app = .ok T)
    (h : (d.step o snap (.commit items policy)).value = .ok (next,receipt)) :
    snap = d.snap ∧ next.origin = d.origin ∧ next.snap.revision = d.snap.revision + 1 ∧
      next.session.Coherent ∧ next.session.app = d.session.app ∧
      ∃ T', next.session.sketch.sourceCheck next.session.app = .ok T' ∧
        (policy = .keepExact → d.session.sketch.sourceCheck d.session.app = .ok T') := by
  obtain ⟨hsnap, horigin, hhist, hcoh, happ⟩ := Doc.step_coherent hc h
  obtain ⟨-, fresh, happly, -, -, hsess, -⟩ := Doc.step_ok h
  refine ⟨hsnap, horigin, ?_, hcoh, happ, ?_⟩
  · show next.history.length = d.history.length + 1
    rw [hhist, List.length_append, List.length_singleton]
  · cases items with
    | nil =>
      simp only [DocInternal.apply, Checked.pure_value] at happly
      cases happly
    | cons it rest =>
      rcases hpolicy with rfl | rfl
      · obtain ⟨T, hT⟩ := hpositive rfl
        obtain ⟨-, hview⟩ := DocInternal.batch_keepExact_viewType
          (fun hs hf => SourceSession.feed_coherent hs hf) _ _ _ _ hc happly
        refine ⟨T, ?_, fun _ => hT⟩
        have hv := SourceSession.view_type hcoh
        rw [hsess, hview, SourceSession.view_type hc, hT, ← hsess] at hv
        cases hsc : next.session.sketch.sourceCheck next.session.app with
        | ok t =>
          rw [hsc] at hv
          cases hv
          rfl
        | error r =>
          rw [hsc] at hv
          cases hv
      · obtain ⟨-, ty, hty⟩ := DocInternal.batch_recheck_final _ _ _ _ (List.cons_ne_nil _ _) happly
        exact ⟨ty, by rw [hsess]; exact hty, fun hk => nomatch hk⟩

/-- **A single kept edit retains both exact observations, including an initially refused root.**
The pointer of `source-document-local-keep`. It is proved modulo `SourceSession.feed_keepExact`,
and it is false at head with it (`FeedCounterexample.commit_one_keepExact_refuted`). -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Doc.commit_one_keepExact {o : Oracle} {d next : Doc} {snap : Snap}
    {place : Place} {change : Change} {receipt : Receipt} {path : List Nat} {expected : NativeEff}
    (hc : d.session.Coherent) (hp : path ≠ [])
    (hplace : place.resolve d.session.app d.session.sketch = .ok (path,expected))
    (h : (d.step o snap (.commit [(place,change)] .keepExact)).value = .ok (next,receipt)) :
    next.session.view.type = d.session.view.type ∧
      Table.typedAt next.session.table path = Table.typedAt d.session.table path := by
  obtain ⟨-, fresh, happly, -, -, hsess, -⟩ := Doc.step_ok h
  obtain ⟨path', q, e, step, hres, hed, hf⟩ := DocInternal.batch_single happly
  have hres' : place.resolve d.session.app d.session.sketch = .ok (path', q) := hres
  rw [hplace, Except.ok.injEq, Prod.mk.injEq] at hres'
  obtain ⟨rfl, rfl⟩ := hres'
  have hepath : e.path = path := DocInternal.editOf_path hed
  have hk := SourceSession.feed_keepExact (e := e) hc (by rw [hepath]; exact hp) hf
  rw [hepath] at hk
  rw [hsess]
  exact ⟨hk.1, hk.2.1⟩

/-- **The old single-edit observations, with the required initial positive-root premise.** The
pointer of `source-document-single-transport`. It is proved modulo
`SourceSession.feed_coherent` and `SourceSession.feed_keepExact`, and it is false at head with
them (`FeedCounterexample.commit_single_sound_refuted`). -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Doc.commit_single_sound {o : Oracle} {d next : Doc} {snap : Snap}
    {path : List Nat} {expected : NativeEff} {change : Change} {policy : FeedPolicy}
    {receipt : Receipt} (hc : d.session.Coherent)
    (hpolicy : policy = .keepExact ∨ policy = .recheck)
    (hpositive : policy = .keepExact → ∃ T, d.session.sketch.sourceCheck d.session.app = .ok T)
    (h : (d.step o snap (.commit [(.at_ path expected,change)] policy)).value = .ok (next,receipt)) :
    snap = d.snap ∧ next.id = d.id ∧ next.revision = d.revision + 1 ∧
      next.session.Coherent ∧ next.session.app = d.session.app ∧
      (∃ e, DocInternal.editOf d.session path change = .ok e ∧
        d.session.sketch.edit d.session.app e = some next.session.sketch) ∧
      ∃ T', next.session.sketch.sourceCheck d.session.app = .ok T' ∧
        (policy = .keepExact → d.session.sketch.sourceCheck d.session.app = .ok T' ∧
          Table.typedAt next.session.table path = Table.typedAt d.session.table path) := by
  obtain ⟨hsnap, horigin, hrev, hcoh, happ, T', hT', hkeep⟩ := Doc.commit_sound hc hpolicy hpositive h
  obtain ⟨-, fresh, happly, -, -, hsess, -⟩ := Doc.step_ok h
  obtain ⟨path', q, e, step, hres, hed, hf⟩ := DocInternal.batch_single happly
  have hpath : path' = path := by
    simp only [Place.resolve] at hres
    split at hres
    · cases hres
      rfl
    · cases hres
  subst hpath
  rw [← hsess] at hf
  have hedit : d.session.sketch.edit d.session.app e = some next.session.sketch := by
    show d.runtime.session.sketch.edit d.runtime.session.app e = some next.session.sketch
    rcases SourceSession.feed_ok_cases hf with ⟨-, hpol, -⟩ |
        ⟨old, c, -, hc', hr | ⟨key, focus, -, -, -, -, -, -, hr⟩⟩
    · rcases hpolicy with rfl | rfl <;> cases hpol
    · rw [hc']
      obtain ⟨hn, -⟩ := Prod.mk.inj hr
      rw [hn]
    · rw [hc']
      obtain ⟨hn, -⟩ := Prod.mk.inj hr
      rw [hn]
  have hT'' : next.session.sketch.sourceCheck d.session.app = .ok T' := by
    rw [← happ]
    exact hT'
  refine ⟨hsnap, ?_, hrev, hcoh, happ, ⟨e, hed, hedit⟩, T', hT'', fun hk => ⟨hkeep hk, ?_⟩⟩
  · show next.origin.id = d.origin.id
    rw [horigin]
  · subst hk
    cases path' with
    | nil =>
      have hd := hkeep rfl
      rw [SourceSession.typedAt_root hcoh hT', SourceSession.typedAt_root hc hd]
    | cons i r =>
      have hepath : e.path = i :: r := DocInternal.editOf_path hed
      have hk := SourceSession.feed_keepExact (e := e) hc
        (by rw [hepath]; exact List.cons_ne_nil i r) hf
      rw [hepath] at hk
      exact hk.2.1

/-- An entry's immediate revert restores its prior program and retains appended hole rows. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
proof_goal Doc.revert_program {o : Oracle} {before after back : Doc} {snap : Snap}
    {action : DocAction} {receipt inverse : Receipt}
    (hc : before.session.Coherent)
    (ha : (before.step o snap action).value = .ok (after,receipt))
    (hr : (after.step o after.snap (.revert before.history.length)).value = .ok (back,inverse)) :
    back.session.sketch.program = before.session.sketch.program ∧
      back.session.sketch.holes = after.session.sketch.holes

/-! ## A commit's counterexample at head

A kept-exact commit of the filling `FeedCounterexample.late` at `[0]` of the typed base
`FeedCounterexample.base` (`Laws/Program/SourceTable.lean`) is accepted. Its root is refused, and
the edited address loses its typed entry. Each statement below is a control, kernel-checked by
evaluation (`decide`): it shows where a law proved modulo `SourceSession.feed_coherent` or
`SourceSession.feed_keepExact` stops at head. Its placement names the concept and no
requirement. They go once the feed splices only where nothing is ill formed. -/

namespace FeedCounterexample

/-- The document the base opens. -/
def baseDoc : Doc := (Doc.open_ ⟨{}, {}, base⟩).value

/-- The kept-exact commit of `late` at `[0]`, from the opened base. -/
def commitLate : Except DocRefusal (Doc × Receipt) :=
  (baseDoc.step Oracle.uncached baseDoc.snap
    (.commit [(.at_ [0] seven, .fill late)] .keepExact)).value

/-- The opened base is coherent. -/
def baseCoherent : Bool :=
  decide (baseDoc.session.table = baseDoc.session.sketch.sourceTable baseDoc.session.app)

/-- The opened base's root is typed. -/
def baseTyped : Bool := (baseDoc.session.sketch.sourceCheck baseDoc.session.app).toOption.isSome

/-- The commit is accepted, and its root is refused. -/
def commitRootRefused : Bool :=
  match commitLate with
  | .ok (next, _) => (next.session.sketch.sourceCheck next.session.app).toOption.isNone
  | .error _ => false

/-- The commit is accepted, and the entry at `[0]` changes. -/
def commitEntryLost : Bool :=
  match commitLate with
  | .ok (next, _) =>
    !decide (Table.typedAt next.session.table [0] = Table.typedAt baseDoc.session.table [0])
  | .error _ => false

set_option maxRecDepth 100000 in
/-- The evaluation of the four verdicts. -/
theorem commitVerdicts : baseCoherent = true ∧ baseTyped = true ∧ commitRootRefused = true ∧
    commitEntryLost = true := by
  decide +kernel

/-- The base's session is coherent. A step of the controls below. -/
theorem baseDoc_coherent : baseDoc.session.Coherent := by
  have h0 := commitVerdicts.1
  unfold baseCoherent at h0
  have h1 := of_decide_eq_true h0
  exact h1

/-- The base's root has a type. A step of the controls below. -/
theorem baseDoc_typed : ∃ T, baseDoc.session.sketch.sourceCheck baseDoc.session.app = .ok T := by
  have hpos := commitVerdicts.2.1
  unfold baseTyped at hpos
  cases hx : baseDoc.session.sketch.sourceCheck baseDoc.session.app with
  | ok T => exact ⟨T, rfl⟩
  | error r =>
    rw [hx] at hpos
    cases hpos

end FeedCounterexample

/-- **`Doc.commit_sound` is false at head**: from the coherent, typed base, the kept-exact commit
of `late` is accepted and its root is refused, where the law concludes a typed root. A control of
the claim `source-document-commit`. -/
@[semantics "initial-algebras-folds"]
theorem FeedCounterexample.commit_sound_refuted :
    ¬ ∀ (o : Oracle) (d next : Doc) (snap : Snap) (items : List (Place × Change))
      (policy : FeedPolicy) (receipt : Receipt), d.session.Coherent →
      (policy = .keepExact ∨ policy = .recheck) →
      (policy = .keepExact → ∃ T, d.session.sketch.sourceCheck d.session.app = .ok T) →
      (d.step o snap (.commit items policy)).value = .ok (next,receipt) →
      ∃ T', next.session.sketch.sourceCheck next.session.app = .ok T' := by
  intro h
  have hcoh := FeedCounterexample.baseDoc_coherent
  have hroot := FeedCounterexample.commitVerdicts.2.2.1
  unfold FeedCounterexample.commitRootRefused FeedCounterexample.commitLate at hroot
  split at hroot
  · rename_i next receipt heq
    obtain ⟨T', hT'⟩ := h _ _ _ _ _ _ _ hcoh (Or.inl rfl)
      (fun _ => FeedCounterexample.baseDoc_typed) heq
    rw [hT'] at hroot
    cases hroot
  · cases hroot

/-- **`Doc.commit_single_sound` is false at head**: the same commit is a single item at an
address, and its root is refused. A control of the claim `source-document-single-transport`. -/
@[semantics "initial-algebras-folds"]
theorem FeedCounterexample.commit_single_sound_refuted :
    ¬ ∀ (o : Oracle) (d next : Doc) (snap : Snap) (path : List Nat) (expected : NativeEff)
      (change : Change) (policy : FeedPolicy) (receipt : Receipt), d.session.Coherent →
      (policy = .keepExact ∨ policy = .recheck) →
      (policy = .keepExact → ∃ T, d.session.sketch.sourceCheck d.session.app = .ok T) →
      (d.step o snap (.commit [(.at_ path expected,change)] policy)).value = .ok (next,receipt) →
      ∃ T', next.session.sketch.sourceCheck d.session.app = .ok T' := by
  intro h
  have hcoh := FeedCounterexample.baseDoc_coherent
  have hroot := FeedCounterexample.commitVerdicts.2.2.1
  unfold FeedCounterexample.commitRootRefused FeedCounterexample.commitLate at hroot
  split at hroot
  · rename_i next receipt heq
    obtain ⟨T', hT'⟩ := h _ _ _ _ _ _ _ _ _ hcoh (Or.inl rfl)
      (fun _ => FeedCounterexample.baseDoc_typed) heq
    obtain ⟨-, fresh, happly, -, -, hsess, -⟩ := Doc.step_ok heq
    have happ : next.session.app = FeedCounterexample.baseDoc.session.app := by
      rw [hsess]
      exact DocInternal.apply_app happly
    rw [happ, hT'] at hroot
    cases hroot
  · cases hroot

/-- **`Doc.commit_one_keepExact` is false at head**: the same commit changes the entry at `[0]`.
A control of the claim `source-document-local-keep`. -/
@[semantics "initial-algebras-folds"]
theorem FeedCounterexample.commit_one_keepExact_refuted :
    ¬ ∀ (o : Oracle) (d next : Doc) (snap : Snap) (place : Place) (change : Change)
      (receipt : Receipt) (path : List Nat) (expected : NativeEff), d.session.Coherent →
      path ≠ [] → place.resolve d.session.app d.session.sketch = .ok (path,expected) →
      (d.step o snap (.commit [(place,change)] .keepExact)).value = .ok (next,receipt) →
      Table.typedAt next.session.table path = Table.typedAt d.session.table path := by
  intro h
  have hcoh := FeedCounterexample.baseDoc_coherent
  have hplace : (Place.at_ [0] FeedCounterexample.seven).resolve
      FeedCounterexample.baseDoc.session.app FeedCounterexample.baseDoc.session.sketch =
      .ok ([0], FeedCounterexample.seven) := rfl
  have hlost := FeedCounterexample.commitVerdicts.2.2.2
  unfold FeedCounterexample.commitEntryLost FeedCounterexample.commitLate at hlost
  split at hlost
  · rename_i next receipt heq
    have hk := h _ _ _ _ _ _ _ _ _ hcoh (List.cons_ne_nil 0 []) hplace heq
    rw [Bool.not_eq_true', decide_eq_false_iff_not] at hlost
    exact hlost hk
  · cases hlost
end Effect4.Program
