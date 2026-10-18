import Effect4.Tool.Wire
import Effect4.Laws.Auto.Semantics

/-!
# Laws.Tool.Wire — the tool's replies pair with their requests

Placement: concept `host-session-protocol`, the tool-transition property (seams S3b), R6.
Question: `tool-serve-answers`, role compatibility; pointer `Tool.serve_answers`.
Reach: every certified oracle, every sealed state and every request: `serve`'s reply pairs with
the request (`Wire.responds`), so the adapter's `response` refusal never fires on a reply that
`serve` produced.
Not established: JSON decoding exactness (`CodecProfile.write_read` owns the write half), native
driver behaviour, or host progress.
Consumer: `Wire.serveJson`'s pairing check, and the transcripts S6 compares across drivers.
-/

set_option autoImplicit false
namespace Effect4.Tool
open Effect4.Program.Check

/-- **An accepted action's answer pairs with the action** (claim `tool-serve-answers`). Each branch
of `Internal.action` is read in turn: every refusal contradicts `h`, and every acceptance answers
its own kind, a played run with its own identity. -/
theorem action_pairs (o : Oracle) (st : Internal.Raw) (a : Action) (next : Internal.Raw)
    (answer : ActionAnswer) (h : (Internal.action o st a).value = .ok (next, answer)) :
    Wire.actionPairs a answer = true := by
  cases a with
  | open_ name app sketch =>
    simp only [Internal.action, bind, Checked.bind', pure, Checked.pure'] at h
    cases h
    rfl
  | edit at_ act =>
    simp only [Internal.action, bind, Checked.bind', pure, Checked.pure'] at h
    cases hd : Internal.checkedDoc st at_ with
    | error why =>
      simp only [hd] at h
      cases h
    | ok d =>
      simp only [hd] at h
      cases hk : (d.step o at_ act).value with
      | error why =>
        simp only [hk] at h
        cases h
      | ok p =>
        simp only [hk] at h
        cases h
        rfl
  | fill at_ batch =>
    simp only [Internal.action, bind, Checked.bind', pure, Checked.pure'] at h
    cases hd : Internal.checkedDoc st at_ with
    | error why =>
      simp only [hd] at h
      cases h
    | ok d =>
      simp only [hd] at h
      split at h
      · cases h
      · cases h
        rfl
  | publish at_ =>
    simp only [Internal.action, bind, Checked.bind', pure, Checked.pure'] at h
    cases hd : Internal.checkedDoc st at_ with
    | error why =>
      simp only [hd] at h
      cases h
    | ok d =>
      simp only [hd] at h
      split at h
      · cases h
      · split at h
        · cases h
        · cases hp : (Internal.fillsFor st d).publication with
          | error why =>
            simp only [hp] at h
            cases h
          | ok act =>
            simp only [hp] at h
            cases hk : (d.step o at_ act).value with
            | error why =>
              simp only [hk] at h
              cases h
            | ok p =>
              simp only [hk] at h
              cases h
              rfl
  | reset =>
    simp only [Internal.action, pure, Checked.pure'] at h
    cases hd : st.doc with
    | none =>
      simp only [hd] at h
      cases h
    | some d =>
      simp only [hd] at h
      cases h
      rfl
  | start at_ budget =>
    simp only [Internal.action, pure, Checked.pure'] at h
    cases hd : Internal.checkedDoc st at_ with
    | error why =>
      simp only [hd] at h
      cases h
    | ok d =>
      simp only [hd] at h
      cases hb : Api.Built.ofSketch d.session.app d.session.sketch with
      | error why =>
        simp only [hb] at h
        cases h
      | ok built =>
        simp only [hb] at h
        cases h
        rfl
  | restore record =>
    simp only [Internal.action, pure, Checked.pure'] at h
    cases hr : record.restore with
    | error why =>
      simp only [hr] at h
      cases h
    | ok live =>
      simp only [hr] at h
      cases h
      rfl
  | play id input =>
    simp only [Internal.action, pure, Checked.pure'] at h
    cases hr : st.runs[id.n]? with
    | none =>
      simp only [hr] at h
      cases h
    | some entry =>
      simp only [hr] at h
      cases he : Internal.events id 0 entry.live input with
      | error why =>
        simp only [he] at h
        cases h
      | ok p =>
        simp only [he] at h
        cases h
        exact decide_eq_true rfl

/-- **A preview's answer pairs with its query** (claim `tool-serve-answers`). -/
theorem preview_pairs (d : Program.Doc) (q : PreviewQuery) (answer : PreviewAnswer)
    (h : Internal.preview d q = .ok answer) : Wire.previewPairs q answer = true := by
  simp only [Internal.preview] at h
  cases ha : Run.Preview.admit (d.session.app.withHoles d.session.sketch.holes)
      d.session.sketch.program with
  | error why =>
    simp only [ha] at h
    cases h
  | ok w =>
    simp only [ha] at h
    cases q with
    | settle tape limit =>
      cases h
      rfl
    | frames tape limit =>
      cases h
      rfl
    | explore budget width =>
      cases h
      rfl

/-- **An answered query pairs with the query** (claim `tool-serve-answers`). A run query answers
its own run in the requested form; a preview pairs by `preview_pairs`, and a `dry` run by
`action_pairs`. -/
theorem query_pairs (o : Oracle) (st : Internal.Raw) (q : Query) (answer : Answer)
    (h : (Internal.query o st q).value = .ok answer) : Wire.queryPairs q answer = true := by
  cases q with
  | doc at_ =>
    simp only [Internal.query, pure, Checked.pure'] at h
    cases hd : Internal.requireDoc st with
    | error why =>
      simp only [hd, bind, Except.bind] at h
      cases h
    | ok d =>
      simp only [hd, bind, Except.bind] at h
      cases at_ with
      | none =>
        cases h
        rfl
      | some path =>
        cases hi : Internal.inspection d path with
        | error why =>
          simp only [hi] at h
          cases h
        | ok found =>
          simp only [hi] at h
          cases h
          rfl
  | history =>
    simp only [Internal.query, pure, Checked.pure'] at h
    cases hd : st.doc with
    | none =>
      simp only [hd] at h
      cases h
    | some d =>
      simp only [hd] at h
      cases h
      rfl
  | fills =>
    simp only [Internal.query, pure, Checked.pure'] at h
    cases h
    rfl
  | suggest at_ place supplied cursor limit =>
    simp only [Internal.query, bind, Checked.bind', pure, Checked.pure'] at h
    cases hd : Internal.checkedDoc st at_ with
    | error why =>
      simp only [hd] at h
      cases h
    | ok d =>
      simp only [hd] at h
      cases hp : place.resolve d.session.app d.session.sketch with
      | error why =>
        simp only [hp] at h
        cases h
      | ok found =>
        simp only [hp] at h
        cases hf : d.session.focusAt found.1 with
        | none =>
          simp only [hf] at h
          cases h
        | some focus =>
          simp only [hf] at h
          split at h
          · cases h
          · cases h
            rfl
  | run id form =>
    simp only [Internal.query, pure, Checked.pure'] at h
    cases hr : st.runs[id.n]? with
    | none =>
      simp only [hr] at h
      cases h
    | some entry =>
      simp only [hr] at h
      cases h
      cases form with
      | view =>
        simp only [Wire.queryPairs, Wire.runPairs, Bool.and_true]
        exact decide_eq_true rfl
      | record =>
        simp only [Wire.queryPairs, Wire.runPairs, Bool.and_true]
        exact decide_eq_true rfl
      | journal =>
        simp only [Wire.queryPairs, Wire.runPairs, Bool.and_true]
        exact decide_eq_true rfl
  | preview pq =>
    simp only [Internal.query, pure, Checked.pure'] at h
    cases hd : st.doc with
    | none =>
      simp only [hd] at h
      cases h
    | some d =>
      simp only [hd] at h
      cases hp : Internal.preview d pq with
      | error why =>
        simp only [hp, Except.map] at h
        cases h
      | ok found =>
        simp only [hp, Except.map] at h
        cases h
        exact preview_pairs d pq found hp
  | dry a =>
    simp only [Internal.query, bind, Checked.bind', pure, Checked.pure'] at h
    cases h
    cases hr : (Internal.action o st a).value with
    | error why => rfl
    | ok p => exact action_pairs o st a p.1 p.2 hr
  | discover =>
    simp only [Internal.query, pure, Checked.pure'] at h
    cases h
    rfl

/-- **Every reply `serve` gives pairs with its request** (`tool-serve-answers`). A refusal pairs
with any request; an accepted action's answer pairs by `action_pairs`, and an answered query by
`query_pairs`. -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem serve_answers : ∀ (o : Oracle) (s : State) (r : Request),
    Wire.responds r (serve o s r).value.2 = true := by
  intro o s r
  cases r with
  | act a =>
    simp only [serve]
    split
    · rfl
    · rename_i next answer h
      exact action_pairs o s.raw a next answer h
  | ask q =>
    show Wire.responds (.ask q)
      ⟨(Internal.query o s.raw q).value, Internal.current s.raw⟩ = true
    cases hq : (Internal.query o s.raw q).value with
    | error why => rfl
    | ok answer =>
      simp only [Wire.responds]
      exact query_pairs o s.raw q answer hq

end Effect4.Tool
