# Design A2: the protocol seam, the common caller first

Status: design (history, not authority), one of nine in the seams round; see `../brief-common.md`.

# The authoring protocol module, with the default case made trivial (seam `src/Effect4/Tool/`)

Both common loops rest on one rule: **every reply names the document's current snapshot (`now`), and the next edit sends that value back.** The snapshot check stays exact. Callers never build a target; they copy one from the last reply. A hole is addressed by its index, so a caller never computes a path or an expected program. A `fill` takes a list whose items resolve in order, so filling two holes seen in one listing is a single request, not a stale second one.

## 1. Interface

```lean
namespace Effect4.Tool          -- src/Effect4/Tool/Protocol.lean; imports no Effect4.Laws
open Effect4.Program

/-- A snapshot's name inside one state. Copied from a reply, never built. -/
structure Snap where
  doc : DocId
  revision : Nat

/-- Where an edit lands, read at the request's snapshot. -/
inductive Place
  | hole (index : Nat)                          -- the one address holding `Sketch.hole app index`
  | at (path : List Nat) (expected : NativeEff) -- an address and the sub-program it held

inductive Request
  -- the common path
  | «open» (name : String) (app : SigApp) (sketch : Sketch)
  | fill (at : Snap) (items : List (Place × NativeEff))
  | start (at : Snap)
  | reply (run : Nat) (call : Api.HostSession.Key) (answer : Api.HostSession.Answer)
  -- the general path
  | commit (at : Snap) (items : List (Place × Change)) (policy : Policy)
  | draft (at : Snap) (edit : Edit) | revert (at : Snap) (entry : Nat) | fork (at : Snap) (name : String)
  | look | inspect (path : List Nat) | history
  | fillsAdd (at : Snap) (items : List (List Nat × NativeEff)) | fillsPublish (at : Snap)
  | fillsView | fillsReset
  | suggest (at : Snap) (place : Place) (limit cursor : Nat) (supplied : List NativeEff)
  | catalogue | ask (app : SigApp) (sketch : Sketch) (q : Query)   -- Tools.Query's eight
  | play (run : Nat) (events : List Run.Event) | liveView (run : Nat) | save (run : Nat)
  | load (record : LiveRecord)
  | settle (at : Snap) (tape : List Machine.ExitV) (limit : Nat)
  | frames (at : Snap) (tape : List Machine.ExitV) (limit : Nat)
  | explore (at : Snap) (budget width : Nat) | discover

structure HoleView where
  index : Nat
  row : Row                               -- declared columns
  path : List Nat
  focus : Option (TyEnv × EffTy)          -- `SourceSession.focusAt path`

structure DocView where
  snap : Snap
  type : Option EffTy                     -- `SourceSession.view`
  refusals : List TypeRefusal
  holes : List HoleView                   -- `Sketch.holeSites`, address order

inductive Answer
  | opened (view : DocView)
  | edited (view : DocView) (entries : List (Nat × Edit.Step))   -- history index per action
  | looked (view : DocView) | inspected (i : Doc.Inspection) | history (actions : List DocAction)
  | fills (outcomes : List AddOutcome) (pending : List (List Nat × NativeEff))
  | suggested (r : CheckCache.SuggestResult) | asked (a : Query.Answer)
  | started (run : Nat) (verdict : Run.Verdict) (view : Live.View)
  | played (run : Nat) (verdicts : List Run.Verdict) (view : Live.View)
  | saved (record : LiveRecord) | loaded (run : Nat) (view : Live.View)
  | previewed (a : PreviewAnswer) | discovered (methods : List (String × Nat))

inductive PlaceRefusal | absent (index : Nat) | repeated (index : Nat) (paths : List (List Nat))

inductive Refusal
  | noDocument | foreign (now : Snap) | stale (now : Snap) | empty
  | place (item : Nat) (why : PlaceRefusal)
  | edit (item : Nat) (why : Doc.Refusal)       -- `.refused` carries located `TypeRefusal`s
  | publish (why : MaterializeRefusal) | pendingStale (anchor now : Snap)
  | admission (why : AdmitRefusal) | preview (why : Run.Preview.Refusal)
  | noRun (run : Nat) | unresolved (event : Nat) (call : Run.Sel) | restore (why : LiveRecord.Refusal)

structure Reply where
  result : Except Refusal Answer
  now : Option Snap                       -- the snapshot after the request

inductive Origin | snapshot (snap : Snap) (app : SigApp) (sketch : Sketch) | restored

structure LiveRun where
  id : Nat
  live : Live
  origin : Origin

structure State where
  private mk ::
  doc : Option Doc               -- S1's document: origin, validated history, proof field
  pending : Option FillSet       -- S2's constructed set, stored only while nonempty
  cache : List CheckCache.Entry
  runs : List LiveRun
  nextGen : Nat
  nextRun : Nat
  valid : Invariant doc pending cache runs nextGen nextRun

def State.now (s : State) : Option Snap := s.doc.map fun d => ⟨d.id, d.revision⟩

def serve (s : State) (r : Request) : State × Reply :=
  match attempt s r with                  -- `attempt` is private
  | .error why => (s, ⟨.error why, s.now⟩)
  | .ok (s', a) => (s', ⟨.ok a, s'.now⟩)
```

`Invariant` is a `Prop`, so it erases. It states five things:
- the document's generation is below `nextGen`;
- run ids are distinct and below `nextRun`;
- an `Origin.snapshot n app sk` origin has `live.run.built.program = sk.program` and `live.run.built.app = app.withHoles sk.holes`;
- a stored pending set is nonempty;
- every cache entry is `CheckCache.Entry.compute` of its own key.

Four new helpers, each placed beside its owner:
- `Sketch.holeSites : Sketch → SigApp → List (Nat × List Nat)`, in `Program/Sketch.lean`;
- `Place.resolve : Doc → Place → Except PlaceRefusal EditTarget`;
- `Api.Built.ofSketch : SigApp → Sketch → Except AdmitRefusal Built`. This is S4's one declaration: it runs `admitProgram` at `app.withHoles`, with `rowNames` taken from the rows;
- `Run.Event.answer k c := [.receive (.key k) c, .apply (.key k), .flush]`, in `Run/Event.lean`.

**Ordering and refusals.**
- **Snapshot check.** Every request that carries `at` checks it first, refusing in this order: `noDocument`, `foreign now`, `stale now`. Both of the last two carry the current snapshot.
- **`commit`.** `commit at items policy` folds `Doc.commit`. Item i resolves at the snapshot left by items 0 to i−1, so it may name a hole that an earlier item placed.
  - The first refused item refuses the whole request (`place i` or `edit i`), and the state is unchanged.
  - Success appends one history action per item.
  - `items = []` refuses as `empty`.
- **`fill`** is sugar: `fill at items = commit at (items.map fun (p, q) => (p, .fill q)) .keepExactType`.
- **`Place.hole k`** resolves to the only occurrence of `Sketch.hole app k`. It refuses as `absent` (the hole was filled or dropped) or `repeated`.
- **`start at`** goes through `Built.ofSketch`. A failed admission refuses as `admission`; otherwise the run's origin is recorded.
- **`play run events`** folds `Live.feed`.
  - An unresolved selector at event i refuses the whole request (`unresolved i`).
  - Refused phases are recorded inside `played`.
  - `reply run k c = play run (Run.Event.answer k c)`.
- **Pending fill set.** It follows plan v2's lifecycle. `fillsAdd` reports a per-item `AddOutcome` inside a successful `fills` answer.
- **Reads** never change state.
- **The three outcome kinds stay apart:**
  - an atomic edit's item refusal is a refused request (kind 1);
  - a `fillsAdd` item refusal is recorded inside a successful answer (kind 2);
  - a refused phase is recorded and the journal grows (kind 3).

**OCaml spelling.** `Effect4_tool.state` is abstract (estate rule 1). `serve : state -> Request.t -> state * Reply.t`. `Request`, `Answer`, `Refusal`, `Reply` and `Snap` are generated.

## 2. Worked calculation

The application `A` has one host row, `ask : unit → nat`. Let `h0 := Row.hole "h0" .nat` and `hole0 := Sketch.hole A 0 = .perform (.external 1) (.lit .unit)`. The sketch is `s0 := {program := .bind (.perform (.external 0) (.lit .unit)) hole0, holes := [h0]}`. The starting state σ0 has no document and no runs.

| # | Request | Answer, and the state after | Law |
|---|---|---|---|
| 1 | `open "demo" A s0` | `opened {snap n0 = ⟨⟨"demo",0⟩,0⟩, type nat!never, refusals [], holes [⟨0, h0, [1], ([nat], nat!never)⟩]}`; now n0. The state holds d0 with an empty history, and nextGen is 1. | `SourceSession.reached_view` (no edits); `holeSites_spec`; `SourceSession.focusAt_typed` |
| 2 | `fill n0 [(.hole 0, .succeed (.var 1))]` | n0 passes the check, and hole 0 resolves to `[1]`. The candidate has no type, so the reply is **`edit 0 (.refused [⟨[1], .term (.var 1)⟩])`**: level 1 is unbound at `[1]`, where the environment is `[nat]`. now n0, and the state is unchanged. | `serve_refuses`, `serve_now` |
| 3 | `fill n0 [(.hole 0, .succeed (.var 0))]`, using reply 2's `now` | The candidate has type `nat!never`. The root type and `typedAt [1] = ([nat], nat!never)` are unchanged. Reply: `edited {snap n1 = ⟨⟨"demo",0⟩,1⟩, type nat!never, holes []} [(0, ⟨.fill [1] _, some hole0, .spliced _⟩)]`; now n1. Revision is 1. | `now_fresh`; `Doc.commit_sound`; `Sketch.table_fill` |
| 3′ | `fill n0 …` sent again | `stale n1`; the state is unchanged. | `edit_at_now`: the check is not weakened |
| 4 | `start n1` | `Built.ofSketch A s1` admits at rows `[ask, h0]`. `Live.open` runs, then `.start`. Reply: `started 0 (.played [.progressed]) {outcome frontier, awaiting [⟨fiber f, token t, external 0, unit; checked ⟨unit, nat, never⟩⟩]}`. The state holds run 0 with origin `.snapshot n1 A s1`. | `Sketch.sourceCheck_of_admitted`, `Live.reached`, `Live.view_awaits`, `Live.view_checked` |
| 5 | `reply 0 ⟨f,t⟩ (.ofExit (.success 7))` | The receive plays `[bind, submit]` with phases `[.bound, .preflight]`; the apply gives `[.applied]`; the flush gives `[.progressed]`. Reply: `played 0 … {outcome finished, exit .success 7, awaiting []}`. The journal grows by 4, and the origin is still n1. | `reply_eq_play`, `Run.feed_fst`, `Live.opened_feed`, `Live.journal_replays` |

If step 5 sends an ill-typed answer, the `submit` phase is `.refused …`. The answer is still `played` (kind 3), the journal grows, and the call stays awaiting.

**The view tool's build loop.** `requests` becomes static data plus a fold that threads `now`:

```lean
def plan (p : NativeEff) : Option (Sketch × List (Place × NativeEff)) := do
  let addrs := effAddresses p
  let rows ← holeRows p addrs
  let steps ← addrs.mapM fun a =>
    (filling p addrs a).map ((Place.hole (addrs.findIdx (· == a)), ·))
  pure ({ program := holeOf addrs [], holes := rows }, steps)

def frames (title : String) (p : NativeEff) : Option (List Frame) := do
  let (sk, steps) ← plan p
  let (s, r) := Tool.serve {} (.open title {} sk)
  let go := fun (s, r, out) x => match r.now with
    | none => (s, r, out)
    | some n => let (s', r') := Tool.serve s (.fill n [x]); (s', r', out ++ [frame s' r'])
  pure (steps.foldl go (s, r, [frame s r])).2.2
```

Take `p = .bind (.succeed (.lit 1)) (.succeed (.var 0))`, whose addresses are `[], [0], [1]`, with holes 0 to 2:
- `open` gives n0, with hole 0 at `[]`.
- `fill n0 [(.hole 0, .bind hole1 hole2)]` is a root commit that is `rechecked`, giving n1.
- `fill n1 [(.hole 1, .succeed (.lit 1))]` is `spliced`, giving n2.
- `fill n2 [(.hole 2, .succeed (.var 0))]` is `spliced`, giving n3.

The repair's guesses are gone: generation 0, "revision i" and the expected hole now come from `now` and `Place.hole`. A refused fill draws its frame with the refusal, and `now` stays unchanged. Sending `fill n0 steps` builds the whole program atomically, because each item resolves after the one before it. A static request file may write `"at": "now"`. The line adapter substitutes its own connection's last `now`, so the core never sees that placeholder.

## 3. What the implementation hides

- **The document:** its history, replay proof and cached `SourceSession`, plus the policy checks of `Doc.commit`.
- **The snapshot check:** place resolution through `holeSites` and the check of the snapshot itself.
- **The fill set:** its lifecycle, including the derived empty set, the refusal of a stale nonempty set, and publication.
- **The check cache:** threading `CheckCache` through `suggest`.
- **Starting and running:** the snapshot-to-`Built` step, `admitProgram`, `Live.open` and `feed`, and selector resolution.
- **Saved runs:** `LiveRecord` save and restore.
- **Preview:** admission under the preview profile.
- **Counters:** allocation of generations and run ids.

Several pieces move behind the seam from `tools/Tools/Session.lean`:
- the state fields `source`, `journal`, `docId`, `revision`, `generation`, `live`, `cache` and `fills`;
- `State.doc`, `withDoc`, `fillsFor`, `fillsStale`, `commitAnswer`, `feedAnswer`, `selFrom?` and `policyFrom?`;
- the hand-built `Built` in the `start` and `run` arms. The `run` arm itself becomes `start` followed by `play`.

`Tools.Query.answer`'s dispatch becomes `Request.ask`. The JSON printers stay in `tools/` until S3b replaces them with generated codecs.

## 4. Adapters

The seam is in-process and pure. Three adapters today make it a real seam:
1. the JSON line driver, whose `Tools.Session` shrinks to decode, `serve`, encode;
2. the view tool (`Tools.View.Build`, `Tools.View.Live`);
3. test transcripts.

The native OCaml shell over the lowered `serve` is a local-substitutable fourth. Across adapters, only transport, encoding and the way `now` is threaded vary: a Lean fold, the line driver's per-connection `"now"`, or an OCaml `state ref`.

## 5. Laws

| Law | Statement | Reuses |
|---|---|---|
| `serve_refuses` | A refused request leaves the state unchanged. | the probe's `refusal_inert` (`CoreSketches.lean`) |
| `serve_now` | `(serve s r).2.now = (serve s r).1.now`. | by definition |
| `now_fresh` | `s.now = some n` means the snapshot check passes at n. Read with `serve_now`, the next edit never refuses as stale. | |
| `edit_at_now` | Every accepted edit named the snapshot that was current then. | `Doc.commit_sound` (revision equality) |
| `fill_eq_commit` | The sugar equation above holds. | `rfl` |
| `commit_cons` | Committing `x :: xs` is committing x, then committing xs at the produced `now`, with refusal indices shifted by one. | |
| `commit_appends` | Success adds `items.length` to the revision. | `Doc.commit_sound` |
| `place_hole_sound` | A resolved hole holds exactly `Sketch.hole app k`, and only there. | new: `holeSites_spec` |
| `look_view` | `DocView.type` and `refusals` are the snapshot's `sourceCheck` and `sourceRefusals`. | `SourceSession.reached_view` |
| `hole_focus` | A hole's focus is the expansion's focus. | `SourceSession.focusAt_typed` |
| `reply_eq_play` | `reply` is `play` of `Event.answer`. | `rfl`; `Event.answer_rows` reuses `Run.Rows.answer` |
| `play_journal` | The journal grows by each event's commands, and refused phases stay. | `Run.feed_fst`, `Live.opened_feed`, `Api.Runner.step_refused` |
| `runs_reached` | Every run in the state is reached and its journal replays. | `Live.reached`, `Live.journal_replays` |
| `start_origin` | A snapshot origin was admitted at the hole-extended application. | `Sketch.sourceCheck_of_admitted` |
| `load_restored` | A loaded run has origin `restored`. | `LiveRecord.restore_save` |
| `suggest_uncached` | Suggestions equal the ones computed from an empty cache, once `fromCache` is erased. | `CheckCache.lookup_sound`, `evaluateCandidate_valid_and_sound` |
| `serve_answers`, `invariant_kept` | Every reply pairs with its request, and every success keeps `Invariant`. | generated pairing |

## 6. Trade-offs

**Where leverage is high.**
- An agent learns one rule: copy `now`.
- A fill carries the next hole listing, so no `inspect` round trip is needed.
- A batched fill removes the commonest stale mistake.
- `Place.hole` removes the need to compute paths and expected programs.
- The view tool shrinks to a plan plus a fold.
- `fill` means one thing, by its defining equation.

**Where leverage is thin.** `commit`, `draft`, `revert` and the fill-set requests mostly pass through to `Doc` and `FillSet`.

**What this makes hard later.**
- **Snap's lifetime.** A `Snap` is unique only within one state. The store's decided name, the entry chain's last address, will enter as an added `head` field. Clients copy `Snap` and never build it, so neither loop changes.
- **Batch undo.** A batch appends k actions, so undoing it takes k reverts. Atomic undo stays on the fill-set path.
- **Partial progress.** An all-or-nothing `fill` keeps no partial progress; `fillsAdd` keeps it.
- **Cost per edit.** Each edit recomputes the whole `DocView`, at a cost proportional to the holes and refusals. The Incremental pass caches it under `look_view`.
- **Hole shape.** `Place.hole` assumes a hole is exactly `Sketch.hole app k`.
- **One document per state.** `Snap.doc` already selects among documents, so more than one later is an extension, not a change of shape.

### Critical Files for Implementation
- /Users/pooks/Dev/lean4-effect4-gemini/tools/Tools/Session.lean
- /Users/pooks/Dev/lean4-effect4-gemini/src/Effect4/Program/Typing/SourceDocument.lean
- /Users/pooks/Dev/lean4-effect4-gemini/tools/Tools/View/Build.lean
- /Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Sketch.lean
- /Users/pooks/Dev/lean4-effect4/src/Effect4/Api/Built.lean

