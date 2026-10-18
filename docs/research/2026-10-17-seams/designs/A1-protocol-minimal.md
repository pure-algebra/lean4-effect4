# Design A1: the protocol seam, minimal

Status: design (history, not authority), one of nine in the seams round; see `../brief-common.md`.

# The authoring protocol module (`src/Effect4/Tool/`): one transition, read and write kept apart, alphabets borrowed from their owners

The design has one entry point, `serve`, over `Request := act Action | ask Query`.
- `Action` nests the alphabets the owners already have: S1's edit alphabet, the `FillSet.add` batch, `Run.Event` and `LiveRecord`.
- `Query` contains `Action` through one constructor, `dry`.
- `State` carries a proof that some transcript reaches it, in the shape of `Live.opened`. The plan's `StateInvariant` then becomes a theorem in `Effect4.Laws`, not a proof field.
- The interface comes to 2 entry points and 15 leaf requests. Today there are 26 operations, plus 8 in `Tools.Query`.

## 1. Interface

```lean
namespace Effect4.Tool
structure RunId where n : Nat  deriving DecidableEq

inductive DocEdit                       -- S1's client alphabet; DocAction := edit DocEdit | publish anchor fills
  | commit (t : EditTarget) (c : Change) (p : Policy) | draft (e : Edit) | revert (entry : Nat)
inductive Start | snapshot (budget : Api.Budget) | record (r : LiveRecord)
inductive Action
  | open (app : SigApp) (sketch : Sketch) (name : String) | edit (e : DocEdit)
  | fill (batch : List (List Nat × NativeEff)) | publish | reset
  | start (s : Start) | play (run : RunId) (events : List Run.Event)
inductive RunForm | view | record | journal
inductive PreviewQuery | settle (tape : List ExitV) (limit : Nat)
  | frames (tape : List ExitV) (limit : Nat) | explore (budget width : Nat)
inductive Query
  | doc (at : Option (List Nat))   -- none: sketch, app, view; some p: Doc.inspect p, SigData, slots
  | history | fills | suggest (at : List Nat) (cursor limit : Nat) (supplied : List NativeEff)
  | run (id : RunId) (form : RunForm) | preview (q : PreviewQuery)
  | dry (a : Action) | discover     -- versions, the static catalogue, the document and run identifiers
inductive Request | act (a : Action) | ask (q : Query)

inductive Origin | snapshot (doc : DocId) (revision : Nat) | standalone
inductive Outcome
  | opened (doc : DocId) (view : EditSession.View)
  | edited (doc : DocId) (revision : Nat) (step : Edit.Step) (view : EditSession.View)
  | filled (anchor : Nat) (items : List AddOutcome) | reset (discarded : List (List Nat × NativeEff))
  | started (run : RunId) (origin : Origin) (view : Live.View)
  | played (run : RunId) (phases : List (List Api.HostSession.Phase)) (view : Live.View)
inductive Answer  -- doc, inspected, history, fills, suggested (no cache, no fromCache), run, preview,
  | dry (r : Except Refusal Outcome) | …   -- discover
inductive Reply | acted (o : Outcome) | told (a : Answer)
inductive Refusal
  | noDocument | noAddress (path : List Nat) | noFocus (path : List Nat)
  | doc (why : Doc.Refusal) | revert (entry : Nat) | staleFills (anchor current : Nat) | emptyFills
  | publish (why : MaterializeRefusal) | admission (why : AdmitRefusal)
  | restore (why : LiveRecord.Refusal) | preview (why : Run.Preview.Refusal)
  | noRun (id : RunId) | unresolved (id : RunId) (event : Nat) (sel : Run.Sel)

structure State where
  private mk ::
  raw     : Raw                                   -- hidden, part 3
  reached : ∃ rs : List Request, Raw.replay Raw.empty rs = raw
def State.empty : State
def serve (s : State) (r : Request) : State × Except Refusal Reply
```

**Ordering and refusals**
- **The document must be open.** Every request except `open`, `start (.record _)`, `play`, `run`, `dry` and `discover` refuses `noDocument` when no document is open.
- **`open`** cannot refuse. It allocates generation `nextGen`, replaces the document and clears the pending fills. Live runs stay.
- **`edit`** goes through S1's `Doc.append`. A pending set that holds fills survives the edit and becomes stale.
- **`fill`** refuses `staleFills` when the pending set's anchor is not the current snapshot. Otherwise each item gets its own `AddOutcome`.
- **`publish`** refuses `emptyFills` or `publish why`, and on refusal the pending set is kept. On success it appends one `DocAction.publish` and clears the set.
- **`start .snapshot`** refuses `admission why`. The check is `admitProgram` at `app.withHoles holes`. A run identifier is allocated only on success.
- **`play`** refuses as a whole on an unresolved selector. If event `i` does not resolve, the reply is `unresolved id i sel` and the earlier events are dropped too. A phase refusal is recorded inside `played`.
- **`dry` and `discover`** never refuse.

**OCaml spelling**

```ocaml
module Effect4.Tool : sig
  module State : sig type t val empty : t end           (* rule 1: abstract *)
  module Request : sig type t = Act of Action.t | Ask of Query.t end
  val serve : State.t -> Request.t -> State.t * (Reply.t, Refusal.t) result
end
```

`RespondsTo` is a `Prop`; it erases and nothing of it is lowered. Every type is flat, so control R9 holds.

**Why one function, and why a two-constructor `Request`**
- **No second dispatch site.** Drivers branch on decoded data anyway, so `act` and `ask` exposed as two functions would add one. With one function, the refusal law, the pairing and the witness are each proved once.
- **The split lives in the type.** Splitting `Request` into `act` and `ask` makes read-only a fact of the constructor. That gives MCP's `readOnlyHint` directly, and lets the shell answer queries concurrently.
- **`dry` needs the split.** The query type can only contain the action type if the two are separate.

## 2. Worked calculation

**Values used in the trace**
- The application is `A := ({} : SigApp)` and the hole row is `h0 := Row.hole "h0" .nat`.
- `τ` is the effect type "answers nat, error never".
- `P₀ := .bind (.perform (.external 0) (.lit .unit)) (.succeed (.lit (.nat 0)))` and `S₀ := ⟨P₀, [h0]⟩`. Address `[0]` is the hole, which is row 0 of `A.withHoles [h0]`. Address `[1]` is the continuation, in environment `[nat]`.
- `n := ⟨"demo",0⟩`, `q₁ := succeed (lit 1)`, `q₂ := succeed (var 0)`.
- The starting state `s₀ = State.empty` has: doc none, pending none, runs [], cache [], nextGen 0, nextRun 0.

| # | Request | Reply | State after | Justification |
|---|---|---|---|---|
| 1 | `act (open A S₀ "demo")` | `ok (acted (opened n v₀))`, with `v₀.type = some τ` and no refusals | s₁: doc d₀ (origin ⟨n,A,S₀⟩, history []), nextGen 1 | `Doc.open` cannot refuse; the witness is `[r₁]` |
| 2 | `ask (doc (some [1]))` | `ok (told (inspected ⟨t₀, focus ⟨succeed (lit 0), [nat], τ⟩, …⟩ σ))`, with `t₀ = ⟨n,0,[1],succeed (lit 0)⟩` | s₁, unchanged | `serve_ask` |
| 3 | `act (edit (draft (fill [1] q₁)))` | `ok (acted (edited n 1 ⟨fill [1] q₁, some (succeed (lit 0)), spliced [[1]]⟩ v₁))` | s₃: d₁, history [edit (draft …)] | `Doc.append`; a draft at an existing address is accepted |
| 4 | `act (edit (commit t₀ (fill q₂) keepExactType))` | `error (doc (stale 1))` | s₃, the whole `State` unchanged | `t₀.revision = 0 ≠ 1`; `serve_refuses` |
| 4′ | `ask (dry (edit (commit t₀ …)))` | `ok (told (dry (error (doc (stale 1)))))` | s₃ | `serve_dry`: a dry run of a refused action is a successful query |
| 5 | `act (edit (commit t₁ (fill q₂) keepExactType))`, with `t₁ = ⟨n,1,[1],q₁⟩` | `ok (acted (edited n 2 ⟨fill [1] q₂, some q₁, spliced [[1]]⟩ v₂))`, with `v₂.type = some τ` | s₅: d₂ with sketch S₂ = ⟨bind hole q₂, [h0]⟩; history length 2 | `Doc.commit_sound`: revision + 1, coherent, source check gives τ, `typedAt [1]` kept |
| 6 | `act (start (snapshot {}))` | `ok (acted (started ⟨0⟩ (snapshot n 2) w₀))`, with `w₀.awaiting = [call on "h0", key k=⟨f₀,t⟩, origin [0]]`, `w₀.steps = 1`, outcome `frontier` | s₆: runs [(⟨0⟩, snapshot of d₂, l₀)], nextRun 1; journal [control evaluate], phases [progressed] | `Api.Built.ofSketch A S₂` admits `P₂` at `A.withHoles [h0]` with rowNames [("h0",0)]; then `Live.open` and `feed .start`; `Sketch.sourceCheck_of_admitted`, `Live.reached` |
| 7 | `act (play ⟨0⟩ [apply (row "h0")])` | `ok (acted (played ⟨0⟩ [[refused noCall]] w₁))`, with `w₁.steps = 2` and the awaiting list unchanged | s₇: journal [control evaluate, apply k], phases [progressed, refused noCall]; the session is l₀'s | `Sel.resolve` finds the one live call; `applyReply` finds no bound call; `Api.Runner.step_refused` keeps the session; `Run.step` grows the journal; `feed_fst` |
| 7′ | `act (play ⟨0⟩ [apply (row "h1")])` | `error (unresolved ⟨0⟩ 0 (row "h1"))` | s₇ | `Verdict.unresolved` becomes a refusal of the request |
| 8 | `act (fill [([1], succeed (lit 7)), ([], q₂)])` | `ok (acted (filled 2 [applied [1], refused [] root]))` | s₈: a pending set anchored at revision 2, holding one entry | `FillSet.add`, `FillSet.add_wf` |

Steps 4, 7 and 8 show the three outcome kinds apart:
- step 4 is a refused request, and the state is unchanged;
- step 8 refuses one item inside a successful answer, and the accepted item is kept;
- step 7 records a refused phase, and the journal grows.

## 3. What the implementation hides

```lean
structure Raw where
  doc : Option Doc
  pending : Option FillSet               -- none is the empty set, which follows the document
  runs : List (RunId × RunOrigin × Live) -- RunOrigin keeps the full Doc snapshot
  cache : List CheckCache.Entry
  nextGen nextRun : Nat
Raw.act : Raw → Action → Except Refusal (Raw × Outcome)
Raw.ask : Raw → Query → List CheckCache.Entry × Except Refusal Answer   -- touches only the cache
```

**What sits behind the seam**
- `Raw.serve` is the wrapper from CoreSketches around `act` and `ask`. The witness grows by `rs ++ [r]`, through `List.foldl_append`, and is proved in core.
- `serve` allocates generations and run identifiers, and names each run's session from its `RunId` so the names are deterministic.
- **Pending-set rules.** Holding the empty set as `none` retires `Tools.Session.State.fillsFor` and `fillsStale`.
- **One snapshot-to-`Built` declaration.** A new `Api.Built.ofSketch` in `src/Effect4/Api/Built.lean` replaces the two `Built`s that today's `start` and `run` arms each assemble by hand. It always sets `rowNames`.
- **The three admission profiles:** `admitProgram`, `Run.Preview.admit`, and `LiveRecord.restore`.
- **Selector resolution.** `Run.Event.commands` resolves selectors, and the module turns an unresolved selector into a refusal.
- **The verdict cache.** `CheckCache.lookup`, `insert`, `evaluateCandidate` and `suggest` stay inside. Answers drop `Evidence.fromCache` and `SuggestResult.cache`.
- **Publication.** The branch journals a publication as a fill at the root; here it is a `DocAction.publish` entry in the history.
- **`Tools.Query`'s semantics.** `slotsAt` becomes part of the `doc (some p)` answer. `fillPremises` and `omitPremises` are superseded by `dry (edit (commit …))`. That leaves `fill` with one meaning: one of the three is gone.

**What moves in, what stays, what goes**
- **Moves in** from `tools/Tools/Session.lean`: `answer`, `commitAnswer`, `feedAnswer`, `State`, `State.withDoc` and `selFrom?`. The old `run` operation becomes `start` followed by `play` with a list of events.
- **Stays in tools:**
  - the generated `Tool` codec group, with its families listed in `tools/Effect4Gen/wire-tags.json`;
  - `Run.Event`, `Run.Sel` and `Run.Verdict` need derived codecs (slice DM3);
  - law names come from a table `lawsOf : Request → Reply → List Name`, which a Test battery resolves;
  - `answerLine`.
- **Dropped:**
  - `fork`, which becomes `open` of the sketch that `doc none` returns, losing the history link;
  - `catalogue`, which is static and moves into `discover`;
  - `sketch`, `view` and `journal`, which merge into `doc`, `history` and `run … journal`;
  - the paired hex and JSON fields.

## 4. Adapters

| Adapter | What varies | Category |
|---|---|---|
| Lean JSON-lines driver: `Tools.Session`, shrunk to decode, `serve`, print and `lawsOf` | framing, codec, law names | in-process |
| Test harness: transcripts folded by `serve`, checked with `#guard` | nothing; it asserts replies | in-process |
| Native OCaml shell, `effect4_tool`, over the lowered `serve` | one owner of `State.t` (O-1); JSON-RPC, MCP and HTTP; may replace the cache with Incremental under law 5 | in-process (the same code, lowered) |
| Stateless face, for example an MCP `check` | a two-request transcript from `State.empty` | in-process |
| Store, later | accepted actions as entry nodes; restore by replay (law 7) | local-substitutable |

The JSON driver and the test harness exist today, so the seam is real now.

## 5. Laws

1. `serve_refuses`: `(serve s r).2 = .error e → (serve s r).1 = s`. This reuses `SessionCompositionSketches.refusal_inert` from `review-probes/CoreSketches.lean`, moved to `src/Effect4/Laws/Tool/`.
2. `serve_answers`: `RespondsTo r (serve s r).2`. `RespondsTo` pairs `act` with `acted` and `ask` with `told` by constructor. It also requires `items.length = batch.length`, `phases.length = events.length` and the requested `RunId` echoed back, and it never pairs `dry` with a refusal.
3. `serve_ask`: `∃ c, (serve s (.ask q)).1.raw = {s.raw with cache := c}`.
4. `serve_dry`: `(serve s (.ask (.dry a))).2 = .ok (.told (.dry ((Raw.act s.raw a).map (·.2))))`. It holds by definition.
5. `serve_cold`: given a valid cache, `(Raw.serve r q).2 = (Raw.serve {r with cache := []} q).2`. It reuses `CheckCache.lookup_sound` and `evaluateCandidate_valid_and_sound`, and it is the Incremental pass's acceptance law, fixed now.
6. `State.valid`, which is the plan's `StateInvariant`:
   - the pending set's anchor lies on a prefix of the document's history, and the set holds fills;
   - run identifiers are distinct and below `nextRun`;
   - each snapshot origin derives its run's `built` program and its `app.withHoles`;
   - the document's generation is below `nextGen`;
   - every cache entry satisfies `Entry.Valid`.

   It is derived from `reached` by induction with `FillSet.add_wf`, `CheckCache.insert_valid` and `Sketch.sourceCheck_of_admitted`.
7. `replay_compact`: a transcript reaches the same state as its accepted actions alone, cache aside. It follows from laws 1 and 3 and `List.foldl_append`.
8. `edit_appends`: an accepted `edit` or `publish` appends exactly one `DocAction` and raises the revision by one. It uses `Doc.commit_sound`, S1's replay law and `materialize_congr`.
9. `play_records`: after an accepted `play`, the slot's run is `l.feedAll events`, and the phases are the ones answered. It uses `Run.feed_fst`, `Live.opened_feed`, `Api.Runner.step_refused` and `Live.journal_replays`.
10. `save_load`: reading `run id .record` and then playing `start (.record r)` gives the same `Run`, with origin `standalone`. It uses `LiveRecord.restore_save`.

## 6. Trade-offs

**Where leverage is high**
- One function carries the refusal law, the pairing and the witness.
- One constructor, `dry`, previews all seven actions and decides the edit premises.
- Nesting the owners' types adds no new run or edit language. The wire alphabet, the history alphabet and the replay alphabet are the same `DocEdit`.
- **Departure from plan §6.** The plan puts `valid : StateInvariant raw` in `State` as a proof field. I propose the `reached` witness instead, because the invariant's proofs need `FillSet.add_wf` and `CheckCache.insert_valid`, which live in `Effect4.Laws`, and core may not import them.
- The witness also makes the transcript the persistence format and the native comparison format.

**Where leverage is thin**
- Most `ask` arms (`doc`, `history`, `fills`, `run`) are projections.
- `Answer` is still wide, with about 9 cases.

**What this makes hard later, and other costs**
- **One document per state.** Several documents would need a selector on `edit`, `fill` and `publish`, which is a wire change. `EditTarget` already names its document, so commits could route by it.
- **Atomic `play`.** On an unresolved selector the earlier events are dropped; nothing ran, but the client must resend them.
- **Cache hits leave the answer.** A hit counter becomes a driver metric instead.
- **Cache discipline.** `serve_cold` needs the cache to be touched only by `ask suggest`.
- **Cost of `dry`.** A dry run costs as much as the action; a dry publish materializes.
- **Answer types that depend on the request.** If F3 lands, `RespondsTo` becomes a type change.
- **Patch streams** have no place in a Mealy reply. A later subscription adapter would have to derive them from replies.

### Critical Files for Implementation
- /Users/pooks/Dev/lean4-effect4-gemini/tools/Tools/Session.lean
- /Users/pooks/Dev/lean4-effect4-gemini/src/Effect4/Program/Typing/SourceDocument.lean
- /Users/pooks/Dev/lean4-effect4-gemini/src/Effect4/Program/Typing/FillSet.lean
- /Users/pooks/Dev/lean4-effect4-gemini/src/Effect4/Program/Typing/CheckCache.lean
- /Users/pooks/Dev/lean4-effect4/src/Effect4/Run/Live.lean
- /Users/pooks/Dev/lean4-effect4/src/Effect4/Api/Built.lean
- /Users/pooks/Dev/lean4-effect4/docs/research/2026-10-17-session-composition/review-probes/CoreSketches.lean
