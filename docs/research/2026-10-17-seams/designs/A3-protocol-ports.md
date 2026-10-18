# Design A3: the protocol seam, ports and adapters

Status: design (history, not authority), one of nine in the seams round; see `../brief-common.md`.

# The authoring protocol module, designed as ports and adapters

The core is one pure Lean module, `Effect4.Tool` in `src/Effect4/Tool/`. It has two functions: `serve`, and `Exchange.apply`, which applies an envelope whose base state is named by digest. Everything that varies sits behind three ports: the driver (wire and framing), the store (residency, persistence, heads) and the memo (the verdict cache). A state is stored as a Merkle image in the content-addressed store. Two states with equal names are equal states, unless SHA-256 collides. So the Lean driver and the native shell answer alike because both run one lowered function, and the load law (`load_nodes`, §5) guarantees they start from the same state. Names marked *S1/S2/S4* are proposals of the composition plan. Everything else cited exists at `774ddc3d7`, where the authoring files are now on main.

## 1. Interface

```lean
namespace Effect4.Tool
-- Stored forms: generated Canonical codecs, with Content at the kind shown
inductive Entry                                    -- kind entry (7)
  | origin (id : DocId) (app : SigApp) (sketch : Sketch)
  | action (parent : AnyRef) (act : DocAction)     -- parent.kind = .entry; DocAction is S1's
structure Job where                                -- kind job (16): LiveRecord without its journal, plus an origin
  app : SigApp; program : NativeEff; session binding : String
  budget : Api.Budget; rowNames : List (String × Nat); origin : Option (Ref Entry)
inductive Tape                                     -- kind tape (17)
  | opened (job : Ref Job) | played (parent : AnyRef) (commands : List Api.Runner.Command)
structure Image where                              -- kind session (24, appended)
  version : Nat                                    -- the compatibility check; the spec digest misses tags (R11)
  generation nextRun : Nat
  doc   : Option (Ref Entry)                       -- the snapshot's name: the head of the entry chain
  fills : Option (Ref Entry × List (List Nat × NativeEff))   -- anchor, then FillSet.entries
  runs  : List (Nat × Ref Tape)                    -- identifiers ascending
-- The certified state: a private constructor, so the whole package is sealed in OCaml
structure State where
  private mk ::
  generation nextRun : Nat
  doc : Option Doc;  fills : Option FillSet        -- S1 and S2 forms, with their proof fields
  runs : List (Nat × Live × Option (Ref Entry))
  names : Names                                    -- cached entry and tape addresses, each with an equation proof field
  valid : StateInvariant generation nextRun doc fills runs names
def State.image : State → Image
def State.name (s : State) : Ref Image := Store.address s.image

abbrev MemoView := CheckCache.CheckKey → Option (Except TypeRefusal EffTy)
def serve (s : State) (m : MemoView) (r : Request) :
    State × Except Refusal Answer × List CheckCache.Entry    -- the last part: entries learned

inductive Base                                     -- how an envelope names its state
  | state (at_ : Ref Image)                        -- an exact state: never stale, forks freely
  | head (name : String) (at_ : Ref Image)         -- as the head of a session, by compare-and-set
  | carried (root : Image) (closure : Store.Word)  -- the state travels whole
structure HostView where                           -- what a driver must supply
  resident : Option State                          -- the state it resolved for at_, if any
  head : Option (Ref Image × Nat)                  -- the head root's digest and version; absent reads (State.empty.name, 0)
inductive Exchange.Refusal
  | staleBase (name : String) (given current : Ref Image)
  | unknownState (at_ : Ref Image) | load (at_ : Ref Image) (why : LoadRefusal)
structure Reply where                              -- base, result, next: the client sees these
  base : Ref Image; result : Except Refusal Answer; next : Ref Image
  publish : Store.Word                             -- the host sees these: nodes created, schemas then children first
  move : Option Store.Root                         -- ⟨"tool/"++name, .daemon, .session, next, v+1⟩
def load (at_ : Ref Image) (closure : Store.Word) : Except LoadRefusal State
def Exchange.apply (v : HostView) (b : Base) (r : Request) (m : MemoView) :
    Reply × Option State × List CheckCache.Entry
```

**`Request`** is one flat type:
- document: `discover`, `open`, `inspect`, `view`, `commit (t : EditTarget) (c : Change) (p : Policy)`, `draft (e : Edit)`, `revert (entry : Nat)`, `fork`, `history`;
- fill set: `fillsAdd (batch)`, `fillsView`, `fillsPublish`, `fillsReset`;
- check: `catalogue`, `suggest`, `query` (the pure part of `Tools.Query`);
- run: `start`, `play (run : Nat) (e : Run.Event)`, `liveView`, `save`, `load (r : LiveRecord)`;
- preview: `settle`, `frames`, `explore`.

**`Answer`** is flat too. `commit` answers ⟨snapshot : Ref Entry, revision, delta, view⟩. `fillsAdd` answers one `AddOutcome` per item. `play` answers a `Run.Verdict`.

**`Refusal`** has these constructors: `exchange`, `edit (Doc.Refusal)`, `materialize (MaterializeRefusal)`, `noDocument`, `fillsStale`, `unknownRun`, `admission (AdmitRefusal)`, `preview (Run.Preview.Refusal)`, `record (LiveRecord.Refusal)`, `unsupported`.

**`LoadRefusal`** has `digest`, `decode (path, reason)`, `wrongKind`, `history (k, Doc.Refusal)`, `fills (k, AddRefusal)`, `admission (run, why)`, `origin (run)`, `invariant`, `version`.

**How a request names its state.** Only through `Base`. `Request` never carries a state, so `serve` stays total.

**Refusal order inside `Exchange.apply`.** The order is fixed, so every host refuses alike:
1. a carried base runs `load`;
2. a `head` base whose current head is not `at_` gets `staleBase`;
3. no resident state gets `unknownState`;
4. otherwise `serve` runs.

**Driver obligations.**
- Supply a decoded `Base` and `Request` (generated reader), a `HostView`, and a sound `MemoView`: every hit equals `Entry.compute`.
- Always keep `State.empty` resident.
- Keep only states that `apply` or `load` returned, keyed by their own `name`.
- Write `publish`, then `move`, then reply.

**The transaction, in each host.**
1. Resolve: the resident table, else `Store.closure` (Lean) or `E4_cas.closure` (OCaml), then `load`.
2. Read the head root.
3. Call `apply`.
4. On a refusal, write nothing.
5. On success, put the nodes: `Word.apply` or `E4_cas.apply_word`. Commit them durably, then move the head: `Store.putRoot` or `E4_cas.advance_root`.
6. A lost race (`staleRoot`, `Stale_root`) calls `apply` again with the fresh head, which refuses `staleBase`. Nodes written before the lost race are orphaned but harmless, since content never changes.

**The revision counter is the head root's `version`.** In-flight work on a `head` envelope is cancelled when the version moves; it would have been refused `staleBase` at step 5 anyway. `state` envelopes are never cancelled, because their answer is a function of the digest.

**The OCaml spelling:**

```ocaml
module Effect4.Tool : sig
  module State : sig type t  val empty : t  val name : t -> Digest.t end   (* sealed *)
  type base = State of Digest.t | Head of { name : string; at_ : Digest.t } | Carried of Image.t * Word.t
  type view = { resident : State.t option; head : (Digest.t * Z.t) option }
  type reply = { base : Digest.t; result : (Answer.t, Refusal.t) result; next : Digest.t;
                 publish : Word.t; move : Root.t option }
  val load  : Digest.t -> Word.t -> (State.t, Load_refusal.t) result
  val apply : view -> base -> Request.t -> memo:(Check_key.t -> Verdict.t option)
              -> reply * State.t option * Check_entry.t list
end
```

## 2. Worked calculation

The values:
- `app = {}`; `p0 = .bind (.succeed (.lit (.nat 1))) (.succeed (.var 0))`; `s0 = ⟨p0, []⟩`; `id = ⟨"main", 0⟩`.
- The target `t = ⟨id, 0, [0], .succeed (.lit (.nat 1))⟩`.
- The request `R = .commit t (.fill (.succeed (.lit (.nat 2)))) .keepExactType`.
- The names: `g = State.empty.name`; `e0 = address (.origin id {} s0)`; `d1 = address ⟨1,1,0,some e0,none,[]⟩`; `e1 = address (.action ⟨.entry,e0⟩ (commit t …))`; `d2 = address ⟨1,1,0,some e1,none,[]⟩`.

| # | Driver, envelope | View | Core | Reply, and the state after | Law |
|---|---|---|---|---|---|
| 1 | Lean: `⟨head "alice" g, open "main" {} s0⟩` | head absent, read as (g, 0) | head check passes; `Doc.open`, generation 0→1 | ⟨g, ok opened(e0, rev 0, `Eff nat never`), d1, [schemas, e0, I1], ⟨tool/alice, d1, 1⟩⟩; the puts are fresh; `putRoot` v1 succeeds | `publish_closed`, `putRoot_root?` |
| 2 | Lean: `⟨state d1, R⟩` | resident S1 | `Doc.commit`: not foreign; revision 0 = 0; position `[0]` holds `succeed 1`; candidate type `Eff nat never` unchanged; `Table.typedAt [0]` unchanged → revision 1; `EditSession.feed` splices `[[0]]` | ρ = ⟨d1, ok committed(e1, 1, spliced [[0]], view), d2, [e1, I2], none⟩; head stays d1 | `Doc.commit_sound` |
| 3 | Native, fresh process, same store: `⟨state d1, R⟩` | no residents | `E4_cas.closure d1` = [schemas, e0, I1], each node re-hashed (`verify_node`); `load`: decode I1; e0 is an origin → `Doc.open {} s0 id`; replay [] succeeds; no fills, no runs; invariant 0 < 1 → S1′ = S1; then `serve` as in step 2 | ρ′ = ρ, equal canonical bytes; the puts are Duplicate, Duplicate | `load_nodes`, `apply_congr` |
| 4 | Native: `⟨head "alice" d1, R⟩` | head (d1, 1) | head check passes; same answer A | move ⟨tool/alice, d2, 2⟩; `advance_root` succeeds | `move_cas` |
| 5 | A client still at d1: `⟨head "alice" d1, commit t (fill (succeed 3)) …⟩` | head (d2, 2) | `staleBase "alice" d1 d2` | ⟨d1, error (exchange staleBase), d1, [], none⟩; nothing written, residents unchanged | `apply_refuses_inert` |
| 6 | Contrast: `⟨state d2, R⟩` | resident S2 | `Doc.commit` refuses `.stale 1` | ⟨d2, error (edit (stale 1)), d2, [], none⟩ | `serve_refuses` |

Step 6 shows two different stalenesses. Step 5 is the store's kind: the named state is behind the session head. Step 6 is the document's kind: the edit target's revision is behind the document.

The race, step 4′: two shells both pass step 4's check at v1. The loser's `advance_root` answers `Stale_root`. It calls `apply` again with (d2, 2) and returns step 5's refusal.

## 3. What the implementation hides

Behind the seam:
- dispatch, and the order in which the parts compose (document, then fill set, then runs);
- the refusal wrapper;
- building entries, tapes and images, and their addresses;
- the checked loader;
- allocation of generations and run identifiers;
- mapping domain refusals into `Refusal`;
- law names, carried as strings.

Declarations that move behind it:
- From `tools/Tools/Session.lean`: `State` with its nine fields, `State.doc`, `State.withDoc`, `State.fillsFor`, `fillsStale`, `commitAnswer`, `feedAnswer`, and the 26 arms of `answer`.
- The hand-built `Built` in the `start` and `run` arms goes to S4's declaration that turns a snapshot into a `Built`.
- The 41-field `Request` and `Request.fromJson?` give way to the generated print. `answerLine` becomes the Lines adapter.
- `CheckCache.suggest`'s threaded `cache` becomes the memo port. `Evidence.fromCache` leaves the answers and becomes telemetry, so an answer cannot reveal the cache.
- `LiveRecord.save` and `restore` serve `save`, `load`, and the run part of `Tool.load`.

Dependencies consumed directly, not through ports (one implementation each, so a port would be hypothetical): `Doc` (S1's `append` and `replayDoc`), `FillSet.add`, `materializeDoc`, `admitProgram`, `Live.open`, `Live.feed`, `Run.Preview.admit`.

## 4. Adapters

| Port | Adapter | Category |
|---|---|---|
| driver | Lean JSON lines (`tools/Tools/Drive/Lines.lean`), `{base, request}` | in-process |
| driver | OCaml JSON-RPC 2.0 shell (`ocaml/tool/`, `Io.Make` over Eio), one method `effect4/apply` | local-substitutable |
| driver | MCP: one tool per `Request` constructor, from the generated table; `base` a required argument; `Refusal` reported as `isError`; a carried base serves as `requestState` | true external client |
| driver | transcript harness (`Test/Tool/Transcript.lean`, with an OCaml twin) comparing canonical bytes of replies | in-process |
| store | the Lean `Store` value (proved) | in-process |
| store | `E4_cas` on disk | local-substitutable |
| store | null store (carried bases only; publish dropped) | in-process |
| memo | none (`fun _ => none`); the `CheckCache.Entry` list; Incremental (phase 4); the C6 action cache (query 8 to result 9) | in-process / local-substitutable |

**What the native side re-checks after proof erasure:**
1. Every fetched node is re-hashed and decoded exactly: `E4_cas.verify_node`, then the generated `of_val`.
2. The document: S1's `replayDoc` reruns each checked action at its prefix, policy and receipt.
3. The fill set: re-`add` the reversed `entries` at the anchor's replayed snapshot. Every outcome must be `.applied` and the entries must come back the same; this rebuilds the erased `constructed` witness.
4. Each run:
   - its origin replays;
   - its program and `app.withHoles holes` equal the job's;
   - full `admitProgram` passes; `Run.Kit.admit` is not enough (R13);
   - `Live.open`, then `feedAll` of the tape's commands as `.wire`, as `LiveRecord.restore` does.
5. `StateInvariant`: run identifiers are distinct and below `nextRun`; the document's generation is below `generation`; the fill anchor is on the head's chain.
6. Persistent memo entries are trusted only under C5 and C7, or recomputed in C6's determinism mode.

The native side never keys a resident by a digest the core did not compute, never makes a `State.t` from `Marshal`, and never reaches a `Built` without admission.

## 5. Laws

- `serve_refuses`: a refusal leaves the state unchanged. This is `SessionCompositionSketches.refusal_inert` from `review-probes/CoreSketches.lean`, moved into `Effect4.Laws`.
- `serve_answers`: `RespondsTo r (serve s m r).2.1`, a generated relation.
- `apply_refuses_inert`: on a refusal, `next = base`, `publish = []` and `move = none`.
- `load_nodes`: `load s.name s.nodes = .ok s`. It composes `LiveRecord.restore_save`, `Live.journal_replays`, S1's replay law and `FillSet.add_wf`.
- `name_determines`: equal names give equal states, or a collision. It uses `address_eq_or_collision` and the Rocq `address_inj_resident`.
- `apply_congr`: equal `HostView`s up to the resident's name give equal replies. It follows from `load_nodes` and `name_determines`.
- `publish_closed`: `Word.wfFrom base.nodes reply.publish`. It uses `closure_wf`, `wf_apply` and `putNode_sound`.
- `move_cas`: `move = some r → r.version = v + 1`, so `Store.putRoot` succeeds exactly when the head is unchanged. It uses `putRoot_root?` and `putRoot_nodes`.
- `memo_free`: with a sound memo, the answer and the next state do not depend on it. It uses `CheckCache.lookup_sound` and `evaluateCandidate_valid_and_sound`.
- `transcript_replays`: replaying a transcript's accepted envelopes from genesis reaches its last `next`. This is the free-monoid action, `List.foldl_append`.

## 6. Trade-offs

**Where leverage is high.**
- One digest names a whole working state. Stateless serving, forking, sharing between agents, and agreement between Lean and native all follow from one function plus `load_nodes`.
- Cancellation and staleness reduce to one refusal on one root.
- Incremental plugs into the memo port. Its acceptance test (cached answers equal uncached ones; a refused revision followed by a valid one recovers) is `memo_free` at each step.

**Where it is thin.**
- `unknownState` depends on the host (garbage collection, store availability). Identical answers are promised only for bases both hosts can resolve.
- The MCP and Lines adapters are shallow.

**Costs.**
- Kind 24 (`session`) must be appended to Lean's `Kind` and to `E4_kind`, and the C2 goldens re-cut.
- Every successful mutation writes at least two nodes. A read writes none.
- A cold `load` replays the whole history and every journal, at cost O(history). Carried bases are O(history) too.

**What this design makes hard later.**
- Forks are free, so R3 becomes ordinary: two states can share a `DocId` and revision with different histories. I recommend that the document seam's `EditTarget` carry the snapshot's `Ref Entry`. Until then, the `moved` check and the base guards carry the load.
- Garbage collection of states needs a reachability rule from the heads (`E4_cas.reachable`). It is not designed here.
- Content cannot be redacted, since content never changes.
- `Run.Event` still needs its generated codec (S3b).
