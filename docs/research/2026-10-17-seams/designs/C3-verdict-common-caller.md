# Design C3: the verdict seam, the common caller first

Status: design (history, not authority), one of nine in the seams round; see `../brief-common.md`.

# Checking and verdicts: one verdict function, two reuse indices, with "kept" as the default case

**Thesis.** The three common callers all ask one question. Does this filling have exactly the type that the document's table holds at this address? Call a yes answer **kept**.

- A kept filling costs one focus check. That one check decides the `keepExactType` commit, the fill set's certification and the splice.
- The view then reads the spliced table and checks nothing.

**One mechanism or two:** two indices over one verdict function.
- The splice reuses by position within one history. Its law is `table_splice`.
- The memo reuses by content across requests, documents and processes. Its law is transparency.
- The splice is a client of the memo: its one check is a memo query.

Correction to the brief: `gemini/authoring` is now merged into main at `774ddc3d7`. The branch files I cite (`CheckCache.lean`, `FillSet.lean`, `SourceDocument.lean`) are on main, with the repair, byte for byte.

## 1. Interface

New file `src/Effect4/Program/Typing/Verdict.lean` (core). `PartSig`, `SigData`, `bodyIndex`, `partSigAt` and `sketchSigData` move here unchanged from `CheckCache.lean`.

```lean
inductive CheckInput where          -- everything one check reads
  | focus  (sig : SigData) (env : TyEnv) (program : NativeEff)   -- a part, or a filling
  | source (app : SigApp) (sketch : Sketch)                      -- a sketch through its references
  deriving DecidableEq              -- generated Canonical; Content at kind `query` (8)

structure Verdict where             -- rooted at the empty path
  table  : List Table.Entry
  result : Except TypeRefusal EffTy
  deriving DecidableEq              -- generated Canonical; `NodeEnv`, `Table.Entry` join the group

def CheckInput.run : CheckInput → Verdict
  | .focus d env q => let o := Annotate.check d.signature env [] q; ⟨o.1, o.2⟩
  | .source app s  => ⟨s.sourceAnnotate app, s.sourceCheck app⟩
def Verdict.rebase (a : List Nat) : Verdict → Verdict  -- TypeRefusal.rebase, Table.Entry.rebase move from Laws to core

structure Memo where
  private mk ::
  entries : List (CheckInput × Verdict)
def Memo.empty : Memo
def Memo.ask (i : CheckInput) : StateM Memo Verdict        -- exact hit, else run and insert
def Memo.seed (m : Memo) (es : List (CheckInput × Verdict)) : Memo   -- shell preload (law 12)

structure FocusCheck where
  path  : List Nat
  focus : TyEnv × EffTy   -- Table.typedAt of the document's table: no walk, no check
  input : CheckInput      -- .focus (sketchSigData x app path) focus.1 q', q' as the expansion x holds it
def Doc.focusCheck (d : Doc) (path : List Nat) (q : NativeEff) : Option FocusCheck
  -- none at the root, or where the table types no root or no focus
def FocusCheck.kept (c : FocusCheck) (v : Verdict) : Bool := v.result == .ok c.focus.2
```

**How the oracle is threaded.**
- Each consumer is written once, over `ask : CheckInput → m Verdict` with `[Monad m]`.
- Its plain name is the `Id` instance at `pure ∘ CheckInput.run`, so every existing statement stands.
- The consumers: `EditSession.feedVia`, `SourceSession.feedVia`, `SourceSession.openVia` (one `.focus` per part, the root assembled from the parts), `Doc.commitVia`, `FillSet.addVia`, `CheckCache.suggestVia`.
- Two rules:
  - a consumer asks before it branches;
  - it hands an answered verdict down rather than asking again, so the `Id` default checks a filling once.
- Lowering: `StateM Memo` is a non-dependent function type (R9), and the generic functions are specialized. `Memo` is abstract in OCaml, built only by `empty`, `ask` and `seed`.

**`Doc.commitVia`, in order** (the policy defaults to `keepExactType`):
1. `foreign`, `stale`, `moved`, `noFocus` refuse as today, and the state is unchanged.
2. A fill with `d.focusCheck t.path q = some c` asks `v ← ask c.input`.
   - If the filling is kept, it is fed with `v.rebase t.path` as the splice's subtree, and the commit is accepted.
   - If not, the commit refuses with the new located `Doc.Refusal.notKept (focus : TyEnv × EffTy) (verdict : Except TypeRefusal EffTy)`. No candidate is built.
3. Every other case takes today's full path: a root target, an untyped root or focus, an omission that does not splice, or an expansion that reopens. The candidate is opened by parts through `ask`, and the refusals are `refused`, `typeChanged`, `localChanged`.

Under `recheckSource`, step 2's acceptance is the same, and a not-kept filling goes to step 3. The commit returns its `Edit.Step`. `Edit.Delta` is unchanged; `.spliced` now also certifies kept (law 7).

**Store** (`src/Effect4/Store/Domain/Action.lean`):

```lean
structure Answered where            -- Content at kind `result` (9)
  engine  : Digest                  -- the checker's identity: the lowered closure's digest (C7)
  query   : Ref CheckInput          -- an edge to kind `query` (8)
  verdict : Verdict
inductive ActionLookup | hit (v : Verdict) | miss | poisoned (residents : List Digest)
inductive ActionOutcome | fresh | duplicate | poisoned (resident : Digest)
def Store.lookupAction (s : Store) (engine : Digest) (q : Ref CheckInput) : ActionLookup
def Store.recordAction (s : Store) (engine : Digest) (i : CheckInput) (v : Verdict) :
    Except Admission (ActionOutcome × Store)
```

- `recordAction` puts the key node, then the answer node.
- If an answer with another verdict is already resident for the same engine and key, `recordAction` answers `poisoned` and leaves the store unchanged. Nothing is overwritten.
- `lookupAction` is the specification, a scan. The OCaml side keeps an index rebuilt from the resident `result` nodes. Like `by_cid`'s, that index is a cache, never a second authority.

```ocaml
module E4_action : sig
  type t
  type lookup = Hit of E4_addr.Addr.t | Miss | Poisoned of E4_addr.Addr.t list
  type outcome = Fresh | Duplicate | Poisoned of E4_addr.Addr.t
  val open_  : E4_cas.ro -> engine:string -> t
  val find   : t -> query:E4_addr.Addr.t -> lookup
  val record : E4_cas.t -> t -> query:E4_node.t -> result:E4_node.t -> (outcome, E4_cas.admission) result
end
```

## 2. Worked calculation

**Setup.**
- Application `{}`. Hole rows `h = Row.hole "h" .nat` and `g = Row.hole "g" .nat`. `N = EffTy.pure .nat`, which is each hole's type.
- `s0 = { program := .bind (.succeed (.lit (.nat 1))) (.perform (.external 0) (.lit .unit)), holes := [h] }`.
- `d0 = Doc.open {} s0` at revision 0. The memo is empty. `σ0 = ⟨{}, [h], .root⟩`.
- Table T0:
  - `[]`: environment `[]`, ok N;
  - `[0]`: environment `[]`, ok N;
  - `[1]`: environment `[nat]`, ok N.

**R1, commit:** target `⟨id, 0, [1], hole 0⟩`, fill `.succeed (.var 0)`.
- The focus is `([nat], N)` and the input is `i1 = .focus σ0 [nat] (.succeed (.var 0))`.
- Memo miss. `run` checks 1 node and answers `⟨[⟨[], env [nat], ok N⟩], ok N⟩`. Kept.
- T1 is T0 with the segment at `[1]` replaced by that verdict, rebased. The answer is `d1` at revision 1, with delta `.spliced [[1]]`. The memo now holds `i1`.
- Reused: `[]`, `[0]` and the root type, by `table_splice`, `Sketch.table_fill` and `Sketch.check_fill_focusAt`.
- The view reads T1 and checks nothing (`SourceSession.reached_view`).

**R2, commit, refused:** target `⟨id, 1, [0], .succeed (.lit (.nat 1))⟩`, fill `.succeed (.lit (.str "a"))`.
- Input `.focus σ0 [] …`. Memo miss; 1 node checked, answering ok `pure .string`. Not kept.
- The answer is `.notKept ([], N) (.ok (pure .string))`.
- `serve`'s wrapper returns the old state, so `d1` and its memo are unchanged. The request's memo growth is discarded with it.
- Today's commit builds the whole candidate instead. Its continuation now reads `[string]`, which is R6's dependent `bind` child, and it answers `typeChanged`.

**R3, commit:** target `⟨id, 1, [0], …⟩`, change `.omitHole "g"`.
- No ask. The row declares N exactly, closed, normal and formed, so the omission arm splices with no check.
- `[0]` now holds `.perform (.external 1) (.lit .unit)`, with entry ok N. The holes are `[h, g]`. The answer is `d2` at revision 2.
- Reused: every entry, by `Sketch.table_omit` and `Sketch.table_more_holes`.
- From here the signature data is `σ1 = ⟨{}, [h, g], .root⟩`. The `σ0` keys stay valid, but this document never asks them again.

**R4, suggest** at `[0]` on `d2`, with `.succeed (.lit (.nat 2))` supplied.
- Input `i4 = .focus σ1 [] (.succeed (.lit (.nat 2)))`. Memo miss; 1 node checked; ok N, so the evidence is `exactFit`.

**R5, commit:** target `⟨id, 2, [0], hole 1⟩`, fill `.succeed (.lit (.nat 2))`.
- The commit's input is `i4`, a memo hit: 0 nodes checked. Kept.
- T3 is T2 with `[0]` taken from the verdict of `i4`, rebased. The answer is `d3` at revision 3.
- Reused by position: `[]` and `[1]`. The environment `[nat]` at `[1]` stands because the exact answer type at `[0]` stands, which is the R6 point.
- Reused from the memo: the entry at `[0]`, by `Memo.ask_valid`, then `tableAt_rebase` and `Checker.check_rebase`.

| Request | asks | nodes checked | today |
| --- | --- | --- | --- |
| R1 | 1 miss | 1 | 2 (the tool feeds twice) |
| R2 | 1 miss | 1 | 1, plus the whole candidate (3) with `Sketch.annotate`'s separate `s.check app` |
| R3 | 0 | 0 | 0 |
| R4 | 1 miss | 1 | 1 |
| R5 | 1 hit | 0 | 2 (no memo on the commit path; fed twice) |

## 3. What the implementation hides

**Hidden:**
- the memo's index, by the input's address with exact comparison inside a bucket;
- eviction, since any sub-list of a valid memo is valid;
- the part decomposition of `.source`: the definition count, formation, `admits` and the layers are computed, and the parts are asked;
- the persistence watermark.

**Moved behind the seam:**
- `CheckCache.CheckKey`, `Entry`, `Entry.compute`, `lookup` and `insert` become `CheckInput`, `Verdict` and `Memo.ask`, with exact keys only. The `extendsB` arm leaves the shared memo.
- The inline `Annotate.check (l.sketch.sigAt l.app a) tys a q` in `EditSession.feed` becomes an `ask`.
- `Sketch.annotate`'s root argument becomes the root assembled from the parts.
- `certifiedB`'s `Sketch.focusAt` walk becomes `Doc.focusCheck` on a base with no layer reference. A base with references keeps `certifiedB`.
- `Api.check` runs two module checks today (`explain`, then `typeOfProgram`); it becomes one `.source` run. `Run.Kit.check` stays a map over it.
- `Tools.Query`'s `check` moves from `Sketch.check` to `.source`.
- The tool's second `feedStep` is removed, and the tool state's `cache` field becomes `memo`.

## 4. Adapters

What varies across the seam is the source of a verdict and how long it lives. The key and `run` never vary.

| `ask` | Lifetime | Category |
| --- | --- | --- |
| `pure ∘ run` in `Id`: the laws, `Api.check`, `Run.Kit.check`, `Tools.Query` | none | in-process |
| `Memo.ask` in `StateM Memo`, with the memo in the tool state | session | in-process |
| the shell seeds from `E4_action` before a request and records fresh entries after a successful one | disk | local-substitutable (the Lean `Store` model, or a temporary store) |
| Incremental, later: one node per part input (rule 1), value `run` (total, rule 8), cutoff by verdict digest (rule 5); it seeds the memo, and Lean keeps the table and its proof | session | in-process |

The first two exist at landing, so the seam is real.

## 5. Laws

1. `CheckInput.run_focus_rebase`: `(.focus d env q).run.rebase a` equals `Annotate.check d.signature env a q`. From `Annotate.check_eq`, `tableAt_rebase` and `Checker.check_rebase`.
2. At `d.focusCheck a q = some c`, the input's signature is `sigAt` at that address (`sketchSigData_signature`).
3. `Memo.ask_valid`. Define `Memo.Valid m` as: every entry `(i, v)` has `v = i.run`. Then `ask` on a valid memo answers `run` and keeps the memo valid. This replaces the exact arm of `CheckCache.lookup_sound`, and `insert_valid`.
4. Seeding valid entries, or evicting any, keeps `Valid`.
5. Transparency.
   - On a valid memo, each `…Via Memo.ask` equals its plain name and returns a valid memo.
   - At the tool level, `serve_memo_transparent`: two states that differ only in valid memos answer alike. The memo is outside the replay identity.
6. `Sketch.annotate_by_parts`: the parts' runs, rebased and assembled, equal `Sketch.annotate`. New; it needs a new `checkModule_by_parts`.
7. `Doc.commit_kept` (new): under `keepExactType`, at a non-root target of a typed document.
   - An accepted commit has a kept focus.
   - A kept focus with no reference site at or above the target is accepted, with `.spliced`.
   - From `Sketch.check_fill_focusAt`, `Sketch.table_fill` and `SourceSession.feed_coherent`.
8. `Doc.commit_sound` keeps its statement.
9. On a base with no layer reference, `exactFit`, kept and `certifiedB` coincide. From `CheckCache.evaluateCandidate_valid_and_sound`, `Table.typedAt_table` and `expandRefs_eq_self_of_refSites_nil`. So when `suggest` answers `exactFit`, the commit accepts.
10. `Api.check` agrees with `.source` (`Sketch.sourceCheck_toOption`, `Api.explain_none_iff`).
11. Store records.
    - After a fresh `recordAction`, the lookup hits (`get_put`).
    - Recording a different verdict answers `poisoned`, with the store unchanged.
    - A hit survives later records (`get_preserves`).
12. Store transparency.
    - `Store.VerdictsValid E s` and a hit `v` for `address i` give `v = i.run`, and `recordAction E i i.run` keeps `VerdictsValid`.
    - Keys are complete by construction, since `run` reads only its argument.
    - Equal addresses mean equal inputs or an exhibited collision (`address_eq_or_collision`).
    - Two assumptions are declared, not proved: C5's collision resistance, and that digest `E` names `run` (C7).
    - A determinism mode recomputes on each hit and reports `poisoned`.

## 6. Trade-offs

**Where leverage is high:**
- A default commit costs one focus check, whether it accepts or refuses.
- `suggest` then commit, and `add` then publish, hit the memo.
- `open` and `.rechecked` re-check only the definitions whose inputs moved.
- `Api.check` traverses the program once.
- Refusals are local and located.

**Where it is thin:**
- Keys are exact. An omission grows the hole table and orphans the document's keys, though the omission itself costs nothing.
- Key nodes inline the whole `SigApp`. A later Merkle split keeps the key complete.
- A root part's verdict table is O(program).
- `notKept` replaces `typeChanged` and `refused` in the common refusal, and that change shows on the wire.

**What this makes hard later:**
- Every new consumer must ask before it branches, or its transparency proof needs relational reasoning.
- The plain and `Via` names double the surface.
- Persisted verdicts rest on engine identity.
- Incremental can pre-warm verdicts but cannot replace the session's table.
- Getting back the hole-extension hits needs `tableAt` under `SigExtends`, which is not proved.

### Critical Files for Implementation
- /Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Typing/CheckCache.lean
- /Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Edit.lean
- /Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Typing/SourceDocument.lean
- /Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Typing/PartsTable.lean
- /Users/pooks/Dev/lean4-effect4/src/Effect4/Store/Domain/Store.lean
