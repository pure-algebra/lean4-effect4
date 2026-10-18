# Design B1: the store seam, minimal

Status: design (history, not authority), one of nine in the seams round; see `../brief-common.md`.

# Seam design: the content-addressed store as its consumers use it

The constraint was a minimal interface. This design gives the store two entry points over one checked value, `Cas`: a write, `commit`, and a read, `read`. Loading, transfer and restore are built from those two. Root versions, kinds, spec edges, the re-hash on conflict and the poisoned check all sit behind them. I read the brief and its inputs and checked every cited name. Note that HEAD is now `774ddc3d7`, with the authoring branch merged, so I cite those declarations on main.

## 1. Interface

There is one new file, `src/Effect4/Store/Domain/Cas.lean`. It sits over the existing model (`Store`, `putNode`, `putRoot`, `Word`), and that model stays as it is printed to Rocq.

```lean
namespace Effect4.Store
abbrev RootName := { s : String // RootName.valid s }   -- 1..512 bytes, lowercase printable ASCII (M8)

inductive Name where
  | root (name : RootName)
  | action (key : Digest)              -- a `query` node, bound to a `result` node
inductive Move where
  | advance (name : RootName) (plane : RootKind) (expected : Option Digest) (target : AnyRef)
  | record (key result : Digest)
structure Txn where
  nodes : List Node                    -- children first; the store computes each digest
  moves : List Move                    -- applied after every node, in order
structure Receipt where
  nodes : List (Digest × Outcome)      -- `Outcome` as today; never `.conflict`
  moves : List Outcome
structure Refusal where
  item : Nat                           -- the position in `nodes ++ moves`
  why  : Admission
inductive Read where
  | node (d : Digest) | name (n : Name) | closure (r : AnyRef)
inductive Answer where
  | node (n : Option Node) | bound (target : Option AnyRef) | word (w : Word)

structure Cas where
  private mk ::
  store   : Store                      -- nodes and roots
  actions : List (Digest × Digest)     -- key ↦ result, each key once
  reached : ∃ ts : List Txn, Cas.replay ts = .ok (store, actions)   -- the shape of `Live.opened`

def Cas.empty : Cas
def Cas.commit (s : Cas) (t : Txn) : Except Refusal (Receipt × Cas)   -- entry point 1
def Cas.read   (s : Cas) (q : Read) : Answer                         -- entry point 2
```

- **Typed helpers.** Two typed functions are built from the entry points and are not entry points themselves:
  - `Txn.put [Content α] (s : Cas) (t : Txn) (a : α) : Txn × Ref α` adds the schema nodes the value's spec needs (the genesis, then the shape's schema node), skipping any already in `s`, then `nodeOf a`.
  - `Cas.get [Content α] (s) (r : Ref α) : Option α` is today's `Store.get`.
- **The one refusal vocabulary.** It is `Admission`, extended:

```lean
inductive Admission where
  | oversize | badVersion | malformedRef           -- the request is wrong (model and every adapter)
  | handleInContent                                 -- M2, after malformedRef; content kinds only
  | dangling (missing : Digest)
  | wrongKind (ref : Digest) (expected actual : Kind)
  | conflict (address : Digest) (occupant : Node)   -- a collision, shown with its occupant
  | staleRoot (name : String) (resident expected : Option Digest)   -- payload was two versions
  | poisoned (key resident offered : Digest)        -- new
  | unknownTag (tag : UInt8)                        -- the boundary: the reader is older than the byte
  | hostLimit (why : String)                        -- M9
  | corrupt (address : Digest)                      -- a record that does not hash to its digest
```

- **Nodes are admitted in order.** Each node is checked against the store grown by the items before it. The order is `putNode`'s, with M2 inserted: `oversize`, `badVersion`, `malformedRef`, `handleInContent`, then the checked edges, spec first. A node already in the store is `duplicate`. A different node at the same digest is `conflict`.
- **Moves follow one rule.** Let `r` be the resident target, `e` the expected one and `t` the new one:
  - If `r = e`, the move binds `t` (`fresh`, or `duplicate` when `t = r`).
  - If `r = some t`, the move is `duplicate`, which makes a retry idempotent.
  - Otherwise a root refuses with `staleRoot` and an action key refuses with `poisoned`.
  - A `record` always has `e = none`, so a key that is bound never moves.
  - Every target must resolve at its kind (`checkEdge`): a key at `query`, a result at `result`.
- **Refusal.** The first refusal wins. It refuses the whole request (the plan's first outcome kind), and nothing of the request persists.
- **Success.** Every item reads back afterwards, with no premise.

The OCaml spelling follows estate rule 1, with the types generated from Lean:

```ocaml
module type CAS = sig
  type t
  val empty  : t
  val commit : t -> Txn.t -> (Receipt.t * t, Refusal.t) result
  val read   : t -> Read.t -> Answer.t
end
module Model : CAS                    (* lowered Effect4.Store.Cas *)
module Disk : sig include CAS val open_ : dir:string -> (t, Refusal.t) result end
```

The generated `Admission` replaces `E4_cas.admission`, `E4_cas.verify_error` and `E4_control.root_error`.

## 2. Worked calculation

**Byte conventions:**
- A node is `00 ‖ kind ‖ spec(32) ‖ payload`.
- A `ref k d` is `0b ‖ be64 33 ‖ k ‖ d`.
- Constructor `i` is `0a ‖ be64 L ‖ 02 ‖ be64 |i| ‖ digits i ‖ args`.

**Digest symbols:**
- `g` is the genesis.
- `σP σE σQ σV` are schema nodes, each with spec `g`.
- `pᵢ` are programs (kind 05) and `eᵢ` are entries (kind 07).

The consumer carriers below are proposals:

```lean
inductive Entry where                                                          -- ⟨.entry⟩
  | origin (id : DocId) (app : SigApp) (holes : RowTable) (program : Ref NativeEff)
  | action (parent : Ref Entry) (act : DocAction) (after : Ref NativeEff)
structure CheckInput where program : Ref NativeEff; sig : SigData; env : TyEnv   -- ⟨.query⟩
structure Verdict where answer : Except TypeRefusal EffTy                        -- ⟨.result⟩
```

The bytes of one entry are `e1 = sha256 (00 07 ‹σE› 0a ‹L› 02 ‹be64 1› 01 · 0b ‹be64 33› 07 ‹e0› · ‹a1› · 0b ‹be64 33› 05 ‹p1›)`. Here `a1` is a checked fill at path `[1]` and `p1` is the program after it. The document's root name is `N = "doc/" ++ hex (sha256 (encode id))`. The trace starts from S0 = `Cas.empty`.

1. **Persist the document.** `commit S0 T1`. T1 puts p0, e0, p1, e1, p2 and e2, then `advance N journal none ⟨07,e2⟩`.
   - Nodes in order: `[g σP p0 σE e0 p1 e1 p2 e2]`.
   - Answer: nine `fresh`, and the move `fresh`.
   - S1: nine nodes, with `N ↦ e2` (internal version 1).
   - Laws: `putNode_fresh` for each item (for `g`, `Node.checkedEdges_of_genesis`); `putRoot_root?` for the move.
2. **Read the root.** `read S1 (.name (.root N))` answers `bound ⟨07,e2⟩`.
3. **Read the history back.** `read S1 (.closure ⟨07,e2⟩)` answers `word [g σE σP p0 e0 p1 e1 p2 e2]`, depth first with the spec edge first.
   - Laws: `closure_wf`, and `closure_closed` with Rocq's `built_closure_premises`, which `reached` supplies.
   - The journal keeps the kind-07 nodes `e0 e1 e2`, which come out in history order, and reads each with `Cas.get`.
   - It replays the origin and `[a1, a2]` through S1's validating step, which rebuilds `Doc.replayed`. Each `after` is checked against the replayed program's digest.
4. **Writer A publishes.** `commit S1 T3`. T3 puts p3 and e3 = `action e2 a3 p3`, then `advance N journal (some e2) ⟨07,e3⟩`.
   - Answer: `fresh`, `fresh`, `fresh`.
   - S2: eleven nodes, with `N ↦ e3` (version 2).
5. **Writer B publishes at the same root version.** B had also read `N ↦ e2`. `commit S2 T4`. T4 puts p3′ and e3′ = `action e2 a3′ p3′`, then `advance N journal (some e2) ⟨07,e3′⟩`.
   - Answer: the refusal `⟨2, staleRoot N (some e3) (some e2)⟩`.
   - S2 is unchanged, and p3′ and e3′ are absent.
   - In today's vocabulary this is `putRoot` at version 2 when `nextVersion` is 3.
6. **Look up a verdict.** Let `c = ⟨ref p3, sig, []⟩` and q its digest. `read S2 (.name (.action q))` answers `bound none`, a miss.
7. **Record the first verdict.** `commit S2 T5`: put c, put v1 = `⟨.ok T⟩`, `record q r1`.
   - Nodes in order: `[σQ q σV r1]`.
   - `q = sha256 (00 08 ‹σQ› 0a ‹L› 02 ‹be64 0› 0b ‹be64 33› 05 ‹p3› ‹SigData› 04 ‹be64 0›)`.
   - `r1 = sha256 (00 09 ‹σV› 0a ‹L› 02 ‹be64 0› 0a ‹L′› 02 ‹be64 1› 01 ‹T›)`.
   - Answer: four `fresh`, and the record `fresh`.
   - S3: fifteen nodes, with `q ↦ r1`. The key's edge to `p3` means the key cannot omit the program it describes.
8. **Record a different verdict for the same key.** `commit S3 T6`: put c, put v2 = `⟨.error ⟨[0], why⟩⟩`, `record q r2`.
   - Answer: the refusal `⟨2, poisoned q r1 r2⟩`.
   - S3 is unchanged, and `read S3 (.name (.action q))` still answers `bound ⟨09,r1⟩`.

**On disk after step 8:**
- The control file holds `be16 len ‖ N ‖ 01 ‖ 07 ‖ e3 ‖ be64 2`.
- An append-only action log holds `q ‖ r1 ‖ crc32`.

## 3. What the implementation hides

- **Edge checks and specs.** `Store.checkEdges` runs inside `commit`; `Txn.put` adds the spec nodes.
- **Kinds.** Each carrier's `Content.kind` chooses its kind. A new `Kind.runRelative` (tape, log, exits, checkpoint, as in `E4_kind.is_run_relative`) decides where M2 applies.
- **Root versions.** `putRoot` still stores `nextVersion`, but the check moves to the resident digest.
  - OCaml's M7 `prev` check becomes the rule for every root, so `Fork` merges into `staleRoot`.
  - A head digest names its whole history, so the digest check cannot be fooled by a root that returns to an earlier value.
- **Re-hash on conflict.** The disk re-hashes the occupant and answers `conflict` or `corrupt`. The model never answers `corrupt`, because its stores are `Store.Sound`.
- **Poisoned check.** It lives in the `record` move. On disk the action log is append-only, the first binding wins, and nothing goes into the control file.
- **Behind `commit`:** `Store.putNode`, `put`, `putOr`, `Word.apply`, `putRoot`, `putRootOr`, `nextVersion`.
- **Behind `read`:** `find`, `getNode`, `get`, `root?`, `Store.closure`.
- **Derived from `reached`:** `Store.Sound`, `Closed`, `Store.Ranked`.
- **Verification.** `Store.verify` stays as the disk's verifier, and `VerifyError` maps into `Admission`.
- **The OCaml modules:**
  - These calls move behind the two entry points: `E4_cas.put`, `put_bytes`, `commit`, `advance_root`, `pin`, `apply_word`, `closure`, and `E4_control.advance_root`.
  - The decode mapping is written three times today (`check_pure`, `put_bytes`, `readmit_tail`) and becomes one.
  - `E4_wal` buffers tape rows between commits.
  - `E4_checkpoint` becomes a replay cache whose restore must equal the replay of the tape.
- **Loading.** `Disk.open_` means `Cas.empty.commit (Txn.ofImage i)`: the pack's records in write order, each root as `advance … none`, each action as `record`.
  - Recovery's re-admission is exactly this replay.
  - The committed prefix is trusted, and that trust is declared; `verify` re-hashes.
- **Transfer.** It is `dst.commit ⟨(src.read (.closure r)).nodes, []⟩`, and `Layered.preload` and `LocalFirst.sync` become it.
- **Durability.**
  - The disk checks the whole request against a read view before writing anything.
  - Then it writes and fsyncs the pack, appends and fsyncs the action log, and renames the control file into place.
  - A crash can leave a request's nodes and bindings durable without its root move, but never the reverse; a retry answers `duplicate`.

## 4. Adapters

| Adapter | What varies | Category |
| --- | --- | --- |
| `Model` | a pure value with list search | in-process |
| `Disk` | pack, index, control file, action log, write-ahead log, checkpoints | local-substitutable (a temporary directory) |
| remote tier, later | closures over a wire (`Layered`, `LocalFirst`, `Cascade.CascadingStore`) | owned remote |

SHA-256 is a `Prim`, so nothing is a true external dependency. The two adapters make the seam real. A differential runs one transcript of requests through both and compares answers and refusals, setting the boundary refusals apart.

**The consumers above the seam:**
- **The journal:** `Entry`, and `Doc.restore : Cas → RootName → Except _ Doc`, which reads the root, then the closure, then each entry with `get`, then replays.
- **Verdicts:** `CheckInput` and `Verdict`. A hit is a `read`; a miss computes `Entry.compute` and commits.
- **Runs:**
  - Three carriers:
    - `Job` (kind 16, content): the program, application, binding, budget, row names, and an origin of type `Option (Ref Entry)`.
    - `Tape` (kind 17, run-relative): the job, `prev : Option (Ref Tape)`, and the commands.
    - `Receipt` (kind 20): the job, the last tape, and the exit.
  - The root `runs/<j>` uses the `registry` plane. Lean's `RootKind` gains `registry` and `pin`, at OCaml's bytes 5 and 6.
  - Restore reads the closure into a `LiveRecord` and calls `LiveRecord.restore`.
  - The job's origin is the checked companion record that plan §5 asks for.
  - Kind 18 (`log`) stays reserved, because `Run.Event` already folds into commands.

## 5. Laws

- `commit_grows`: a successful commit keeps every node (`putNode_sub`; Rocq `put_grows`, `apply_grows`).
- `commit_reads`: after success, every node of the request reads at its digest (`putNode_find`; Rocq `put_get`).
- `bytes_never_change`: published bytes never change (Rocq `put_bytes_never_change`).
- `commit_binds`: each name reads the target of its last move (`putRoot_root?`).
- `advance_stale`: if `r ≠ e` and `r ≠ some t`, the move refuses with `staleRoot`.
- `record_once`: a bound key keeps its result through every later commit.
- `record_poisoned`: a second, different result for a key refuses with `poisoned`.
- `cas_sound`, `cas_ranked`: these hold for every `Cas`, declared from Rocq `built_sound`, `built_ranked` and `apply_built`.
- `cas_closure_closed`: closure is closed with no hash premise (`closure_closed`, `built_closure_premises`).
- `cas_resident_inj`: one node per digest (Rocq `address_inj_resident`), with collision resistance as the only assumption (C5).
- `model_no_boundary`: the model never refuses with `unknownTag`, `hostLimit` or `corrupt`.
- `transfer_closed`: a transferred closure arrives closed (`closure_wf`, `wf_closed`, `apply_idempotent`).
- `Doc.restore_save`: restoring a saved document gives it back (new, proved by replay).
- `LiveRecord.restore_save`: reused as it is.
- `verdict_hit`: a hit equals `Entry.compute` of the key, or a collision is exhibited (`address_eq_or_collision`, `CheckCache.lookup_sound`).

## 6. Trade-offs

**Where leverage is high:**
- Two entry points serve every consumer, and one rule serves every name.
- Success needs no premise.
- Load, transfer and restore are built from the two entry points.
- Incremental plugs in at the digest. The action cache is a derived cache whose answers equal the uncached ones, and a restore cache keyed by head digest would be the next.

**Where leverage is thin:**
- `read` is a three-case dispatcher.
- Requests are atomic, so one poisoned verdict refuses its whole batch. `suggest` should record one verdict per request.
- Keys are exact. `CheckCache.lookup`'s prefix-extension hit stays above the seam.

**What this makes hard later:**
- The digest check changes `putRoot` and means re-cutting golden G3.
- Replication can no longer use versions as an order; it would need the moves stored as nodes.
- A grow-only store cannot collect garbage without a new operation.
- Restore costs time in proportion to the history's length.
- Carriers that refer to their own type need an `Effect4Gen` rule for `Ref` at a fixed kind byte.
- `TypeRefusal`, `SigApp`, `Sketch`, `DocId` and `SigData` have no `Canonical` instance today.
- There is one writer per store (CS4), so the digest check guards logical races between sessions, not between processes.

### Critical Files for Implementation
- /Users/pooks/Dev/lean4-effect4/src/Effect4/Store/Domain/Store.lean
- /Users/pooks/Dev/lean4-effect4/src/Effect4/Store/Domain/Word.lean
- /Users/pooks/Dev/lean4-effect4/ocaml/engine/cas/e4_cas.mli
- /Users/pooks/Dev/lean4-effect4/ocaml/engine/cas/e4_control.mli
- /Users/pooks/Dev/lean4-effect4/rocq/StoreLaws.v
