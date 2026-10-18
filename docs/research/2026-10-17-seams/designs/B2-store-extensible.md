# Design B2: the store seam, extensible

Status: design (history, not authority), one of nine in the seams round; see `../brief-common.md`.

## The content-addressed store as its consumers use it: the flexibility design

Paths are relative to `/Users/pooks/Dev/lean4-effect4`. Files marked (B) are on the branch at `/Users/pooks/Dev/lean4-effect4-gemini`. Every new declaration below is a proposal.

The rule of the design: a new consumer never adds a store mechanism. It adds carriers (`Content`), and optionally an `ActionId` or a root under an existing policy. The kind byte types the edges. The spec (edge 0, `specOf α`) is the carrier's type tag, as `Traits.lean` already uses it for trait keys. None of the consumers named here appends a byte. Kinds 7, 8, 9, 10, 11, 12 and 16 to 21 each gain their first Lean consumer.

### 1. Interface

Additions to `src/Effect4/Store/Domain/Store.lean`:

```lean
def Store.read [Content α] (s : Store) (r : Ref α) : Option α
  -- version 0, kind = Content.kind α, spec = specFor a, payload reads; else none
def Store.register (α) [Content α] (s : Store) : Except Admission Store
  -- puts schemaNode (shape α).document; an α put before it refuses dangling (specOf α)
inductive RootKind | stdlib | journal | daemon | schema | char | registry | pin  -- 5, 6 = E4_control's
inductive MovePolicy | swap | extend | once
def RootKind.policy : RootKind → MovePolicy   -- journal, registry ↦ extend; pin ↦ once; else swap
-- Admission gains handleInContent (M2, decided), fork (name) (head : Digest), pinned (name)
def Store.putRoot (s : Store) (r : Root) : Except Admission Store
  -- staleRoot, dangling, wrongKind as today; then extend: a resident head h needs
  -- ⟨r.kind, h⟩ ∈ target.refsOf, else fork; once: a resident root refuses pinned
def Store.resolve (s : Store) (root : String) (path : List String) : Option AnyRef
  -- the root's target, then one Tree binding (kind 11) per segment, each through read
```

`Store.get` checks the kind only. A `Ref (Query κ)` frames as `ref 8` (`instCanonicalRef`), so admission never sees which carrier sits behind an edge. `read` closes that gap.

The action cache lives in a new module, `src/Effect4/Store/Domain/Action.lean`. It is generic over the carrier, as `Annotation τ` is, with its instances written by hand:

```lean
structure ActionId where name : String; version : Nat
structure Query (κ : Type) where action : ActionId; input : κ
structure Result (κ ρ : Type) where query : Ref (Query κ); output : ρ
instance [Canonical κ] : Content (Query κ) := ⟨.query⟩
instance [Canonical κ] [Canonical ρ] : Content (Result κ ρ) := ⟨.result⟩
inductive Lookup (ρ : Type) | miss | hit (output : ρ) (at_ : Digest) | poisoned (at_ : List Digest)
inductive Recorded | fresh | duplicate
inductive ActionRefusal | admission (why : Admission) | poisoned (occupant : Digest)
def Store.resultsFor (s : Store) (q : Digest) : List Digest  -- residents at `result` whose first ref is ⟨query, q⟩
def lookup (s : Store) (q : Query κ) : Lookup ρ
def record (s : Store) (q : Query κ) (out : ρ) (outputs : Word) :
    Except ActionRefusal (Recorded × Ref (Result κ ρ) × Store)
  -- order: poisoned check, then Word.apply (outputs ++ [q, ⟨q, out⟩]); nothing is put first
def memoize (id : ActionId) (f : κ → ρ) (k : κ) (s : Store) : ρ × Store  -- total; records on a miss
def Faithful (id : ActionId) (f : κ → ρ) (s : Store) : Prop  -- each resident result under id is f of its input
```

The action plane is derived: a result node names its query. So there is no new mutable plane and no new disk file. Durability, `verify`, `closure` and sync all apply unchanged.

Blobs come in through the generator manifest's `Kinds` list (`tools/Effect4Gen/manifest.json`):
- `Chunk` holds bytes and files at `chunk`.
- `Blob := whole (b : Bytes) | chunked (parts : List (Ref Chunk))` files at `manifest`.
- `Blob.ofBytes : Bytes → Blob × Word` cuts at `E4_chunk.threshold` (1 MiB).

Two tiers become one value in `Word.lean`, replacing `Layered`, `LocalFirst` and `Cascade.CascadingStore`:

```lean
structure Tiered where near : Store; far : Store; outbox : Word
def Tiered.find   (t) (r : AnyRef) : Option Node × Tiered   -- near; on a miss apply far.closure r
def Tiered.lookup (t) (q : Query κ) : Lookup ρ × Tiered     -- near; on a miss fill far's results for q
def Tiered.put    (t) (n : Node) : Except Admission (Outcome × Digest × Tiered)  -- LocalFirst.putNode
def Tiered.push   (t) : Except Admission Tiered              -- LocalFirst.sync; outbox := []
```

Two rules govern a fill. A fill that would make the near store answer `poisoned` is dropped and reported. A filled node is not a local write, so it never joins the outbox.

The OCaml spelling:

```ocaml
module type FAR = sig
  type t
  val closure     : t -> E4_addr.Ref.t -> E4_cas.binding list
  val results_for : t -> E4_addr.Addr.t -> E4_cas.binding list
  val apply_word  : t -> E4_cas.binding list -> (unit, E4_cas.word_error) result
end
module Tiered (Far : FAR) : sig
  type t
  val create      : near:E4_cas.t -> Far.t -> t
  val get_node    : t -> E4_addr.Ref.t -> E4_node.t option
  val results_for : t -> E4_addr.Addr.t -> E4_addr.Addr.t list
  val put         : t -> E4_node.t -> (E4_cas.outcome * E4_addr.Addr.t, E4_cas.admission) result
  val push        : t -> (unit, E4_cas.word_error) result
end
```

- `results_for` on the disk store is `E4_index.Deps.find`, filtered to kind `result`.
- `E4_control.advance_root ?prev` becomes the policy. `prev` is read from the node's refs, never trusted from the caller.

Each consumer is a set of carriers and a root:

| Value | Carriers (kind) | Root | Existing owner |
| --- | --- | --- | --- |
| document history | `Entry := origin DocOrigin \| step (parent : Ref Entry) DocAction` (7) | `doc/<name>/<gen>`, journal | `Doc` (S1); a snapshot is its last entry's address (decided) |
| program | `Eff NativeOp` (5), `instContentEff` | none | `Derived/Program.lean` |
| verdict | `Query CheckKey`, `Result CheckKey (Except TypeRefusal EffTy)` | none | `CheckCache.CheckKey`, `Entry.compute` (B) |
| gate pass | `Query GateInput`, `Result GateInput Unit` | none | `gate_cache.snapshot`, reached through a command-line adapter |
| lowered artifact | `Query LowerInput`, `Result LowerInput Lowered`, `Blob` | none | `OCaml5.Lcnf.Gen` |
| live run | `Job` (16) naming program, app, binding, budget, rowNames, engine and `origin : Option (Ref Entry)`; `RunPart α := {job : Ref Job, body : α}` for tape (17), log (18) and checkpoint (21); `Receipt` (20) | `runs/<job>/tape` journal, `/checkpoint` registry, `/pin/…` pin | `LiveRecord` (B), `E4_wal`, `E4_checkpoint` |

`Entry` and the tape segment refer to themselves. Those frames are written by hand, as `Annotation.prevToVal` is.

**Extension points, and what each owes:**
- **A carrier** owes the `Canonical` laws (generated) and a consumer that cites it.
- **An action** owes determinism and key completeness: κ holds everything the run reads.
- **A root kind** is an append plus a policy.
- **A kind** is byte 24 or later. It owes:
  - the table theorems decided again;
  - a `#guard` on every old byte;
  - `E4_kind` and the goldens cut again from Lean;
  - a fresh `make gen-rocq`.

  A new kind is warranted only when admission must tell edges apart, or for a new class of kind, as M2 split content kinds from run-relative ones.
- **A tier** owes laws 14 and 17.

### 2. Worked calculation: a new consumer, the lowered-artifact cache

The values:
- `aid := ⟨"lcnf.lower", 1⟩`.
- `i : LowerInput` has these fields:
  - `command := commandOf argv`, from the recipe entry for `ocaml/engine/test/rocq/rocq_gen.ml` (cap 200, roots `Effect4.Run.Tree.InRocq` and `.Plain`);
  - `decls`: each closure declaration with the SHA-256 of its `OCaml5.Lcnf.Dump.ppMono` text, which that module says is deterministic;
  - `externs := none` and `prelude := none`;
  - `generator`, the translator's digest, and `toolchain`.
- Digests are `Digest` frames, foreign hashes on `Pin`'s precedent, so the only edge of `q := ⟨aid, i⟩` is its spec.

Notation: `#x` is the address of x, `S_α` is α's schema node, and `G` is `genesisNode`.

| # | Before | Call | Answer | After | Justified by |
| --- | --- | --- | --- | --- | --- |
| 1 | ∅ | `record ∅ q ℓ [Bt, Bm]` | `.error (.admission (.dangling (specOf Blob)))` | ∅ | spec edge checked first (`checkedEdges`); a pure value, so nothing changed |
| 2 | ∅ | register G, `Blob`, `Query LowerInput`, `Result LowerInput Lowered` | four `fresh` | N0 = {G, S_B, S_Q, S_R} | `putNode_fresh`; the genesis exemption `checkedEdges_of_genesis` |
| 3 | N0 | `lookup N0 q` | `.miss`, since `resultsFor N0 #q = []` | N0 | `nodeOf` reads no store |
| 4 | | the lowering runs outside the seam | text t (22,342 B) and manifest text m | | |
| 5 | N0 | `record N0 q ℓ [Bt, Bm]`, with ℓ = ⟨⟨#t⟩,⟨#m⟩⟩ | no resident result; Bt, Bm, q and r each `fresh`; `.ok (.fresh, ⟨#r⟩, N1)` | N0 ∪ {t, m, q, r} | `putNode_ok` per binding: r's edges S_R, ⟨query,#q⟩, ⟨manifest,#t⟩, ⟨manifest,#m⟩ all resolve |
| 6 | N1 | `lookup N1 q` | `read ⟨#r⟩` gives ⟨⟨#q⟩, ℓ⟩, so `.hit ℓ #r`; `read ℓ.module = whole t` | N1 | laws 3 and 6 |
| 7 | N1 | a second run at another thread count yields t' ≠ t (C7's double run); `record N1 q ℓ' [Bt']` | `.error (.poisoned #r)` | N1 | law 8 |
| 8 | worktree 2: ⟨M0 = N0, far N1, []⟩ | `Tiered.lookup` for q | near misses; the far answers `[#r]`; W = `N1.closure ⟨result,#r⟩` = [G, S_R, S_Q, q, S_B, t, m, r]; `Word.apply W M0` gives four `duplicate` and four `fresh`; then `.hit ℓ #r` | ⟨M1, N1, []⟩ | `closure_wf`, `apply_mem`, `layered_get` (M1 ⊆ N1) |
| 9 | M0 with a far that sends bytes hashing to #z ≠ #r | `Tiered.find ⟨result,#r⟩` | the node is filed at #z, so the near store still misses #r | grows by #z only | law 14 |
| 10 | root `doc/a/0` at e1, version 2 | `putRoot ⟨"doc/a/0", .journal, .entry, #e2, 3⟩`, where e2's parent is e0 | `.error (.fork "doc/a/0" #e1)` | unchanged | law 12 |

### 3. What the implementation hides

- the result index: a scan in Lean, `E4_index.Deps` in OCaml (a cache under its rule L-IDX-0);
- schema registration, and the children-first order of every word;
- chunking (`E4_chunk.cut`);
- durability: the `E4_pack` group commit, `E4_control`'s rename, and `E4_wal` rows sealed into tape segments at `checkpoint_mark`;
- the fill and its poison check.

Existing declarations that move behind the seam:
- `CheckCache.insert`'s list becomes `record`. The prefix-extension rule of `CheckCache.lookup` stays consumer logic over the results under one action.
- `LiveRecord.encode` and `decode` become a `Job` and its tape. `LiveRecord.restore` stays as the replay a load runs.
- `Layered`, `LocalFirst` and `CascadingStore` become `Tiered`.
- `E4_checkpoint.ensure_schema` becomes `register`.
- `gate_cache.run`'s result files become action-cache results.

That last move repairs a defect in `scripts/lib/gate_cache.py` today:
- **What happens:** the key omits the command. A changed command with unchanged inputs rewrites the record through `write_changed`, and the `seconds` field makes two runs disagree.
- **The repair:** the command goes into `GateInput`, and the timing becomes an `Annotation` on the result node, which never enters identity (`nodeBytes_trait_free`).

### 4. Adapters

| Seam | Adapters | Category |
| --- | --- | --- |
| node store (`find`, `putNode`, `resultsFor`) | the Lean `Store` value; `E4_cas` | in-process; local-substitutable |
| far tier | the Lean `Store`; a second `E4_cas` (another worktree); an HTTP tier we run; a third-party store | in-process; local-substitutable; owned remote; true external |
| action runner (outside the seam) | a Lean function (verdicts); MetaM (lowering); a subprocess (gates) | in-process; local-substitutable |

The node store and the far tier each have two adapters today, so both seams are real.

### 5. Laws

1. Grow-only: put, record, fill and push never remove a node (`putNode_sub`, `apply_sub`; Rocq `put_grows`).
2. Exact read: `read r = some a → find r.digest = some (nodeOf a)`; under `Store.Sound`, `r = address a` (new, from the `Canonical` field `ofVal_exact`).
3. A read after a put that is not a conflict answers the value (as `get_put`; Rocq `put_get`).
4. Addresses read no store (`nodeBytes_trait_free`).
5. Equal addresses mean equal values or an exhibited collision (`address_eq_or_collision`; Rocq `address_inj_resident`).
6. Lookup sound: `Faithful id f s` and a `hit o` for `⟨id,k⟩` give `o = f k`, or a collision (new; the store form of `CheckCache.lookup_sound`, B).
7. Memoize agrees: `(memoize id f k s).1 = f k`, or a collision, and `Faithful` is kept (new; the shape of `Tools.Session.Snapshot.resolve_agrees`; this is the acceptance the Incremental pass inherits).
8. Poison never overwrites: a different output refuses, and the store is unchanged (new; the action-level `put_conflict`).
9. Recording the same output again is `duplicate` and changes nothing (`put_duplicate`, `apply_idempotent`).
10. A store built by `put` and `record` holds at most one result per query (new; by induction, as `LocalFirst.Built` is).
11. Swap: `putRoot_root?`, `putRoot_nodes`.
12. Extend: a successful move keeps the old head among the new target's refs, so history stays reachable (new).
13. Once: a resident pin refuses every move (new).
14. Fill integrity: every filled node sits at the hash of its bytes (`putNode_ok`, `wf_digest`).
15. A faithful near store and a faithful far stay faithful after a fill (new).
16. Tier read: when near ⊆ far, the tiered read is the far's (`layered_get`).
17. Push: `outbox_wf`, `sync_sub`, `sync_idempotent`.
18. Transfer: `closure_wf`; `closure_closed` with Rocq `built_ranked`.
19. Kind append: `byte_injective` and `byte_ne_sentinel` decided again; Rocq `kind_separation`.
20. Verify: `verify_sound`.

### 6. Trade-offs

**High leverage.**
- A consumer is a carrier and an `ActionId`. It needs no kind append and no new plane or file. Durability, verify, transfer and recovery reuse what C1 to C3 made true.
- One `Lookup` serves every key type, and the spec keeps apart carriers that share a kind.

**Thin.**
- `register` is a ritual every process repeats.
- `Faithful` is provable only for Lean functions. The MetaM and subprocess actions rest on determinism, checked by recomputing (C6 and C7).
- The result index is a scan in Lean.

**Hard later.**
- Poison is permanent: the store is grow-only and never collects (CS8). The only repair is a version bump, which leaves dead entries behind.
- `specOf` drops wire tags (C4, R11), so a tag change must come with an `ActionId` bump.
- A result names its query, so results never dedup across queries. Outputs dedup only through refs, such as blobs.
- A far's results are trusted claims. The fill checks their integrity, not their correctness, so an external tier needs recompute-on-fill or object-only use.
- A key that holds refs instead of values owes a `reads_closure` law, which this design does not draft.
- Caches grow until a collector exists. Results are left unrooted on purpose, so a later collector can drop them while document histories and runs stay rooted.
- **Incremental** plugs into `memoize`. Its cutoff compares `Result.output` by its payload digest (a `Cid`, never an address), following graph rule 5.

### Critical Files for Implementation
- /Users/pooks/Dev/lean4-effect4/src/Effect4/Store/Domain/Store.lean
- /Users/pooks/Dev/lean4-effect4/src/Effect4/Store/Domain/Word.lean
- /Users/pooks/Dev/lean4-effect4/src/Effect4/Store/Domain/Traits.lean
- /Users/pooks/Dev/lean4-effect4/ocaml/engine/cas/e4_cas.mli
- /Users/pooks/Dev/lean4-effect4/ocaml/engine/cas/e4_control.mli
