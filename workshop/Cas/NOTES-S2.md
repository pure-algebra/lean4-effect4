# Lane S2 notes — the node, the store, the word, the traits

Running notes of lane S2 (`Cas/{Node,Store,Word,Traits,Probe}.lean` against lane S1's frozen
codec layer). One dated entry per module: what is defined, what is proved with its axioms, what
is open and why. S1's `NOTES.md` is frozen; the hazards it lists were the working rules here.

## 2026-09-04 23:45 — start; machine and toolchain facts

Read in the brief's order: `BRIEF.md`, `BRIEF-S2.md` (with the amendments after S1),
`REPORT-S1.md`, `NOTES.md`, `RECEIPTS.md`, then `Cas/{Digest,Val,Kind,Shape,Canonical}.lean`
for the signatures, the facts note §5–§6 and the plan §2, `Templates.lean` (`Templates.entry`,
`Templates.Entry.instCanonical`) and `Program.lean` (`ProgramCanonical.Corpus.p42`,
`EffC.instCanonicalEff`) for the probe's values.

Machine state at start: no `lean.exe` or `lake.exe` running; S1's oleans present under
`.lake/build/lib` from its green build; the `Cas` lakefile hunk in place (`-M6144`). Every
lean invocation of this lane runs through `scratchpad/run-lean.ps1`, which polls the working set
of every `lean.exe`/`lake.exe` every two seconds and kills the process tree past 600 s or 5 GB.
Nothing was killed.

Toolchain facts pinned by `probe1.lean` (`lake env lean -M 4096`, 2 s):

- `deriving DecidableEq` on `structure Ref (α : Type) where digest : Digest` demands
  `[DecidableEq α]` for the phantom parameter; `Ref`'s `DecidableEq` and `Repr` are by hand
  (both axiom-free). `deriving DecidableEq` on `Node` (fields `UInt8`, `Kind`, `Digest`, `Val`)
  works and is `[propext]`; on `AnyRef` it is axiom-free.
- `class Content (α) extends Canonical α where kind : Kind` gives `Content.kind : (α : Type) →
  [Content α] → Kind` (α explicit) and `Content.mk : [toCanonical : Canonical α] → Kind →
  Content α`, so `⟨.annotation⟩` is the whole `Content` instance once the `Canonical` instance is
  in scope.
- `structure Annotation (τ) where subject : AnyRef; value : τ; prev : Option (Ref (Annotation τ))`
  elaborates as a nested inductive (three motives in `Annotation.rec`); the phantom `Ref` is
  unnested like `List` would be.
- `local` is a keyword: `Layered`'s and `LocalFirst`'s field is spelled `«local»` and read as
  `l.local`, as S1 did with `«export»` and `«scoped»`.
- Present with these signatures: `Function.Injective`, `List.take_left'`/`drop_left'`
  (`l₁.length = i → take i (l₁ ++ l₂) = l₁`), `List.take_append_drop`, `List.Perm.filter`,
  `List.Perm.any_eq`, `Option.orElse`, `List.find?_some`, `List.mem_filter`, `List.filter_cons`,
  `List.any_eq_true`, `List.all_eq_true`, `List.append_cons`, `List.filter_congr`.
- `theorem … := Canonical.fits metaSchema` under `variable [Content Document]` is accepted and
  the instance variable is included in the statement (`∀ [inst : Content Document], …`).

## 2026-09-05 00:00 — `Cas/Node.lean`: green alone (`lake env lean`, 2 s); gate next

### What is defined

`Ref (α : Type) := {digest : Digest}` (phantom; `Ref.ext`, hand `DecidableEq`/`Repr`);
`AnyRef := {kind : Kind, digest : Digest}`; `class Content (α) extends Canonical α := kind :
Kind`; `Digest.ofBytes? : Bytes → Option Digest` (the one thirty-two-byte check the codecs share,
with `ofBytes?_bytes` and `ofBytes?_exact`); `instCanonicalRef [Content α] : Canonical (Ref α)`
(shape `.ref (kind α)`, `toVal r = .ref (kind α).byte r.digest.bytes`, `ofVal` refuses another kind
byte or a wrong length); `instCanonicalAnyRef` (shape `.anyRef`, `ofVal` through `Kind.ofByte?`
and `Digest.ofBytes?`).

`structure Node := {version : UInt8, kind : Kind, spec : Digest, payload : Val}` (deriving
`DecidableEq`, `Repr`); `Node.encode n := n.version :: n.kind.byte :: (n.spec.bytes ++ Val.encode
n.payload)`; `Node.decode : Bytes → Option Node` (version `0`, `Kind.ofByte?`, `Digest.ofBytes?
(rest.take 32)`, `Val.decode (rest.drop 32)`, one three-way `match`); `Node.length_encode`.
`Val.refs`/`Val.refsList` (the scan: every `ref` frame with a registered kind byte and a
thirty-two-byte digest, traversal order), `Val.malformedRef`/`malformedRefList`; `zeroDigest`;
`Node.refsOf`, `Node.malformedRef`, `Node.edges n := ⟨.schema, n.spec⟩ :: n.refsOf`,
`Node.IsGenesis n := n.kind = .schema ∧ n.spec = zeroDigest` (decidable), **`Node.checkedEdges n
:= if n.IsGenesis then n.refsOf else n.edges`** — the list admission resolves, which the store
and the word modules read.

Under `variable [Content Document]`: `metaSchema := (shape Document).document`; `genesisNode :=
⟨0, .schema, zeroDigest, toVal metaSchema⟩`; `genesisAddress := sha256 genesisNode.encode`;
`schemaNode (d : Document) : Node` (spec zero when `toVal d = toVal metaSchema`, else
`genesisAddress`); `specOf (α) [Content α] := sha256 (schemaNode (shape α).document).encode`;
`specFor (a : α) := if Content.kind α = .schema ∧ toVal a = toVal metaSchema then zeroDigest else
specOf α`; `nodeOf a := ⟨0, Content.kind α, specFor a, toVal a⟩`; `address a : Ref α := ⟨sha256
(nodeOf a).encode⟩`.

### Interpretation taken (not a redesign; recorded for the coordinator)

The brief sketches `nodeOf a := ⟨0, kind α, specOf α, toVal a⟩` with a per-type `specOf` and says
"the meta-schema itself gets `zeroDigest`". Q6 needs both: the meta-schema's node is the unique
zero-spec node, and every other schema node's spec is the genesis's address. A per-type spec
cannot give two different specs to two values of `Document`, so the spec is chosen per value:
`specFor` is `specOf α` everywhere except at the genesis (kind `schema` and payload equal to the
meta-schema's tree), where it is zero. With `Content.kind Document = .schema` (the kind lane G
will set), `nodeOf metaSchema = genesisNode` and `nodeOf d = schemaNode d` for every document
(`nodeOf_metaSchema`, `nodeOf_document`), and `specOf Document = genesisAddress`
(`specOf_document`). The comparison is on value trees (`Val.instDecidableEq`), never on
`Document` itself, so no `DecidableEq Document` is needed.

### What is proved (axioms in brackets; `∅` = none)

`Ref.ext`, `Ref.instDecidableEq`, `instDecidableEqAnyRef`, `Digest.ofBytes?`,
`Digest.ofBytes?_bytes`, `Digest.ofBytes?_exact`, `Node.encode` — ∅. `instCanonicalAnyRef`,
`instDecidableEqNode`, `Val.refs`, `Val.malformedRef`, `zeroDigest`, `Node.refsOf`,
`Node.malformedRef`, `Node.edges`, `Node.IsGenesis`, `Node.checkedEdges` and its two equations,
`Node.mem_checkedEdges_of_mem_refsOf`, `metaSchema`, `genesisNode`, `metaSchema_accepts` —
[propext]. `instCanonicalRef`, `Node.decode`, `Node.length_encode`, **`Node.decode_encode (h :
n.payload.WF) (hv : n.version = 0)`**, **`Node.decode_exact : decode b = some n → b = encode n ∧
n.payload.WF ∧ n.version = 0`** (the spec length is carried by `Digest`, as the amendment says),
`Node.encode_injective`, `genesisAddress`, `schemaNode`, `specOf`, `specFor`, `nodeOf`,
`address`, `schemaNode_metaSchema`, `specOf_document`, `nodeOf_metaSchema`, `nodeOf_document`,
`address_congr`, `nodeOf_encode_injective`, **`address_eq_or_collision`** (level 0),
**`address_inj (hInj : Function.Injective sha256)`** (level 1) — [propext, Quot.sound]. The
level-2 `example` (two nodes, one constant hash) is closed by `nomatch` on the payload
constructors.

`metaSchema_accepts : (shape Document).accepts (toVal metaSchema) = true` is `fits metaSchema`:
the genesis theorem is the class law at the meta-schema, so it needs no `decide` and holds for
every lawful instance the moment lane G's lands.

### Departure from the brief's statements, and why

Both lattice levels take `(toVal a).WF` and `(toVal b).WF`. `Val.encode` is injective only on
well-formed trees (S1's `Val.encode_injective`; a payload of `2^64` bytes or more has a wrapped
length prefix, and the split of a `pair`'s two frames is then not determined by the bytes), so
"equal node bytes ⇒ equal carriers" is unprovable without the premise. It is not a premise
about the hash — level 0 stays hash-free — and admission refuses every node outside it as
`oversize`, so every stored node satisfies it.

### Hazards met

- Inside `namespace Val`, `| some k, some dg =>` in a `match` on two `Option`s is parsed as the
  `Val.some` constructor (S1's note, met again): spelled `Option.some`.
- `simp only [decode, …]` rewrites the version test `0 = 0` to `True` before `if_pos rfl` can
  match; `if_true` closes it.
- A `rfl` that has to evaluate `sha256` of the abstract meta-schema's node (`specOf Document =
  genesisAddress` by unfolding) hits the heartbeat limit at `whnf`: the `Decidable` instance of
  `toVal metaSchema = toVal metaSchema` tries to run `Val.beq` on an opaque tree. The proof goes
  through `if_pos rfl` on the syntactic condition instead (`schemaNode_metaSchema`), and the
  `if_pos`/`if_neg` steps come before any `rw [hk]` into a field the condition mentions.
- `⟨…, fun h => nomatch …, rfl⟩`: the `nomatch` swallows `, rfl` as a second discriminant (S1's
  hazard); parenthesised.

### Guards (all passing)

`sampleNode := ⟨0, .«export», zeroDigest, sampleEntry⟩`: 108 bytes, header `[0, 2]`, payload at
offset 34 is `Val.encode sampleEntry`, round trip, refused with a trailing byte, version `1`,
kind byte `16`, kind byte `0`, a 33-byte prefix, and `[]`; `refsOf = []`, `edges = [⟨.schema,
zeroDigest⟩]`, the genesis-shaped node's `checkedEdges = []`; the scan finds registered refs in
order and drops or flags kind byte `16` and a 31-byte digest; an `AnyRef` frames as 42 bytes
`0b …21 02 …`, round-trips, and refuses kind byte `16` and 31 bytes.

Gate after the module: `lake build Cas`, 48 jobs, "Build completed successfully"; `Cas.Node`
built in under a second.

## 2026-09-05 00:07 — `Cas/Store.lean`: green alone (`lake env lean`, 2 s); gate next

### What is defined

`RootKind` (`stdlib | journal | daemon | schema | char`, `name`); `Root := {name, rootKind, kind,
digest, version : Nat}`; `Store := {nodes : List (Digest × Node), roots : List Root}`;
`Store.empty`; `findIn : List (Digest × Node) → Digest → Option Node` (the first binding) with
`Store.find`/`Store.getNode` over it and the four list lemmas the proofs use
(`findIn_append_some`, `findIn_append_none`, `findIn_mem`, `findIn_append_single`).
`Admission` is the brief's six constructors **plus `conflict (address : Digest) (occupant :
Node)`**, the refusal `Word.apply` needs when a binding's address holds another node (the brief
says "conflict refuses" but gave `Admission` no constructor to refuse with). `Outcome := fresh |
duplicate | conflict (occupant : Node)`.

`Store.Resolves s e : Prop := ∃ m, s.find e.digest = some m ∧ m.kind = e.kind`; `checkEdge`,
`checkAll`, **`checkEdges s n := checkAll n.checkedEdges`** (the genesis exemption is
`Node.checkedEdges`, so the spec edge is skipped exactly for kind `schema` with the zero spec);
`checkEdge_ok_iff`, `checkAll_ok_iff`, `checkEdges_ok_iff` (both directions, used by
`put_duplicate` and by `Word.apply_idempotent`). **`Closed s := ∀ d n, s.find d = some n → ∀ e ∈
n.checkedEdges, s.Resolves e`**; `Store.sub a b := ∀ d n, a.find d = some n → b.find d = some n`
(placed here rather than in `Word.lean` because the put lemmas need it), `sub_refl`, `sub_trans`,
`resolves_mono`.

**`Store.putNode`**: `oversize` (`¬ n.payload.WF`, decided by S1's `decWF`), `badVersion`,
`malformedRef`, then `checkEdges`, then the address `sha256 n.encode`; `duplicate` when the
resident equals `n`, `conflict resident` otherwise (the store untouched), `fresh` appends
`(address, n)` at the end of `nodes`. **`putNode_ok`** is the one characterization of `.ok (o, d,
s')`: the four admission facts, `d = sha256 n.encode`, and the three-way disjunction on the
outcome with the store it left. `putNode_fresh`/`putNode_duplicate` are the converses;
`putNode_sub`, `putNode_find` (after `fresh` or `duplicate` the node is at `d`), `putNode_closed`
(alias `putNode_fresh_closed`, the brief's name, for every outcome). `structure Store.Sound s :
Prop` — every resident node is version `0`, has a well-formed payload and no malformed
reference, sits at `sha256` of its own bytes, and the store is `Closed`; `empty_sound`,
`putNode_sound`. This is the invariant `Word.closure_closed` and `Word.verify_sound` speak in.

Under `variable [Content Document]`: `Store.put a s := putNode (nodeOf a)` with the digest as
`Ref α`; `Store.get r s` finds, checks `n.kind = Content.kind α`, then `ofVal n.payload`;
`put_ok` (`r = address a`), **`get_put (hc : ∀ m, o ≠ .conflict m)`**, `put_conflict` (the store
unchanged, another node at `r.digest`), **`put_duplicate`**, **`put_preserves`**, `get_preserves`.

Roots: `Store.root?`, `Store.nextVersion` (resident + 1, or 1), **`Store.putRoot`** (compare-and-
set: `staleRoot name expected actual` unless the version is the next one; the target must
resolve at `r.kind`, else `dangling`/`wrongKind`; the resident root of the name is replaced),
`putRoot_nodes` (a root move touches no node), `putRoot_root?`.

### Departures from the brief's statements, and why

- `get_put` carries `∀ m, o ≠ .conflict m`. After a `conflict` the address holds the occupant,
  never the new carrier (grow-only), so `get` answers the occupant's payload; the brief's
  unconditional statement is false in that case. `put_conflict` states what does hold.
- `put_duplicate` carries `(toVal a).WF`, `(nodeOf a).malformedRef = false` and `Closed s`
  besides the residency premise: `putNode` runs admission before the lookup (the brief's order),
  so a resident node that would not be admitted is refused, not a duplicate. The three premises
  are exactly what the resident's own admission established; on a `Sound` store they are free.
- `Admission.conflict` added (above). `Store.sub` lives here, not in `Word.lean`.

### What is proved (axioms in brackets; `∅` = none)

`RootKind.name`, `Store.empty`, `findIn`, `Store.find`, `Store.getNode`, the four `findIn`
lemmas, `Store.Resolves`, `checkEdge`, `checkAll`, `Store.sub`, `sub_refl`, `sub_trans`,
`resolves_mono`, `bool_eq_false_of_not`, `Store.root?`, `Store.nextVersion`, `Store.putRoot`,
`putRoot_nodes` — ∅. `Store.checkEdges`, `checkEdge_ok_iff`, `Closed`, `empty_closed`,
`Store.get`, `putRoot_root?` — [propext]. `checkAll_ok_iff`, `checkEdges_ok_iff`, `Store.putNode`,
`putNode_ok`, `putNode_fresh`, `putNode_duplicate`, `putNode_sub`, `putNode_find`,
`putNode_closed`, `putNode_fresh_closed`, `empty_sound`, `putNode_sound`, `Store.put`,
`put_ok`, `get_put`, `put_conflict`, `put_duplicate`, `put_preserves`, `get_preserves` —
[propext, Quot.sound].

### Hazards met

- `cases hl : findIn l d' with | some k => …` substitutes the discriminant in the goal too, so a
  later `rw [hl]` finds nothing and the `none` branch's witness is `rfl`, not `hl`.
- The `nomatch`-comma hazard a third time: `⟨fun _ _ h => nomatch h, fun …⟩` parses the rest of
  the tuple as discriminants ("Insufficient number of fields", "Missing cases: _, _"). Every
  `nomatch` inside an anonymous constructor is parenthesised.
- `rw [hp]` on a goal whose left side is a `match` over `s.putNode …` leaves the matcher
  unreduced and its closing `rfl` runs at reducible transparency; an explicit `rfl` after it
  closes the goal at default transparency.

### Guards (all passing)

A stand-in genesis `⟨0, .schema, zeroDigest, .str "schema"⟩` enters the empty store `fresh`; the
census entry under its address enters `fresh`, then `duplicate` (and the stand-in duplicates);
two nodes resident, found at their addresses, nothing at `zeroDigest`; the entry into the empty
store is `dangling <stand-in address>`; the entry under the zero spec is `dangling zeroDigest` (a
zero spec is the genesis's alone); a `tree` node whose `ref 2` names the schema node is
`wrongKind … .«export» .schema`, and the same ref at the entry's address is `fresh`; version `1`
is `badVersion`; kind byte `16` and a 31-byte digest are `malformedRef`; a hand-built store with
another node at the entry's address answers `conflict <occupant>` and keeps its two nodes; a root
at version 1 lands and reads back, version 2 first is `staleRoot … 1 2`, kind `schema` on the
export node is `wrongKind`, an unfiled target is `dangling`, and a second move at version 2
replaces the root (one root resident).

Gate after the module: `lake build Cas`, 49 jobs, green.

## 2026-09-05 00:29 — `Cas/Word.lean`: green alone (`lake env lean`, 2 s); gate next

### What is defined

`Binding := {digest, node}`; `abbrev Word := List Binding`; `resolvesAmong (bs : Word) (e :
AnyRef) : Bool`; **`Binding.admissibleAfter earlier b`** (version `0`, `payload.wf`, no malformed
ref, `digest = sha256 node.encode`, the digest not among `earlier`, every checked edge resolving
among `earlier`); `Word.wfFrom earlier`, **`Word.wf w := wfFrom [] w`** — children first, digests
exact, each digest once; **`Word.apply`** (a fold of `putNode`; `fresh`/`duplicate` continue, a
`conflict` refuses with `Admission.conflict d m`); `Word.toStore w := ⟨w.map (digest, node), []⟩`;
`Word.Faithful w` (every binding is found at its digest). **`emit`** (append a node only when it
is admissible after the bindings emitted so far) and **`closureGo s fuel d acc`** (skip if
emitted, walk the node's `checkedEdges` with one unit less fuel, then `emit`);
**`Store.closure s r := closureGo s s.nodes.length r.digest []`**; `FromStore s w`;
**`Store.Ranked s rank`** (`rank e.digest < rank d` along every checked edge of every resident
node). `Layered {«local», remote}`, `Layered.getNode` (`orElse`), `Layered.preload`
(the remote's closure applied into the local). `LocalFirst {«local», outbox}`, `LocalFirst.empty`,
`LocalFirst.putNode` (a `fresh` put joins the outbox), `LocalFirst.sync l remote := apply l.outbox
remote`, `inductive LocalFirst.Built` (from `empty` by `putNode`). `VerifyError` (`digestMismatch
| undecodable | malformedRef | dangling node missing | wrongKind node ref expected actual |
rootUnresolved name`); `verifyEdges`, `Store.verifyNode` (address recomputed, `Node.decode` of the
bytes equal to the node, no malformed ref, edges), `verifyNodes` (**with `Except.bind`, not a
`match`**, see the hazards), `verifyRoots`, **`Store.verify`**.

### What is proved (all [propext, Quot.sound] or below; none other)

Replay: `apply_cons_ok`, `apply_cons_of`, `apply_sub` (grow-only), `apply_mem` (every binding's
node is resident at its hash after a replay), **`apply_idempotent : apply w s = .ok s' → apply w
s' = .ok s'`**. Well-formedness: `admissibleAfter_spec`/`_of` (the six conjuncts, both ways),
`wfFrom_append`, `wfFrom_digest`/`wf_digest`, `findIn_map_none`, `findIn_map_ne_none`,
`resolves_of_resolvesAmong` (needs `Faithful`), `resolvesAmong_of_resolves`, `faithful_nil`,
`faithful_append`, **`wfFrom_apply`** (the replay invariant: from a faithful closed prefix, the
word applies to `toStore (prefix ++ word)`, faithful and closed), `wf_apply`, **`wf_closed`**.
Closure: `foldl_preserves`, `emit_wf`, `closureGo_wf`, **`closure_wf : (s.closure r).wf = true`**
(every store, every fuel), `emit_prefix`, `foldl_prefix`, `closureGo_prefix`, `emit_fromStore`,
`closureGo_fromStore`, `closureGo_rank`, `foldl_rank`, `foldl_edges_complete`,
`closureGo_complete` (with fuel above the rank, a resident digest is emitted),
**`closure_closed (hs : s.Sound) (hr : s.Ranked rank) (hb : rank r.digest < s.nodes.length) (h :
s.find r.digest = some n) : ∃ s', apply (s.closure r) empty = .ok s' ∧ Closed s' ∧ s'.find
r.digest = some n`**. Layers: **`layered_get : l.local.sub l.remote → l.getNode d = l.remote.find
d`**. Local-first: `built_invariant` (`l.local = toStore l.outbox ∧ l.outbox.wf`),
**`outbox_wf : l.Built → l.outbox.wf = true`**, **`sync_sub (hwf : l.outbox.wf) (hcov : ∀ d n,
l.local.find d = some n → remote.find d = some n ∨ ⟨d, n⟩ ∈ l.outbox) : l.sync remote = .ok r →
l.local.sub r`**, `sync_idempotent`. Verify: `verifyEdges_ok`, `verifyNode_ok`, `except_bind_ok`,
`verifyNodes_ok`, `verifyRoots_ok`, `verify_ok`, **`verify_sound : s.verify = .ok () → s.Sound`**,
`verify_sound'` (the brief's form: `Closed s ∧ ∀ d n, s.find d = some n → d = sha256 n.encode`),
`verify_roots`.

### Departures from the brief's statements, and why

- **`closure_closed` takes `Sound s`, a rank, and `rank r.digest < s.nodes.length`** instead of
  `Closed s` alone. Completeness of any closure algorithm needs the reachable graph to be
  acyclic: a hash cycle (`n₁` names `d₂`, …, `nₖ` names `d₁ = sha256 n₁.encode`) is not refutable
  without a premise about the hash, and on such a store no word can replay (the first node of
  the cycle to be put has a dangling edge), so the statement with `Closed` alone is false. The
  rank is the acyclicity, stated as a hypothesis on the store and never as a field;
  `Sound` supplies what `Closed` does not (version, well-formedness, no malformed reference,
  keys equal to hashes), all of which `apply` needs and `verify_sound` establishes. Owed: the
  lemma that a store built by a `wf` word is ranked by binding index below `nodes.length`.
- **`closure_wf` is unconditional** because `emit` checks admissibility after the bindings
  emitted so far: a node whose children the fuel cut off is left out rather than emitted with a
  dangling edge. This is what makes `closure` safe to replay on any store.
- `Word.wf` checks version, well-formedness and malformed references besides the brief's two
  conditions (children first, digest exact): otherwise `wf_closed` is false (`apply` would refuse
  `oversize` or `badVersion`). It also requires each digest once (a repeated digest is either a
  pointless duplicate or an exhibited collision).
- `sync_sub`'s coverage hypothesis is stated as the plan says ("the local was the remote and the
  outbox"): every local node is in the remote or is a binding of the outbox; `outbox_wf`
  supplies `hwf` when the local was built from `LocalFirst.empty`.
- `outbox_wf` is stated over `inductive LocalFirst.Built` (from `LocalFirst.empty` by
  `putNode`), the brief's "built from `LocalFirst.empty` by `putNode`" made a predicate.

### Hazards met

- **Reducing a discriminant that starts with a hash comparison.** `verifyNode s d n` begins with
  `if sha256 n.encode = d`; anything that `whnf`s it — `simp only [verifyNodes] at h` (matcher
  reduction), a type ascription `have h' : (match s.verifyNode d n with …) = … := h`, or the
  structural-recursion compiler of a theorem recursing on the node list — evaluates the hash
  symbolically and times out at 200000 heartbeats, with the error at the theorem header. Three
  moves close it: `verifyNodes` is written with `Except.bind`, the bind is split by
  `except_bind_ok` (which cases on a *variable*), and `verifyNodes_ok` is proved by the
  `induction` tactic, never by recursion. `split at h` on an `ite` whose condition is a hash
  comparison is fine (it does not reduce the condition), which is how `verifyNode_ok` works.
- `List.singleton_append` never fires after `List.cons_append` has turned `[x] ++ w` into
  `x :: ([] ++ w)`; `List.nil_append` is the lemma `wfFrom_append` needs.
- `rename_i` after `induction h with | step _ hp ih` names the implicit constructor arguments
  in an order that is not the declaration's; `| @step l n o d l' _ hp ih =>` names them exactly.
- A `#guard` whose `match` arm is a `Prop` on a variable bound by an outer pattern cannot be
  coerced to `Bool` (no `Decidable` for a `match` on a variable); leaves are joined with `&&`
  and `Except` results, which have no `DecidableEq`, are tested with a Bool `match`.

### Guards (all passing)

`probeWord := [⟨schema stand-in⟩, ⟨entry⟩]` is `wf`; reversed, the entry alone, and the entry
under the stand-in's digest are not; it replays to `probeStore`'s nodes and replaying it into its
own result changes nothing; the reversed word refuses `dangling <stand-in address>`; the closure
of the entry's `AnyRef` in `probeStore` is exactly `probeWord`, of the stand-in is its singleton,
of `zeroDigest` is `[]`; the layered read over an empty local answers the remote's node and
`none` for `zeroDigest`; `preload` puts both nodes into the local; `probeLocal` (the empty
local-first store after both puts) has outbox `probeWord` and local nodes `probeStore.nodes`, a
third put is `duplicate` and leaves the outbox alone, `sync` into the empty remote gives
`probeStore`'s nodes and syncing again into the result changes nothing, and `sync` into
`probeStore` itself is a no-op; `probeStore` and the replayed word verify; the entry with one
payload byte flipped (`1947 → 1946`, `0x9b → 0x9a`) under its old key is `digestMismatch <entry
address>`; the entry without its spec node is `dangling <entry> <stand-in>`; a root of kind
`schema` on the export node is `rootUnresolved "stdlib/rc112"`, and the same root at kind `export`
verifies.

Gate after the module: `lake build Cas`, 50 jobs, green.

## 2026-09-05 00:34 — `Cas/Traits.lean`: green alone (`lake env lean`, 2 s); gate next

### What is defined

`structure Annotation (τ) := {subject : AnyRef, value : τ, prev : Option (Ref (Annotation τ))}` (a
nested inductive through the phantom `Ref`). In `namespace Annotation`: `prevToVal`/`prevOfVal`
(the `prev` frame by hand — `.none`, or `.some (.ref 6 digest)`; the reader refuses another kind
byte or length), `shapeDoc τ := ⟨.struct "Annotation" [("subject", .anyRef), ("value", (shape
τ).root), ("prev", .option (.ref .annotation))], (shape τ).defs⟩`, `toVal a := .ctor 0 [toVal
a.subject, toVal a.value, prevToVal a.prev]`, `ofVal` (the generator's shape: one `ctor 0 [s, v,
p]` arm, a three-way `match` on the field readers), and the three laws. **`instCanonicalAnnotation
[Canonical τ] : Canonical (Annotation τ)`**, **`instContentAnnotation : Content (Annotation τ) :=
⟨.annotation⟩`**. `Node.subjectOf n := n.refsOf.head?` (field 0 is the subject, edge 1 after the
spec), `Node.prevOf` (the third field when it is a `ref` at kind 6); **`Store.annotationsOf`**
(kind-6 nodes with the subject, store order), **`Store.superseded s d`** (some annotation names `d`
as `prev`), **`Store.traitsOf`** (the heads), `Store.headsUnder s subject key` (the heads whose
spec is `key`), **`Store.effective s registry n key`** (own heads, else the spec node's, else the
registry node's — the registry's kind read off the store).

### What is proved

`prevOfVal_prevToVal` [propext], `prevOfVal_exact` [propext, Quot.sound], `ofVal_toVal`
[propext], `ofVal_exact` [propext, Quot.sound], `fits` [propext, Quot.sound] (by
`accepts_struct` and three `acceptsFields_cons`: the subject's law lifted from the empty table
by `acceptsIn_mono_of_subset`, the value's law as is, `prev` by cases), both instances [propext,
Quot.sound]. `nodeBytes_trait_free` (`rfl`: the node bytes of a carrier are the header, the spec
chosen for the value and the value tree — no store), **`trait_put_preserves`** and
`trait_get_preserves` (the store half of "traits never enter identity": `put_preserves`/
`get_preserves` at a trait), **`effective_deterministic`** (`s = s' → effective … = effective …`,
trivially), `superseded_perm` (`Perm.any_eq`), `annotationsOf_perm` (`Perm.filter`),
**`traitsOf_perm : s.nodes ~ s'.nodes → s.traitsOf x ~ s'.traitsOf x`** (the Perm-invariance the
brief asked for if cheap; it was: `Perm.filter` plus `List.filter_congr` pointwise through
`superseded_perm`), `headsUnder_perm` — all [propext, Quot.sound] or below.

### Interpretations

- "`address_ignores_traits`": stated as the two real facts, `nodeBytes_trait_free` (`rfl`) and
  `trait_put_preserves`; the brief's tautology `address a = address a` is not stated.
- The `prev` frame is written by hand because `Canonical (Ref (Annotation τ))` needs `Content
  (Annotation τ)`, the instance under construction; the bytes are exactly those the derived
  `Canonical (Option (Ref (Annotation τ)))` would write (`Val.none`, or `Val.some (Val.ref 6 d)`).
- `effective` takes the registry node's kind from the store (`s.find registry`), since `AnyRef`
  needs one; an unfiled registry contributes nothing.
- `Node.subjectOf` reads the first reference of the payload, as the brief says (edge 1); it does
  not check that the payload is a `ctor 0`. `Node.prevOf` reads the third field structurally.

### Hazards met

- `fun _ hp => nomatch hp` as the first explicit argument of `acceptsIn_mono_of_subset` is
  elaborated before `d1` is known ("Missing cases: _"); pin `(d1 := [])`. Same for
  `acceptsIn_of_not_named _ _ _ (fun _ h => nomatch h)`: pass the shape explicitly.
- `List.not_mem_nil` takes the membership proof as its explicit argument on this toolchain (S1's
  note, met again): `(List.not_mem_nil hp).elim`.
- `Canonical.ofVal (Canonical.toVal t)` in a `#guard` leaves `α` undetermined; `(α := …)`.
- `#guard e |>.map f = x` parses `= x` as a new command; parenthesise.

### Guards (all passing)

`trait1 := ⟨entry ref, "trusted", none⟩` frames as 85 bytes and round-trips through `ofVal` and
through `decode`, `trait2` (with `prev`) too; a `prev` at kind byte 2, a 31-byte `prev`, and a
constructor index 1 are refused; `Content.kind (Annotation String) = .annotation`; `refsOf`,
`subjectOf`, `prevOf` read the fields; the trait into `probeStore` without its spec node is
`dangling <trait spec>`, with it `fresh`; `traitStore` (probe store + trait spec + trait1 +
trait3 on the spec node + registry tree + trait4 on the registry + two more exports) has nine
nodes, the entry's node and bytes unchanged; `traitsOf entry = [trait1]`; `effective` at the
node (`trait1`), at the spec (`export2`, whose own heads are empty, resolves to `trait3`), at the
registry (`export3`, whose spec node carries nothing, resolves to `trait4`), `[]` under another
key and under an unfiled registry; `trait2` supersedes `trait1` (`traitsOf = [trait2]`,
`superseded trait1 = true`, `superseded trait2 = false`, `effective = [trait2]`), the entry still
unchanged, and the store verifies.

Gate after the module: `lake build Cas`, 52 jobs, green.

## 2026-09-05 00:40 — `Cas/Probe.lean` and the final gate: every §6 number reproduced

`Cas/Probe.lean` (imports `Cas.Traits`, `Cas.Templates`, `Cas.Program`) compiles alone in 2 s
and in the gate: `lake build Cas`, 52 jobs, "Build completed successfully". Final census over the
five S2 modules (`RECEIPTS-S2.md`, cut from the gate's log): 202 `#print axioms` lines — 42 with
no axioms, 48 `[propext]`, 112 `[propext, Quot.sound]`, none other; no `sorryAx`, no
`Classical.choice` anywhere in the log (S1's 251 receipts replay unchanged beside them). No
`lean.exe`/`lake.exe` left running; nothing was killed during the lane.

### The §6 numbers, as guards

- `entrySpec := Digest.ofHex? "6a1c…cac8"` (today's `entryDoc` address, the explicit stand-in
  spec); `entryNode := ⟨0, .«export», entrySpec, toVal Templates.entry⟩` is 108 bytes, header
  `00 02`, then the 32 spec bytes, then `Val.encode sampleEntry` (whose digest is `8fab16…61fa`);
  **its address is `1437a122e15ed5fd0fe9e9933d1deec1e010def465b65a2b662aeb1549c3705b`**; it
  round-trips through `Node.decode` and refuses a trailing or a dropped byte.
- The kind-6 twin (same spec, same payload, kind byte 6) is
  **`ca07857e6301ef7b052d889bc1296cd280d13e7050b9326235333533b7ba0990`**, another address for the
  same bytes after the kind byte (one payload at two kinds is two addresses).
- `p42Node := ⟨0, .program, zeroDigest, toVal Corpus.p42⟩`: `p42`'s 66 bytes with digest
  `fa5f40…62a3`, node 100 bytes, **address `8032405e589e111c77c13b95b8a2ea408627f4e855ee3e8891fb3ac51676c13a`**.
- With `instance : Content Templates.Entry := ⟨.«export»⟩` (what the generator emits for lane C),
  `entryTyped : Ref Entry := ⟨1437…⟩` frames as the **42-byte `0b 0000000000000021 02 1437a1…705b`**,
  round-trips, decodes as `AnyRef ⟨.«export», 1437…⟩`, and is refused at kind byte 6 and at 31 bytes.

### The store half of the probe

No node hashes to `6a1c…` (it is an address of the old store), so the spec is *seeded* by hand:
`seeded := ⟨[(entrySpec, ⟨0, .schema, zeroDigest, .str "entryDoc"⟩)], []⟩`, a store whose key is
not its node's hash — `seeded.verify` is `digestMismatch 6a1c…`, guarded. In it the entry is
`fresh` at `1437…` and found there, again `duplicate` (two nodes), the twin `fresh` at `ca07…`
(three nodes), and `p42` under the seeded spec `fresh`; in the empty store the entry is
`dangling 6a1c…` and the zero-spec `p42` node is `dangling zeroDigest` (a zero spec is the
genesis's alone; so is it in `seeded`); a `tree` seed under the spec key is `wrongKind 6a1c…
.schema .tree`; a `tree` node whose `ref 6` names `1437…` is `wrongKind 1437… .annotation
.«export»`, and the same reference at kind byte 2 is `fresh`.

The word, closure, layered, outbox, verify and trait guards are restated on the genuine world
(`probeSchema`/`probeEntry`/`probeWord`/`probeStore`/`probeLocal`/`traitStore` of the three
modules; `probeEntry` is the §6 entry under the stand-in genesis's real address), and the
lattice and the typed face are `#check`ed with their `[Content Document]` binder visible.

### Commands run by this lane (all through `scratchpad/run-lean.ps1`, 600 s / 5 GB caps)

`lake env lean -M 4096 <scratchpad>\probe1.lean` (once); `lake env lean -M 4096
workshop\Cas\Cas\Node.lean` (×2), `…\Store.lean` (×2), `…\Word.lean` (×4), `…\Traits.lean` (×3),
`…\Probe.lean` (×1); the gate `lake build Cas` (×5: after Node, Store, Word, Traits, Probe), each
green. Peak `lean.exe` working set seen by the monitor: 612 MB; longest wall clock: 10 s.

The lane's final report is delivered as its closing message to the coordinator, as S1's was:
the tool harness refuses to write `REPORT-S2.md` as a file. Its content is these five entries
(definitions, proofs with axioms, departures, hazards, guards) plus the census above and the
open items: `Content Document` (lane G) instantiating the `[Content Document]` sections; the owed
lemmas that a `wf` word's store is `Ranked` by binding index below `nodes.length` and is `Sound`;
Perm-invariance of `effective` (not stated: it reads `find`, the first binding, which a
permutation with repeated keys can change — on a `Sound` store keys are unique); the `Probe`'s
stand-in spec `6a1c…`, whose `1437…` guard moves once the spec is the derived document.
