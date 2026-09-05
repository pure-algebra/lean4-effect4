# Lane S2 report — the node, the store, the word, the traits

Filed by the coordinator from the lane's closing message (the lane could not write this
file itself). Running notes: `NOTES-S2.md` (one dated entry per module — definitions, proofs
with axioms, departures, hazards, guards). Receipts: `RECEIPTS-S2.md` (every `#print axioms`
line, cut from the final gate's log). Real clock by file times: 2026-09-04 23:35 →
2026-09-05 00:40 (the lane's own timestamps run fast). Branch `main`, v4.33.1.

## Outcome

All four modules of `BRIEF-S2.md` plus the probe battery are written, proved and green:
`Cas\{Node,Store,Word,Traits,Probe}.lean`, each imported by `Cas.lean`. Final gate `lake
build Cas`: 52 jobs, "Build completed successfully" (S2 modules compile in 1–3 s each). 202
receipts: 42 with no axioms, 48 `[propext]`, 112 `[propext, Quot.sound]`, none other — no
`sorry`, `partial`, `unsafe`, `native_decide`, `axiom`, `extern`, `implemented_by`, no
`Classical.choice`; S1's 251 receipts replay unchanged beside them. Every `#guard` passes.
S1's frozen files, `src\`, `Test\`, `docs\`, `COORDINATION.md` untouched; one `lake` at a
time; nothing killed (peak `lean.exe` 612 MB, longest run 10 s); nothing left running.

Everything needing `Canonical Document` — `metaSchema`, the genesis, `specOf`, `nodeOf`,
`address`, the lattice, `put`/`get` and their laws, the trait-identity theorems — sits under
`variable [Content Document]`, compiles now, and instantiates when lane G's instance lands.
The node layer, admission, words, closures, layers, outbox, `verify` and trait queries are
tested with explicit spec digests.

## Proved (P `[propext]`, PQ `[propext, Quot.sound]`, ∅ none)

- Node: `Ref α` (phantom; hand `DecidableEq`/`Repr`), `AnyRef`, `class Content α extends
  Canonical α := kind`; `Canonical (Ref α)` and `Canonical AnyRef` with the three laws (wrong
  kind byte/length refused); `Node.encode/decode` exact — `decode_encode (h : payload.WF) (hv :
  version = 0)`, `decode_exact`, `encode_injective` (PQ); the scan `Val.refs`,
  `Val.malformedRef`, `Node.edges`/`checkedEdges` (genesis = kind `schema` ∧ zero spec, exempt);
  under `[Content Document]`: `metaSchema`, `genesisNode/Address`, `schemaNode`, `specOf`,
  `specFor`, `nodeOf`, `address`, `metaSchema_accepts` (= `fits metaSchema`, P),
  `nodeOf_metaSchema`/`nodeOf_document` (under `Content.kind Document = .schema`),
  `address_eq_or_collision` (level 0), `address_inj (hInj : Function.Injective sha256)` (level
  1), level 2 shown empty.
- Store: `findIn/find` + lemmas (∅); `Admission` (+ `conflict address occupant`), `Outcome`;
  `Resolves`, `checkEdges_ok_iff`; `Closed`, `empty_closed`, `sub`; `putNode` with `putNode_ok`
  (the one characterization), `putNode_fresh/duplicate/sub/find`, `putNode_closed` (=
  `putNode_fresh_closed`), `Store.Sound`, `putNode_sound`; `get_put (∀ m, o ≠ .conflict m)`,
  `put_conflict`, `put_duplicate`, `put_preserves`, `get_preserves`; `putRoot`
  (compare-and-set), `putRoot_root?`.
- Word: `Word.wf`, `Word.apply`, `apply_idempotent`, `apply_sub/mem`, `wfFrom_apply`,
  `wf_closed`; `Store.closure` (DFS emitting a node only when admissible after the emitted
  bindings) — `closure_wf` unconditional, `closure_closed` under `Sound s`, `Ranked s rank`,
  `rank r.digest < s.nodes.length`; `layered_get`; `LocalFirst.Built`, `outbox_wf`, `sync_sub`,
  `sync_idempotent`; `Store.verify`, `verify_sound : verify = .ok () → Sound` (+ the brief's
  form `verify_sound'`), `verify_roots`.
- Traits: `Annotation τ {subject, value, prev : Option (Ref (Annotation τ))}`, `Canonical
  (Annotation τ)` (three laws), `Content := ⟨.annotation⟩`; `annotationsOf`, `superseded`,
  `traitsOf`, `headsUnder`, `effective` (node → spec → registry); `nodeBytes_trait_free`
  (`rfl`), `trait_put_preserves`, `trait_get_preserves`, `effective_deterministic`,
  `traitsOf_perm` (Perm-invariance, proved), `headsUnder_perm`.

## Guards (the facts note's §6 numbers, `Cas\Probe.lean`)

Entry node under explicit spec `6a1c…cac8`: 108 bytes, address `1437a122e15ed5fd0fe9e9933d1d
eec1e010def465b65a2b662aeb1549c3705b`; kind-6 twin `ca07857e6301ef7b052d889bc1296cd280d13e70
50b9326235333533b7ba0990`; `p42` (66 bytes, `fa5f40…62a3`) at kind 5, zero spec: `8032405e58
9e111c77c13b95b8a2ea408627f4e855ee3e8891fb3ac51676c13a`; typed ref frame 42 bytes `0b …21 02
1437…`, refused at kind 6 / 31 bytes. Store: `fresh` then `duplicate` on the entry (spec
seeded by hand under `6a1c…`, which `verify` flags `digestMismatch`), twin `fresh`, `dangling
6a1c…` in the empty store, `dangling zeroDigest` for zero-spec `p42`, `wrongKind` both ways,
hand-built occupant → `conflict`, `staleRoot`. Word `wf`, applied twice; closure = the word;
layered read; outbox synced twice; `verify` passes then refuses after flipping `0x9b→0x9a`; a
trait on the entry leaves its bytes unchanged, `effective` resolves at node/spec/registry,
`prev` supersession moves the head.

## Departures (all in NOTES-S2.md)

1. `nodeOf` chooses its spec per value (`specFor`: zero exactly at the genesis) — a per-type
   `specOf` cannot satisfy Q6 for both the meta-schema and other documents.
2. Lattice levels take `(toVal a).WF`/`(toVal b).WF` (`Val.encode` is injective only there; not
   a hash premise; admission enforces it).
3. `get_put` needs `o ≠ conflict`; `put_duplicate` needs WF, no malformed ref, `Closed s`
   (admission runs before the lookup, per the brief's order).
4. `Admission.conflict` added for `Word.apply`'s refusal; `Word.wf` also checks
   version/WF/malformed/digest-once (else `wf_closed` is false).
5. `closure_closed` needs `Sound` + a rank: completeness needs acyclicity, unprovable without a
   hash premise, and on a cyclic store no word replays.
6. "`address_ignores_traits`" stated as `nodeBytes_trait_free` + `trait_put_preserves`.

## Open

`Content Document` (lane G) instantiates the `[Content Document]` sections as stated; owed
lemmas: a `wf` word's store is `Ranked` by binding index below `nodes.length`, and is `Sound`;
Perm-invariance of `effective` not stated (reads `find`); the Probe's `1437…` guard moves once
the spec is the derived document.

## Key hazards for the generator and the landing

Inside `namespace Val`, `some` is `Val.some`; anything that whnf-reduces a discriminant
starting with a hash comparison times out (use `Except.bind` + case on a variable + the
`induction` tactic, never structural recursion on that theorem); `nomatch` inside anonymous
constructors swallows the following components (parenthesise); `#guard` match arms that are
Props on outer-bound variables have no `Decidable` (use `&&`).

## Commands

All via `scratchpad\run-lean.ps1` (600 s / 5 GB monitor): `lake env lean -M 4096` on
`probe1.lean` (×1), `Node.lean` (×2), `Store.lean` (×2), `Word.lean` (×4), `Traits.lean`
(×3), `Probe.lean` (×1); `lake build Cas` ×5 (after each module; final 52 jobs, green).
