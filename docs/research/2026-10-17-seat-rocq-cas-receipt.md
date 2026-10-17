# 2026-10-17 seat rocq-cas receipt: the content-addressed store's math in Rocq, over Lean's own code

**The one thing to know before merging:** `make gen-rocq` now also writes `rocq/StoreCode.v`, the
store's code printed from Lean over an abstract hash. Properties 1 to 5 are proved over it in
`rocq/StoreLaws.v` and `rocq/StoreGrammar.v`. Each rests on the printed parameters and three
equality laws, and on no hash assumption. The branch sits on `6689f0833` and waits for the
coordinator's tip to rebase onto. No Lean theorem changed.

The research note, with the byte language for the code seat, is
`docs/research/2026-10-17-seat-rocq-cas/README.md`.

## Base and head

| Item | Value |
| --- | --- |
| Branch | `seat/rocq-cas`, in the worktree `.claude/worktrees/modest-sammet-90f7b7` |
| Base | `6689f0833` (slice 1.2a) |
| Commits | `3fadf051f` the `gen-rocq` repair; `e96aec466` the store's code and its laws; `30de6d516` one byte language; the commit that adds this receipt and the note |
| Pushed | no |
| Rebase | pending: the coordinator sends the tip |

## Changed files

| File | Change |
| --- | --- |
| `rocq/tools/split_types.ml` | flattens the module-shaped program types into one group in the Rocq names, then splits it as before |
| `src/OCaml5/Lcnf/Gallina.lean` | a second spec, `storeSpec`; the rules it needs, each by name or refused |
| `src/OCaml5/Tools/GallinaGen.lean` | a second output path for the store's file |
| `Makefile` | `gen-rocq` builds `Effect4.Store.Domain.Word` and writes `rocq/StoreCode.v` |
| `rocq/StoreCode.v` | GENERATED: the store's code as the functor `Code (E : Prim)` |
| `rocq/StoreLaws.v` | new: properties 1 to 4 and `verify_sound` |
| `rocq/StoreGrammar.v` | new: property 5 |
| `rocq/StoreAssumptions.v` | new: the assumptions of 16 store theorems |
| `rocq/README.md`, `rocq/_RocqProject` | the map, the printer's rules, the compile command |
| `docs/research/2026-10-17-seat-rocq-cas/README.md` | new: the note |
| `docs/research/2026-10-17-seat-rocq-cas-receipt.md` | new: this receipt |

## Part 1: the `gen-rocq` repair

Slice 1.2a puts each program type in its own module, and the cycles in `module rec`. rocq-of-ocaml
reads neither shape. `split_types.ml` now flattens the modules into one type group in the names the
workspace was built on: `Ty.t` is `ty`, and `Eff.Succeed` is `Eff_succeed`. Then it splits the
group as before.

| Command | Result |
| --- | --- |
| `lean-slot.sh make gen-rocq` | writes the three files; `rocq/Eff_types.v` and `rocq/Skeleton.v` are byte for byte the committed ones |
| the compile command of `rocq/README.md` | the eight files compile; the slowest takes 1.12 s |
| `rocq compile -Q . E4 Assumptions.v` | the 25 parameters of `Eval`, and nothing else |

## Part 2: the store's code, printed

`storeSpec` prints 43 declarations of `Effect4.Store`:

* the value and node codecs, with `Val.tag` and `Val.payload`, and the well-formedness check;
* the kind table and the edge scan;
* the find, the put with its admission, `Word.apply` and `Word.wf`;
* `verify`.

`Prim`'s parameters are the hash, `be64`, `natBytes`, the UTF-8 bytes of a string, the float test,
`Node.decode`, the zero digest and three equality deciders.

The printer's new rules:

* a library constant prints only by its row of `prims` (`List.appendTR` is `app`, `Nat.decLt` is
  `Z.ltb`, `ByteArray.data` is `id`);
* a `UInt8` and a `UInt64` print as `int`; the store compares them and never computes with them;
* a `Decidable` prints as `bool`; a proof field and a proof binder are erased;
* a function on `List T` recursive with one on `T` prints as a local `fix`, since Rocq refuses the
  mutual form over a nested type;
* the types print before the module type, because a parameter's type names one.

`Skeleton.v` is byte for byte unchanged by these rules. The closure walk is not printed:
specialization makes its nested `foldl` a mutual recursion that the guard checker refuses.

## Part 3: the proved properties

| Property | Rocq theorems | Assumes |
| --- | --- | --- |
| 1. The hash is injective on a store's residents | `Laws.residents_hash_injective`, `Laws.residents_bytes_injective` (needs `Addressed`); `Laws.address_inj_resident` (needs nothing of the store) | the parameters and `digest_eqb_spec` |
| 2. Domain separation | `Laws.version_byte_separates`, `Laws.val_tag_range`, `Laws.domain_separation`, `Laws.kind_separation`, `Laws.address_cid_collision` | the parameters |
| 3. A built store is ranked by insertion order | `Laws.put_ranked`, `Laws.built_ranked`, `Laws.rank_below_length`, `Laws.put_sound`, `Laws.built_sound`, `Laws.built_closure_premises` | the parameters and the three equality laws |
| 4. The store as a growing map from digest to bytes | `Laws.putNode_ok`, `Laws.put_get`, `Laws.put_grows`, `Laws.put_bytes_never_change`, `Laws.put_conflict`, `Laws.put_conflict_collision`, `Laws.apply_grows`, `Laws.apply_built`, `Laws.verify_sound` | the same; `verify_sound` also takes `Node.decode_exact` as a premise |
| 5. One byte language | `Grammar.encode_prefix_free`, `Grammar.encode_injective`, `Grammar.node_encode_injective`, `Grammar.put_conflict_bytes` | the same; the codec laws are a premise (`Grammar.CodecLaws`) |

The parameters are `Prim`'s. The three equality laws are `PrimLaws`: each decider decides
equality, which is what the compiler erased from the `DecidableEq` instance.

`rocq compile -Q . E4 StoreAssumptions.v` prints 16 reports. Every axiom in them is a parameter of
`Prim` or a law of `PrimLaws`, and nothing else: no `eq_rect_eq`, no classical axiom.

Every result also assumes its translators. They are Lean's base-phase LCNF, the printer with its
`prims` table, and rocq-of-ocaml for `val_` (`Eff_types.v`).

Three red controls, each a mutant of the generated code in a scratch copy:

| Mutant | Result |
| --- | --- |
| `unit` framed under tag 0 | `val_tag_range` fails |
| `verify` without the hash check | `verify_sound` fails |
| `none` framed under `unit`'s tag 9 | `encode_prefix_free` fails: the case `unit` against `none` stays open |

The model writes a natural, a `UInt8` and a `UInt64` as Z. A theorem quantifies over every Z, so it
specializes to Lean's values. The grammar theorems take `InRange` and `NodeInRange` where a range
matters. That is a natural at least 0, float bits below 2^64, and a spec of thirty-two bytes
(`Digest.length_eq`, which the compiler erased).

The statement vocabulary is written by hand, because LCNF carries no `Prop`. These are `Resolves`,
`Closed`, `Addressed`, `Sound`, `Sub`, `Ranked`, `Built`, `rank_of`, `bytes_at`, `InRange` and
`NodeInRange`. Each restates a Lean `Prop` field for field, or names the range Lean's types carry.

## Axiom output

No Lean declaration of `Effect4` changed. `OCaml5.Lcnf.Gallina` is a tool library, and its narrow
build passes (`lean-slot.sh lake build OCaml5.Lcnf.Gallina`). Not run, by the brief: any wider
project gate.

## Proposed Lean declarations (proposals only)

Each proposal is no wider than its Rocq fragment. The four cheap ones are proved in Lean directly;
the Rocq theorem is the second proof.

**1. The replacement of `address_inj`** (`src/Effect4/Store/Domain/Node.lean`), placed in
`Store.lean` after `Store.find`. Proof: the two finds meet at one digest, so `nodeOf a = nodeOf b`,
then `Canonical.toVal_injective`.

```lean
theorem address_inj_resident {α : Type} [Content α] {s : Store} {a b : α}
    (ha : s.find (address a).digest = some (nodeOf a))
    (hb : s.find (address b).digest = some (nodeOf b))
    (h : address a = address b) : a = b
```

**2. The replacement of `Pin.holds_of_injective`:** delete it, and keep `holds_or_collision`. A
pin's span digest is a foreign hash checked by recomputation. No store holds the span's bytes, so
no store-relative statement applies, and level 0 is the honest guarantee.

**3. Cheap theorems in Lean**, each with its Rocq counterpart:

```lean
theorem Store.Sound.hash_injOn {s : Store} (hs : s.Sound) {d₁ d₂ : Digest} {n₁ n₂ : Node}
    (h₁ : s.find d₁ = some n₁) (h₂ : s.find d₂ = some n₂)
    (h : sha256 n₁.encode = sha256 n₂.encode) : n₁ = n₂            -- residents_hash_injective
theorem Node.encode_ne_val_encode {n : Node} (h : n.version = 0) (v : Val) :
    n.encode ≠ Val.encode v                                           -- domain_separation
theorem Node.kind_eq_of_encode_eq {n m : Node} (h : n.encode = m.encode) :
    n.kind = m.kind                                                   -- kind_separation
theorem putNode_conflict_bytes {s s' : Store} {n m : Node} {d : Digest} (hs : s.Sound)
    (h : s.putNode n = .ok (.conflict m, d, s')) :
    m.encode ≠ n.encode ∧ sha256 m.encode = sha256 n.encode         -- put_conflict_bytes
```

**4. Declared from Rocq.** A store built by puts is ranked by insertion order. It needs
`Store.Built` and `Store.rankOf` in `Word.lean`. `closure_closed_built` then follows in Lean from
`closure_closed`, `putNode_sound` and the rank bound.

```lean
inductive Store.Built : Store → Prop
  | empty (roots : List Root) : Store.Built ⟨[], roots⟩
  | put {s s' : Store} {n : Node} {o : Outcome} {d : Digest} :
      s.Built → s.putNode n = .ok (o, d, s') → s'.Built
  | roots {s : Store} (roots : List Root) : s.Built → Store.Built ⟨s.nodes, roots⟩

/-- The position of the first binding at `d`, or the number of nodes. -/
def Store.rankOf (s : Store) (d : Digest) : Nat := …

@[semantics "exact-codecs" (requirement := R13)]
declared Store.built_ranked {s : Store} (h : s.Built) : s.Ranked s.rankOf
  from "rocq/StoreLaws.v: Laws.built_ranked, over rocq/StoreCode.v (make gen-rocq)"
```

**5. Declared from Rocq.** The value codec is prefix-free. The Rocq premises hold of every Lean
`Val`: `InRange` by its types, and `CodecLaws` by four Lean theorems.

```lean
@[semantics "exact-codecs" (requirement := R3)]
declared Val.encode_prefix_free {v w : Val} {r₁ r₂ : Bytes} (hv : v.wf = true)
    (hw : w.wf = true) (h : Val.encode v ++ r₁ = Val.encode w ++ r₂) : v = w ∧ r₁ = r₂
  from "rocq/StoreGrammar.v: Grammar.encode_prefix_free, over rocq/StoreCode.v (make gen-rocq)"
```

Placement of 4 and 5:

* Concept: `exact-codecs` (`docs/core/semantics.md` §2.5), the data plane.
* Question: two new registry claims, `built-store-ranked` and `value-codec-prefix-free`.
* Reach: the printed code, for every hash, with the translators above.
* What they do not establish: a store read from disk and then verified is `Sound`, not ranked. A
  hash cycle among verified bytes is not ruled out, and only puts rule it out.
* Unlock: `closure_closed` with no rank premise, for every built store (R13); one byte language
  for the code seat (R3).

The requirement choices, R13 and R3, are the coordinator's call.

When `Store.rankOf` lands, add it to `storeSpec`. The Rocq proof then reads the printed function
in place of the hand `rank_of`, the same function.

## Proposed decisions rows (proposals only)

1. **One node language.** DI-25's kinds 16 to 23 land in `Kind.lean`, or OCaml refuses them.
   Until then OCaml mints none (`E4_checkpoint` mints kind 21 today).
2. **No handle in content.** Lean's `Store.putNode` refuses a handle frame in a content kind, as
   OCaml does (`Handle_in_content`, attack B2).
3. **The store's parameters in `rocq/`.** A law a proof needs of a `Prim` parameter is a premise
   or a field of `PrimLaws`. Each one names the Lean theorem or the erased proof that holds it.

## Open obligations

1. Rebase onto the coordinator's tip, then rerun `make gen-rocq` and the compile command.
2. The code seat's fixes: tags 13 and 14 in `E4_node.walk`, the kinds 16 to 23 decision, and an
   `Unknown_tag` refusal (the note's §3).
3. The Lean proposals above.
4. Some code is not printed, so no proof reads it. That is the closure walk (the guard checker),
   `Val.decode` and `Node.decode` (parameters), the pin, and the roots plane (`Built`'s `roots`
   arm stands in).
5. Scope only, no statement written in Rocq: the log's prefix semantics, checkpoint replay and an
   action cache (the note's §4).

## Evidence

| Claim | Evidence |
| --- | --- |
| `split_types.ml` keeps the Rocq types' spelling on the new layout | tested: `Eff_types.v` is byte for byte the committed one |
| The printer's store rules leave `Skeleton.v` unchanged | tested: byte for byte |
| Properties 1 to 5 hold of Lean's printed store code, for every hash | proved in Rocq 9.0.1, assuming the parameters, the equality laws and the translators; property 5 also takes the codec laws as a premise |
| The proofs read the code they name | tested: three mutants of the generated code fail |
| The note and the receipt follow the writing rules | `python3 scripts/check-language.py --strict` passes on both |
