# Seat W4 — Lean carriers for the OCaml libraries the avatar, daemon and codegen will use

Status: 2026-09-04, landed and elaborating on `main` (base `72939ed`). Not committed by this
seat. Seat W4 of the 2026-09-04 wave.

Files owned and written: `workshop/OCaml5/Lib/Order.lean`, `Lib/Map.lean`, `Lib/Set.lean`,
`Lib/Deque.lean`, `Lib/Sexp.lean`, `Lib/Derived.lean`, `Lib/Stream.lean`, `Lib/Eio.lean`,
`Lib/Picos.lean`, `workshop/OCaml5/LibTest.lean`, this report. Nothing else was edited;
`Effect.lean`, `Value.lean`, `Promise.lean` and `Ml/Reflect.lean` were read only.

```
$ lake build OCaml5.LibTest
Build completed successfully (22 jobs).
```

Every `#guard` in `LibTest.lean` is checked by the kernel at build time. No declaration under
`Lib/` uses `sorry`, `axiom`, `partial` or `native_decide`; all are total.

## 1. The ruling, discharged

*Every OCaml library construct the avatar/daemon/codegen use must have a Lean carrier with the
laws we rely on; what has no carrier is a refusal row.* Nine modules, one per construct family;
each module's docstring opens with a **named-property list** — one theorem name per line, stable,
citable by W1/W2/W3 — and closes with its **refusal rows**, each with a `W4-…` identifier.

| deliverable | module | carrier | headline laws |
| --- | --- | --- | --- |
| 1a | `Lib/Order.lean` | `LinOrd`: `Base.Comparator.S` as a class (compare's *sign*, four laws); instances for `Nat`, `Char`, `List`, `String` | `cmp_self`, `eq_of_cmp_eq`, `cmp_swap`, `cmp_trans_lt`, `cmp_eq_iff`, `cmp_total` |
| 1b | `Lib/Map.lean` | `Base.Map` as the strictly ascending assoc list, invariant in the type | `find_set_same/other`, `find_remove_same/other`, **`ext_find`** (canonical form), `set_comm`, `keys_nodup`, `fold_visits_keys_in_order`, `fold_length`, `toAlist_sorted`, **`ofAlist_toAlist`**, **`find_merge`** |
| 1c | `Lib/Set.lean` | `Base.Set` = `Map κ Unit` | `mem_add_same/other`, `mem_remove_same/other`, `ext_mem`, `add_comm`, `add_idem`, `toList_nodup`, `ofList_toList`, `mem_union/inter/diff` |
| 2 | `Lib/Deque.lean` | `Core.Deque` as its `to_list`; `Buckets = Map Nat (Deque τ)`; **projection onto `Effect4.Deep.Dispatcher`** | `Deque.fifo`, `popAll_eq_toList`, `Buckets.drain_eq_flatten`, `drain_priority_ascending`, `drain_fifo_within_bucket`, `drained_once`, `drain_enqueue_length`, `drain_enqueue_mem`, **`Dispatcher.bucketPairs_enqueue`**, `enqueue_wf`, **`drain_projection`** |
| 3 | `Lib/Sexp.lean` | `Sexplib.Sexp.t`, hand-written `DecidableEq` (nested inductive), canonical quoted-atom printer + fuel-bounded parser; `SexpOf` over W3's `TypeDesc` | **`parse_print`** (exactly-once round trip), `parse_print_append`, **`print_inj`**, `instLinOrdSexp`, `record_shape`, `variant_shape_*`, **`record_inj`**, **`variant_inj`** |
| 4 | `Lib/Derived.lean` | `ppx_jane` as a contract: `Derived` + `Derived.Lawful` + the template `ofSexp_lawful`; `Fields.fold` and `Variants.toRank` over `TypeDesc` | `compare_eq_iff_eq`, `equal_iff_compare_eq`, `hash_eq_of_eq`, **`ofSexp_lawful`**, **`Fields.fold_visits_each_field_once`**, `Fields.fold_length`, **`Variants.toRank_eq_index`**, `toRank_inj`, `rank_lt_length` |
| 5 | `Lib/Stream.lean` | `Take` / `Channel` / `Stream` / `Sink` (bounded) / `Runner` (fuel-bounded) | **`pipeline_invariant`** (FIFO + no loss + no duplication in one equation), `delivered_prefix_step`, `delivered_prefix_emitted`, **`backpressure_bound`**, `step_blocks_when_full`, **`terminator_once`**, `terminator_only_at_halt`, `pull_halt_stable` |
| 6a | `Lib/Eio.lean` | Switch / Promise / fork / first / any as `Term`s over `OCaml5.Effect` + first-order state carriers | `fork_is_perform`, `scheduler_is_deep_handler`, `switchRun_is_try_with`, **`Promise.resolve_once`**, `Promise.await_one_shot` (= `Machine.takeCont_twice`), `await_second_resume_raises` (= `Machine.doResume_null`), **`Switch.exit_settles_every_fiber`**, `exit_cancels_on_failure`, `exit_finishes_on_success`, **`Race.settle_cancels_losers`**, `settle_cancels_each_loser_once`, `settle_spares_winner` |
| 6b | `Lib/Picos.lean` | Computation / Trigger / Ivar, plus the five effects as `perform`s | `await_is_perform` (×5), `scheduler_is_deep_handler`, **`Computation.settle_once`**, `tryReturn_succeeds_once`, `tryCancel_succeeds_once`, `isRunning_monotone`, `Trigger.signal_idem`, `onSignal_only_before_signal`, **`Ivar.fill_once`**, `read_after_fill`, `Ivar.resume_one_shot` (= `Machine.takeCont_twice`) |
| 7 | `LibTest.lean` | ~95 `#guard`s and two `decide`s across all nine | see §4 |

## 2. Three findings the seat had to record

1. **`Effect4/Channel/` does not exist.** The only `Channel` Lean modules in the tree are
   `vendor/foldlab/pinned/tree/formal/effect-core-v1/EffectCore/Channel/Core.lean` and
   `…/Channel/Stream.lean`, both **reserved empty module boundaries** (eleven lines: docstring,
   `namespace`, `end`). The only other trace of the shapes is the rc.112 census in
   `Effect4/StdLib/Rc112.lean:32-34` (digests of `src/Stream.ts`, `src/Sink.ts`,
   `src/Channel.ts`) and its export table. So `Lib/Stream.lean` is the **first** Lean carrier for
   these shapes, and it is taken from rc.112's own vocabulary. **W2 must match it**: a streaming
   reply *is* a `Channel Sexp ε` — a finite sequence of `emit` chunks and `pause` turns
   terminated by exactly one `halt`, built by `Stream.replyOfChunks` / `Stream.replyFailing`.
2. **`eio` and `picos` are not installed.** `opam switch list` gives `4.14.2`, `default`
   (ocaml 5.1.1) and `effect4`; `~/.opam/effect4/lib` holds only `stublibs` and `toplevel`, and
   neither `~/.opam/effect4/lib/{eio,picos}` nor `~/.opam/default/lib/{eio,picos}` exists. **No
   line of Eio's or Picos's source is cited anywhere in this work.** Both modules carry a
   "SOURCE STATUS — READ THIS BEFORE CITING" section and the refusal rows `W4-EIO-UNCITED` /
   `W4-PICOS-UNCITED`: every claim about their *implementation* is unverified until the switch is
   populated and the two files are re-derived against `lib_eio/core/*.ml` and `lib/picos/*.ml`.
   What is *not* uncited is the OCaml 5 side those files rest on.
3. **`Effect4.Deep.Dispatcher.insert` is `private`**, so it cannot be named from another module.
   The projection is nevertheless *proved*, not merely executed, via a **reflected unfolding
   equation** that holds by `rfl`: `Dispatcher.enqueue_unfold` states
   `((Dispatcher.mk (b :: rest) a).enqueue p t).buckets = if b.priority = p then … else … else
   b :: ((Dispatcher.mk rest a).enqueue p t).buckets`, expressing the private recursive call as
   `enqueue` on the tail. Everything about `enqueue` follows from it.

## 3. Status per module — laws proved, axioms, what remains

`#print axioms` on the headline theorems (run against the built `OCaml5.LibTest`):

| theorem | axioms |
| --- | --- |
| `Map.ext_find` | `propext` |
| `Map.ofAlist_toAlist` | `propext` |
| `Map.fold_visits_keys_in_order` | `propext` |
| `Map.find_merge` | `propext`, `Quot.sound` |
| `Set.ofList_toList` | `propext` |
| `Set.mem_union` | `propext`, `Quot.sound` |
| `Deque.fifo` | `propext` |
| `Buckets.drain_enqueue_length` | `propext`, `Quot.sound` |
| `Dispatcher.bucketPairs_enqueue` | `propext`, `Quot.sound` |
| `Dispatcher.drain_projection` | `propext`, `Quot.sound` |
| `Sexp.parse_print` | `propext`, `Quot.sound`, **`Classical.choice`** |
| `Sexp.print_inj` | `propext`, `Quot.sound`, **`Classical.choice`** |
| `SexpOf.record_inj` | `propext`, `Quot.sound`, **`Classical.choice`** |
| `SexpOf.variant_inj` | `propext`, `Quot.sound`, **`Classical.choice`** |
| `Derived.ofSexp_lawful` | `propext`, `Quot.sound`, **`Classical.choice`** |
| `Fields.fold_visits_each_field_once` | `propext` |
| `Variants.toRank_eq_index` | `propext`, `Quot.sound`, **`Classical.choice`** |
| `Runner.pipeline_invariant` | `propext` |
| `Runner.backpressure_bound` | `propext`, `Quot.sound` |
| `Runner.terminator_once` | `propext` |
| `Eio.Promise.resolve_once` | `propext` |
| `Eio.Switch.exit_settles_every_fiber` | `propext`, `Quot.sound` |
| `Eio.Race.settle_cancels_each_loser_once` | `propext` |
| `Picos.Computation.tryReturn_succeeds_once` | `propext` |
| `Picos.Ivar.fill_once` | `propext` |
| `Picos.Ivar.resume_one_shot` | `propext` |

**Open, and the one thing that did not meet the brief.** The brief asked for
`propext`/`Quot.sound` only. Twenty-one of the twenty-six headline theorems meet it; **five do
not**, all in the `Sexp` → `Derived` chain, and all through `by_cases` / `Classical.byCases`
introduced inside the round-trip and `Nodup` proofs (`readAtom_escape`'s three-way character
split, `indexOfName_*`'s `by_cases`, and `Variants.toRank_eq_index` through `List.Nodup`). The
fix is mechanical and was not attempted for time: replace each `by_cases h : c = d` on a
`DecidableEq` type by `match h : decide (c = d)` / `if h : … then … else …` (`Decidable.byCases`,
not `Classical.byCases`), and re-check. Nothing in the *statements* needs classical reasoning —
every predicate involved is decidable.

Per module, everything else stated in the docstrings is proved; nothing is stated-only, and there
is no `sorry` anywhere.

## 4. The witnesses (`LibTest.lean`)

About ninety-five `#guard`s and two `by decide` examples, sectioned per carrier. The ones that
carry weight:

* `#guard m1 == m2` — two maps built by *different* insertion orders are the same term:
  insertion-independent canonical form, executed.
* `#guard Map.ofAlist m1.toAlist == m1`, `#guard m1.fold [] (…) == [1,2,3]`.
* `#guard Buckets.drainTasks b1 == ["lo","hi","hi2"]` — ascending priority between buckets, FIFO
  within one.
* `#guard Dispatcher.bucketPairs dsp.buckets == bsp.entries` and
  `#guard (Effect4.Deep.Dispatcher.drain dsp).1 == Buckets.drainTasks bsp` — the same three
  `enqueue`s driven through the Deep dispatcher and through `Buckets`, at
  `Task Nat Nat Nat Nat Nat Nat Nat`, agreeing.
* `#guard Sexp.parse (Sexp.print sx) == some sx` on a sexp containing `"` and `\`.
* `#guard (Runner.run 40 (Runner.start reply 2)).sink.delivered == [row1, row2, row3]` with
  `#guard … .sink.ending == some none` — the daemon reply shape, driven to completion through a
  capacity-2 buffer.
* `#guard ((sw.settle 1).exit true).fibers == [(1, finished), (2, cancelled)]`,
  `#guard (race.settle 2).cancels == [1, 3]`,
  `#guard ((Promise.create.resolve 5).resolve 9).peek == some 5`,
  `#guard !(((Ivar.create).tryFill 7).1.tryFill 8).2`.

## 5. Refusal rows

Every row is written in the module docstring beside the construct it refuses.

| row | what is refused |
| --- | --- |
| `W4-ORD-INT-MAGNITUDE` | `compare`'s `int` magnitude — only the sign is modelled |
| `W4-ORD-PHYS-EQUAL` | `phys_equal` fast paths inside `Base`'s compare |
| `W4-ORD-POLY-COMPARE` | `Base.Poly.compare` / `Stdlib.compare` (plan §4.4 "no magic") |
| `W4-MAP-TREE-ORDER` | `Map.min_elt`/`max_elt`/`nth`/`rank`/the `Tree` module |
| `W4-MAP-OF-ALIST-EXN` | `of_alist_exn`'s `Duplicate_key` rejection (carrier is total, last-wins) |
| `W4-MAP-COMPARATOR-VALUE` | two maps at one key type under two different comparators |
| `W4-MAP-SHARING` | physical sharing, `merge_skewed`'s complexity promise |
| `W4-SET-TREE-ORDER`, `W4-SET-SEQUENCE` | as `Map`; `Set`'s `Sequence`-returning operations |
| `W4-DEQ-CAPACITY` | `Core.Deque`'s capacity, `blit`, `Exn` face, physical mutation |
| `W4-DEQ-ARMED` | `Dispatcher.armed` — a host fact, forgotten by the projection |
| `W4-DEQ-CROSS-DISPATCHER` | the cross-dispatcher flush order (existing Deep gap, `Fibers.lean:1130`) |
| `W4-SEXP-HUM`, `W4-SEXP-BARE-ATOM` | `to_string_hum`, whitespace-tolerant reading, unquoted atoms — normalisations, not bijections |
| `W4-SEXP-BINPROT` | `bin_prot`: a byte layout, not a term |
| `W4-SEXP-OPAQUE` | `sexp_of` for functional/abstract types (`<fun>`, `<opaque>` are not injective) |
| `W4-DERIVED-COMPARE-ORDER` | *which* total order `ppx_compare` picks |
| `W4-DERIVED-HASH-VALUE` | `ppx_hash`'s actual values, collisions, cross-version stability |
| `W4-DERIVED-OF-SEXP-PARTIAL` | `t_of_sexp` on malformed input (`Of_sexp_error`) |
| `W4-DERIVED-HIGHER-ORDER` | `Field.fset`, mutable `Fields.iter`, `Variants.map` |
| `W4-DERIVED-OTHER-PPX` | `ppx_enumerate`, `ppx_let`, `ppx_here` |
| `W4-STREAM-SEQUENCE` | `Core.Sequence` (a closure pair; cannot be first-order) |
| `W4-STREAM-EIO-STREAM`, `W4-STREAM-EIO-BUF` | `Eio.Stream` as a concurrency object; `Buf_read`/`Buf_write` |
| `W4-STREAM-NO-RETRY` | **at-least-once**: no retry model is defined, so none is claimed |
| `W4-STREAM-CHUNK-BOUNDARY` | chunk boundaries as semantics |
| `W4-EIO-UNCITED`, `W4-PICOS-UNCITED` | every claim about Eio's / Picos's *implementation* (not installed) |
| `W4-EIO-DOMAINS`, `W4-PICOS-ATOMIC` | multi-domain, the continuation CAS, atomics |
| `W4-EIO-HOST`, `W4-PICOS-STD` | `Flow`/`Net`/`Path`/clock, `Picos_io` — the host boundary |
| `W4-EIO-CANCEL-TIMING`, `W4-PICOS-ATTACH` | *when* cancellation propagates (rc.112 vs Deep already disagree here) |
| `W4-EIO-ON-RELEASE` | `Switch.on_release` finalizer order |
| `W4-PICOS-EXN-BT` | `Exn_bt` — the machine has no backtraces |

## 6. What W1/W2/W3 should take

* **W1 (port).** `Buckets = Map Nat (Deque τ)` is justified: `Dispatcher.bucketPairs_enqueue` +
  `drain_projection` say replacing the hand-rolled bucket list changes no delivered task and no
  order. Cite `Buckets.drain_priority_ascending`, `drain_fifo_within_bucket`, `drained_once`,
  `drain_enqueue_length`.
* **W2 (daemon).** The streaming reply is `Channel Sexp ε`, built by `Stream.replyOfChunks` /
  `Stream.replyFailing`, consumed by `Runner` with a stated capacity. Cite
  `Runner.pipeline_invariant`, `backpressure_bound`, `terminator_once`. **No at-least-once**
  (`W4-STREAM-NO-RETRY`) — if redelivery is wanted, an acknowledgement alphabet has to be added
  here first.
* **W3 (profile allowlist).** Each module's "What each definition stands for" table is the
  profile's semantic column: `Base.Map.find`/`set`/`fold`/`to_alist`/`of_alist_reduce`/`merge`,
  `Base.Set.*`, `Core.Deque.enqueue_back`/`dequeue_front`/`to_list`, `Sexplib.Sexp`,
  `ppx_sexp_conv`/`ppx_compare`/`ppx_hash`/`fieldslib`/`variantslib`. A construct not in a table
  is a refusal row, not a dependency.

## 7. Next

1. Remove `Classical.choice` from the five `Sexp`/`Derived` theorems (§3) — mechanical.
2. Populate the `effect4` switch, then re-derive `Lib/Eio.lean` and `Lib/Picos.lean` against real
   sources and replace `W4-EIO-UNCITED` / `W4-PICOS-UNCITED` with line citations.
3. Land the streaming carrier at `Effect4/Channel/` (or wherever the Path-D home ruling puts it),
   replacing the two reserved empty modules.
