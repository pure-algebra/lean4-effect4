# Receipt: seat R1, the store (`ocaml/engine/cas/`)

## The one thing to know

Two defects I reproduced remain at the checked open (`E4_disk.open_`), and both wait on one
ruling. In the first, a store damaged below its published end saves an index that stops at the
damage, yet claims the whole published range. After the damage is repaired, the open succeeds
and a published node reads as absent. In the second, a commit with nothing staged publishes the
head of an empty segment as the durable end. The next checked open then refuses the healthy
store. Both turn on one rule that no module owns: where a scan counts as reaching the published
end (see "Open", O1 and O2). The four assigned fixes landed to the coherence note's shapes. The log's three fixes are held, and `e4_wal.ml` is
untouched. One commit goes beyond the brief: it fixes a data loss, where an unlistable pack
directory made the open truncate a committed segment (`4d69afc18`).

## Base and head

- Base: `fb3a1daa0`. During the seat the coordinator committed `0bf9c986d` and `bea584f1b`,
  research notes only. My first commit sits on `bea584f1b`.
- Head: the last commit that touches this receipt. The coordinator's `43d45df6f`, research
  notes only, landed between `9b0386c1e` and the receipt.
- Evidence kind: finite runs on this Mac (Darwin 25.2, user 501), host-only. Nothing here is
  proved, and no power-loss experiment was run.

## The commits

| Commit | Fix | Files |
| --- | --- | --- |
| `7593dbbe6` | A3.1, one verifier | `e4_cas.ml`, `e4_cas.mli`, `e4_cache.mli`, `e4_pack.mli`; tests `test_cas.ml`, `test_crash.ml`, `test_cache.ml`, `test_checkpoint.ml`, `disk_test_support.ml`, `bench_cas.ml` |
| `17fa9a83c` | A2.1, one header parse | `e4_pack.ml`, `e4_pack.mli`, `test/test_pack.ml` |
| `68f81d1bb` | A3.3, one durable file step | new `e4_file.ml`, `e4_file.mli`; `e4_control.ml`, `e4_control.mli`, `e4_disk.ml`, `e4_disk.mli`, `e4_index.ml`, `e4_index.mli`, `e4_pack.ml`, `e4_pack.mli`, `e4_cas.mli`; tests `test_disk.ml`, `test_index.ml` |
| `4d69afc18` | beyond the brief: an unlistable pack directory | `e4_pack.ml`, `e4_pack.mli`, `test/test_disk_damage.ml` |
| `9b0386c1e` | B2.1, frame tags | `e4_shape.ml`, `e4_shape.mli` |

Every code path is under `ocaml/engine/cas/`, and this receipt is the only other file.
`stm_disk.ml` needed no change.

## Each fix, red then green

**A3.1.** As the note rules, `verify`, `verify_error`, `verify_error_word` and the
`verify_on_open` option are deleted. The store's one verification is `checked_image`, which
`E4_disk.open_` runs. `verify_node` now answers `(unit, admission) result` over the resident
bytes, their digest, `E4_node.decode` and `admissible`.
- Reproduced before: on Codex's tag corruption, `verify` answered `Ok` and the verified open
  succeeded (`test_cas`: 2 failures in 121 checks).
- Tested after: the checked open refuses the corruption as `record 0:27`, and `verify_node`
  refuses the address.
- Test X2(b1) is now a refused `E4_disk.open_` (`Fault (Corrupt _)`). X2(b2) is refused at the
  record's own offset.
- G7 now reads Lean's `Store.verify` words through the checked open, and 9 of 9 rows agree.
  `Fault Corrupt` reads as `digestMismatch`, and `Fault Root` reads as `rootUnresolved`.
- Lean forges G7's two result rows with forward references (`g7ResultCases` in
  `src/OCaml5/Tools/CasGoldens.lean`). The checked open admits in write order, so it refuses
  them first, as `dangling` at a node the store holds later. The test names exactly those two
  rows, and CS7's text states the difference.

**A2.1.** One `record_span` parses a record's header for `read_full` and `step_at`. It checks
the length by subtraction. Each caller maps its fault to its own words, and the reader's
mapping checks its range the same way.
- Reproduced before: `test_pack` had 15 failures in 94 checks. Four of the five lengths raised
  or scanned to a negative offset, and `max_int - 100` passed, as Codex logged.
- Tested after: 94 of 94 checks pass.
- Codex's own probe, `a2/pack_boundary.ml`, ran from a scratch copy. It now prints
  `Truncated(seg=0,off=27)` and `Short(seg=0,off=27)` for all five lengths, and `Ok` and `Eof`
  for the restored file.

**A3.3.** `E4_file` owns the durable steps: `sync_dir` and `replace` (tmp, sync, rename,
directory sync). It swallows nothing.
- It replaces the pack's and the index's `fsync_dir` copies, `E4_control.commit`'s body, and
  `E4_index.save`'s replace steps.
- `E4_disk`'s three copies of the exception map are now one `fault_of_exn`.
- The index stays best effort only in `E4_cas.close`, and both interfaces say why.
- Reproduced before: with the store directory at mode 0300, `E4_disk.commit` acknowledged the
  commit (`test_disk`: "a failed directory sync was acknowledged").
- Tested after: the commit is refused as `Fault (Io _)`, the writer is closed, and a reopen
  keeps what the first commit acknowledged.

**Beyond the brief, `4d69afc18`.** `list_segments` read every `Sys.readdir` failure as "no
segments".
- Reproduced before: with `pack/` at mode 0300, the checked open recreated segment 0 with
  `O_TRUNC`, and only then refused. In my probe its committed bytes went from 121 to 27; in
  `test_disk_damage` the pack's evidence changed.
- Tested after: the open is refused as `Fault (Io _)`, and the pack's evidence is unchanged.

**B2.1.** `E4_shape`'s six tag bindings are deleted, and the literal `2` (the nat tag) goes too.
Each use names `Eff_frame`'s constant. No byte moves.

## Commands and results

All dune commands ran as `opam exec --switch=effect4 -- dune …` from `ocaml/`.

| Command | Result |
| --- | --- |
| `dune build`, at the base and after every fix | clean |
| `dune test engine/cas --force`, at the base | all pass |
| the red runs, before each fix | as listed under each fix above |
| `dune test engine/cas --force`, after the last fix | exit 0; `test_bytes` 158, `test_wal` 59, `test_control` 88, `test_pack` 94, `test_cas` 124, `test_crash` 55, `test_index` 69, `test_cache` 56, `test_checkpoint` 116 checks, all pass; `test_disk`, `test_disk_damage`, `test_disk_boundary`, `test_disk_kill` (6 cuts), `test_disk_stm` (300 cases) and `test_shared_facts` pass |
| `dune test engine/test/stm --force`, after A3.3 | all pass; `E4_disk` S1, P1, K1 and K2 pass, and its S2 red fails as designed |
| `dune fmt`, before each commit | applied |
| `make check-ocaml`, once, at the end, from the repository root | exit 0 in 28 s; it stamped the ocaml lane `980ba3c2a938` (17.7 s); `native` and `compiler` reused their shared results |

The benches ran three times before the first change and three times after the last. Each figure
is the mean of the three runs, from `dune exec engine/cas/test/bench_wal.exe` and
`dune exec engine/cas/test/bench_commit.exe -- 400`.
The raw output of each run is in `bench/`.

| Bench cell | Before | After | Change |
| --- | ---: | ---: | ---: |
| `bench_wal` B8, 256 B rows, batch 512 (rows/s) | 717,144 | 766,289 | +6.9% |
| `bench_wal` B8', 256 B rows, batch 4096 (rows/s) | 856,541 | 870,902 | +1.7% |
| `bench_wal` 1 KiB rows, batch 512 (rows/s) | 242,162 | 230,895 | -4.7% |
| `bench_wal` B9, replay of 51,200 rows (rows/s) | 1,145,719 | 1,091,184 | -4.8% |
| `bench_commit`, first 100 of 400 commits (ms) | 0.292 | 0.298 | +2.1% |
| `bench_commit`, last 100 of 400 commits (ms) | 0.265 | 0.268 | +1.1% |

`e4_wal.ml` did not change, so the log's movement is this host's noise. B8, B8' and B9 meet
their bounds before and after. A store commit now makes one more system call, the `unlink` of an absent
tmp, and the bench shows no cost from it.

## What moved on disk

- No format version and no byte layout changed: the pack, the control file, the index file and
  the log are byte for byte as before.
- The index snapshot's tmp is now created read-only (0444) at once, instead of being written and
  then made read-only. The published file is 0444, as before (IX9).
- A failed directory sync, and the failed open of a directory to sync it, now raise. Before, both
  were ignored.

## Property text changed

- `e4_cas.mli`, properties: CS5 (a failed sync fails the commit), CS10, D4 and D9.
- `e4_cas.mli`, CS7: the checked image is the verification, and it admits in write order.
- `e4_cas.mli`, declarations: `open_opts`, `verify_node`, and `close` (the best-effort index).
- `e4_pack.mli`, properties: PK3 (an unlistable directory is a failure), PK8 and the new PK10
  (`record_span`).
- PK8 now says the head and the directory are synced at rotation. Its old text said the head
  was staged, which the code did not do.
- `e4_pack.mli`, declarations: `sync`, `open_at`, `segments` and `read_at`.
- `e4_cache.mli`: CA6 (verification is `checked_image` and `verify_node`).
- `e4_control.mli`: CF4 is new. In `e4_control.ml`, the best-effort directory sync, D7, ends.
- `e4_index.mli`: `save` (it raises; the cache's one caller catches).
- `e4_disk.mli` and the `e4_disk.ml` header: a failed sync is a failed commit.
- `e4_file.mli`: F1 to F3, new.
- `e4_shape.mli`: the dependency on `Eff_frame` for the tags.

## The fault-injection seam

I chose none. The note forbids a seam, and A3.3's red control needs none. A directory that
cannot be opened takes the same path as a failed sync, because nothing catches either. Two
things this does not establish:
- No test makes `fsync` itself fail. I assume an `fsync` error raises `Unix.Unix_error` as the
  failed open does, since the code catches neither.
- The existing `?hook:(commit_point -> unit)` was not needed.

## Where I departed from the note's sketches

- `record_span` answers `(len, header)`, not `len`. Both callers need the 41 header bytes for
  the digest and the CRC, and returning them saves a second read of each record.
- The note's comment label "PK-R" is PK10 in the pack's property list.
- `E4_file.replace` first removes a stale tmp; an absent tmp is no failure. A read-only tmp
  left by a stopped index save would otherwise block the next save (IX9, `test_index` F12).
- `E4_disk.fault_of_exn` answers `E4_fault.t option`. `commit` keeps its own
  `Invalid_argument` to `Capacity` arm, which was never among the three copies.
- The log's `fsync_dir` stays; see O3.

## Open

**O1. A partial index saved as covering the published end.** Reproduced at `9b0386c1e` by a
scratch probe.
1. Commit a schema and two exports through `E4_cas`, then close.
2. Write `X` over the second record's tag byte, and delete `index/000000.idx`.
3. `E4_disk.open_` refuses (`record 0:121 durable boundary: Bad_tag(…)`). Its close saves
   `index/000000.idx`, from a scan that stopped at the damage.
4. Restore the tag byte. `E4_disk.open_` loads the saved file, whose `covers` equals the
   published end, and succeeds.
5. `E4_disk.read` of the third node answers `Ok None`, though the node is published and intact.

The cause: `E4_cas.rebuild_index` ignores where its walk stopped and stores the index as covering
the published end, and `E4_cas.close` saves it so. The brief asked that `rebuild_index` never
mark a partial index finished. The note's A3.1 shape does not cover this, so I left it.

**O2. The head of an empty segment, published.** Reproduced at `9b0386c1e` by a scratch probe.
1. Commit one node, then close.
2. Put a valid 27-byte head of segment 1 at `pack/000001.pack`. A crash leaves this shape when
   it falls after rotation synced the new head and before the staged record was flushed.
3. `E4_cas.open_rw`, then `commit` with nothing staged: the control file now publishes `1:27`.
4. `E4_disk.open_` refuses the healthy store: `record 0:121 durable boundary: Eof`.

The cause: `E4_pack`'s walk hops into the empty segment, so the pack's end is the head `1:27`.
`checked_image` compares the end of the last record, `0:121`, with the published end by
equality.

Options for O1 and O2:
- (a) `E4_pack` owns the rule. Its walk already tracks the place it reached, hops included. A
  bounded scan would answer whether it reached the published end exactly.
  - `checked_image`, `rebuild_index`, `addresses` and the two derived caches would all use it.
  - `rebuild_index` would refuse with `Store_error` when it falls short.
  - This closes O1 and O2 together. It adds one function to `E4_pack` and deletes
    `checked_image`'s own comparison.
- (b) The pack never publishes a segment head: its end names the end of the last durable record.
  That closes O2 at the source. O1 then needs `rebuild_index` to refuse a short walk.
- (c) Leave both, and document that an operator deletes `index/` after any repair of a pack.

Recommendation: (a). It gives the rule one owner, in the module that knows the hops. Closing O1
with today's equality rule would refuse O2's healthy stores in one more place.

**O3. The log, held.** A3.2, A3.4 and A5.1 are not started, as the coordinator ruled.
- `E4_wal.fsync_dir` still swallows. A raising sync inside `do_rotate` would leave `w_fd` closed
  before its replacement, so the writer would write to a closed or reused descriptor. It waits for
  the log's failure rule, or for the log's retirement (coherence note §5).
- `E4_wal.segment_files` reads a failed `Sys.readdir` as no segments, the shape `4d69afc18`
  fixed in the pack. `open_` would then create segment 0 with `O_APPEND`, and an existing segment
  would gain a second head.
- Data for the note's §5 condition, from the benches above, on this host only:
  - a one-node `E4_disk` commit costs 0.27 ms (`bench_commit`, the mean of the last 100);
  - a one-row log commit costs 0.021 ms (`bench_wal`, 256 B rows, batch 1);
  - a 512-row log commit costs 0.67 ms (`bench_wal`, 256 B rows, batch 512).
- Both fsync once per commit, and I assume macOS `fsync` does not flush the drive's cache. These
  figures measure no run's journal rate, and `bench_commit` tries no multi-node transaction.

**O4. Smaller items.**
- `E4_cas.open_rw` keeps its own exception map, a second owner of the `Io` and `Store` arms.
  `E4_cas` cannot call `E4_disk`. An option: `E4_cas` owns `fault_of_exn`, and `E4_disk` calls it.
- The pack still ignores a failed `Sys.remove` in three places: during recovery's truncation, in
  `truncate_to`, and of a trailing headless segment. A segment left behind can be walked by a
  later recovery. These are not among the note's sites.
- G7's two result rows assert only that both judgments refuse. The checked open applies the
  result rule through `admissible`, which G8 tests through `put`. Exact verdicts would need
  children-first variants of those two stores in `CasGoldens.lean`, a Lean change.
- `writer_source.read` allocates before it checks a range. Every caller passes a length that
  `record_span` bounded, so no stored length reaches it unchecked. I left it unchanged.

## Proposed decisions rows

- The owner of "a scan reached the published end", from O1's options; my recommendation is (a).
- A record that the store's verification is the checked image (A3.1). It differs from Lean's
  `Store.verify` on a forged forward reference, and G7 states the difference.
