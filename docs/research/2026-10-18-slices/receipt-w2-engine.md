# 2026-10-18 seat 2 receipt, wave 2: the engine's reference carriers and test hygiene (C4, H3, H5, H8)

Status: receipt (history, not authority). Seat 2 of wave 2, from `wave2.md` §4.3 and §6.

**The one thing to know before merging:** C4 deleted `Ref`, and its commit edits seat 3's
`test/todo/test_todo.ml` and `todo/dune`: expect one small conflict with C5.
The gate's `stm_admit` P1, which no change here reaches, fails now and then on a loaded host
(§ A finding outside the brief).

## Base and head

- Branch `seat/w2-engine`, worktree `/Users/pooks/Dev/wt-w2-engine`.
- Base `b83188cb2` (`refactor/phase1-phase3`).
- Head: the commit that adds this receipt. Its parent is `6ceee8b11`.

## Commits and changed files

| Step | Commit | What changed |
| --- | --- | --- |
| C4 | `461befef3` | `api_engine_ref.ml`, `E4_engine.Ref` and six list twins deleted; the tests compare with the generated machine; the 56 mutants, the runner and the tape check under `w2-engine-mutants/` |
| H3 | `cf53ddea6` | `Corpora`, `E4_diff` and `E4_memo_list` move to the private library `e4_reference` |
| H5 | `2600b89b1` | `E4_check` and its test; 28 tests move onto it; the six scratch variables retired |
| H8 | `9c614e057` | `corpora.mli`, `e4_memo_list.mli` and `disk_test_support.mli` |
| C4, the campaign's findings | `d01646fa6` | PP3 and PP7 compare nodes on the tree; T9 reads `of_list`; MM6a states its order |
| C4, two headers | `6ceee8b11` | `test_diff.ml` and `e4_instance.ml` say what the campaign found, not more; `summarize.py` keeps `stm_admit` out of the verdicts |
| receipt | the head | this file; `results-A.tsv`, `results-B.tsv`, `results-A-recheck.tsv`, `stm_admit-p1.txt` and `stm_load.py`; `summarize.py` escapes a pipe in a cell and counts the `Ref` catches |

The files, by step:

- C4 deleted `ocaml/engine/api_engine_ref.ml`, `e4_table_list.ml`, `e4_trace_list.ml`,
  `e4_buckets_list.ml`, `e4_ppath_list.ml`, `e4_env_list.ml` and `e4_fibers_view_list.ml`.
  - It edited `e4_engine.ml`, `e4_engine.mli`, `e4_engine_intf.ml`, `e4_instance.ml`,
    `api_engine_inst.ml` and four carrier headers (`e4_table.mli`, `e4_ppath.mli`,
    `e4_env.mli`, `e4_fibers_view.mli`) in `ocaml/engine/`.
  - It edited `dune`, `test_diff.ml`, `test_engine.ml`, `test_serve.ml`, `test_replay_steps.ml`,
    `test_stable_step.ml`, `e4_engine_bench.ml` and the four `prop_*` files that read a twin in
    `ocaml/engine/test/`, and `scenarios/test_scenarios.ml`.
  - It edited `test_mask.ml`, `test_pool.ml`, `test_queue.ml`, `test_semaphore.ml` and
    `test_todo.ml`, each with the `dune` beside it.
  - It force-added `docs/research/2026-10-18-slices/w2-engine-mutants/`: 56 patches,
    `make_mutants.py`, `campaign.py`, `summarize.py`, `lines.py` and `tapecheck/`.
- H3 renamed four files into `ocaml/engine/test/reference/`.
  - `corpora.ml` moved unchanged, its JSON calls as they were for seat 1.
  - `e4_diff.ml`, `e4_diff.mli` and `e4_memo_list.ml` each gained one module alias.
  - It added `reference/dune` and edited `test/dune` and the header of `e4_memo.mli`.
- H5 added `ocaml/engine/test/check/`: `dune`, `e4_check.ml`, `e4_check.mli`, `test_check.ml`.
  - It edited the 28 tests of § H5 and their `dune` files.
  - It edited `cas/test/disk_test_support.ml`, `cas/test/bench_index.ml` and
    `ocaml/engine/tools/run-bench.sh`.
- H8 added `test/reference/corpora.mli`, `test/reference/e4_memo_list.mli` and
  `cas/test/disk_test_support.mli`, and moved each header from the `.ml` into its interface.
- The findings commit edited `prop_point.ml`, `prop_table.ml`, `prop_memo.ml`, `test/dune` and
  `e4_table.mli` (the law T9).

## C4: the mutant campaign

### Method

1. `make_mutants.py` writes each mutant as a patch: one exact snippet of one carrier replaced.
   The 56 mutants cover the seven fast carriers: `E4_table` (T01-T12), `E4_trace` (R01-R06),
   `E4_memo` (Y01-Y07), `E4_buckets` (B01-B08), `E4_ppath` (P01-P07), `E4_env` (V01-V07) and
   `E4_fibers_view` (F01-F09).
2. `campaign.py` applies one patch to a copy of the tree, runs `dune build @engine/runtest
   --force`, records each failing test and each `FAIL` line, and reverts the patch.
3. It runs on two trees. Tree A is the base `b83188cb2`, with `Ref`. Tree B is the C4 commit
   `461befef3`, without `Ref`.
4. `summarize.py` joins the two result tables. A tree A check is a `Ref` check when it compares
   with `Ref` or runs on it.

The tables come from runs in copies of the trees under the scratch directory, apart from the
worktree. Earlier runs in the worktree were stopped, and their rows are not in the tables.

- Tree A's run went in one pass.
- Tree B's run went in two passes in one copy. The first pass was stopped during B04, to free
  the host for the C4 gate.
- Between the passes, B04's patch was reverted, the copy's `ocaml/engine` was compared with the
  worktree's (no difference), and the copy's build was cleaned.
- The second pass ran B04 to Y07. So B01-B03 come from the first pass.

A test that gives no verdict within 600 s counts as failing.
After each mutant, the tree B run and the recheck of tree A compare dune's copies of the
carriers with their sources. A run whose copies differ is INVALID, and no row is.
The tree A run predates that check; § Commands gives the recheck of its two rows at risk.

### The decision rule's two clauses, measured

- Every mutant that a `Ref` check caught in tree A is caught in tree B (the table's summary
  line below).
- Each property test keeps a model, written in the test from Lean's `List` operations.
  `prop_memo` keeps `E4_memo_list`, since that twin models Lean's duplicates.
  `test_buckets` keeps `dispatcher_ref.ml`, which was already its model.

The differential draws the same tapes on the generated machine as it drew on `Ref`.
`tapecheck/tapecheck.ml` compares the two draws for every program and seed of `test_diff`.
Its log: 2,132 tapes the same, none different, 67,360 decisions.

### The table

Run `python3 docs/research/2026-10-18-slices/w2-engine-mutants/summarize.py` for it.
`results-A.tsv` and `results-B.tsv` hold each row's failing checks.

| Mutant | What it breaks | Caught in A by Ref checks | Caught in A by other checks | Caught in B (no Ref) |
| --- | --- | --- | --- | --- |
| B01 | a new lower priority bucket goes after the higher one (ascending order broken) | test_diff | test_buckets | test_buckets, test_diff |
| B02 | drain does not reverse the back list (FIFO broken past two tasks) | test_diff | test_buckets, test_scenarios | test_buckets, test_diff, test_scenarios |
| B03 | enqueue does not arm | — | test_buckets | test_buckets |
| B04 | drain keeps the drained tasks | — | test_buckets | test_buckets |
| B05 | length counts the front list only | — | test_buckets | test_buckets |
| B06 | to_list does not reverse the back list | — | test_buckets | test_buckets |
| B07 | a task at a bound priority goes to the front of its bucket | test_diff, test_pool, test_semaphore | test_buckets, test_scenarios | test_buckets, test_diff, test_pool, test_scenarios, test_semaphore |
| B08 | priority -1 is admitted (the refusal is off by one) | — | test_buckets | test_buckets |
| F01 | set leaves the completed view stale when an exit changes | test_diff, test_engine, test_mask, test_pool, test_queue, test_semaphore | prop_fibers_view, test_engine, test_stable_step | prop_fibers_view, test_diff, test_engine, test_mask, test_pool, test_queue, test_semaphore, test_stable_step |
| F02 | view_put inserts at the wrong position (the view loses its order) | test_diff, test_engine, test_mask, test_pool, test_queue, test_semaphore | prop_fibers_view | prop_fibers_view, test_diff, test_engine, test_mask, test_pool, test_queue, test_semaphore |
| F03 | add does not move the count | test_diff, test_engine | prop_fibers_view, test_engine | prop_fibers_view, test_diff, test_engine |
| F04 | map derives the view from the old table (a stale input) | — | prop_fibers_view | prop_fibers_view |
| F05 | for_all answers exists | test_diff | prop_fibers_view, test_scenarios | prop_fibers_view, test_diff, test_scenarios |
| F06 | set on an absent id inserts it (on the path with no exit anywhere) | — | prop_fibers_view | prop_fibers_view |
| F07 | completed answers descending | test_diff, test_engine, test_mask, test_pool, test_queue, test_semaphore | prop_fibers_view | prop_fibers_view, test_diff, test_engine, test_mask, test_pool, test_queue, test_semaphore |
| F08 | to_list answers descending | — | prop_fibers_view, test_scenarios | prop_fibers_view, test_scenarios |
| F09 | add of a fresh fiber that has already exited leaves the view without it | — | prop_fibers_view | prop_fibers_view |
| P01 | snoc descends from the root instead of the current node | test_diff, test_engine, test_mask, test_pool, test_queue, test_semaphore | prop_point, test_engine, test_kit, test_mask, test_pool, test_queue, test_replay_steps, test_scenarios, test_semaphore, test_serve, test_todo, test_transcript | prop_point, test_diff, test_engine, test_kit, test_mask, test_pool, test_queue, test_replay_steps, test_scenarios, test_semaphore, test_serve, test_todo, test_transcript |
| P02 | to_list answers the spine reversed | test_diff | prop_point, test_todo | prop_point, test_diff, test_todo |
| P03 | append adds its indices in reverse order | test_diff | prop_point, test_todo | prop_point, test_diff, test_todo |
| P04 | walk stops one step short | — | prop_point | prop_point |
| P05 | length counts the root as a step | — | prop_point | prop_point |
| P06 | snoc off the tree comes back to the root | — | prop_point | prop_point |
| P07 | root answers the current node | — | — | — |
| R01 | emit appends one batch in reverse order | test_diff, test_engine, test_mask, test_pool, test_queue, test_semaphore | prop_trace | prop_trace, test_diff, test_engine, test_mask, test_pool, test_queue, test_semaphore |
| R02 | emit drops the first event of each batch | test_diff, test_engine, test_mask, test_pool, test_queue, test_semaphore | prop_trace | prop_trace, test_diff, test_engine, test_mask, test_pool, test_queue, test_semaphore |
| R03 | emit [] resets the trace | — | prop_trace | prop_trace |
| R04 | to_list answers newest first | test_diff, test_engine, test_mask, test_pool, test_queue, test_semaphore | prop_trace, test_checkpoint | prop_trace, test_checkpoint, test_diff, test_engine, test_mask, test_pool, test_queue, test_semaphore |
| R05 | nth_opt reads one row late (off by one) | — | prop_trace | prop_trace |
| R06 | length counts one row too many | test_diff, test_engine | prop_trace, test_checkpoint | prop_trace, test_checkpoint, test_diff, test_engine |
| T01 | set on an absent key inserts it (set behaves as add; the count is not moved) | — | prop_table | prop_table |
| T02 | add on a big table never moves the count (cardinal stale after the first add) | test_diff, test_pool, test_queue, test_semaphore | prop_table, test_checkpoint, test_pool, test_queue, test_scenarios, test_semaphore | prop_table, test_checkpoint, test_diff, test_pool, test_queue, test_scenarios, test_semaphore |
| T03 | add counts a replacing add as fresh (cardinal off by one after add on a bound key) | — | prop_table | prop_table |
| T04 | remove does not move the count | — | prop_table | prop_table |
| T05 | bindings (and so to_list) answer descending | test_pool, test_queue, test_semaphore | prop_table, test_checkpoint, test_scenarios | prop_table, test_checkpoint, test_pool, test_queue, test_scenarios, test_semaphore |
| T06 | filter_map answers descending (the reverse is dropped) | — | prop_table | prop_table |
| T07 | for_all answers exists | — | prop_table | prop_table (and stm_admit, not reached) |
| T08 | map leaves a big table unchanged | — | prop_table | prop_table |
| T09 | find_opt reads the neighbouring key (off by one) | test_diff, test_engine, test_mask, test_pool, test_queue, test_semaphore | prop_table, test_engine, test_kit, test_mask, test_pool, test_queue, test_scenarios, test_semaphore, test_todo | prop_table, test_diff, test_engine, test_kit, test_mask, test_pool, test_queue, test_scenarios, test_semaphore, test_todo (and stm_admit, not reached) |
| T10 | set keeps the old table when a key is present (the physical test inverted: a stale write) | test_diff, test_engine, test_mask, test_pool, test_queue, test_semaphore | prop_table, test_engine, test_kit, test_mask, test_pool, test_queue, test_scenarios, test_semaphore | prop_table, test_diff, test_engine, test_kit, test_mask, test_pool, test_queue, test_scenarios, test_semaphore |
| T11 | remove that shrinks to the small arm keeps the removed binding (the old map) | — | prop_table | prop_table |
| T12 | of_list writes with set, which never inserts (an empty table) | — | — | — (and stm_admit, not reached) |
| V01 | get reads one binding too deep (off by one) | test_diff, test_engine, test_mask, test_pool, test_queue, test_semaphore | prop_point, test_engine, test_kit, test_mask, test_pool, test_queue, test_scenarios, test_semaphore, test_serve, test_todo, test_transcript | prop_point, test_diff, test_engine, test_kit, test_mask, test_pool, test_queue, test_scenarios, test_semaphore, test_serve, test_todo, test_transcript |
| V02 | snoc does not move the cached length | test_diff, test_engine, test_mask, test_pool, test_queue, test_semaphore | prop_point, test_engine, test_kit, test_mask, test_pool, test_queue, test_scenarios, test_semaphore, test_serve, test_todo, test_transcript | prop_point, test_diff, test_engine, test_kit, test_mask, test_pool, test_queue, test_scenarios, test_semaphore, test_serve, test_todo, test_transcript |
| V03 | take drops from the wrong end | — | prop_point | prop_point |
| V04 | append binds its values in reverse order | test_diff, test_engine, test_pool, test_queue, test_semaphore | prop_point, test_engine, test_kit, test_pool, test_queue, test_scenarios, test_semaphore, test_transcript | prop_point, test_diff, test_engine, test_kit, test_pool, test_queue, test_scenarios, test_semaphore, test_transcript |
| V05 | to_list answers newest first | — | prop_point | prop_point |
| V06 | of_list keeps the list unreversed | — | prop_point | prop_point |
| V07 | take keeps the old cached length | — | prop_point | prop_point |
| Y01 | insert over a bound key overwrites it (the last insert wins, not the first) | — | prop_memo | prop_memo |
| Y02 | update writes into an empty table (every other entry dropped) | — | prop_memo | prop_memo |
| Y03 | delete removes nothing | test_diff | prop_memo | prop_memo, test_diff |
| Y04 | compare_path puts a prefix last (still a total order) | — | — | — |
| Y05 | compare_call answers equal when one call is a proper prefix of the other (two keys collide) | — | prop_memo | prop_memo |
| Y06 | lookup starts with fuel \|world\| - 1 (a chain as long as the world is cut short) | — | prop_memo | prop_memo |
| Y07 | insert never binds a fresh key (the membership test inverted) | test_diff | prop_memo | prop_memo, test_diff |

56 mutants.  Caught by a Ref check in A: 24.  Of these, caught by a check without Ref in A too: 24.  Caught by a Ref check in A and by nothing in B: none.  Caught in A and by nothing in B: none.  Caught by nothing in either tree: P07, T12, Y04.

### What the campaign found

- No mutant needs `Ref`. In tree A, 24 mutants failed a `Ref` check, and each of them also
  failed a check that runs no `Ref` (the table's summary line).
- Three mutants passed every test in both trees. Each showed a check weaker than its name, or
  no check at all.
  - P07, a path's root answers its current node. PP3 walked one path, which left the tree at
    its first step under the seed. So no node on the tree was ever compared.
  - T12, `of_list` writes with `set`: no check read `E4_table.of_list`.
  - Y04, a prefix sorts last: MM6a compared the order with `compare_key` itself.
- P01 passed PP3 and PP7 for the reason P07 passed PP3.
- Commit `d01646fa6` repairs PP3, PP7 and MM6a, and adds T9. Each of the four mutants, applied
  by hand and then reverted, fails a repaired or added check (§ Commands).
- Under the engine's projection, three mutants change nothing the machine shows:
  - B04: the machine discards the dispatcher that `drain` answers and installs `D.empty`.
  - P07: `sh_node_at` walks from the root whenever the roots differ, so only its speed moves.
  - Y04: every engine, `Gen` included, sorts its memo paths with `E4_memo.compare_key`.
  `test_buckets` catches B04, and the repaired PP3 and MM6a catch P07 and Y04.

### Where `Ref` was a second instance

Every whole-report comparison with `Ref` now compares with the generated machine, `Gen`:

| Test | The check |
| --- | --- |
| `test_diff` | every projection at every position, Gen against Fast |
| `test_engine` | G0's 14 programs, `Fast = Gen, whole report`; the layer environment on both; the W1 and W2 bench rows measure Gen |
| `test_mask`, `test_pool`, `test_queue`, `test_semaphore` | M2/M3, P2/P3, Q2/Q3, S2/S3 on Gen |
| `test_todo` | T5 to T8 and T14 to T17 on Gen |

Every check that ran on `Ref` alone and compared with no other instance goes. Each ran the
shared drive loop, prelude and generated bodies over the list twins, and the `Fast` half of
each remains. The PASS and FAIL lines of each test, counted at the base and at C4, from each
test executable run alone:

| Test | Base | C4 | What went |
| --- | ---: | ---: | --- |
| `test_engine` | 184 | 113 | G0 on `Ref` and its drive-loop check; the creation origin, the clocks, the numeric ingress and the multiplication profile on `Ref` |
| `test_scenarios` | 271 | 139 | every run on `Ref` |
| `test_serve` | 72 | 36 | the `Ref` half |
| `test_replay_steps` | 41 | 29 | the laws on `Ref` |
| `test_diff` | 32 | 31 | the classification control of the `Ref` slot |
| `prop_trace` | 9 | 8 | TR8, the twin's agreement, which TR1 states against Lean's list |
| `test_stable_step` | 3 | 2 | the `Ref` line |

Every other test keeps its count: the five `Gen` tests above, and the property tests whose
model moved into the test.

## A finding outside the brief: `stm_admit` P1

`stm_admit` (`ocaml/engine/test/stm/stm_admit.ml`, wave 1's E2) failed its green test P1 in
three runs of the tree B campaign: during T07, T09 and T12. P1 is "E4_sched admission, two
client domains".

- qcheck-stm reported results incompatible with the linearized model.
- The test runs a toy engine, so no carrier, no mutant and no change of this seat reaches it.
  No other run of either campaign lists it as failing.
- The three runs fell at 21:05 to 21:09, after tree A's run had ended. Other seats' builds ran,
  and the load average read at 21:08 was 29.
- Host runs of the test, N copies at a time (finite, this host only; § Commands names each
  run):
  - one at a time, 60 runs in three batches: none failed;
  - 12 at a time, 120 runs in two batches: 2 failed P1;
  - 24 at a time, 240 runs in two batches: 2 failed P1.
- `w2-engine-mutants/stm_admit-p1.txt` keeps the seven counterexamples: three of the campaign
  and four of the load runs.
- reading: `E4_sched.enqueue` (`ocaml/engine/e4_sched.ml`) enters the pending count, then takes
  the next stamp, inside its own mailbox's lock. `pending` and `last_seq` read without that lock.
- assumed (a cause, not tested): each of the seven counterexamples shows that interleaving.
  - A send raises the pending count. The other domain then reads the count, or sends and takes
    a stamp. Only then does the first send take its own stamp.
  - No order of atomic sends gives such a history, and the model's send is atomic.
- The choice belongs to the coordinator. One way takes both steps and both reads under one lock.
  The other lets the model read `Pending` and `Last_seq` as values that a concurrent send may
  straddle.
- This seat changed neither: `E4_sched` is outside C4, H3, H5 and H8.

## H3: what leaves the installed library

`Corpora`, `E4_diff` and `E4_memo_list` move to `e4_reference`, a private library in
`ocaml/engine/test/reference/`. It is unwrapped, so every test keeps its names, and it has its
rule-7 lint.

`corpora.ml` keeps its JSON calls as they were, for seat 1's edits. H3 renamed it unchanged, and
H8 replaced only its header comment, which moved into `corpora.mli`.

`api_gen_inst.ml` opens `Effect4_engine` only for `E4_memo_list`. This wave the file is the
coordinator's, so `test/dune` turns warning 33 off for that one module, with the reason beside
it.

The installed `effect4_engine`, read off `_build/install/default/lib/effect4_engine/`. Each
count leaves out the wrapper module `Effect4_engine`.

| | Modules |
| --- | --- |
| Base | 36 |
| After H3 | 26 |
| Out: C4 deleted seven, H3 moved three | `Api_engine_ref`, `Corpora`, `E4_diff`, `E4_buckets_list`, `E4_env_list`, `E4_fibers_view_list`, `E4_memo_list`, `E4_ppath_list`, `E4_table_list`, `E4_trace_list` |
| Kept, the 26 | `Api_engine`, `Api_engine_inst`, `E4_abandon`, `E4_admit`, `E4_buckets`, `E4_engine`, `E4_engine_intf`, `E4_env`, `E4_fibers_view`, `E4_host`, `E4_inbox`, `E4_instance`, `E4_log`, `E4_logindex`, `E4_mailbox`, `E4_memo`, `E4_ppath`, `E4_query`, `E4_quiescence`, `E4_reply`, `E4_ring`, `E4_sched`, `E4_shutdown`, `E4_table`, `E4_trace`, `E4_trigger` |

The installed package and library set does not move, so `installed.expected` is unchanged.

## H5: one harness

`E4_check` (`ocaml/engine/test/check/e4_check.mli`) holds the behaviours C1-C4.

- `check name ok` prints `PASS name` or `FAIL name` and flushes the line.
  `~gap:Two` prints two spaces, as the store's tests and `test_buckets` always did.
- `finish ()` prints `== ALL PASS: 0 failure(s) in N checks ==` or the `FAILED` line, and exits
  0 or 1.
- `temp_dir prefix` makes a directory with `Filename.temp_dir`, under the system's temporary
  directory (TMPDIR). `remove_tree` removes it, sealed entries included.
- `test_check` checks C1-C4. Its red control runs the executable itself as a child with one
  failing check, which must exit 1 with the `FAILED` line.

The 28 tests on it:

- 19 of the engine's: `test_host`, `test_buckets`, the five `prop_*`, `test_sched`,
  `test_log`, `test_replay_steps`, `test_engine`, `test_query`, `test_diff`, `test_serve`,
  `test_scenarios`, `test_mask`, `test_pool`, `test_queue`, `test_semaphore`.
- 9 of the store's: `test_bytes`, `test_control`, `test_checkpoint`, `test_cache`, `test_wal`,
  `test_index`, `test_pack`, `test_crash`, `test_cas`.

The six variables `E4_CAS_TMP`, `E4_PACK_TMP`, `E4_INDEX_TMP`, `E4_CHECKPOINT_TMP`,
`E4_CACHE_TMP` and `E4_DISK_TMP` are gone. `disk_test_support.ml` and `bench_index.ml` read
none. `run-bench.sh` sets TMPDIR to its disk directory instead.

Every PASS and FAIL line keeps its text. Each of the 36 engine and store test executables ran
before and after the move, and their PASS and FAIL lines are identical. Only the summary line
moved to the one form.

## H8: the interfaces

- The installed libraries under `ocaml/engine/` (`effect4_engine`, `effect4_engine_cas` and
  `effect4_bytes`) already gave every module an interface. The two exemptions of rule 5 are
  `api_engine_inst.ml` and `e4_engine_intf.ml`.
- The test libraries gain theirs: `corpora.mli`, `e4_memo_list.mli` and
  `disk_test_support.mli`. Each holds the header with its behaviours.
- Each interface exports the values its callers name, read off their typed trees with
  `compiler-libs` (a scratch reader, not kept). `E4_memo_list`'s `mem`, `cardinal` and `raw`
  had no reader and go.

## Commands and results

Every dune command ran in `ocaml/` through `opam exec --switch=effect4 --`. Every gate ran as
`python3 /private/tmp/seams-lean-one.py make check-ocaml` from the worktree's root.

| Command | Result |
| --- | --- |
| `make check-ocaml` at the base | exit 0: `PASS native` and `PASS compiler` from the shared gate cache; `PASS ocaml: shared result 04ac7db15bed`; 2 min 32 s wall |
| `dune build @engine/runtest --force` at the base | exit 0, no `FAIL` line; 13.8 s wall |
| `campaign.py --label A --corpus .lake/corpus --root <copy of b83188cb2>` | 56 rows in `results-A.tsv`; 57 min 46 s wall on a host shared with two other seats |
| `campaign.py --label A-recheck … B05 P02`, with the runner that checks dune's copies | both rows the same as tree A's, none INVALID: the two mutants that ran right after a timeout |
| `tapecheck.exe`, built in a copy of the base | 2,132 tapes the same, none different, 67,360 decisions; exit 0 |
| `make check-ocaml` at C4 | exit 0: `PASS ocaml: recorded f9beb44f0fc8 (54.741s)`; gen-check PASS; 3 min 31 s wall |
| `dune build @engine/runtest --force` at C4 | exit 0, no `FAIL` line; 58 s wall |
| `campaign.py --label B --corpus .lake/corpus --root <copy of 461befef3>`, then the same with B04 to Y07 named | 56 rows in `results-B.tsv`, none INVALID; the second pass 50 min 30 s wall |
| `summarize.py` | the table of § C4; its summary line: 24 mutants caught by a `Ref` check in A, each also by a check without `Ref`; none missed in B; P07, T12 and Y04 caught in neither tree |
| `dune build @install`, then the modules under `_build/install/default/lib/effect4_engine/` | 26 modules after H3, 36 at the base, the wrapper module aside |
| `make check-ocaml` at H3 | exit 0: `PASS ocaml: recorded e31161d486ac (78.742s)`; the install lane I1-I4 within it |
| `dune build @engine/test/check/runtest --force` | `test_check`: 6 checks, its red control among them; exit 0 |
| each of the 36 engine and store test executables, run alone before and after H5 | every PASS and FAIL line the same; every exit 0 |
| T08 applied, `prop_table.exe`, then reverted | `FAIL T6 …`, `== FAILED: 1 failure(s) in 10 checks ==`, exit 1; after the revert exit 0 |
| `make check-ocaml` at H5 | exit 0: `PASS ocaml: recorded 2e7e9b389584 (84.460s)` |
| `make check-ocaml` at H8 | exit 0: `PASS ocaml: recorded 18c2c7b60a7c (84.176s)` |
| P07, P01, T12 and Y04 applied in turn with the repaired checks, then reverted | P07 fails PP3; P01 fails PP3, PP5 and PP7; T12 fails T9; Y04 fails MM6a; each exit 1 |
| `make check-ocaml` at the findings commit | exit 0: `PASS ocaml: recorded 58d08759fea2 (100.107s)`; `test_diff`'s totals: 3,248 tapes, 72,840 positions, 0 divergences |
| `make check-ocaml` at the headers commit | exit 0: `PASS ocaml: recorded 26bbca20d6c8 (54.879s)` |
| `dune fmt`, then `dune build @fmt`, before each commit | clean |
| a shell loop over `stm_admit.exe`, one at a time, 20 runs (21:07) | none exited non-zero |
| a scratch copy of `stm_load.py` with N = 1, 12 and 24 (21:23 to 21:27) | 0 of 20 failed; 1 of 60 failed P1; 2 of 120 failed P1 |
| `stm_load.py <stm_admit.exe> <dir> 1 20`, then `12 5`, then `24 5` (21:28 to 21:32) | 0 of 20 failed; 1 of 60 failed P1; 0 of 120 failed |
| `make check-ocaml` before the receipt commit, whose files are all under `docs/research/` | exit 0: `PASS ocaml: shared result 26bbca20d6c8`, the headers commit's |
| `python3 scripts/check-language.py --strict` on this file | exit 0: `PASS check-language: no finding` in this file |

One observation came from a run that stopped. A campaign stopped in the worktree killed dune
in the middle of a build. Its next builds kept the reverted mutant P01's text in
`_build/default/engine/e4_ppath.ml`, and the kit's tests then ran for minutes.
`dune clean` cleared it, and the runner now kills only the tests and checks dune's copies.

## Lines removed and moved

`python3 docs/research/2026-10-18-slices/w2-engine-mutants/lines.py` counts the hand `.ml` and
`.mli` lines under `ocaml/engine`. It leaves out the files `ocaml/.ocamlformat-ignore` lists.

| Part | Base `b83188cb2` | C4 `461befef3` | H3 `cf53ddea6` | H5 `2600b89b1` | H8 `9c614e057` | findings `d01646fa6` |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| engine library | 8,307 | 7,849 | 6,750 | 6,750 | 6,750 | 6,752 |
| engine tests | 16,461 | 16,350 | 17,456 | 17,460 | 17,548 | 17,612 |
| store library | 12,017 | 12,017 | 12,017 | 12,017 | 12,017 | 12,017 |
| store tests | 13,474 | 13,474 | 13,474 | 13,149 | 13,245 | 13,245 |
| total | 50,259 | 49,690 | 49,697 | 49,376 | 49,560 | 49,626 |

- C4 deletes 454 lines: `api_engine_ref.ml` (34) and the six twins (420). The tests' own
  models add back less than they remove.
- H3 moves 1,100 lines out of the installed library: `corpora.ml` (528), `e4_diff.ml` (341),
  `e4_diff.mli` (126) and `e4_memo_list.ml` (105).
- H5 removes 321 lines net: the harness and its test add 206, and the 28 tests lose their copies.
- H8 and the findings add interfaces and checks: 250 lines.
- `git diff --stat b83188cb2 d01646fa6 -- ocaml`: 71 files, 1,242 insertions, 1,778 deletions,
  `dune` files included.

## Axiom output

No Lean declaration changed, so no `#axiom_audit` is owed.

## Evidence

Every result here is host-only: finite runs on this host, eight cores shared with other seats.
No theorem reaches any of them.

- tested: the campaign, 56 mutants in each tree, and the recheck of two of tree A's rows.
- tested: each copy's `ocaml/` equals its commit's `git archive`, apart from the mutant applied
  at the time of the comparison.
- tested: the tape check, 2,132 tapes drawn on `Ref` and on `Gen`, the same.
- tested: each step's gate, `make check-ocaml`, exit 0.
- tested: the 36 test executables' PASS and FAIL lines, the same before and after H5.
- tested: `test_check`'s red control, and each repaired check against its mutant.
- assumed: a copy behaves as its commit does. The copy holds `ocaml/` and
  `harness/truth/corpus.json`, and its Lean corpus is the worktree's `.lake/corpus`.
- tested: `stm_admit` run one at a time, 60 runs, none failed.
- A host run that failed, not a pass: under 12 and 24 copies at a time, 4 of 360 runs failed P1.
- reading: `E4_sched.enqueue` takes its two steps inside one mailbox's lock, and the two reads
  take none.
- assumed: that interleaving causes each of P1's seven failures.

## Landed theorems and their placement

None. No Lean declaration changed.

## Open obligations

1. **`api_gen_inst.ml`** (the coordinator's or seat 3's file): drop `open Effect4_engine`, then
   drop `-w -33` from `e4_gen_instance` in `ocaml/engine/test/dune`.
2. **The to-do lane after C5.** C4 edited `test_todo.ml` and `todo/dune`, where `Ref` was a
   second instance; the merge with C5 resolves them by hand.
   - Then move the four generated lanes' tests onto `E4_check` (`test_todo`, `test_ctors`,
     `test_modeled`, `test_rocq`): one `dune` line each, held back because C5 rewrites those
     stanzas.
   - Give `todo_lane`'s three modules their interfaces (`native_todo`, `todo_core`,
     `todo_fixture`).
3. **Documents outside this seat's files** that name what C4 deleted:
   - `docs/core/machine-state.md`, the row "optimized containers": "list twins" becomes
     "property tests over Lean's list operations, and a differential against the generated
     machine".
   - `Test/Counterexamples/REGISTER.md`, `E4-PROV-CE-005`: "Fast and Ref" becomes "Fast and Gen".
4. **`ocaml/engine/tools/run-bench.sh`** is outside the brief's files. Two of its lines exported
   the retired variables, and now one exports TMPDIR. The coordinator may keep or revert it.
5. **`E4_memo.lookup`** has no reader but `prop_memo`'s MM5: the machine's lookup is the
   generated `MemoWorld.lookup`. Keep it or delete it with MM5; the coordinator's call.
6. **Tests not on `E4_check`:**
   - `test_stable_step` asserts.
   - `test_shared_facts` and the `test_disk*` tests raise on a failure and print no PASS line.
   - The kit's tests are seat 1's, and `ocaml/engine/bytes/test/test_math.ml` is outside this
     seat's files.
7. **Seeds hide branches.** The property tests draw from one fixed LCG seed, and PP3 showed a
   seed that never reached the branch a check names. PP3 and PP7 now fail when a named side goes
   unvisited; the other property tests were not audited for this.
8. **`stm_admit` P1** (§ A finding outside the brief): an atomic send in `E4_sched`, or a model
   that lets a send straddle `Pending` and `Last_seq`. Until then the gate can fail on a
   loaded host.

## Proposed decisions rows (proposals only)

1. **C4, the reference instance (method).** The `Ref` instance and six list twins are deleted.
   Over 56 carrier mutants, every mutant a `Ref` check caught is caught without it, and the
   differential runs the same tapes against the generated machine. A hand reference stays only
   for a catch that no other check makes, measured by a mutant campaign kept as patches.
2. **Test libraries (representation).** A test library under `ocaml/engine/test/` has no
   `public_name` and carries its rule-7 lint. It is unwrapped when the tests name its modules
   directly (`e4_reference`, `e4_check`).
3. **One harness (method).** The engine's and the store's tests print their checks through
   `E4_check`. A scratch directory lies under TMPDIR; no test reads a variable of its own.
4. **A check visits what it names (method).** A property test that names a branch or a side
   fails when its run reaches none of it, as PP3 and PP7 do since `d01646fa6`.
