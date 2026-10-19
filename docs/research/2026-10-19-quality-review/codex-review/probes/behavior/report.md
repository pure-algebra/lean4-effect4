# Behaviour review: A9 and A10, with partial A2 evidence

The 64 selected test binaries pass. The loaded scheduler test passes all 60 runs. The old campaign failures do not establish current failures.

The review uses `3471cbe35` in `/Users/pooks/.codex/worktrees/quality-review-3471/lean4-effect4`.
The shared build is `../_build/default`, relative to this report.
No reviewed source changes. No commits, pushes, merges, or source mutations run.

The coordinator narrows this seat to A9 and A10 after the first A2 probe run.
A2 remains partial. Its limitations appear below.

## A9: one small cleanup finding

| Field | Finding |
| --- | --- |
| ID | A9.1 |
| Severity | low |
| Kind | cleanup |
| Where | The C2 tool-list checks in `ocaml/engine/test/kit/test_mcp.ml`. The kind census in `ocaml/engine/cas/test/test_shared_facts.ml`. |
| Evidence | `python3 analyze_tests.py` writes `test-analysis.json`. C2 requires 20 names, then compares those names with generated supported methods plus `describe`. `test_shared_facts` requires 23 generated kinds. An additive method preserves the table equality but fails the literal count. |
| Why | The literal counts add manual edits when the generated tables grow. The MCP table equality already checks the complete expected list and order. |
| Fix | Delete C2's literal count check. Replace the standalone kind count with a comparison against the generated manifest if independent generation coverage is required. Retain behavioural controls. |
| Deletes | The two literal checks occupy 4 lines, measured by `analyze_tests.py`: 3 MCP lines and 1 kind-census line. |
| Test | The additive-table control in `test-analysis.json` changes 20 to 21 entries. Table equality stays true; the literal check becomes false. This is a finite check of the assertions, not a modified MCP run. |
| Plan | Existing H5 test hygiene; new follow-up. |
| Size | XS |

The fixed ordinal checks in `test_log.ml` deserve a different verdict.
They protect the append-only wire table's existing positions.
Keep those checks when the table grows; replace the exact total with a documented lower bound.
The malformed ordinal controls in `test_eff.ml` also test the decoder's boundary.
They are not redundant generated-output comparisons.

The `test_engine.ml` counter counts reached exception messages containing `extern table incomplete`.
It does not count occurrences of `failwith` in generated source.
Its description still names two rows, but the behavioural check rejects any reached hole.
Treat that wording as stale prose, not a missing exception check.

## A9: measured test cost

Commands from this directory:

```sh
python3 time_tests.py
python3 recheck_tests.py
python3 analyze_tests.py
```

`time_tests.py` finds built binaries named `test_*`, `prop_*`, or `stm_*`.
It runs each serially with a 30-second timeout.
It sets `TMPDIR` inside this report and reads the main checkout's existing Lean corpus.
The Lean corpus is an input, not regenerated evidence.

Four first-run failures come from this harness's invocation.
Two environment overrides name directories where the tests expect marker files.
`test_lean_wire` needs its explicit golden directory outside dune's usual build layout.
`test_interface` needs three fixture arguments.
`recheck_tests.py` supplies those paths and arguments. All four then pass.
The first-run logs remain available. They are not product defects.

`test-analysis.json` combines the passing first runs with the corrected runs.
It reports 64 passing binaries and 36.110 seconds of combined process time.
This is not the complete dune test alias: installation scripts, formatting, and typed-lint rules are outside this measurement.

| Slowest selected binary | Seconds | Result |
| --- | ---: | --- |
| `engine/test/stm/stm_disk.exe` | 4.551 | pass |
| `engine/cas/test/test_checkpoint.exe` | 2.772 | pass |
| `engine/test/stm/stm_mailbox.exe` | 2.318 | pass |
| `engine/test/stm/stm_inbox.exe` | 2.142 | pass |
| `engine/test/test_diff.exe` | 1.863 | pass |
| `engine/test/stm/stm_tool.exe` | 1.409 | pass |
| `engine/test/test_buckets.exe` | 1.189 | pass |
| `engine/test/test_sched.exe` | 1.075 | pass |

Each timing includes process startup. One run establishes cost on this host, not a regression distribution.
The tests with the highest costs exercise disk behaviour and concurrency.
Their costs alone justify no deletion.

## A9: C4 mutation coverage

`analyze_tests.py` reads the retained `results-B.tsv` without modifying any source.
Its full per-test mutant list appears in `test-analysis.json`.
The table covers 56 mutants of seven engine carriers.
Thirty-one selected engine binaries have no attributed failure in that campaign.

| Binaries with no attributed C4 failure | What they chiefly exercise | Verdict |
| --- | --- | --- |
| `test_math` | Byte arithmetic | keep |
| CAS `test_bytes`, `test_cache`, `test_cas`, `test_control`, `test_crash`, `test_disk`, `test_disk_boundary`, `test_disk_damage`, `test_disk_kill`, `test_disk_stm`, `test_index`, `test_pack`, `test_shared_facts`, `test_wal` | Store, bytes, durability, cache, and disk boundaries | keep |
| `test_check`, `test_ctors`, `test_modeled`, `test_rocq` | Test support and generated comparison lanes | keep |
| `test_mcp`, `test_shapes`, `test_tool` | Protocol and JSON admission | keep |
| `stm_admit`, `stm_disk`, `stm_inbox`, `stm_mailbox`, `stm_tool` | Concurrent host structures and sessions | keep |
| `test_host`, `test_log`, `test_query`, `test_sched` | Host protocols, log parsing, queries, and scheduling | keep |

These results show the campaign's reach. They do not show that these tests are redundant.
The historical `stm_admit` failures are excluded because the seven mutated carriers do not reach that toy engine.

The old campaign misses P07, T12, and Y04 after unrelated scheduler failures are excluded.
`receipt-w2-engine.md` records their repair in `d01646fa6`.
The pinned sources contain the repaired PP3/PP7, T9, and MM6a checks.
The current binaries pass those checks.
This review does not rerun mutations in source. Their reported red outcomes remain historical evidence from that receipt.

C4 already removes the `Ref`-only checks and the six list twins.
No additional whole test earns deletion from the retained campaign evidence.

## A9: load and retries

```sh
python3 load_tests.py
```

The wrapper runs the existing `stm_load.py` with 12 copies and 5 rounds.
It limits the process group to 90 seconds.
`load-tests.json` records 60 runs, zero nonzero exits, and zero P1 failures in 40.978 seconds.
The 60 raw outputs remain under `stm-load/`.
The fixed generator seed is 20261018. Scheduling remains nondeterministic.

The historical failure interleaves the pending counter and the send stamp.
The pinned `E4_sched.enqueue` calls `E4_quiescence.enter_with` to perform both under one lock.
This source change and the current finite load run support treating the historical lead as repaired.
They do not prove absence of every race.

The `~retries:2` lead is refuted.
It belongs to `stm_tool` P2, the expected-failure shared-session control.
`Stm_support.par_test` passes it to QCheck's shrinking machinery.
The installed `QCheck2.Test.run_law` repeats candidates while shrinking.
The initial property evaluation calls `run_law ~retries:1`.
A failing green test does not become green through this parameter.

## A10: measured paths

```sh
python3 ../run_ml.py hot_paths.ml
./hot_paths.exe > hot-paths.log
```

The second command runs after the load campaign ends.
`hot-paths-loaded.log` preserves the overlapping run.
`hot-paths-initial.log` contains preliminary per-domain allocation counters; use the final global allocation measurements instead.

`hot_paths.ml` times 20,000 reads at each environment size.
It reports the best and median of five runs.
The table below gives milliseconds from the final run.

| Bindings | Outer binding, current carrier | Latest binding, current carrier | Outer binding, existing persistent vector |
| ---: | ---: | ---: | ---: |
| 100 | 2.148 | 0.054 | 1.959 |
| 1,000 | 18.384 | 0.042 | 0.090 |
| 10,000 | 210.682 | 0.045 | 0.264 |

`E4_env.get` in `ocaml/engine/e4_env.ml` walks the reversed list for an early binding.
Its cost grows with environment length. Its `.mli` already describes this tradeoff.
The persistent vector demonstrates a possible faster read carrier for large environments.
This experiment measures reads only. It does not measure snapshot retention, prefix truncation, or whole-program execution.
It therefore does not establish that replacing the carrier improves the product.
No new defect finding rests on this microbenchmark.

The scheduler experiment uses one worker, a toy engine, batch 64, and no trace rows.
Every accepted send reaches `step`; the probe checks the applied count and quiescence.
It measures total allocated words using `Gc.stat` around the complete run, including scheduler startup and shutdown.

| Sends | Applied | Milliseconds | Allocated words | Words per send |
| ---: | ---: | ---: | ---: | ---: |
| 1,000 | 1,000 | 0.668 | 73,708 | 73.71 |
| 10,000 | 10,000 | 2.980 | 724,281 | 72.43 |
| 100,000 | 100,000 | 25.909 | 7,266,356 | 72.66 |

Allocation remains approximately constant per send across this measurement.
This does not profile every allocation site or set a production throughput target.
It gives no evidence of allocation growing with the queue length.

Other inspected candidates do not justify a finding:

- `E4_logindex.arg_int` indexes short event-argument lists. This review establishes no growing-loop cost there.
- `E4_logindex.decision_keys` appends once to its completed result. It does not repeatedly append during recursion.
- The kit builds small fixed JSON field lists. Their concatenations are not an observed scaling failure.
- Store hash tables use fixed-length address strings. The cache reads seven selected bytes; scheduler triggers hash three integers.
- Memo keys use an explicit ordered-map comparison. They do not use structural hashing.

No whole-application sampling profile runs in this slice. No performance defect is asserted without one or a representative end-to-end timing.

## A2: partial evidence and limitations

The initial command is `python3 run_fuzz.py` after compiling `fuzz.ml` with `../run_ml.py`.
The fixed byte-mutation seed is `[3471; 20261019]`.
Each family receives valid seeds, every seed prefix, three byte flips per position, 1,000 random mutations, and 1,000 random byte strings.
The subprocess timeout is 20 seconds per family.

| Decoder family | Cases | Exceptions observed | Evidence |
| --- | ---: | ---: | --- |
| `Eff_frame` | 2,330 | 0 | `frame.log` |
| `Eff_wire` | 2,234 | 0 | `wire.log` |
| `E4_shape` | 2,330 | 0 | `shape.log` |
| `E4_node` | 2,330 | 0 | `node.log` |
| `E4_control` | 2,288 | 0 | `control.log` |
| Pack read and scan | 2,326 | 0 | `pack.log` |
| WAL replay | 2,222 | 0 | `wal.log` |
| `Kit.Json.parse` | 2,276 | 0 | `json.log` |
| `nat_json_parse` | 2,276 | 0 | `nat_json.log` |
| `Kit_mcp.line` | 2,276 | 0 | `mcp.log` |

The index campaign is invalid.
`E4_index.save` creates a read-only fixture; the harness then fails while overwriting it.
Its 3,242 exceptions are `Sys_error` from the harness, not decoder failures.
`index.log` and `index-failure-*.bin` preserve that distinction's evidence.

The subsequent setup tries reopening the corrupted pack fixture and exits with `Bad_pack`.
Consequently, the near-2^62 pack cases and the deep JSON/wire cases do not run.
The coordinator ends A2 work in this seat before those harness issues are repaired.
No deep-input, oversized-input, or index-decoder acceptance conclusion follows.
The absent `fuzz-results.json` reflects that interrupted driver, not a completed campaign.

The byte campaign checks return versus exception. It does not independently classify every return as a correct refusal.
All A2 outcomes are bounded host probes, not universal decoder guarantees.
