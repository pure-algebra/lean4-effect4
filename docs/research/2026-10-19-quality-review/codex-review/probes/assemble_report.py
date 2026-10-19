from pathlib import Path
import re,json
R=Path(__file__).resolve().parent.parent;P=R/'probes'
stand=(P/'standards/report.md').read_text(); behavior=(P/'behavior/report.md').read_text()
def section(s,title,next_title):return s.split(title,1)[1].split(next_title,1)[0]
findings={}
for m in re.finditer(r'^### (A\d+\.\d+) — .*$',stand,re.M):
 e=stand.find('\n##',m.end());findings[m.group(1)]=stand[m.start():e if e>=0 else len(stand)]
intro='''# Quality review at 3471cbe35

The public kit can return the wrong integer after accepting a reply that the machine's numeric checks would refuse.
The review also reproduces failures in pack decoding, storage verification, failed-write recovery and shutdown acceptance.
Fix these before widening the public interface.

The reviewed commit is `3471cbe35e3f91949170e2147dbe46f75cb795fd` on `refactor/phase1-phase3`.
The isolated worktree is `/Users/pooks/.codex/worktrees/quality-review-3471/lean4-effect4`.
A1 completed first. Its retained checkpoint and probes supplied the numeric direction before the remaining review began.
The work changes no tracked source, commits, pushes or merges.
Every review output is under this folder's `README.md` or `probes/`.

Finishing criteria: cover all ten A angles, every B group, fifteen branches, 49 dated folders, and every named follow-up.
Each ranked finding needs evidence, a fix, a deletion scope and a regression control.
Finite probes, source inspection, historical receipts and open choices remain distinct.
The review meets those criteria. It does not claim exhaustive input coverage or physical power-loss certification.

## The ten findings that matter most

| Rank | ID | Severity | Finding | First action |
| ---: | --- | --- | --- | --- |
| 1 | A1.1 | high | An admitted kit reply produces the wrong integer. | Apply shared ingress checks, then finish E6 with exact carriers. |
| 2 | A3.2 | high | A failed journal write loses pending rows; a later commit acknowledges a gap. | Preserve pending state or poison the writer until recovery. |
| 3 | A4.1 | high | A send reports success after shutdown has joined its workers. | Count in-flight admissions before sealing and draining. |
| 4 | A3.1 | high | CAS verification reports success after corruption before the published boundary. | Require the scan to reach that boundary. |
| 5 | A3.3 | high | Directory sync errors are acknowledged as success. | Propagate synchronization failure through one durable-file helper. |
| 6 | A2.1 | high | A short pack file with a huge claimed length raises an exception. | Check remaining lengths before addition or allocation. |
| 7 | B5.1 | medium | The lanes interface exports 2,454 removable lines. | Use the checked reachable-type selector. |
| 8 | A5.1 | medium | Failed journal opening leaks its writer claim. | Bracket opening and transfer ownership only after success. |
| 9 | A5.2 | medium | A negative CLI budget reaches a generated-array exception. | Validate numeric options before evaluation. |
| 10 | A3.4 | medium | Journal recovery retains part of a batch despite its stated all-or-none promise. | Add batch framing, or obtain an explicit contract ruling. |

## Part A: ranked findings

### A1.1 — An outside reply reaches arithmetic beyond its declared domain

| Field | Finding |
| --- | --- |
| Severity | high |
| Kind | defect |
| Where | `ocaml/engine/kit/kit.ml`, `admitted` and `run`; `src/Effect4/Machine/Integers.lean`, `intNeg`, `intAdd`, `intSub`; their generated closure functions. |
| Evidence | `probes/a1.ml` passes a wire-decoded program and reply through the public kit. `probes/A1Lean.lean` evaluates the same subtraction in Lean. |
| Why | The kit's call-tree path checks reply typing without the engine's numeric admission. A raw Nat addition wraps before a subtraction branch avoids checked growth. This violates the builtin's declared domain and decision 394's host-ingress rule. |
| Fix | Apply the same program-literal and reply checks before either run route. Return a profile refusal before accepting the host's new state. Then complete E6 with exact Nat/Int and an exact UInt64 carrier. |
| Deletes | No immediate deletion. E6 replaces the bounded numeric representation; its measured scope follows below. |
| Test | Retain the negative reply, native-host route, tape route, wire round trip and Lean result. Keep ordinary addition's refusal as a control. |
| Plan | E6 and owner decision 12; immediate ingress repair. |
| Size | M for E6; S for shared ingress repair. |

The input reply is `Val.negInt 4611686018427387903`, representing negative 2^62.
The program computes negative one minus that reply.
Lean returns natural `4611686018427387903`.
The kit returns `NegInt 0`, representing negative one.
The default cross-check records `agrees=false` but retains that wrong finished result.
Both the tape and native callback paths reproduce it.

The operation first computes `Nat.add max_int 1` inside `intNeg`.
The following subtraction branch never calls `Profile.grow`.
Ordinary additions at the profile bound and at `max_int` refuse in the controls.
This finding therefore concerns the demonstrated path, not every arithmetic row.

### A2.1 — Pack-length arithmetic wraps before allocation

| Field | Finding |
| --- | --- |
| Severity | high |
| Kind | defect |
| Where | `ocaml/engine/cas/e4_pack.ml`, `read_full`, `step_at`, and `reader_source.read`. |
| Evidence | `probes/a2/pack_boundary.ml` changes only a valid record's length field to `max_int - 4`. A small file then raises `Invalid_argument("Bytes.create")`. |
| Why | The length fits the be64 host domain, but adding the header and offset wraps. The reader's second addition also wraps, so an impossible allocation reaches the runtime. |
| Fix | Validate offsets against file size, then compare lengths against the remaining size using subtraction. Check allocation limits before allocation. Use the same checked range helper in direct reads and scanning. |
| Deletes | Replace the three unchecked range calculations. No net line saving is claimed. |
| Test | Keep the valid file, changed lengths `max_int`, `max_int-4`, `max_int-16`, `max_int-64`, and `max_int-100`, then restore the valid file. Every malformed case must refuse without exception or a negative cursor. |
| Plan | New. |
| Size | S |

`probes/a2/pack-boundary.log` records valid and restored reads as `Ok`, with scans ending at `Eof`.
The three middle lengths raise during direct reading.
Scanning also constructs negative offsets before stopping.
The test changes untrusted bytes; it does not request a large allocation through a programmer-only API.
The header mutation invalidates the record checksum, which the reader never reaches before this failure.

'''
# Keep the prior A1 checkpoint as evidence, then publish the completed report.
if not (P/'a1-checkpoint.md').exists():(P/'a1-checkpoint.md').write_text((R/'README.md').read_text())
parts=[intro]
for ident in ['A3.2','A4.1','A3.1','A3.3','A5.1','A3.4','A5.2','A7.1','A7.2']:parts.append(findings[ident])
parts.append('### A9.1 — Remove two literal census checks\n\n'+section(behavior,'## A9: one small cleanup finding\n\n','## A9: measured test cost'))
parts.append('''## A1: reachability, word carriers and E6 size

Evidence status: finite native probes, finite Lean evaluations, and a source census.
The exact commands and outputs are under `probes/a1*` and `probes/A1*`.

| Outside input | Checked path and result |
| --- | --- |
| Wire bytes | The program and large negative reply both decode before the wrong kit result. |
| Tape answer | The public in-memory tape reproduces A1.1. |
| Native host reply | The callback route reproduces A1.1. |
| JSON request | The large magnitude becomes a numeral. Carrier reading refuses it; this path does not reproduce the arithmetic failure. |
| Stored node | The node reader accepts valid full float payload bytes. It does not construct the lowered float carrier. No stored-node float corruption is established. |

`UInt64` remains OCaml `int` in the generated carrier.
An explicit probe conversion with `Int64.to_int` makes positive and negative 0.5 identical as lowered float values and encoded digests.
That conversion demonstrates the representation gap. It is not a production conversion discovered in the tree.
The wire value decoder refuses float frames, and the engine's native float-answer boundary refuses unrepresentable patterns.
Ordinary negative binary64 values still need an exact 64-bit carrier in E6.
Zarith naturals alone do not supply that carrier.

| Measured E6 surface | Result | Measurement |
| --- | ---: | --- |
| Builtin rows | 128 | Multiline row parser in `a1_size.py` |
| Exact / domain / approximate / unsound rows | 75 / 45 / 6 / 2 | Same parser; the brief's 43 misses two multiline domain rows |
| Direct Nat, Int, UInt64 and USize rows | 39 | Explicit row-name list in `a1-size.json` |
| Constructor fields containing Nat in the program-type recipe | 19 | Lean type reduction in `A1Fields.lean`; includes one `List Nat` field |
| Hand consumer candidate files | 53 | Paths retained in `a1-size.json`; candidates are not a promised edit count |
| `eff_types.ml` int tokens / integer tokens | 25 / 7 | Source token census |
| `closure_gen.ml` int tokens / integer tokens | 3,227 / 6,546 | Source token census |
| `api_engine.ml` int tokens / integer tokens | 1,543 / 1,322 | Source token census |
| `lanes_gen.ml` int tokens / integer tokens | 292 / 200 | Source token census |

The 39 direct rows exclude numeric crossings in arrays, string positions and profile arithmetic.
`Native.ctorValue` builds numeric constructors outside the builtin table.
`Translate.letValueExpr` saturates large Nat literals and refuses unrepresentable UInt64 literals.
Those translator paths belong in the migration too.

The current `bench_todo` baseline allocates 23,824 words per host call for the lowered reference repository.
Its typed lowered model allocates 23,378 words per call.
`probes/a1-bench-before.log` retains every stage.
No complete Zarith switch exists in this pinned tree, and this review edits no tracked source.
There is no after measurement and no measured overhead claim.

Decision 12: retain exact naturals and integers everywhere as the target direction, with an exact word carrier too.
The interim input checks are necessary because the current crossings do not bound every admitted computation.

## A2: decoder coverage and limits

`python3 probes/a2/run.py` rebuilds the local harness and creates fresh transient fixtures.
It tests every seed prefix, three bit flips per byte, 1,000 random mutations and 1,000 random byte strings per family.
The fixed seed is `[3471; 20261019]`. Each subprocess has a fifteen-second timeout.

| Decoder | Cases in final byte campaign | Exceptions |
| --- | ---: | ---: |
''')
for row in json.loads((P/'a2/results.json').read_text()):
 m=re.search(r'(\w+) cases=(\d+) exceptions=(\d+)',row['stdout'])
 if m:parts.append(f'| `{m[1]}` | {m[2]} | {m[3]} |\n')
parts.append('''
The targeted near-limit pack case then exposes A2.1.
The frame near-limit controls return without exception.
The positive controls in `a2/controls.log` confirm accepted program, node, shape, control and JSON fixtures.
`a2/deep_run.py` confirms accepted JSON arrays and wire option types through depth 2,000,000.
MCP returns a structured non-object refusal for those arrays; the executable stdio route also returns normally through depth 300,000.
No tested case hangs or overflows the stack.
These bounds do not prove safety at every depth or classify every corrupted return independently.

The initial worker harness overwrote a read-only index fixture and restarted from a damaged pack.
Those initial errors are harness failures, retained under `probes/behavior/`.
The final harness replaces the index file, recreates its fixtures, and starts pack scans at the first record.
Use `probes/a2/results.json` and `pack-boundary.log` for the final results.

''')
# Append the full qualified lead audit, keeping exact findings only once.
lead=stand.split('## A3: persistence and lock audit',1)[1].split('## Reproduction and retained evidence',1)[0]
parts.append('## A3: persistence and lock audit'+lead)
parts.append('## A9: measured test cost'+behavior.split('## A9: measured test cost',1)[1].split('## A2: partial evidence and limitations',1)[0])
parts.append((P/'part-b.md').read_text());parts.append((P/'part-c.md').read_text())
parts.append('''## Decisions only the owner can make

| Decision | Recommendation and boundary |
| --- | --- |
| Decision 12, exact generated numbers | Confirm E6 now, including UInt64. The wrong admitted integer result is reproduced. No performance penalty has been measured for the unbuilt switch. |
| WAL batch guarantee | Keep LG3 and add batch completion framing. If row-prefix recovery is intended instead, record the contract amendment explicitly. |
| Supported persistence profile | State the supported local-filesystem and fork discipline. Propagate sync failures under that profile. NFS support needs its own failure contract and tests. |
| Public JSON before F1 | Use canonical tagged JSON. Retain V only for internal fixtures during migration; require a named consumer before keeping two public spellings. |
| Research and probe cleanup | Apply C1/C2 dispositions after preserving unique and untracked evidence. Keep only active notes and stable references in the working tree. |
| Optional features | Defer the sexp public face, Incremental abstraction and unused adapters until each has a concrete consumer. |

No approval is needed to read this review or rerun its retained probes.
These choices govern future implementation. This task performs no implementation landing.

## Verification and reproduction

The pinned OCaml workspace builds successfully with output redirected into this report.
The documentation build succeeds with 37 warnings. All 64 selected test binaries pass after correcting four harness invocations.
Sixty loaded concurrency runs pass. The newly scheduled shutdown history fails its model as expected.
The generated interface reduction passes all eleven retained compilation steps.
The finite Lean integer and JSON-spelling probes pass against matching source definitions in the built main checkout.
No new theorem, axiom audit, full-tree battery, TypeScript compiler run, or physical crash test is claimed.

Use these paths for the principal reproductions:

```sh
R=/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-19-quality-review/codex-review
W=/Users/pooks/.codex/worktrees/quality-review-3471/lean4-effect4
cd "$W/ocaml"
opam exec --switch=effect4 -- dune build --build-dir "$R/probes/_build"
python3 "$R/probes/run_ml.py" "$R/probes/a1.ml"
python3 "$R/probes/a2/run.py"
python3 "$R/probes/a2/deep_run.py"
python3 "$R/probes/run_ml.py" "$R/probes/a2/pack_boundary.ml"
python3 "$R/probes/standards/fault_injection.py"
python3 "$R/probes/standards/shutdown_model.py"
python3 "$R/probes/b5_interfaces.py"
```

The shutdown model's exit one is the expected counterexample, not a passing product test.
For storage, lock, CLI and interface commands, use [the retained detailed receipt](probes/standards/report.md#reproduction-and-retained-evidence).
For test timings, load and hot-path measurements, use [the behavior receipt](probes/behavior/report.md).

Run the Lean evaluations from the built main checkout:

```sh
cd /Users/pooks/Dev/lean4-effect4
python3 /private/tmp/seams-lean-one.py lake env lean "$R/probes/A1Lean.lean"
python3 /private/tmp/seams-lean-one.py lake env lean "$R/probes/A1Fields.lean"
python3 /private/tmp/seams-lean-one.py lake env lean "$R/probes/B4Json.lean"
```

`probes/final-verification.json` records source cleanliness, retained evidence checks and report coverage.
The owner's untracked `tools/view/make_videos.py` remains untouched.
''')
s='\n'.join(parts)
# Evidence names in the delegated prose are relative to their original folders.
# Readers get explicit resolution without rewriting the preserved receipt.
s=s.replace('## A3: persistence and lock audit','The A3–A8 evidence filenames below resolve under `probes/standards/`.\n\n## A3: persistence and lock audit',1)
s=s.replace('## A9: measured test cost','The A9–A10 evidence filenames below resolve under `probes/behavior/`.\n\n## A9: measured test cost',1)
s=s.replace('### A3.2 — A failed WAL flush destroys its retry state','The A3–A8 finding logs and scripts resolve under `probes/standards/`.\n\n### A3.2 — A failed WAL flush destroys its retry state',1)
s=s.replace('### A9.1 — Remove two literal census checks','The A9 evidence files resolve under `probes/behavior/`.\n\n### A9.1 — Remove two literal census checks',1)
(R/'README.md').write_text(s)
print('report lines',len(s.splitlines()),'words',len(s.split()))
