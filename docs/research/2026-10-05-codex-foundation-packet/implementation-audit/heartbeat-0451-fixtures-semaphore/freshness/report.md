# Fixture freshness review

## Finding

The new generated group repairs ordinary fixture drift in the existing Queue and DOGFOOD lanes.
Two small checker gaps remain.
Neither shows a wrong current Queue or DOGFOOD runtime result.

**Role:** tooling review. **Evidence:** source inspection and isolated Python controls. **Scope:** frozen commit `e6d63ddb440b5d171a9699b10182083ba54551d6`.
The reviewed base is `a02126a85051ab7ec0be0a3bd30471feb18fbdd3`.
No Lean, compiler, generator, build or host runtime ran during this review.

## What the change establishes

`fixtures`, in `scripts/generate.py`, discovers the two existing writer folders.
It builds their imported modules, runs their writers into temporary folders, and installs or compares the resulting bytes.
Its source refuses missing expected output, changed known output, and extra output inside a discovered lane.

The Makefile places `fixtures` in `HERMETIC_GROUPS`, `GEN_GROUPS`, and the prerequisites of the OCaml check.
Its marker depends on fixture bytes, writer sources, and the traces of the writers' imported modules.
`GENERATED_PATHS` includes the fixture files.
A normal fixture edit therefore reaches the existing generation and drift machinery.
The writers retain their default locations and accept an alternate output folder.
The committed fixture bytes and OCaml source do not change in this commit.

This closes the ordinary stale-fixture route without changing Lake's treatment of `include_str`.
An isolated `lake build` still does not discover fixture-only changes.
The commit explicitly retains Make 3.81's same-second timestamp limitation.
This review does not report that known limitation as a new finding.

## Follow-up 1: reject output aliases before writing

**Priority:** small correctness repair. **Consumer:** the generator's `--output-dir` check mode.
**Owner:** `fixtures` in `scripts/generate.py`.

The check mode accepts an output folder that aliases the repository.
For example, the CLI admits `--only fixtures --output-dir .`.
`fixtures` then unlinks the repository lane's text files before invoking its writer.
The comparison subsequently compares the freshly written file with itself.
The check passes after silently replacing a changed file or deleting an extra file.

The isolated control uses the actual extracted Python functions and a mock writer.
A changed Queue fixture is refused with a separate output folder.
With the repository as output, the same changed fixture is overwritten and accepted.
An extra file is likewise refused with a separate folder, but deleted and accepted with the alias.

Reject a lane output folder whose resolved path aliases its repository destination.
Perform that check before clearing temporary files or invoking any command.
The existing `derived` function already performs an equivalent destination-alias refusal.
Use the same rule, including resolved paths so symlink aliases cannot bypass it.
Retain positive separate-output controls and exact before/after byte checks on alias refusal.

**Observation:** checker result and repository fixture bytes.
**Hypotheses:** check mode; overlapping source and output lane destinations.
**Exclusions:** ordinary temporary-output operation, Lean writer correctness, and runtime agreement.
**Prerequisite:** none beyond the existing generator functions.
This is a checker property, not a proposed semantic theorem or registry claim.

## Follow-up 2: account for fixtures whose writer disappears

**Priority:** bounded completeness repair. **Consumer:** fixture inventory and generated-file drift checks.
**Owner:** `fixture_lanes` in `scripts/generate.py`, with the existing Make input inventory.

Discovery visits only folders containing `write.lean`.
If one writer disappears while another remains, the former lane's retained text files are never examined.
A new folder containing text files but no writer is also ignored.
Both cases pass the extracted checker.
This falls outside the documented refusal for a committed text fixture that no writer writes.

The frozen repository has two writer folders and no such orphan.
This is a refusal gap, not evidence that a current fixture lacks its writer.

Compare all candidate fixture folders with the discovered writer folders before invoking writers.
Refuse retained text files in a folder that has no writer.
Also reuse the existing source-path inventory pattern to invalidate the Make marker when a writer disappears.
Wildcard prerequisites alone do not remember a removed path.
Keep the same-folder extra-file refusal as a positive red control.
Add a deleted-writer control while another valid lane remains.

**Observation:** complete fixture accounting and checker refusal.
**Hypotheses:** one writerless fixture folder and at least one valid discovered lane.
**Exclusions:** directories outside `ocaml/engine/test/*`, writer semantics, and target execution.
**Prerequisite:** define the fixture folder domain consistently with `GENERATED_PATHS`.
This needs no second registry or new program representation.

## Independent checks

`probe.py` extracts the unchanged `install`, `fixture_lanes`, and `fixtures` functions from the frozen Python source.
Every `run` call uses a mock; no subprocess runs in the probe.
The mock writes deterministic fixture bytes into its requested folder.
All files live inside temporary scratch directories.

Nine controls pass their recorded expectations:

1. Unchanged known fixtures pass and retain their bytes.
2. A changed known fixture refuses in check mode.
3. A missing known fixture refuses in check mode.
4. An extra file inside a discovered lane refuses.
5. Write mode repairs a changed known fixture.
6. A writerless folder passes without examination.
7. Removing one writer leaves its retained fixture unchecked.
8. An aliased check output replaces a changed fixture and passes.
9. An aliased check output deletes an extra fixture and passes.

Command:

```sh
python3 /private/tmp/codex-effect4-overnight-monitor/heartbeats/2026-10-06T045135Z/freshness/probe.py
```

Output: `controls: 9`, `all_expectations_pass: true`, `actual_subprocesses: 0`.
These are Python checker results with mock writer outputs.
They do not establish Lean writer output or Make execution behavior.

## Retained coordinator evidence

`commit-receipt.txt` preserves the commit message as the available receipt.
It reports unchanged-tree stability, Queue edit repair, routing check refusal, and extra-file refusal.
It reports a successful default build: 953 jobs, 703 modules, 85805 declarations, and 29 planned goals.
It explicitly reports no dune run because no OCaml source or fixture byte changed.
Those counts and outcomes are coordinator-reported evidence, not independent reruns.
No separate raw command logs were supplied or discovered through the relevant tracked documents.

`source-hashes.json` binds all 18 retained source files to the frozen commit.
`receipt.json` also records the probe and retained-evidence hashes.
No active repository file was edited by this review.
