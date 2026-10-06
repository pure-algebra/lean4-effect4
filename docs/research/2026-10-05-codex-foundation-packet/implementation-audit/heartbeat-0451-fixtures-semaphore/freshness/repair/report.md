# Fixture repair review

The active repair resolves the two original witnesses.
Fourteen focused controls confirm the expected repair behavior.
A fifteenth control finds one remaining output-alias case.

**Role:** checker review. **Evidence:** extracted Python functions with mocked commands.
**Scope:** the two source snapshots recorded in `source-hashes.json`, on base HEAD `6a8ee9c2b11035d79d373d7717add33b9439e22b`.
These are active working-tree bytes, not a commit or acceptance receipt.
No repository file was edited by this review.
No build, Lean, generator, compiler or host runtime ran.

## Verified repairs

`fixture_lanes` now checks for text files whose folder has no writer.
It refuses both a new writerless folder and a folder whose writer was removed.
Both controls refuse before requesting any command.

`fixtures` now checks resolved output paths before clearing files or requesting commands.
A direct output alias refuses without changing any repository bytes.
A root symlink and a lane symlink to the same destination also refuse without changes.
An alias in the second lane refuses before any first-lane command runs.
An output symlink to independent scratch storage remains accepted.
Write mode also refuses a direct repository alias.

The original unchanged, changed, missing, extra-file and write-repair controls keep their expected results.

The Makefile adds a forced path-inventory comparison for all fixture files and writers.
The fixtures marker depends on that inventory.
Its comparison follows the existing source-inventory pattern and remembers deleted paths.
This is source evidence only; this review does not run Make or test its timestamps.

## Remaining case: an output lane aliases another repository lane

The preflight compares each output folder only with that lane's matching repository folder.
It does not compare against the other repository lanes.

The control links the temporary Queue output folder to the repository scenarios folder.
That resolved path differs from the repository Queue folder, so preflight accepts it.
The checker clears `routing.txt` and writes `queue.txt` inside the repository scenarios folder.
A later check refuses the unexpected `queue.txt`, after those bytes have already changed.

This narrows the remaining issue to mutation before refusal.
It does not show a normal current generator run corrupting fixtures.
All command requests use a deterministic mock writer in isolated scratch directories.

Compare every resolved output lane with every resolved repository lane before any mutation.
Retain the existing direct-alias and independent-symlink controls.
Make this cross-lane control refuse with zero requested commands and identical before/after bytes.

**Consumer:** `--only fixtures --output-dir` and the fixture checker.
**Property:** check-mode alias refusal occurs before any repository fixture mutation.
**Hypotheses:** a supplied output lane resolves to any repository fixture lane.
**Observation:** refusal, command requests, and exact repository bytes.
**Exclusions:** unrelated directories, Lean writer behavior, and runtime agreement.
**Prerequisite:** the existing complete lane inventory.
No new semantic registry or proof claim is required for this Python checker repair.

## Reproduction

Run only this isolated probe:

```sh
python3 /private/tmp/codex-effect4-overnight-monitor/heartbeats/2026-10-06T045135Z/freshness/repair/probe.py
```

It extracts `install`, `fixture_lanes`, and `fixtures` from the retained repair source.
It replaces every `run` request with a mock writer.
It compares all repository files before and after each control.
Its output reports 15 controls, all expected observations confirmed, and zero actual subprocesses.
The last expected observation is the remaining failure, not a successful repair assertion.
