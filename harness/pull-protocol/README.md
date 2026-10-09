# Emitted Pull protocol callers

This packet checks exact emitted declarations for the existing Chunk/End value protocol.
The producer uses the sources in `Test/Program/Pull.lean` through `Api.Author.program`.
It checks emission, source reading, and numeric observations on the Lean machine.
Expected numbers come from the case inventory, independently of the machine observation.

The callers observe batch payloads, end leftovers, input failures, retained Ref state, and finalizer failures.
An outer cause handler receives failures from the selected success or end handler.
A deliberately wrong expansion catches those failures inside Pull's handler selection.
The correct cases answer 42, and the wrong controls answer 99.
The compiler must accept both before their observations are compared.

## Run

Use installed Effect 4.0.1 and tsgo 7.0.0-dev.20260629.1.
The shared runner checks both versions and refuses an occupied output directory.
It installs nothing.

```sh
python3 harness/pull-protocol/run.py --install /path/to/node_modules --out /path/to/new-evidence
```

Pass `--skip-build` only after `LEAN_NUM_THREADS=3 lake build Test.Program.Pull` passes in this worktree.

The evidence retains emitted declaration bytes, the manifest, compiler inputs, commands, version pins, observations, and hashes.
The checks establish finite emitted-program observations for these callers.
They establish no native Pull.Done correspondence or mixed Done cause behavior.
They establish neither nonempty batches nor asynchronous progress.
They establish no simulation against Effect's Pull implementation.
