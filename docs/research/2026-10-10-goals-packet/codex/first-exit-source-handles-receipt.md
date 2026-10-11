# First-exit source handle receipt

The compiled first-exit action names only handles already captured at its source point.
This slice depends on the checked backend handle commit `d70a1e35`.

Concept: residual-program-typing, serving the existing `actionAt_keys` source bound.
The consumer is `Handles.Hooks`, the native handle bridge used by the timeout form.
The new case uses the existing entrant handle theorem at the same source child addresses.
It establishes no reply admission, cleanup progress or outside-host execution claim.

- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.Handles.Layer`: the target passes in the bridge build.
- Lake reports the changed module build as 5.5 seconds.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/FirstExitSourceHandlesAudit.lean`: passes.
- The audit walks 363 declarations within `[propext, Quot.sound]`, with zero goals and zero declarations modulo goals.

The combined typed bridge build still reaches an unfinished backend `Simulation.Drive` selection transport.
The backend lane owns that dependency.
