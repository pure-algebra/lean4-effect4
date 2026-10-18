# ST2 checked disk writer

Merge requires the current ST1b source and the listed root connections.
Production remains unchanged by this packet.

## Scope

The disk boundary owns one writer and immutable checked images.
Images contain ordered accepted bytes, exact roots, and their durable boundary.
Every raw node passes byte reading before the shared semantic admission.
The generated admission family includes the concrete disk fault owner.
Three former byte-error mappings now use the generated adapter.

`RecoveryImage.read` checks every raw node with `Node.read`.
`Cas.restoreBytes` then records an accepted restore event from the empty store.
Recovery retains exact checked root generations.
It establishes no historical ancestry or past generation provenance.
ST4 Exchange and S6 can consume the resulting `Cas` directly.

## Evidence

Proof role: checked recovery preservation and compatibility.
Evidence status: Lean-proved.
Scope: accepted empty-store restoration, exact roots, node closure, and fixed-kind durable root targets.
`RESTORE-PLACEMENT.md` records all five placement facts.
`Effect4.Store.restore_roots`, `restore_closed`, and `restore_targets` compile.
The audit reports 1041 declarations within `[propext, Quot.sound]`.
It reports zero goals and zero declarations modulo goals.
The exact commands and output remain in `build-overlay.log`.

Evidence status: finite host checks.
Scope: the explicit native test inputs and process interruptions.
`opam exec --switch=effect4 -- dune runtest --force --root /private/tmp/seams-st2-sol/ocaml engine/cas/test` passes.
`native-full-store.log` and `native-full-store-final.log` retain the complete output.
`opam exec --switch=effect4 -- dune build --root /private/tmp/seams-st2-sol/ocaml @all` passes.
`native-all-build.log` retains its output.

The actual Cas producer emits 12 states, 14 actions, and 168 transitions.
The qcheck-stm harness passes 300 command lists, each bounded by 40 commands, using seed 1739.
Unknown actions and missing transitions refuse before writing.
The model transition is a table lookup over actual Cas results.
It contains no independent store interpreter.

Six children receive SIGKILL at actual write, sync, and publication hooks.
Reopened images match the corresponding actual accepted `Cas.interrupted` cuts.
These checks establish no power-loss or general filesystem theorem.

Snapshot checks retain earlier nodes, roots, and boundaries through later writes and index rebuilds.
The retained old mutable-view assertion fails in a child, as expected.
A premature-publication mutation fails the same kill harness before the first write.
A missing-table-row mutation fails before writer initialization.
`retained-controls/` contains original failures, mutated artifacts, and source hashes.

## Corrections retained

A legacy v1 generation-two root differs from a new create plus identical duplicate at generation one.
Recovery therefore admits a checked image instead of inventing a commit journal.
The original byte phase assertion fails and remains retained.
Native raw strings now pass byte reading before semantic admission.
The Lean Val-data oversize-before-version law remains unchanged.
Identical encoded bytes receive the same native put and put_bytes answer.

Published bytes lost and sealed segment damage return concrete faults.
Only a writable, uncommitted tail permits truncation.
The original X1/X4 witnesses and three damage failures remain retained.
All damage controls check unchanged pack evidence and control bytes.
The empty no-root `(0,0)` boundary sentinel alone normalizes to the pack header.
This normalization changes no root generation.
The pre-existing vacuous R4 row is removed; the real checksum row remains.

## Integration

`source-manifest.json` records every source, target, preimage hash, and final hash.
`st2-all.patch` passes read-only `git apply --check` against current production.
The coordinator connects Recovery to Laws and SeamsRecovery to Test/All.
SeamsRecoveryAudit remains a receipt audit input.
The coordinator places the three registry questions from `RESTORE-PLACEMENT.md`.
The cas producer gains both actual disk oracle outputs and their Makefile inputs.
Its existing cross-artifact alias guards remain intact.
The generated fault family requires E4_fault before native compilation.

qcheck-stm 0.10 requires qcheck-core 0.91 and qcheck-multicoretests-util 0.10.
Installation changes no existing package or compiler version.
`opam-install.log` and the before/after inventories retain that evidence.

The actual CasGoldens, CasDiskOracle, CasDiskCuts, and Gallina producers pass.
The wrapper command is `python3 /private/tmp/seams-lean-one.py lake env python3 /private/tmp/seams-st2-sol/final-producers.py`.
It runs from the production worktree and writes only the isolated packet.
The child commands remain in the corresponding generation logs.
All five Rocq files compile under the rocq switch; `rocq-st2.log` retains the commands and hashes.
These existing Rocq facts establish no native crash theorem.

Packet base HEAD is `709f9f10a9401150af66870a8665860e45cc63d3`.
Unrelated V1 edits present in production remain outside this patch.
The packet has no commit; the source manifest identifies its exact bytes.
The native suite runs again against the newly emitted goldens in `native-full-store-final.log`.
The CI OCaml setup adds the same three pinned qcheck package versions.


## Freeze

The final concrete legacy-root reader and audit pass.
#axiom_audit: 1041 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals

No agent process remains active or queued.
ST3 implementation has not started.
`NEXT-ST3.md` records the compiled coordinator preparation and the uncompiled next integration.
