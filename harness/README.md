# Host conformance harnesses

This directory holds exact-pin TypeScript, Effect v4 runtime/replay, and
`@effect/tsgo` language-service checks. Harness output is evidence about a
named host profile and file set; it never defines the Lean semantics. Each
section below states one harness's purpose, its entry script, its pins, and
what a pass does and does not establish.

The entry point for all of them together is the Makefile (`make help`): `make check`
is the tier that runs after every change, `make check-full` adds the outside oracles
(the TypeScript typing oracle, the schema codec, the OCaml tests, the ingest smoke), and
`make check-full` is everything, the long censuses included.
Each check is a rule keyed on the files it reads -- its fixtures, the goldens it
compares with, the Lake trace of the compiled core, the pinned host manifests -- and is
skipped while none of that has changed; `make -B <target>` or `make clean-check`
forces it. One Lean process runs at a time. (Until 2026-09-13 this was
`git:c67ff096:scripts/sweep.sh` with a per-script result cache; the script survives as a wrapper.)

`truth/` holds the truth corpus and the host its printed modules import. `Truth.lean` writes
the hand corpus's manifest (`harness/truth/corpus.json`) and one printed module per program
(`harness/truth/generated/`); `make gen-truth-corpus` runs it. The target and reader lanes of
`make check-ts` read both. The prelude (`harness/truth/prelude.ts` and its siblings) is the host
of every printed module. The rc.112 differential that ran these modules was deleted on
2026-10-20, with its tapes, its results and the lane of the 400 generated programs
(`git:fa7bdc304:harness/truth`).

`schema-generation/` and `schema-host/`, the schema-ts lane retired on 2026-10-18, were deleted on
2026-10-20 with the seven hand packets and `ts_packet.py` (`git:38b94bdec:harness/`).

`trace/` and `effect-v4-family/` were archived to branch `archive/flow-route`
on 2026-09-04 with the Flow route they served, together with their gates
(`check-trace-*.sh`, `check-lowering-*.sh`), their goldens under
`git:606918eb:generated/traces`, and the trace DAG note (not retained).

The former fiber-supervision harness was retired with the old supervision calculus.
Its observations remain historical evidence in git; it is not a runnable lane here.

