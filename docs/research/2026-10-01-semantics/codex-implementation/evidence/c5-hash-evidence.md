# C5 saved-output and publication controls

Twelve private Python controls passed. The log, runnable controls and JSON receipt are adjacent files. The receipt identifies the exact checker bytes checked, command, output and source hashes.

## Command and result

```sh
PYTHONDONTWRITEBYTECODE=1 python3 /private/tmp/codex-second-eyes-2026-10-01/semantics-implementation/c5-guard-controls.py > /private/tmp/codex-second-eyes-2026-10-01/semantics-implementation/c5-guard-controls.log
```

Exit 0; final output: `PASS C5 guard controls: 12 finite controls; no compiler or live artifact mutation`. Python parsing occurs before the controls. `git diff --check -- scripts/check-semantics.py` also exits 0.

## Hash algorithm and boundary

The checker computes MurmurHash64A over binary bytes with seed 11, then wraps that UInt64 value in `mixHash(1723, value)` and renders sixteen lowercase hexadecimal digits. UInt64 operations wrap modulo 2^64; full eight-byte chunks use native byte order, and the final byte tail uses the shifts in the pinned C++ implementation. It compares with saved trace descriptors, never a sibling mutable `.hash` cache.

Each prepared target is checked directly; its Lake setup file supplies the resolved transitive import artifact paths. The checker verifies primary/server/private oleans and optional IR/signature files recorded in each module trace. No rebuilt module is exempt. Each file is limited to 128 MiB; the traversal checks a 180-second deadline. An earlier read-only comparison of 1,051 existing artifact files passed in 15.05 seconds. This does not claim cryptographic authentication or full-library axiom auditing; bundled toolchain imports remain the pinned-toolchain boundary.

The report roots must fall within the verified preparation targets. Generation stages its bytes, checks source/trace stability and artifact freshness, then publishes both reports; a failed partial publication restores prior bytes. The controls cover accepted and corrupt root/import artifacts, unprepared report roots, size/time bounds, publication success/rollback, and final snapshot/freshness failures leaving outputs intact.

## Pinned source references

- `/Users/pooks/.elan/toolchains/leanprover--lean4---v4.33.1/src/lean/lake/Lake/Build/Common.lean:213–219, 394–408`: Input freshness/existence does not compare saved output bytes. SHA-256 `a6bb844e1fa5b3129aaa2f1f20697a713bccffd95e6a2e821cd9877432b8ea35`.
- `/Users/pooks/.elan/toolchains/leanprover--lean4---v4.33.1/src/lean/lake/Lake/Build/Module.lean:635–643, 1069–1078`: Resolved transitive setup map and the already-up-to-date computeArtifacts path. SHA-256 `cd7b3e4802980fb9a9c1ed116650b2a95231917e4e024ca5b46b4f3821effa5c`.
- `/Users/pooks/.elan/toolchains/leanprover--lean4---v4.33.1/src/lean/lake/Lake/Build/Trace.lean:108–109, 169–182, 228–229`: Lake hash wrapper and binary file hashing. SHA-256 `ae8987432fdb2f722971c7dfa10096e138dfc9f244a75aeb5e7abbd2cbd94bff`.
- `/Users/pooks/.elan/toolchains/leanprover--lean4---v4.33.1/src/lean/lake/Lake/Build/ModuleArtifacts.lean:29–51`: Saved outputs.o, rs and r descriptors. SHA-256 `1091eb0ead35906bee28ac2e4e66fa8b6ae356fd411383aa65b0ea6853aaff1e`.
- `/Users/pooks/.elan/toolchains/leanprover--lean4---v4.33.1/src/lean/Lean/Setup.lean:66–107`: ImportArtifacts nested-array encoding. SHA-256 `eff05a30636e084ecf7c52e4019a1f5497d48b5b023b73f0e979abde91d419a5`.
- `/Users/pooks/.elan/toolchains/leanprover--lean4---v4.33.1/include/lean/lean.h:2152–2160`: UInt64 hash mixing implementation. SHA-256 `02af0040283143b264e3a44b06b348b6973ae6037fa8f550701c83dd7a062ace`.
- [MurmurHash64A and hash_str.](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/runtime/hash.cpp), lines 13–54.
- [ByteArray hash calls hash_str with seed 11.](https://raw.githubusercontent.com/leanprover/lean4/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/runtime/object.cpp), lines 2460–2462.
