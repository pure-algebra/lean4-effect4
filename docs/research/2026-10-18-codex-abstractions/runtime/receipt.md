# Prepared interpreter receipt

## Current verification receipts

- `python3 /private/tmp/seams-lean-one.py lake build Effect4.Program.Admit Effect4.Laws.Program.Admit`: pass, 317 jobs.
- `python3 /private/tmp/seams-lean-one.py lake build Test.Program.PreparedAudit Test.Program.TypedContract Effect4.Api`: pass, 962 jobs.
- Temporary audit imports `ProofGraph.AxiomAudit` and names only `Effect4.Program.Admit Effect4.Laws.Program.Admit`.
- Audit: `792 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals`.
- Actual generated-package client checks: retaining `Effect4_gen.Api_gen.prepared` compiles; constructing it from `unit` fails; replacing its table fails.
- The table update fails with `Unbound record field table`, so the whole generated package is abstract.
- The first gate attempt reaches native compilation and exposes one stale hand adapter type signature; it is repaired.
- That attempt uses the Makefile `LAKE` override, which does not wrap `scripts/generate.py`'s hardcoded `lake` calls.
- The final gate instead uses a PATH shim that forwards every `lake` invocation through the approved wrapper.
- Final command: `PATH=/private/tmp/abstractions-runtime-bin:$PATH make check-ocaml LAKE=lake`.

The `Prepared.step_eq` placement has five fields:

- Concept: `translation-simulation`; property: exact interpreter reuse at a fixed source.
- Question: proposed registry claim `native-prepared-step`, role compatibility. Pointer: `Effect4.Program.Prepared.step_eq`, `src/Effect4/Laws/Program/Admit.lean`. Consumer: `E4_instance.step`, then `E4_engine.Make.step`.
- Reach: every prepared package, machine, decision and fuel. Observation: the whole resulting machine and command-sufficiency flag. Decision row 391 bounds the LCNF lowering claim.
- Does not establish: reply admission, source ownership of an arbitrary supplied machine, progress, outside-host behavior, lowering correctness or machine/tree agreement.
- Unlocks: interpreter reuse in the native R6 interface without changing its decision step.

Reference pins, read directly:

| Shelf | HEAD |
| --- | --- |
| InteractionTrees | `68b3568d3f0f48c057192c58c8db88ef4412747a` |
| Eio | `1fa776212551d717dfa19041328cceda1db97797` |
| CompCert | `e276a3f881669252e2a5c4b5fec06f51f7143161` |
| Vellvm | `4c6db50077cbc0df3fb3156c0570129201cc35f3` |
| Aeneas | `557eff83ecef5083b98a52a94ca7fae63d6c1dab` |
| lean-mlir | `b8c4a771319a044854a4bbb49b8821381ef86ff8` |

## Final landing receipt

**The one thing to know before integration:** only the native engine's decision path reuses the prepared interpreter.
The recursive replay walkers and `Api.HostSession` retain their current construction paths.
No claim covers all `Live` or `Tool` requests.

- Base: `cd2cea0de813ed2e22ecf53f1c0eb6c20468b131`.
- Head: `79e2c4d84601f32ca6d2ae0cff2eb8ca4f4952e8`.
- Branch: `codex/abstractions-runtime`.
- Patch: `/private/tmp/abstractions-runtime.patch`.
- Worktree status after commit: clean.
- `git diff --check`: pass.
- Final focused build: `python3 /private/tmp/seams-lean-one.py lake build Test.Program.PreparedAudit Test.Program.TypedContract`: pass, 962 jobs.
- Final audit: `792 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals`.
- The temporary audit module is deleted after verification. It is not an orphan in the committed tree.
- `python3 scripts/check-lcnf-sealing.py`: pass, 2 lawful aliases and 12 hostile sealed-package clients.
- Final behavior gate: `PATH=/private/tmp/abstractions-runtime-bin:$PATH make check-ocaml LAKE=lake`: exit 0.
- The gate reports `PASS native: shared result eae05ee17bd3`, `PASS compiler: shared result 623ea144ee19`, and `PASS ocaml: recorded 9913e5e23f3b (45.151s)`.
- The native differential reports zero divergences or unvalidated tapes across its golden, truth and Lean corpora.
- The Lean corpus portion covers 408 programs, 2,448 tapes and 106,080 projection comparisons.
- `gen-check: PASS` confirms the generated engine and its current prelude compile through the checked interface.

The changed files are the core package, its law and battery, native engine adapters, their interface and controls, and regenerated OCaml closures.
`scripts/check-lcnf-sealing.py` retains the new package's positive alias and hostile table/interpreter clients.
`Program.stepChecked` and its generated root are removed.
Raw `interp_of` remains for low-level spawn controls, and no native step accepts it.

The benchmark command is `cd ocaml && opam exec --switch=effect4 -- dune exec engine/test/test_stable_step.exe`.
It repeats the same closed source and decision 10,000 times.
It compares constructing a new package each time with reusing one package.
It does not measure the old `stepChecked` implementation or a whole application workload.

| Instance | Prepare and step, allocated bytes per decision | Reuse and step, allocated bytes per decision | Difference |
| --- | --- | --- | --- |
| Fast | 10071.3 | 9020.1 | 1051.2 |
| Ref | 10494.0 | 9440.4 | 1053.6 |
| Gen | 9236.0 | 8188.2 | 1047.8 |

CPU timing changes direction across runs and instances.
This evidence establishes about one KiB less allocation per decision in this finite control.
It establishes no general runtime speedup.

The source interpreter remains trusted after lowering under row 391.
The law proves the Lean decision step's equality, not the lowering or outside host behavior.
The `native-prepared-step` registry row remains a coordinator proposal, with the exact pointer and five-field placement above.

The audit module contains:

```lean
import Effect4.Laws.Program.Admit
import ProofGraph.AxiomAudit
#axiom_audit Effect4.Program.Admit Effect4.Laws.Program.Admit
```

The PATH shim contains:

```sh
#!/bin/sh
exec python3 /private/tmp/seams-lean-one.py /Users/pooks/.elan/bin/lake "$@"
```
