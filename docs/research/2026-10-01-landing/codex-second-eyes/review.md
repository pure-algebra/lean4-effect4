# Second-eyes review: allocation loses scope-presence evidence

**One confirmed blocker in the current M5 statement:** an ordinary checked program that creates a scope and forks into it cannot satisfy the reference-program typing judgment after seat I's new scope-presence premises. The program has no finalizer, external call, layer reference or malformed value. This is a proof-contract mismatch, not an observed runtime failure.

Reviewed seat I at `509d243c31b5c324fd7af19a70781dd5ea810e10`. Main was `25f47ce0`; seat I was not merged. Its subsequent `9247d623` does not change `Residual.lean`. No Claude repository/worktree was changed; no Claude seat was contacted. One independent read-only reviewer helped identify the candidate; all compiler runs were serial in this temporary snapshot.

## Checked evidence

The final [probe](ScopeAllocationPost.lean) imports production definitions, with an independently recompiled `Residual.lean` from the exact reviewed commit.

- `forkAfterMake_checked` proves the source checker accepts “make a sequential scope; fork a unit-returning child into that scope” at `pure (fiberOf unit never)`.
- `forkAfterMake_denotation_refused` proves its denotation at compile budget 20 has no `TypedProg` derivation, at any result type, in any world where scope 0 is absent. No assumption that the program fails to type is smuggled into the premises.
- `m5_denotation_shape_false` refutes the exact quantified proposition of `DenotesTyped` (`Assembly.lean:797–800` at the pinned commit). It restates that proposition locally to avoid building unrelated active integration modules. All source-location, checker and environment premises are supplied.
- A finite runtime control at fuel 40 succeeds and returns fiber 1. It establishes only that concrete run.
- `makeThenClose_refused` independently isolates the same mismatch without fork machinery.
- Passing controls prove the allocator alone is typed, and closing an existing scope is typed. Guards check real allocation returns a handle and installs the corresponding store entry. A malformed source using a number in place of a scope is rejected.
- `enriched_post_supports_close` proves a post carrying scope presence suffices for the close continuation. This is a local repair-direction check, not a repaired M5 theorem.
- `absent_scope_still_fits` proves the related value-membership gap: a scope handle can currently fit `Ty.scope` while its scope is absent. This broader scope-validity issue is already recognized by decision row 139.

All nine printed theorems use only `[propext, Quot.sound]`; no `sorryAx`, `Classical.choice`, or native decision axiom occurs. The five guards pass. See [final compiler output](scope-allocation-post.log) and [exact commands, timings and exit codes](verification.json).

## Why the new rules fail to compose

The allocator's post (`Residual.lean:90`) says only that its answer is a scope-shaped handle. It supplies no evidence that the handle names an entry in the answer world's scope store. `TypedProg.store` must handle every answer allowed by that post at every later world, including the unchanged world. Choose scope 0 in an empty store: the post accepts it, but `forkIn` (`:177–178`) and `closeScope` (`:169`) now require its entry to exist. The continuation is therefore impossible to type even though actual allocation creates that entry.

This is distinct from the already-recorded lone-finalizer and encoded-defect findings (rows 151–152), the layer-reference issue (153), and the known scopeExit special-constructor bypass that seat I already documents. It is a concrete allocation/consumer consequence of row 139 that the present integration acceptance controls do not cover.

## Recommended follow-through

Keep the new consumer checks. Carry the existing scope-presence fact through scope-producing posts, establish it from the actual store operation, and preserve it through world extension. Check scopeMake, scopeFork, memoBuild, memoRelease and ambientScope individually; their similar answer shapes are candidates for inspection, not five proved defects.

Use one shared scope-presence predicate and its transport lemma across allocation, value/environment membership and consumers, consistent with row 139. A post-only amendment repairs the demonstrated continuation but does not establish the broader M5 statement while scope membership still ignores presence. The closed allocation/fork source should remain a positive acceptance control, alongside allocation/close. Validate ordinary admitted programs under any value-judgment amendment before calling it a repair.

The unchanged admission census counts which operations programs reach; that count cannot establish that their denotations remain typable after a contract change. These source-level positive controls are the useful acceptance criterion.

## Isolation, provenance and limits

The dependency snapshot uses filesystem copy-on-write copies, not hard links into an active build. All project dependency sources were compared byte-for-byte with the reviewed commit. 1,372 source/artifact hashes were checked against Lake build records; the module and source manifests are in `manifest.json`, `root-provenance.json` and `hash-verification.log`. External dependency hashes were checked against their recorded builds. The toolchain is Lean 4.33.1.

The final probe used one compiler thread, a 2,048 MiB Lean memory limit and a 60-second process timeout; it completed in 1.336 seconds. No full build, test suite, generator, dependency installation, production edit or branch movement was performed. `verify.py` reruns the provenance check and final probe. Earlier `scope-attempt*.log` files are exploratory iterations, not verification results; the final log is clean.

This review does not establish M6 command preservation, M7 runtime equivalence, host safety, verified lowering or performance of a repaired implementation. It identifies one false current proof target and tests a bounded repair direction. Existing M7 scope restrictions and historical/current refutation distinctions remain intact.
