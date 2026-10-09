# Explanation module axiom repair

The reporting implementation keeps its extra axiom allowance through exact declaration roots.
The answer structures and their generated schema certificates retain `[propext, Quot.sound]`.

Base: `8785c6f989f7b25df220649a238e93eda03921cb`.
Repair head: `7251e432442c9751d6acdf4ef495276fffc703b1`.
Branch: `codex/explain-admission-fix`.
Worktree: `/Users/pooks/.codex/worktrees/module-field-inference/lean4-effect4`.
The preserved branch `codex/step-callback` stays at `e4fedc27e8d7f9c15a81fa224b149d3c73f5dddc`.

Proof role: trust detector controls.
Evidence status: checked finite metaprogram controls and narrow builds.
Scope: every compiled declaration of `Effect4.Laws.Author.Explain` and one generated certificate fixture.
No semantic theorem statement changes.
No whole-library acceptance or host result is established.

## Change and findings

`Test/Audit/AxiomGate.lean` removes the explanation module from `auditImplementationModules`.
It adds 24 reporting roots to `choiceImplementationDeclarations`.
The existing ancestor rule covers their same-module descendants.
No private explanation root requires an owner-name exception.
No answer structure or namespace receives an exception.

The compiled explanation module has 223 declarations.
Its 41 choice-reaching declarations include 24 exact roots and 17 descendants covered by the existing ancestor rule.
The probe checks all declarations, including generated helpers and instances.
The 12 generated `modeled_*` certificates reach only `[propext, Quot.sound]` or `[propext]`.
Every new exact root exists, reaches `Classical.choice`, and is not a theorem.
No measured choice-reaching descendant escapes the revised policy.

The fixture appends a structure that derives `Modeled` to the unchanged explanation source.
Its ordinary field model uses `inferInstance`.
Its mutant field model uses `Classical.choice` to select that same available model.
Lean compiles both fixtures under the real `Effect4.Laws.Author.Explain` module name.
The generated certificate's statement stays unchanged between the two sources.
The probe loads each compiled fixture into a separate environment.

The old policy accepts the mutant certificate.
The revised policy refuses its `Classical.choice` dependency.
The revised policy accepts the restored certificate and the reporting declaration `Tools.Explain.render`.
The certificate mutant reaches `[propext, Classical.choice, Quot.sound]`.
The restored certificate reaches `[propext, Quot.sound]`.

## Private policy extraction

The retained Python producer copies the actual private lists, ancestor functions, declaration predicate and axiom-filter loop.
Its JSON manifests record SHA256 hashes for each copied block and the whole gate source.
The predicate, ancestor functions and filter loop retain identical hashes across the two policies.
Only the declarations and module-exception lists change.

Old gate source SHA256: `bbda73dcef10641f48f80d7b5c572d3b88e92b4471338abbd6187a2100547201`.
Revised gate source SHA256: `7071b74017f5b039b584587bb34db0e7667ddff881271d756ff23bc3fee43ba4`.
Explanation source SHA256: `09d5eb11b793887209f4416b04fee2fa7c05f3d78df57615bd106b61e81e9bfd`.

The wrapper receives axiom arrays from the actual memoized `ProofGraph.reachedAxiomsMany` traversal.
It uses public exact exceptions because the private Config exceptions cannot identify an explanation declaration.
It does not run private-exception resolution, global staleness checks, module closure, unsafe checks or the whole gate.
The finite controls establish the revised axiom allowance for the named module and fixture only.

## Commands and results

Compiler: the pinned `leanprover/lean4:v4.33.1`.
Each completed command below exits with status zero.
Only one Lean command runs at a time in this worktree.

```sh
LEAN_NUM_THREADS=3 lake build Effect4.Laws.Author.Explain Test.Audit.AxiomGate
# Build completed successfully (265 jobs).

python3 docs/research/2026-10-08-explain-admission-probe.py --label old-mutant --policy old --certificate mutant
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true --root=docs/research/2026-10-08-explain-admission-probe-fixture-mutant -o docs/research/2026-10-08-explain-admission-probe-fixture-mutant/Effect4/Laws/Author/Explain.olean docs/research/2026-10-08-explain-admission-probe-fixture-mutant/Effect4/Laws/Author/Explain.lean
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true docs/research/2026-10-08-explain-admission-probe-old-mutant.lean
# PASS fixture certificate accepted.

LEAN_NUM_THREADS=3 lake build Test.Audit.AxiomGate
# Build completed successfully (263 jobs).

python3 docs/research/2026-10-08-explain-admission-probe.py --label revised-mutant --policy revised --certificate mutant
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true docs/research/2026-10-08-explain-admission-probe-revised-mutant.lean
# PASS certificate choice mutant rejected by the extracted policy.

python3 docs/research/2026-10-08-explain-admission-probe.py --label restored-clean --policy revised --certificate clean
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true --root=docs/research/2026-10-08-explain-admission-probe-fixture-clean -o docs/research/2026-10-08-explain-admission-probe-fixture-clean/Effect4/Laws/Author/Explain.olean docs/research/2026-10-08-explain-admission-probe-fixture-clean/Effect4/Laws/Author/Explain.lean
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true docs/research/2026-10-08-explain-admission-probe-restored-clean.lean
# PASS fixture certificate accepted.

python3 scripts/check-language.py --strict docs/research/2026-10-08-explain-admission-plan.md docs/research/2026-10-08-explain-admission-receipt.md
git diff --check
```

The `.txt` files retain the full measurement and detector output.
The producer creates links to existing dependency artifacts inside each fixture directory.
It excludes the fixture module's own output files from those links.
Replay the fixture compilation before the revised mutant reader on a fresh checkout.

Earlier research-wrapper drafts fail during compilation, module-owner lookup and compiled dependency lookup.
Those failures are not detector evidence.
The retained passing controls use genuine compiled ownership and the actual axiom walker.

## Changed files and remaining work

The production change is `Test/Audit/AxiomGate.lean` at the existing exception lists.
The research artifacts share the prefix `docs/research/2026-10-08-explain-admission-`.
They include the plan, producer, three hashed readers and their outputs, two fixture sources, and this receipt.
Compiled artifacts and dependency links are not committed.

The root agent independently reviews and replays the controls before integration.
The full axiom gate and the Test sweep remain outside this authorized slice.
No main-worktree build, merge or push occurs.
