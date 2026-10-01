# F application and verification

Prepared from the saved F implementation patch with SHA-256
646bce8ad956bf8b898e85dd22d33a763af33b61cbbcac823ac7babaecdf3715.
This preparation ran no Lean, lake, dune, make, or generators and changed no repository file.

## Application

The script is /private/tmp/f-source-apply.py. Its default renders only under /tmp.
For root to apply, after the serialized C work has settled:

    python3 /private/tmp/f-source-apply.py --apply

It validates all old hunk text before writing, requires exactly one match per hunk, and admits
exactly eight source/test paths. The one deliberate context adjustment is Test/All.lean:
LayerEnvironment is inserted immediately after A's now-landed HostHandleForgery import,
as addendum 2 requires. The original F patch used the LiveStack anchor because A was stopped.

The eight paths are:

- Test/All.lean
- Test/Counterexamples/Machine/Runtime/LayerEnvironment.lean (new)
- ocaml/engine/test/test_engine.ml
- src/Effect4/Program/Compile.lean
- src/Effect4/Laws/Program/Agreement.lean
- src/Effect4/Laws/Program/DenoteR.lean
- src/Effect4/Laws/Program/Handles/Layer.lean
- src/Effect4/Laws/Program/Intro/Layer.lean

These original-patch snapshots are EXCLUDED entirely:

- ocaml/engine/api_engine.ml
- ocaml/gen/api_gen.ml
- ocaml/gen/closure-api_engine.tsv
- ocaml/gen/closure-api_gen.tsv

All generated output is produced by the real generators after applying F. Copying those old
snapshots would lose A/C changes. Other generated paths may be emitted by the prescribed
producer chain; retain them as producer output, never patch them from the old snapshot.

Both supported starting states were checked read-only: the current tree after C step4 and
step5 source deletion, and git ref 90df5d21 (A only, if C is restored under a scope stop).
The exact old hunk assertions passed on both, and all eight resulting source/test files were
byte-identical between the two renders. The script does not change C's machine files or its
research. --base-ref is validation-only and cannot be combined with --apply.

The current rendered source.patch and deferred register-after-success.patch passed
git apply --check. Python syntax passed. This is patch validity, not Lean/build verification.

## Narrow source and test checks

Run sequentially in the designated worktree, preserving exact commands and exits. One lake at
a time. These names follow the old F receipt and include changed source plus direct proof users:

    env LEAN_NUM_THREADS=1 lake build Effect4.Program.Compile Effect4.Laws.Program.DenoteR Effect4.Laws.Program.Agreement Effect4.Laws.Program.Handles.Layer Effect4.Laws.Program.Handles.Hooks Effect4.Laws.Program.Intro.Layer Effect4.Laws.Program.Intro.Scope Effect4.Laws.Program.Intro.Memo Effect4.Laws.Program.Guard.RaceSites Effect4.Laws.Program.RuntimeR

    env LEAN_NUM_THREADS=1 lake build Test.Counterexamples.Machine.Runtime.LayerEnvironment Test.Program.RuntimeRContract Test.Program.ProvisionContract Test.Program.LayerSharingContract

    env LEAN_NUM_THREADS=1 lake env lean -DwarningAsError=true docs/research/2026-09-30-seat-codex-slice6-evidence/F/axioms.lean

The battery itself prints axioms for seven theorem declarations. The separate F/axioms.lean
prints Point.layerBuild_env, Point.layerBuild_path, and Point.layerBuild_fuel. Capture those
outputs. The fixture's concrete executions are finite guards at budget 200; its
fiber_exit_agreement theorem uses the existing native/reference simulation and does not turn
the concrete guards into a general typed-preservation theorem.

Required results in LayerEnvironment:

- errLeak: string failure x on native and reference.
- forkLeak: child 1 succeeds with string x on both.
- discardLeak: string failure x on both.
- crash1: succeeds with nat 2 on both, no badName defect.
- The existing controls, bodyRetainsOuter, and serviceContextRetained remain green.
  Both settings of localBuild must pass for the latter two controls.

## Fresh regeneration and OCaml runtime check

Because the old generated snapshots were excluded, start at derived and lcnf again. Do not
resume at eff merely because the historical run already generated an older tree.

    env LEAN_NUM_THREADS=1 make gen-derived
    env LEAN_NUM_THREADS=1 make gen-lcnf
    env LEAN_NUM_THREADS=1 make gen-eff
    env LEAN_NUM_THREADS=1 make gen-wire
    env LEAN_NUM_THREADS=1 make gen-cas

In the worktree's ocaml directory:

    opam exec --switch=effect4 -- dune build
    opam exec --switch=effect4 -- dune exec engine/test/test_engine.exe

The engine executable now contains layer_environment_check on both Fast and Ref carriers.
Retain its actual printed lines, each with the expected value:

    layer environment Fast: failure [fail(text x)]
    layer environment Ref: failure [fail(text x)]

Then from the worktree root:

    make check-ocaml

Use the existing effect4 switch. Do not adjust the OCaml test carrier API or hand-edit generated
code to make the expected result pass. Inspect the actual producer diffs, including the two
closure manifests explicitly allowed by addendum 4. The generated output must include whatever
A/C runtime state is retained at the F landing.

## Deferred register change and receipt

The exact current CE005 row replacement is rendered to:

    /private/tmp/f-source-candidate/register-after-success.patch

The source apply script NEVER applies it. After the source, tests, generated targets and
actual Fast/Ref engine assertions succeed, apply this one-row patch by explicit path. Its
default repair date is 2026-10-01, configurable using --repair-date before rendering. Row 104
in docs/core/decisions.md remains the coordinator's; no decisions edit is included.

The proposed row cites the committed repaired battery and the engine assertion, states the
closed build environment and retained body/service context, and claims engine success only
on the understanding that this deferred patch is applied after those runs succeed.

Addendum 4 explicitly retains the historical run comparison as finite evidence: 37 truth
fixtures and 400 random depth-4 programs, no run/runSync value changed. The saved commands,
before/after JSON and run-comparison.log remain under the original F evidence directory.
Do not describe this historical finite comparison as a fresh comparison at the new F commit,
as unrestricted equivalence, or as an M5/M6 proof. The freshly rerun battery and engine
assertions provide the new landing evidence.

Commit F in one commit by explicit source/test/register/generated/evidence paths, with force-add
for selected research files, and no push. The script neither commits nor modifies the register.
