# Module authoring receipt

The declared operations use the existing program checker, machine and TypeScript printer.
The change adds no module simulation law.
Queue and Semaphore definitions execute in the focused Lean and pinned TypeScript checks.

## Revision and scope

Base: `f0ca3dcb30741622ea08341ae8ebc8499b1f4291`.
Implementation head: `c7e63c9612911ce323df33525122227872a21b27`.
Branch: `codex/module-authoring`.
This receipt follows that implementation head.
The original checkout remains unchanged. Nothing is pushed.

| Files | Change |
| --- | --- |
| `src/Effect4/Program/Authoring/Defs.lean` | Reject declared arity mismatches and encode printable operation names |
| `src/Effect4/Program/Authoring/Module.lean` | Generate an authoring record, definitions, invocations and installation from `eff_module` |
| `src/Effect4/Modules/Queue/Defs.lean` | Declare each signature once and retain the old entry points and names |
| `src/Effect4/Modules/Semaphore/Defs.lean` | Declare `take`, `release` and `takeIfAvailable` through the same command |
| `src/Effect4.lean` | Reach both new library modules from the runtime root |
| `Test/Program/AuthoringDefs.lean` | Control parameter count and printable names |
| `Test/Program/AuthoringModule.lean` | Exercise generated declarations, metadata, recursion, installation, refusals and macro hygiene |
| `Test/Program/ModuleDefinitions.lean` | Run Queue and Semaphore through generated invocations and explicit dependencies |
| `Test/All.lean` | Reach the new batteries |
| `docs/core/api-surface.md` | Describe the implemented syntax and its boundaries |
| `docs/STATE.md` | Link this receipt from the procedures entry |
| `docs/research/2026-10-08-module-authoring-design.md` | Record the design before implementation |
| `docs/research/2026-10-08-module-authoring-probe.lean` | Audit changed declarations and write finite host examples |
| `docs/research/2026-10-08-module-authoring-host.py` | Typecheck and run those examples using the existing truth prelude |

## Checks on 2026-10-08

Run these commands from the implementation worktree.
The final focused build reports success for 513 jobs.

```sh
LEAN_NUM_THREADS=3 lake build Effect4.Modules.Queue.Defs Effect4.Modules.Semaphore.Defs Test.Program.AuthoringDefs Test.Program.AuthoringModule Test.Program.ModuleDefinitions Test.Program.QueueDefs Test.Program.QueueEngine
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true --run docs/research/2026-10-08-module-authoring-probe.lean
python3 docs/research/2026-10-08-module-authoring-host.py --modules /Users/pooks/Dev/lean4-effect4/ts/eff/node_modules
git diff --check
python3 scripts/check-language.py --strict docs/research/2026-10-08-module-authoring-design.md
```

Each command exits zero.
The probe uses the existing `ProofGraph.Audit.auditedFacts` and `ProofGraph.reachedAxiomsMany` scanners.
It audits the changed library modules and their focused batteries.
Its final output follows.

```text
Narrow authoring audit: 7 modules, 548 declarations; axioms [propext, Quot.sound]
Wrote 4 finite host examples
```

The pinned host command reports the following versions and observations.

```text
Effect 4.0.0-rc.112; tsgo 7.0.0-dev.20260629.1; bun 1.4.2
{"queue":[3,"three","None"],"semaphore":[1,2,true,false],"waiting":[1,1],"combined":[23,1]}
PASS: four generated authoring examples typecheck and return their expected answers
```

The existing Queue fixture remains byte-identical through `Test.Program.QueueEngine`.
The focused batteries check missing dependencies, duplicate installation and conflicting specializations.
They check primitive definition-header reconstruction and retain the complex-header refusal.
No whole-library battery or closure sweep runs in this slice.

## Review repairs

The original `Def.of` accepted missing and surplus parameter declarations.
It now requires the declared parameter count to equal the operation's arity.

An independent probe found generated helper names capturing an author's global name.
Fresh macro scopes repair that capture. The probe now returns the author's value.

The final declaration inspection found error-recovery declarations from an expected macro failure.
That negative control now elaborates inside `Lean.withoutModifyingEnv`.
The failed command leaves no declarations, and the ordinary trust check passes.
A corrected comment boundary also restores execution of the primitive reader and unusual-name controls.

## Evidence and open connections

No new semantic theorem lands here.
The design names the existing invocation typing, conservative extension and target reconstruction claims with their scopes.
Their proof placement stays in `tools/Tools/SemanticsRegistry.lean` and `docs/core/semantics.md`.
The finite checks establish only their named inputs, budgets and observed answers.
They run the generated implementations on Effect primitives, not native Effect Queue or Semaphore.

The general invocation and inlining observation remains G7 under decisions row 329.
Generic stored definitions remain G8 under decisions row 328.
Higher-order builders retain their existing expanded form.
The command does not establish liveness, scheduling laws or TypeScript execution correctness for all inputs.

Queue and Semaphore requests fail the existing `DefDecl.readable` predicate.
Their definitions print to TypeScript, but the definition-header reader refuses them.
The old Queue definitions have the same refusal.
This slice changes no reader profile, target primitive or module behavior.
