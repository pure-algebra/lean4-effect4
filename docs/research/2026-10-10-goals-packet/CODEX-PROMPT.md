# Prompt for Codex: organize and land the last planned goals

Work in the lean4-effect4 repository, branch `refactor/phase1-phase3`, from commit
`2b355a9af` or later. Read `AGENTS.md` first; it binds you. Then read
`docs/research/2026-10-10-goals-packet/README.md` and the four family folders under it.

## The goal

Fourteen planned goals remain, all properties of the five example applications in
`Test/Dogfood/Scenario/`. Four probe seats decomposed them. Each family folder holds a
`README.md` (the plan) and a `Probe.lean` that compiles and proves the family's goals modulo
named planned goals. Your job has two parts:

1. **Organize and probe.** Produce one landing plan for all fourteen: the order, the dependency
   graph (Mermaid), the lanes that run in parallel, and the owner decisions on the way. Probe
   wherever the order is uncertain, so the plan rests on compiled Lean, not on prose.
2. **Plan for fast, compile-first development.** The owner wants proof structures landed fast:
   state each structure with planned goals (`proof_goal`) as scaffolding, prove it by narrow
   builds, and repair the gates only after the major proof structures land.

Ignore the seats' hour estimates. The owner expects most goals to land within hours now that
the probes exist. Plan in landings, not in weeks.

## What the probes found (verify, do not trust)

- **Two goals are false as stated.**
  - `retries_declared`: refuted by `retries_declared_refuted` (`host-protocol/Probe.lean`). The
    cause is `timeoutForm` (`Test/Dogfood/P1HttpCache.lean`), which races two forked awaits so
    the timer can win after the attempt has finished; rc.112's `raceAllFirst` settles at the
    body's exit. Recommended: repair the form. Confirm the repair against rc.112's source
    (`vendor/effect-4.0.0-rc.112/src/…`), then restate nothing.
  - `cleanup_keeps`: false over raw decisions (a direct answer to the root's join). It holds
    over `RunReachable` (`release-once/Probe.lean`). Propose the restated premise.
- **One frame, four spellings**: `RunKeeps`, `RowKeeps`, `MachineKeeps` with `RunReachable`,
  `scenario_keeps`. Unify them into one module under `src/Effect4/Laws/Run/` and decide which
  reachability it uses (`RunReachable` keeps why a parked fiber resumed; `Guard.Reachable` does
  not).
- **One large shared law**, named three ways: control linearity (`once_placed_registers_once`
  and its siblings), fiber-local positions (G2 in `store-invariants/README.md`), and the crew's
  stage table (`crew_invariant`, `crew_host_invariant`). Decide whether it is one general step
  law of the frame machine for many fibers, or whether per-program stage tables checked by the
  kernel avoid most of it. Probe both on the smallest program that forks (Workers' crew at
  `total = 1`) before choosing.
- **Smaller general laws**: `heap_sites_keep` (a cell invariant from its write sites),
  `release_starts_le_registrations` and `finalizer_starts_le_pushes` (R11 per registration),
  a join law, and the session's keys (`Ledger`, `session_keys_once`, `ending_of_tape`, proved in
  `host-protocol/Probe.lean`).
- **Ready or nearly ready**: `stale_never_applies` clauses 1 to 3 (proved for every program),
  clause 4 restated as `ending_of_tape` (proved); `bounded` rests on `heap_sites_keep` alone;
  `infrastructure_escapes` rests on `escape_session` (a budget fact of one funded run, or raise
  the routing battery's fuel to at least 8200).
- **A trap**: the crew's elaboration at a symbolic job count does not reduce (a generated binder
  name; `whnf` folds `Nat.mod` only on closed arguments). The repair in
  `queue-run/scratch/StuckFix.lean` is unverified. Verify or replace it early: three goals and
  both `releases_once` depend on it.
- **Tools found on the way**: `kernel_rfl` (a kernel check of an equation with free values,
  no axiom) and `decide +kernel` on `elaborateModule`; `decide` on `Author.build` does not
  reduce.

## How to work

- **Compile first.** Land structure before proofs: a planned goal is a `proof_goal` placed at
  its concept and requirement (`@[semantics "concept" (requirement := Rn)]`), and downstream
  proofs use it at once. Replace a goal by its proof in place.
- **Narrow builds only** while structures land: `LEAN_NUM_THREADS=3 lake build <Module>` or
  `lake env lean <file>`, then `#axiom_audit` over the touched modules. Do not run `make check-*`,
  `lake build Test` or the whole-tree axiom gate until a major structure has landed; then repair
  the gates in one pass. Record each deferred gate in the receipt.
- **Avoid rebuild cascades**: put new laws in new modules; do not edit docstrings of widely
  imported modules on the way.
- **Probe before you commit to a route**: a probe is a file under the packet folder that
  compiles. Keep each probe's verdict in the plan.
- The banned tactics, the axiom ceiling and the writing rules of `AGENTS.md` hold throughout.
- The scenario files (`Test/Dogfood/Scenario/*.lean`) keep their goal statements unless a goal
  is false; a restatement is an owner decision, written as a proposed decisions row.

## Deliverable

1. `docs/research/2026-10-10-goals-packet/PLAN.md`:
   - the order of landings, each with its modules, the goals it closes or reduces, its narrow
     build and its audit;
   - the dependency graph as Mermaid, with the parallel lanes marked;
   - the owner decisions, each with a recommendation (the `timeoutForm` repair, the
     `cleanup_keeps` premise, the routing fuel, the scope of `unauthorized_calls_nothing`'s
     scripts, the symbolic job count);
   - the gate repair pass, after the structures: which gates each landing reaches.
2. The probes that settled the order, under `docs/research/2026-10-10-goals-packet/codex/`.
3. Then start landing in that order, on your own branch, one commit per landing, each after its
   narrow build and audit. Hand back with a receipt
   (`docs/research/<date>-codex-goals-receipt.md`): first the one thing to know before merging,
   then base and head, changed files, commands and results, audit output, open goals, deferred
   gates.

Never push. Commit by explicit paths; `git add -f` for `docs/research`. Do not edit
`docs/core/decisions.md` or `lakefile.toml`; propose rows in the receipt.
