# Refactor plan, 2026-09-03

Two surveys of the tree at `645067a` produced 95 verified findings:
`docs/research/2026-09-03-survey-lean-core.md` (findings L1–L55) and
`docs/research/2026-09-03-survey-target-harness.md` (findings H1–H40). This plan
turns them into six waves. A wave is a set of agent packets with disjoint file
ownership; a wave is done when its packets are merged and the gate sweep is green.
Packet briefs cite findings by number; the survey is the evidence, this file is the
order.

## Rules that every packet obeys

1. Branch from the base hash the brief states; check `git merge-base` before the
   first edit. Never bulk-remove worktrees.
2. Semantics change only with the proof, golden or counterexample row that moves with
   it, in the same commit.
3. No hand-copied constant crosses Lean and host. If two faces need a value, Lean emits it.
4. Identity by name, never by position: rules, atoms, families, register ids.
5. Everything generated lives under `generated/`; nothing there is hand-edited.
6. A gate that swallows an error is a defect. Every script fails loudly with the tool's
   own diagnostic.
7. Build `Effect4` and the batteries the packet touches; the sweep runs once per wave.
8. One lean or node process per agent; the machine is memory-bound.
9. A gate does not re-run when its inputs are unchanged. Every check keys a stamp under
   `.lake/stamps/<name>/` on the content hash of its sources, fixtures and the Lake
   traces of the compiled closure it reads (`scripts/lib/stamp.sh`, wave 0a), and a hit
   prints PASS with the stamped summary and exits. `--force` re-runs.

## Wave 0 — main is green, hermetic, and the trust gate is real

Packet 0a, trust gate (Lean): L1, L2, L3, L12, L23, L29, L31, L47, plus the sweep-9
break in `FrameSimulationContract` (`FlowAlphabet` needs `errorTy`/`boolTy`).
Tokenizer refuses `native_decide`/`sorry`/`admit`/`axiom`/`extern`/`implemented_by`;
the live `native_decide` goes; blanket module admissions become 66 exact roots with
`#effect4_print_choice_reachers`; admission crosses a module only through names Lean
reserves (`isReservedName`), never by spelling; the closure gate honours `known-red.txt`;
`Effect4TestGreen` default target and per-area test targets; the trust gate is root-only
(planted tokens are a source copy elaborated against the real build, planted declarations
are one module compiled alone) and stamped (rule 9): 84 s on a miss, 1 s on a hit; nine
planted defects; Derive's receipt is a named theorem. Landed 2026-09-03 (2876fe9 + stamp).

Packet 0b, sweep (scripts, harness, generators): H1, H2, H5, H10 (assert width), H11,
H18, H19, H36, H39, plus the sweep-9 breaks (`Property.lean` lacks the v3 cases; the
property and mutation scripts swallow the Lean error; `flow-fixture.ts` drift).
`trace.mjs` copy filter (effect4-tools), `Generate.lean all <dir>`, portable shim,
one regenerate function in `check-trace-host.sh`, mutant total asserted, hermetic gates
in CI, regenerate and commit.

## Wave 1 — semantics and lowering API

Packet 1a, Flow v3 semantics (Lean): L4, L5, L32, L7, L6, L9 (local), L17, L16.
Branch with no boolean reading refuses; `refused` splits into site and value; the
performCatch clause is derived from perform; the plan inversions move to `Effect4.Flow`;
`BlockLaw` record and one general block proof; `idBind`/`erasedBlock` hoisted; scoped
simp sets; the nineteen unused simp arguments. Counterexample row first.

Packet 1b, lowering API (Lean target + lean4-typescript): H9, H15, H16, H17, H28, L8,
L50 (target headers). Rule identity by id in one owning battery, `Rule.all` in
inductive order; `tupleArgs` returns `Option`; `OpSpec` loses its defaults;
`Expr.member` in lean4-typescript (bump) so `Slot.expr` stops forging identifiers;
`Skeleton.lean` split into IR and renderer; `StructureDominators` stops re-proving
`StructureOrder`.

Packet 1c, effects boundary release (lean4-effects v0.8.0, then the pin bump here):
L36, L37, L38, L39, L40, L41, L42, L43, L44, L45, L46, L48, L49. Region clauses as a
structure with `regionWF_iff_check`; the pigeonhole pair and the two `reachSet` theorems
published; saturation scaffolding private; `errorTy : Op → Option Ty`; the unknown
release arm; `diagnoseAll`; the missing axiom reports; the gate hardening backported;
docs and counts. Effect4 deletes its `namespace Effects` block and its private copies on
the pin bump.

Packet 1d, stamped sweep (scripts): apply rule 9 to every script the sweep runs
(`check-*`, `test-*-gate`, `generate-*`), with the inputs each one actually reads; a
`scripts/sweep.sh` that runs them in dependency order, writes `generated/sweep-summary.tsv`
(name, status, seconds, hit or miss), and is the single entry point until the wave 3
`justfile` wraps it. A warm sweep with nothing changed must finish in under a minute.

## Wave 2 — the ledger and the host faces tell the truth

Packet 2a, ledger (scripts + coverage battery): H3, H6, H26, H37, H40, H21, H22, H24.
Coverage columns derived from receipts on disk; a property drift gate; receipts and
types move under `generated/` with a pin-only drift gate; the 39 uncited goldens
classified in the ledger header; doc counts quoted from the generator.

Packet 2b, faces (harness + Derive): H4, H7, H8, H12, H13, H14, H29, H30, H31, H32, H33,
H27. Every harness root typechecked; `foreign`, scenarios and seed emitted from Lean;
tape-mismatch parity settled against wave 1's ruling with planted mutants;
`Atoms.eval` returns `Option`; `dec` over `Int` or a register row; the dead `Decisions`
class and the duplicated tape reader go; `effect_atoms` takes any arity;
`effect-v4-family` uses it; masks documented as nested.

## Wave 3 — library structure and hygiene

Packet 3a, structure (Lean): L27, L10, L53, L19, L20, L18 (semantics directory first).
`Effect4Meta` library; stubs leave the umbrella and essays move to `docs/`;
`FrameSimulation` moves to `Runtime`; `Equiv`/`Logic` at `Type uTy`; fuel theorems
over `DetRun` or their headers say `StateT σ Id`; `autoImplicit false` by directory.

Packet 3b, records (docs, register, scripts): L11/H23, L13, L14, L33, L34, L35/L54,
L50, L51, L55, H20, H25, H34, H38, L30. COORDINATION split; register gains `REPAIRED`,
a validator, the ten wire rows and bidirectional id checks; dead declarations and
dangling citations; namespace map; header normalisation; `scripts/README.md` and a
`justfile` that writes the sweep summary.

## Wave 4 — a family is a row

Packet 4, H35 with L29's targets: `FamilySpec` in `Generate.lean` drives the generator,
the host loop and the tsconfig list; adding a program family touches about twelve files.

## Wave 5 — frozen-surface ergonomics (last, alone)

Packet 5: L15, L21, L22, L24, L52. `FiberAssurance` lists derived against the gated TSV;
`Supervision` statements reformatted with a `ValidSpec` record; `FieldAdmissible` as
per-shape records; fuel-20 `decide`s replaced by `rfl` on extracted outcomes; the
`?`-means-`Bool` names. Fiber assurance and census gates green before and after.

## Scheduling

| wave | packets in parallel | lean builders |
| --- | --- | --- |
| 0 | 0a, 0b | 2 |
| 1 | 1a, 1b, 1c (other repo), 1d (scripts) | 3 |
| 2 | 2a, 2b | 1 |
| 3 | 3a, 3b | 1 |
| 4 | 4 | 1 |
| 5 | 5 | 1 |

Waves are sequential; the sweep between them is the only gate.
