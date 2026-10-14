# Codex: close out the procedures line

## The one thing to know first

PROC-6 landed and is merged (`36ddb0b56`; decisions row 379). The procedures line still owes six
things: the inlining law that PROC-6 set aside, its two consumers, two typed laws, generic
definitions, the value form and one activation stack. Land the laws now, in track 1. Design the
three syntax changes in track 2, then stop for review before any edit to `Eff`, `Ty`, `Store.Val`
or `Point`.

**The owner's rule for every choice (2026-10-14):** decide on semantics, never on rebuild cost, and
take the complete option. A shortcut is a finding to report, not a choice to make.

## What the line owes

| Item | What it is | Where it was planned |
| --- | --- | --- |
| G7 `inline_agrees` | an invocation and its inlining give equal observations | PROC design §4.4 form (c) and §8; row 379 (1) set it aside |
| `queue-expansion-agrees`, `semaphore-expansion-agrees` | the Queue's and the Semaphore's operations as definitions agree with their expansions | proposed claims in `tools/ProofGraph/Registry.lean`; their helpers are proved |
| CX3, CX4 | the typed substitution law for parameters, and the typed unfolding law | `docs/research/2026-10-10-cx-lexical-scope.md` §8 |
| PROC-7, G8 `check_subst` | generic definitions: template rows, a body at rigid variables, the typed print at an invocation, a host call's instance in a generic body | PROC design §9; row 340 (3), slice HO-4 |
| PROC-8, G9 `resolve_typed` | the value form: a closure held as data | PROC design §9; rows 82, 381 (3), 382 (2) |
| one activation stack | `Point.params` and `Point.call` merged into one stack of frames | PROC-6 scout §6 (d) |

The PROC design is `docs/research/2026-10-08-seat-PROC-design.md`.

## Read first

- `AGENTS.md`, all of it.
- The PROC design: §4.4, §8 (G7 to G9) and §9.
- `docs/research/2026-10-09-program-parameters.md`, the plan of row 340 and HO-4.
- `docs/research/2026-10-10-cx-lexical-scope.md`, §8 and §9.
- Decisions rows 82, 328, 340, 379, 381 and 382.
- PROC-6's receipt: `docs/research/2026-10-14-proc6-prep/landing-receipt.md`.

## Where you work

Reuse your worktree, `/Users/pooks/Dev/lean4-effect4-codex`. Its `.lake` is current and its kit
package holds `3e5e793`. Start a new branch at the coordinator's head:

```sh
git -C /Users/pooks/Dev/lean4-effect4-codex switch -c codex/proc-close 85639873e
```

## The rules that bind every slice

PROC-6's brief holds them: `docs/research/2026-10-14-proc6-prep/landing-prompt.md`, "The rules
that bind every slice". In short:
- build only through `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`;
- place before you prove;
- `#axiom_audit` each slice, at `[propext, Quot.sound]`;
- in the law graph, `aesop` and `simp only`, with no `simp_all`, `first` or `try`;
- commit by named paths;
- never push, download nothing, and never write `2>/dev/null`;
- `lakefile.toml` and `docs/core/decisions.md` are the coordinator's;
- append to the root imports.

## Track 1: the laws, landed now

### Slice L1: the inlining law, G7

- State the claim `inline-agrees` (role simulation, concept `translation-simulation`, R10:
  "laws proved once per definition instead of per expansion").
- **The route.** Prove it at the block meaning, which has no schedule. Then seat SIM's
  relation (the PROC design §4.4, items 1 to 4) is not needed there:
  - a call: `C[perform (.call k) r]` against `C[bind (succeed r) (shift body)]`;
  - an invocation: the body's parameter runs replaced by the relocated argument programs.
- **The observation.** The convergence form: some budget gives the same exit, stores and host
  state, as `call_unfolds_at_limitB` and `invoke_unfolds_at_limitB` state it.
- **The steps.** The unfolding laws PROC-6 proved; the shift and relocation lemmas of the code;
  and a congruence of the convergence relation for every `Eff` constructor, the PROC design
  §4.4 item 5.
- **The machine.** On `BlockRows` the statement reaches the machine by `h9_blocks` on both
  programs, receipt-conditioned, as `H9Blocks` is.
- Check first, and report it: whether the convergence relation is a congruence as it stands, or
  needs `Effects.Program.Approx` and monotonicity to be one.

### Slice L2: CX3 and CX4

- CX3, the typed substitution law: a parameter's run replaced by its argument keeps the typing
  of `denotesTyped`.
- CX4, the typed unfolding law: an invocation's typed run is its body's typed run at the
  definition's point.
- Their consumer is L1's typed side: an inlining pass needs its output typed. Place both under
  `residual-program-typing`, as steps of the claim `denote-typed`, at the requirement that claim
  serves.

### Slice L3: the two expansion claims

- Register `queue-expansion-agrees` and `semaphore-expansion-agrees`, and prove each from L1
  applied at every definition of the module (`src/Effect4/Library/Queue/Defs.lean`, `Semaphore`).
- Their existing helpers stay where they are.

Each slice ends with its narrow build, its `#axiom_audit`, its commits and its receipt section.
No behaviour gate is reached, since nothing in track 1 changes a compile or a machine definition.

## Track 2: design the three syntax changes, then stop

Write one design note, `docs/research/2026-10-14-proc-close/design.md`, in PROC-6's scout
form: rulings, stages, placements of the planned goals, fan-out, gates and open checks.

- **D1, PROC-7: generic definitions.** The PROC design §9's slice. G8 is `check_subst` with
  `sub_subst`, under `subtyping-algebra` and `initial-algebras-folds`. Its reach is the
  closed instances of formed templates (`Bounds.TemplateOK`), and the instance of a host call
  in a generic body (row 323).
- **D2, PROC-8: the value form.** It is held as data (row 381 (3)): a code reference and
  captured values, a program path now and a content digest with content addressing.
  - A module's instance and a service are one record of closures (row 382 (2)).
  - Settle each item row 82 lists: typed entry resolution; lexical captures against a captured
    service context; lifetime and portability ("a digest alone is not proof of code identity");
    recursive admission; the printer and reader contract; the `Val`, `Ty` and `Eff` forms.
  - Choose between the PROC design's V1 (a value, a type and an apply form) and V2 (closure
    records and dispatch definitions), on semantics. A bank entry's code must be reachable by its
    digest, which a dispatch over one program's definitions cannot name.
  - G9 is `resolve_typed`, R7's top node.
- **D3, one activation stack.** Since PROC-6's stage 0a, `Point.params` and `Point.call` move
  together. Show that invariant first, then plan their merge into one stack of frames.
- **Stop after the design note** and report. The coordinator reviews it before any of D1 to D3
  touches source.

## Stop and report at once when

- a goal is false as stated: give the counterexample;
- a track 1 proof needs an edit to a compile, a machine or a syntax definition;
- a gate fails beyond its baseline.

## What you report

The receipt is `docs/research/2026-10-14-proc-close/receipt.md`. It opens with the one thing the
coordinator must know before merging. Then, per slice:
- the base and head commits;
- the files;
- the commands and their results;
- the `#axiom_audit` output;
- each goal's status;
- the open obligations;
- whether any evidence is bounded or host-only;
- any place the plan is wrong, with evidence.

Propose decisions rows in the receipt, never in the register.
