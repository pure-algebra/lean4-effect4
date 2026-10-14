# Codex: close out the procedures line

## The one thing to know first

PROC-6 landed and is merged (`36ddb0b56`; decisions row 379). This brief is rewritten after
Gemini's review (`gemini-review.md`), the coordinator's corrections (`review-notes.md`) and the
modelling check (`modelling-check.md`) and Gemini's review of it (`gemini-math-review.md`,
`review-notes.md` §5). Decisions rows 383, 384 and 385 record the rulings. Track 1 lands now:
- the `effects` package's simulation with a relation on results, an Effects release;
- the one refinement order on the meaning, with its congruence;
- the inlining law G7 in that order;
- CX3, the typing of an inlined program;
- the generic definitions connector, with the Queue's and Semaphore's as its instances.

The line ends at the proof closure (`modelling-check.md` §8): every slice here is a node of it.
Track 2 designs the syntax changes as one note, then stops for review before any edit to `Eff`,
`Ty`, `Store.Val` or `Point`.

**The owner's rule for every choice (2026-10-14):** decide on semantics, never on rebuild cost, and
take the complete option. Every item here is wanted and its users are known. If a statement falls
short of its users, the plan widens. Never drop or defer an item; report the gap and the step
that closes it.

## What the line owes

| Item | What it is | Its users |
| --- | --- | --- |
| the refinement order (L1) | inclusion of completed observations, proved by simulation up to a relation on states, with its congruence and the lift law in the call handler (rows 383 (1), 384 (1), (2)) | G7; every module claim of row 382 (1); G10 |
| G7 `inline-agrees` (L2) | an invocation and its inlining give equal completed observations, in every context (row 383 (2)) | the to-do's cached service now; the Queue's and Semaphore's connectors through SCOPE-1 and CONC-1 |
| CX3 `inline-types` (L3) | an inlined program keeps its typing at the checker (row 383 (4)) | G7's typed side: the inlined program meets H9's typed premises |
| `definitions-agree` (L4) | over an acyclic block, a client over the definitions agrees with the same client with every invocation inlined (row 384 (7)); the Queue's and Semaphore's connectors are its instances | every module built from definitions |
| PROC-7 and HO-5 (D1) | generic definitions (G8 `check_subst`) and methods with program parameters | the module form (row 383 (6)) |
| the closure stage (D2) | closures held as data (PROC-8, G9 `resolve_typed`), one activation stack, and SCOPE-1's stage 0, as one stage (row 383 (5)) | services as records of closures (rows 381 (3), 382 (2)); SCOPE-1 |
| the module form's inputs (D3) | what D1 and D2 owe the module form, and the generic object specification and claim template (row 384 (5) to (8)) | the ports of row 382 (3); every bank entry |

CX4 is proved already (`call_arm`, `invoke_arm` and `param_arm` with `hop_typed`,
`src/Effect4/Laws/Program/Typed/Denotation.lean`). Record its placement in the receipt.

## Read first

- `AGENTS.md`, all of it.
- `docs/research/2026-10-14-proc-close/modelling-check.md`: every relation of the line, written
  out. It is the frame for every slice below.
- `docs/research/2026-10-14-proc-close/gemini-review.md`, `review-notes.md` and
  `probes/Probes.lean`. Where the review and the notes disagree, the notes win.
- `docs/research/2026-10-14-proc-close/gemini-math-review.md` and `probes/MathProbes.lean`:
  `PeelSim` there is the prototype of slice L0.
- Decisions rows 82, 259, 328, 331, 340, 361, 379, 381, 382, 383, 384 and 385.
- The PROC design (`docs/research/2026-10-08-seat-PROC-design.md`): §4.4, §8 and §9.
- `docs/research/2026-10-09-program-parameters.md` (HO-4, HO-5) and
  `docs/research/2026-10-10-cx-lexical-scope.md` (§3.4, §8, §9).
- `docs/research/2026-10-14-one-fiber-scout.md`, stage 0; D2 designs that stage.
- PROC-6's receipt: `docs/research/2026-10-14-proc6-prep/landing-receipt.md`.

## Where you work

Reuse your worktree, `/Users/pooks/Dev/lean4-effect4-codex`. Its kit package holds `3e5e793`.
Start a new branch at the coordinator's head, given in the launch message.

## The rules that bind every slice

PROC-6's brief holds them: `docs/research/2026-10-14-proc6-prep/landing-prompt.md`, "The rules
that bind every slice". In short:
- build only through `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`;
- place before you prove;
- `#axiom_audit` each slice, at `[propext, Quot.sound]`;
- in the law graph, `aesop` and `simp only`, with no `simp_all`, `first` or `try`;
- every new traversal of `Eff` is a fold (an `EffAlgebra` and `cata_eff`), never a hand `match`;
- reuse before you add: name the existing declaration each new one could have been;
- commit by named paths;
- never push, download nothing, and never write `2>/dev/null`;
- `lakefile.toml` and `docs/core/decisions.md` are the coordinator's;
- append to the root imports.

## Track 1: land now

The order: L0, then L3 while the coordinator releases L0, then L1, L2 and L4.

### Slice L0: the simulation with a relation on results (the `effects` package)

- Work in `/Users/pooks/Dev/lean4-effects` (the pin `bf5ab8f`, v0.10.1), on a new branch
  `codex/result-relation`. Its own build and its own audit hold; read its `AGENTS.md` or
  `README.md` first.
- `Step.Lift` gains a relation on results: two finished steps relate when their values relate.
  `IsSim` and `IsBisim` take it, and so do `run_of_sim`, `run_eq_of_bisim`, the compositions
  (`IsSim.comp`) and `unfold_approx_of_sim`. Today's forms are the equality instances, stated as
  abbreviations or theorems, so every existing caller keeps its name and its proof.
- Add the result relation on `Option` results that puts a cut below everything. With it, a
  program's budget cut is the bottom of a peeled system (`System.peel`).
- Prove the peeled form's soundness for every host, as `PeelSim.sound_host` does in the probe.
- Stop after this slice's commit in the `effects` repository, and report. Releasing it and
  bumping the pin are the coordinator's, after the owner's push.

### Slice L1: the refinement order on the meaning

- Define the order as inclusion of completed observations of runs, up to a relation on states
  (rows 384 (1), 385 (1)). Then use L0's simulation with a result relation, after the stores are
  peeled. Write no second simulation framework.
- Its identity instance is the limit order on budget-indexed trees: every budget of the left is
  approximated, by `Effects.Program.Approx`, at some budget of the right. It is not `Approx`
  itself (row 382 (3)). Define `RefinesB` as that instance's pullback through `denoteBlockB`,
  and `EquivB` as refinement both ways. Quantify over the context, the environment and parameter
  frames that approximate each other.
- Prove the observation law: equivalent programs give equal completed observations (exit, stores,
  host state) of `hostRunBlockB` at some budget, under every host. Start from
  `hostRunBlockB_stable` and `denoteBlockB_approx`.
- Prove the congruence once per `BlockRows` constructor, from `cata_blockAlgB_approx`. Keep the
  proof one per constructor, so SCOPE-1 and CONC-1 add their constructors' cases beside it.
- **The lift law** (row 384 (2)). Take two call handlers related by a simulation up to a
  relation on states. They give related observations for every client whose own operations keep
  the relation (the frame condition). Generalize `cata_blockAlgB_approx`, which proves the identity
  case (its hypothesis `hc` relates the two handlers). A module's claim then relates its two
  handlers operation by operation, and never quantifies over clients.
- The frame condition (row 385 (2)): the abstraction splits the stores into the module's
  owned keys and the client's. A client's store operations act outside the owned keys. A
  module's operation establishes the relation at its success and failure exits. A budget cut is
  the bottom.
- Prove the frame condition for the identity relation now. State the module case's frame
  condition as a premise (row 384 (3)). It has two readings: the module form's opaque closures,
  or a located refusal that the client uses the handle only through the operations.
- Claim: `meaning-refines`, role simulation, concept `translation-simulation`, R10. It is row
  382 (3)'s first step.

### Slice L3: parameter substitution and CX3

L2 uses the substitution, so this slice lands before it.

- The shift is the existing generated `Eff.weaken` (`src/Effect4/Program/Fold.lean`), typed by
  `check_weaken` (`src/Effect4/Program/Typing.lean`). Write no second shift.
- Define `Eff.substParams` as a fold in a new core module, `src/Effect4/Program/Inline.lean`,
  with a carrier indexed by binder depth (`binders.json`). It replaces each run of a parameter by
  its argument, weakened to the depth of the site. Define the inlined forms of a call and of an
  invocation there too.
- Prove `check_substParams`: an inlined body checks, and its answer and error are subtypes of the
  definition's. Compose with `check_weaken`, `check_replace` and `table_splice`, so that replacing
  a call or an invocation by its inlined body at any address keeps the module typed.
- Prove that the substitution keeps `BodyRows`, so an inlined block stays in `BlockRows`.
- Prove the meaning's weakening law, `denoteBlockB_weaken`: a weakened program at a longer
  environment means the program at the shorter one (row 385 (6)). L2's sandwich uses it.
- Claim: `inline-types`, role preservation, beside `check_replace` under `initial-algebras-folds`
  (R14). The typed run keeps its path-addressed points (the CX note §3.4): CX3 types the inlined
  program, not a point inside it.

### Slice L2: the inlining law G7

- The step laws: `inline_call_approx` and `inline_invoke_approx`, each the two-sided sandwich.
  The inlining at budget `k` approximates the call or invocation at `k + 1`, which approximates
  the inlining at `k + 1`. The probe's controls A and B show why no single budget holds.
- The law: `inline_agrees`. In every context on `BlockRows`, a call or an invocation and its
  inlining are `EquivB`, so they give equal completed observations at some budget. It follows
  from L1's congruence and the step laws.
- The machine: on `BlockRows` both programs reach the machine by `h9_blocks`, receipt-conditioned
  as `H9Blocks` is. The inlined program's typed premises come from L3.
- Its first user now: the to-do's cached service (`Test/Dogfood/Scenario/Todo/Cached.lean`,
  `src/Effect4/Laws/Library/Ref/Cache.lean`). Inlining the cache's definitions keeps the
  to-do's observations.
- Claim: `inline-agrees`, role simulation, concept `translation-simulation`, R10. It is the PROC
  design's form (c).

### Slice L4: the generic definitions connector

- Register `definitions-agree` in `tools/ProofGraph/Registry.lean`, concept
  `translation-simulation`, R10 (row 384 (7)). Over an acyclic definition block, a client over the
  definitions and the same client with every invocation inlined give equal observations. It
  follows from L2 at each invocation, then the laws of `bind` and `succeed`.
- Prove it on `BlockRows` now, as a theorem over every acyclic block, and place it.
- Register the Queue's and Semaphore's connectors (`queue-definitions-agree`,
  `semaphore-definitions-agree`) as its instances. Each relates a client over the definition form
  (`src/Effect4/Library/Queue/Defs.lean`, `Semaphore/Defs.lean`) to the same client over the
  expansion (`Ops.lean`). State that each composes with `queue-expansion-agrees` or
  `semaphore-expansion-agrees` by transitivity of L1's order.
- Write each claim's route as its open parts, one per stage, by the constructs each operation
  uses (the probe):
  - SCOPE-1's congruence cases (masks, interruption, scopes, finalizers, layers) cover the
    protection wrapper (`protectedBy`) of `withPermits`, `withPermitsIfAvailable` and
    SynchronizedRef's `modify`;
  - CONC-1's cases (forks, awaits, deferred awaits, races) complete every operation that waits
    or wakes another fiber. They are the Queue's `take`, `offer` and `poll`, and Semaphore's
    `take` and `release`. The `withPermits` family and `modify` complete there too: their take
    waits, and their release wakes waiters.
- Each instance is proved at the stage that brings its last operation. The SCOPE-1 and CONC-1
  scouts carry those steps.

Each slice ends with its narrow build, its `#axiom_audit`, its commits and its receipt section.
L3 adds a core module that nothing in the `Effect4` root imports until a user does. No behaviour
gate is reached, since no compile or machine definition changes.

## Track 2: design, then stop

Write one design note, `docs/research/2026-10-14-proc-close/design.md`, in PROC-6's scout form.
Give its rulings, stages, placements of the planned goals, fan-out, gates and open checks.

- **D1, PROC-7 and HO-5.** Generic definitions: the PROC design §9's slice, with G8
  `check_subst` and `sub_subst` under `subtyping-algebra` and `initial-algebras-folds`. Its reach
  is the closed instances of formed templates (`Bounds.TemplateOK`), and the instance of a host
  call in a generic body (row 323). HO-5: methods with program parameters (`withPermits`,
  `withPermitsIfAvailable`, Pool's `use`), as the program-parameters plan sets it out.
- **D2, the closure stage** (rows 383 (5), 385 (5)). Closures stay first-order data: a code
  address and captured values. Show that the renaming argument for names extends to them. One
  design for three things:
  - closures held as data (row 381 (3)): a code reference and captured values; a program path
    now, and a content digest with content addressing;
  - one activation stack: first show the invariant that `Point.params` and `Point.call` move
    together, then merge them into one stack of frames;
  - SCOPE-1's stage 0, which this design becomes.

  Settle each item row 82 lists:
  - typed entry resolution;
  - lexical captures against a captured service context;
  - lifetime and portability ("a digest alone is not proof of code identity");
  - recursive admission;
  - the printer and reader contract;
  - the `Val`, `Ty` and `Eff` forms.

  **Closures are opaque** (row 384 (3)). No operation projects a closure's captured values. A
  closure has no equality, the codec refuses it, and the printer writes its type only. A module's
  cell is then private by construction, which is what makes a module claim hold for every client.

  Choose between the PROC design's V1 (a value, a type and an apply form) and V2 (closure records
  and dispatch definitions), on semantics. A bank entry's code must be reachable by its digest,
  which a dispatch over one program's definitions cannot name. G9 is `resolve_typed`, R7's top
  node.
- **D3, the module form's inputs and the generic object** (row 384 (5) to (8)).
  - Say what D1 and D2 give the module form (rows 331 (6), 382 (2)). The module form is a record
    of opaque closures over a cell, generic in its types, and its methods take programs.
  - Design one object specification with three transitions (row 385 (3)): an attempt, a signal
    and a withdrawal, under the two wrappers `waitRetry` and `waitAnswer`. Start from the probe's
    `ObjectSpec`, with its relation on replies. Design one `StepsAgree` over it. Show each of the
    five existing structures (Queue, Semaphore, Pool, Latch, Ref) as its instance. Each adapter
    theorem leaves the proved theorem unchanged. Do the Queue first: it is the hard case,
    with its relation on signals (`Notified`).
  - State the wrapper law that CONC-1 proves once. A `waitRetry` operation is linearized at its
    successful attempt. A `waitAnswer` operation is linearized at the step that commits its
    answer.
  - Design the claim template. It has four parts:
    - refinement;
    - progress as the model states it (row 385 (4)): freedom from deadlock by default, from
      starvation where the model serves in order;
    - names compared up to renaming;
    - the trust chain, as `ClaimRecord.assumes` premises with their grades.
  - Do not design the module form itself.
- **Stop after the design note** and report. The coordinator reviews it before D1 or D2 touches
  source.

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
