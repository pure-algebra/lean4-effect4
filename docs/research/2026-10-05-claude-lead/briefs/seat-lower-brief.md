# 2026-10-05 brief for seat LOWER: four follow-ups of the OCaml route

Status: a brief (history, not authority). Base: `2ba1775c` (`refactor/phase1-phase3`). The
owner asked for these slices on 2026-10-05 (decisions row 252). They come from Codex's packets,
and none touches a generated group.

## Who and where

You are one seat of the Effect4 estate. The coordinator wrote this brief and merges your
branch. You work alone and hand back a receipt. Seat FOLD runs beside you in another worktree,
on the term language. Your files and its files do not meet.

- **Worktree:** `/Users/pooks/Dev/lean4-effect4-lower`, new. Its branch is `seat/lower`, at the
  base `2ba1775c`. The dependency packages are cloned there already. Your first build restores
  the outputs from Lake's artifact cache.
- **The coordinator's checkout** is `/Users/pooks/Dev/lean4-effect4`. Read it freely. Write
  nothing there.
- **Lean:** run every Lean and Lake command through
  `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`. Never run a bare `lake build`. Never
  send a Lean command's standard error to `/dev/null`. Run one `lake` at a time.
- **OCaml:** only through `opam exec --switch=effect4 -- dune …`, or the `ocamlopt` of that
  switch as `scripts/check-conform.py` finds it.
- **No install and no download.**
- **Git:** never push. Commit on your branch, by explicit paths. Use `git add -f` for a file
  under `docs/research`. Read `git status` before each commit.
- **Scratch files:** under
  `/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/e4a67264-1213-4b33-b3e2-68332653bd83/scratchpad/lower/`.
- **Disk** has about 18 GiB free. Stop and report below 4 GiB.

## Read first, in this order

1. `AGENTS.md`, in full.
2. `docs/core/lcnf-route.md` §9, and
   `docs/research/2026-10-05-claude-lead/lowering-table/lowering-table.md`: what landed today.
3. Codex's three packets, under
   `docs/research/2026-10-05-codex-foundation-packet/implementation-audit/`:
   - `conformance-api-review/recommendations.md`, with `runner/review.md`,
     `core/recommendations.md` and `semantics/review.md`;
   - `ocaml-lowering-scout/recommendations.md`, with `ocaml/recommendations.md` and
     `proof/review.md`;
   - `builtin-table-review/recommendations.md`.
4. The sources: `tools/Conform/Lcnf/SemanticsTarget.lean`, `tools/Conform/Effect4/LcnfMl.lean`,
   `CompilerControls.lean` and `Normalization.lean` beside it, `scripts/check-conform.py`,
   `scripts/lib/conform_report.py`, `ocaml/engine/e4_be.ml` with its interface, and
   `ocaml/eff/eff_frame.ml`.

## The four slices

Land each as its own green commit, in this order.

### 1. The conformance runner

Codex's review of the runner names three faults (`conformance-api-review/runner/review.md`,
`core/recommendations.md`). Each has an isolated Python control there.

- **A failed attempt keeps its evidence.** `step_compiler` writes `actual.txt` before it
  compares. A producer that fails keeps its raw files, its command, its standard output and its
  standard error in a retained attempt folder. The attempt stays invalid: nothing of it is
  published as a result.
- **`fresh_run` refuses two expected reports** when one of them lost its format tag. State
  which named file is a report and which is an artifact.
- **The negative controls name their failure.** The coordinator already made both mutations
  name the observation that must fail, and require the expected output before it
  (`mutation` in `scripts/check-conform.py`). Check that against Codex's control. One point is
  open: the UTF-8 mutation names the fixture by its number, `12`. Give the fixtures stable
  names in `expected.txt`, and name the mutation's fixture by that name.
- **The selection is an input.** `validate` takes expected identities, pins and inputs. Pass
  them from the requested fixture selection, not from the report that came back.

Keep Codex's controls as tests that run without Lean and without a compiler. Correct the line
of `tools/Conform/README.md` that says `Core.Proof` serves the normalization reports: their
rows are tested, not proved.

### 2. Callback functions in the target evaluator

The evaluator has no rule for a library function that takes a function. So it refuses
`lcnf_list_contains`, and only compiled OCaml runs that support body today.

- Add `List.exists` to `Conform.Lcnf.Target`, with its callback applied through `applyT`. Keep
  the fuel discipline: the evaluator stays total, and exhaustion stays the frontier.
- Add another callback function only with a control that reaches it. `List.for_all` has one
  through the row `List.all`.
- Read the exact labelled call of the row `Option.getD` in `LcnfMl.ofExpr`:
  `Option.value o ~default:d`. Refuse every other labelled call, as today.
- Let a target case expect a named exception where a control needs one. An out-of-fuel result
  is never an expected answer.
- Then run the asymmetric `contains-order` control on the evaluator too, beside its compiled
  check. Add a control that a callback's exception passes through, and one for the order of
  the callback's two arguments.

The source interpreter's primitive meanings stay apart from the target's. Do not merge the two
tables.

### 3. `E4_be` forwards to `Eff_frame`

`ocaml/engine/e4_be.ml` transcribes the framing of `ocaml/eff/eff_frame.ml`. Its interface gives
a reason that no longer holds: the engine has linked `effect4_eff` since then, and
`ocaml/engine/dune` says that `E4_be` forwards.

- Delegate each operation that matches. Keep the interface of `E4_be` as it is:
  - its checked `read_be64`;
  - its exceptions on a negative input;
  - its offset checks, and its refusal of trailing bytes.

  The shared reader assumes a valid window, so the guard of `read_be64` stays before the call.
- Correct the deviation `D1` in `e4_be.mli` and the property list at its head.
- Acceptance: `ocaml/eff/test/test_frame.ml`, `ocaml/engine/test/test_math.ml` and the engine's
  golden tests pass, and no golden changes. No LCNF group is regenerated.
- The standard library's big-endian functions are not part of this slice.

### 4. The law of `let x = e in x`

`OCaml5.Lcnf.code` writes `v` where the LCNF has `let x := v; return x`. The target evaluator
should give both forms one outcome.

```lean
Target.evalT prog (n + 2) env (.letIn x e (.var x)) = Target.evalT prog (n + 1) env e
```

- The statement is Codex's candidate (`ocaml-lowering-scout/proof/review.md`). The fuel differs
  by one on purpose: the same-fuel statement is false at fuel one. Keep that as a red control.
- Prove it in a new battery file, `Test/Audit/LetReturn.lean`. Import it in `Test/All.lean` on
  the line after `import Test.Audit.ClockLowering`. `Effect4.Laws` must not import `Conform`.
- **Placement.** Concept: `translation-simulation`. Requirement: R8, its open part "typed
  lowering open". Proposed claim: `ocaml-let-return-outcome`. Consumer: the identity-continuation
  case of `OCaml5.Lcnf.code`. Reach: every outcome of the target evaluator, under the two
  related fuels, for any environment, with `x` bound or not before. It does not establish the
  emitted bytes, the cost, or any other rule of the translation. It unlocks the first checked
  local rewrite of the route.
- Write the placement in the theorem's docstring, and propose the registry claim in the
  receipt. Do not edit `tools/Tools/SemanticsRegistry.lean`: seat FOLD edits it now.
- The axiom gate holds the theorem to `[propext, Quot.sound]`. A `simp` at `(x == x) = true`
  for a `String` reaches `Classical.choice`: use the lawful equality of `String` by name.
- Add a finite control that connects the law to the route. Take one translated declaration
  whose body the cleanup shortened, and evaluate it in both forms.

## What is not in this assignment

- The read-back of emitted OCaml by the compiler's own parser. It waits for its own design.
- The numeric policy (decisions row 108), and any row's meaning or class in `builtins`.
- The generated OCaml, the wire, and the term language. Seat FOLD owns those now.
- `docs/core/decisions.md`, `lakefile.toml` and `docs/STATE.md`: propose in the receipt.

## Acceptance

Give each result in the receipt.

- `lake build Conform OCaml5 Test.Audit.LetReturn`, through the slot.
- `python3 scripts/check-conform.py compiler`: PASS, with the number of observations.
- `make check-cases` and `make check-native`.
- `python3 scripts/generate.py --only lcnf`, then `git status`: no generated file changes.
- `cd ocaml`, then `dune build`, `dune test --force eff gen clock` and
  `dune test --force engine`. Run `make corpus` first if the engine's corpus check fails on a
  stale `.lake/corpus`.
- Codex's Python controls, as kept tests.
- `make check-docs` and `make check-language`.
- The default `lake build` once at the end, with the gate lines of `Test/All.lean`.

## Known, and not yours to repair

- `make check-tsdiag` and `make check-schema-ts` are red for reasons outside this work.
- `lake build Effect4Gen`, the library target, fails. It is not a gate.

Report anything else that is red for a reason outside your slices. Do not repair it.

## The receipt

Write `docs/research/2026-10-05-seat-LOWER-receipt.md`, in the handoff form of `AGENTS.md`:

1. first, the one thing the coordinator must know before merging;
2. the base and head commits, and each slice's commit;
3. the changed files;
4. each command with its result, and the evidence word for each claim;
5. the axiom output of the law;
6. the law's placement, and the proposed registry claim;
7. each choice you made, and each point where you left Codex's advice, with the reason;
8. the open obligations;
9. proposed decisions rows. Do not edit the register.

Your last message gives the head commit, the receipt's path and the first item of the receipt.
