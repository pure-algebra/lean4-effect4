# 2026-10-16 seat itrees budget receipt: Lean's budgeted call tree is the truncated tree meaning

**The one thing to know before merging:** Lean's divergence of a program, a cut at every budget, is
now the Rocq divergence `≈ ITree.spin`. Rocq proves this for every host and, with definitions
unfolded by budget, for every program. `Print Assumptions` finds no axiom behind it. The two
commits add research files only, under `docs/research/2026-10-16-itrees/`, and join no gate.

The research note is `docs/research/2026-10-16-itrees/README.md`, §6.

## Second commit: definitions by budgeted unfolding

The first commit covered the fragment both meanings have arms for. The second gives the budgeted
tree every arm of `Denote.denote`, so the relation holds for every program (README §6.3).

| File | Change |
| --- | --- |
| `rocq/BudgetDefs.v` | new: `denoteW`, `denoteD`, `denoteBD`, `M`; monotone, below, adequacy, the three outcomes for every program; node for node Lean's tree on the fragment |
| `rocq/TodoBudgetCheck.v` | new: the to-do fixture at a budget, 14 checks and two controls |
| `rocq/Budget.v` | the loop lemma bounded (`adequacy_loop_upto`); `adequacy_loop` its corollary; monotonicity proved without unfolding `iterB` |
| `rocq/Api.v` | the runner runs `denoteBD`, so every run theorem holds for every program; `run_at_lean`; constructors for definitions, calls, invocations, parameters and the context |
| `rocq/Examples.v`, `rocq/BudgetCheck.v` | three programs with definitions; `self_call_diverges` from the budgets |
| `rocq/BudgetExtract.v`, `gen/budget_view.ml`, `gen/budget_view.html`, `generated/budget-view.html` | the new examples and two to-do requests in the view |
| `reproduce.sh` | `BudgetDefs.v` and `TodoBudgetCheck.v` built; 13 more assumptions printed; step 11, the control on the call arms |
| `logs/9-budget.log` to `logs/13-defs-mutant.log` | the final reproduction's logs |
| `README.md` §6, this receipt | updated |

| Command | Result |
| --- | --- |
| `bash docs/research/2026-10-16-itrees/reproduce.sh OUTDIR` | exit 0 in 1 min 53 s from an empty folder, under a load average of 14 |
| `python3 scripts/check-language.py --strict` on the README and this receipt | PASS, no finding |

| Result | Assumes |
| --- | --- |
| `denoteD_approx`, `denoteD_below`, `adequacyD`, `finishesD_iff`, `waitsD_iff`, `divergesD_iff`, `meaning_divergesD_iff`, `denoteBD_same`, `run_at_lean` | nothing: closed under the global context |
| `doubling_rec_finishes`, `self_call_diverges`, `TodoBudgetCheck.reference_0`, `TodoBudgetCheck.broken_6` | nothing |

| Claim | Evidence |
| --- | --- |
| The budgeted tree with definitions is below the meaning, and reaches each of its ends, for every program and host | proved in Rocq |
| Where `denoteRowsB` has an arm, the tree with definitions is Lean's transcription, node for node | proved in Rocq |
| A definition that calls itself at once has a divergent meaning | proved in Rocq, from the budgets |
| The seven to-do requests under both tapes settle at budget 2 or 3 on Lean's calls and exits | finite checks by kernel computation |
| The call arms follow `Denote.v`: a call at the wrong environment fails `denoteW_below` | tested (`logs/13-defs-mutant.log`) |

## The first commit

The sections below record the first commit, `2051d3249`; base, branch and open obligations hold
for both.

## Base and head

| Item | Value |
| --- | --- |
| Branch | `claude/interesting-volhard-6ceb2e`, moved onto `seat/itrees` before any change |
| Base | `5e2c01d99` (`seat/itrees`) |
| Head | `2051d3249` (first commit), then the commit that adds the definitions |
| Pushed | no |

## Changed files

| File | Change |
| --- | --- |
| `docs/research/2026-10-16-itrees/rocq/Budget.v` | new: `denoteRowsB` transcribed, the truncation, the order, adequacy, the three outcomes |
| `docs/research/2026-10-16-itrees/rocq/Api.v` | new: writing, hosts, `run_at`, `settle`, `frames`, holes and `EffEq`, each with its theorems |
| `docs/research/2026-10-16-itrees/rocq/Examples.v` | new: six programs written with `Author`, and two hosts |
| `docs/research/2026-10-16-itrees/rocq/BudgetCheck.v` | new: finite checks on the examples, and the theorems they give |
| `docs/research/2026-10-16-itrees/rocq/BudgetExtract.v` | new: the extraction of the runner |
| `docs/research/2026-10-16-itrees/gen/budget_view.ml` | new: the driver that writes the frames as JSON and times them |
| `docs/research/2026-10-16-itrees/gen/budget_view.html` | new: the template of the animated view |
| `docs/research/2026-10-16-itrees/generated/budget-view.html` | new: the view as the final reproduction wrote it |
| `docs/research/2026-10-16-itrees/logs/9-budget.log` to `logs/12-budget-mutant.log` | new: the final reproduction's new logs |
| `docs/research/2026-10-16-itrees/reproduce.sh` | steps 8 to 10 added: the budget files, their assumptions, the view, the red control |
| `docs/research/2026-10-16-itrees/README.md` | §6 added; a row of what was read; proposal 6 marked done; proposal 8 added |
| `docs/research/2026-10-16-seat-itrees-budget-receipt.md` | new: this receipt |

Logs 1 to 8 are left as the earlier reproduction wrote them, since the README cites their numbers.
The final reproduction rewrote them in its own folder, and every check in them passed again.

## Commands and results

Each command ran from the repository root, in this worktree. The opam switches are `effect4`
(OCaml 5.1.1), `rocq` (Rocq 9.0.1, coq-itree 5.2.1) and `ctree` (Coq 8.20.1, coq-ctree 2.0).

| Command | Result |
| --- | --- |
| `git checkout -B claude/interesting-volhard-6ceb2e seat/itrees` | the branch moved from `9187b9b60` (main) to `5e2c01d99`; nothing of it was lost, it is on main |
| `opam exec --switch=effect4 -- dune build eff engine/test/todo` (in `ocaml/`) | exit 0; the libraries the drivers link |
| `bash docs/research/2026-10-16-itrees/reproduce.sh OUTDIR` | exit 0 in 45 s from an empty folder; every step passes, the earlier eight and the three new ones |
| `python3 scripts/check-language.py --strict docs/research/2026-10-16-itrees/README.md` | PASS, no finding |
| `python3 scripts/check-language.py --strict docs/research/2026-10-16-seat-itrees-budget-receipt.md` | PASS, no finding |

What the new logs hold:

| Log | Content |
| --- | --- |
| `logs/9-budget.log` | five Rocq files compiled, each timed (2.8 s for `Budget.v`); Rocq's `vm_compute` timed on two runs |
| `logs/10-budget-assumptions.log` | `Print Assumptions` of 21 results: each closed under the global context |
| `logs/11-view.log` | the driver built and run: seven examples, each frame checked to take back no step; the timing |
| `logs/12-budget-mutant.log` | Lean's tree with one more test per loop fails `truncation_is_denoteB`, after monotonicity passes |

Not run, by the brief: any Lean build. No `lake`, `make gen-*` or `make check-*` ran. Nothing
under `src/`, `Test/`, `tools/`, `ocaml/`, `docs/core/` or `lakefile.toml` changed.

## Axiom output

No Lean declaration changed. The Rocq assumptions, from `logs/10-budget-assumptions.log`:

| Results | Assumes |
| --- | --- |
| `denoteB_approx`, `meaning_fragment`, `truncation_is_denoteB`, `denoteB_below_meaning`, `adequacy` | nothing: closed under the global context |
| `meaning_finishes_iff`, `meaning_waits_iff`, `meaning_diverges_under_iff`, `meaning_diverges_iff` | nothing |
| `run_at_finished`, `run_at_waits`, `run_at_grows`, `settle_finished`, `settle_complete`, `diverges_iff_never_settles` | nothing |
| `edit_congruence`, `edit_keeps_outcomes` | nothing |
| `doubling_finishes`, `doubling_waits`, `forever_cut_everywhere`, `edit_outcomes` | nothing |

ITree's own axioms (`ITree/Axioms.v`) are reached by none of them. Every result assumes its
translators for the program syntax: the LCNF route, `gen/split_types.ml` and rocq-of-ocaml. The
extracted runner also assumes Rocq's extraction.

## Evidence

| Claim | Evidence |
| --- | --- |
| `denoteRowsB k` is below the meaning at every budget, up to silent steps, on the fragment | proved in Rocq |
| The meaning with each loop cut after `k` tests is `denoteRowsB k`, up to `eutt` | proved in Rocq |
| Lean's three chain outcomes under a host are the run's `≈ Ret`, frontier node and `≈ ITree.spin` | proved in Rocq, every host and start |
| With no host, the meaning diverges exactly when every budget cuts | proved in Rocq |
| The transcription follows Lean's `denoteRowsB`, `iter`, `thenOpt` and `loopStep` | reading, arm by arm, cited in `Budget.v`; no theorem across the provers |
| The red control fails exactly at `truncation_is_denoteB` | tested |
| A reported finish or wait of `run_at` and `settle` is the meaning's; `settle` finds every finish | proved in Rocq |
| The six examples behave as stated | finite checks by kernel computation; `forever_cut_everywhere` is a theorem at every budget |
| An edit by `EffEq` programs keeps the three outcomes | proved in Rocq |
| The extracted runner computes frames 0 to 1000 of `ping` in 0.059 s, Rocq's evaluator in 0.494 s | tested, one machine under load |

## Open obligations

1. Definitions by budgeted unfolding: done by the second commit, above. The call depth is this
   folder's count, a proposal for Lean's arms (README proposal 1).
2. The README's proposal 8, for the math seat: R12 by the route of `adequacy_loop`.
3. A Rocq `host` is any function. That Lean's `rowsHost` is the instance `route cells_host` is
   read, not proved.
4. The branch is not pushed. It carries `seat/itrees`, which is not merged into main either.

## Proposed decisions rows (proposals only)

1. **The budget relation as research evidence.** A chain outcome of `denoteRowsB` is the tree
   meaning's outcome, by `Budget.v`, under the transcription and the translators above. It moves
   no number of the tree.
