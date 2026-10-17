# 2026-10-16 seat itrees receipt: interaction trees in Rocq for Eff and the vessel

**The one thing to know before merging:** this commit adds research files only, under
`docs/research/2026-10-16-itrees/`. No tracked source, generated file or gate changed. Its Rocq
results join no gate of the tree, and each names what it assumes. The Lean-side items are
proposals, and three of them are for the math seat.

The research note is `docs/research/2026-10-16-itrees/README.md`.

## Base and head

| Item | Value |
| --- | --- |
| Branch | `seat/itrees`, cut from `d3bca195a` (`seat/ocaml-interop`) |
| Base | `d3bca195a` |
| Head | the commit that adds this receipt |
| Pushed | no |

## Changed files

| File | Change |
| --- | --- |
| `docs/research/2026-10-16-itrees/README.md` | new: the research note |
| `docs/research/2026-10-16-itrees/reproduce.sh` | new: one command that rebuilds every artifact, check and log |
| `docs/research/2026-10-16-itrees/rocq/*.v` | new: the meaning, the hosts and runner, the judgments, the fixture checks, the typed vessel, the choice-tree refinement, the extraction |
| `docs/research/2026-10-16-itrees/gen/*` | new: the type splitter, the extraction map, the fixture generators and their byte checks, the extracted tree's driver |
| `docs/research/2026-10-16-itrees/generated/` | new: the generated Rocq syntax and fixtures, as the final reproduction wrote them |
| `docs/research/2026-10-16-itrees/logs/` | new: the final reproduction's logs |
| `docs/research/2026-10-16-seat-itrees-receipt.md` | new: this receipt |

## Commands and results

Each command ran from the repository root. The opam switches are `effect4` (OCaml 5.1.1), `rocq`
(OCaml 5.4.1, Rocq 9.0.1, coq-itree 5.2.1, rocq-of-ocaml `1ac69a7`) and `ctree` (Coq 8.20.1,
coq-ctree 2.0).

| Command | Result |
| --- | --- |
| `opam repo add --switch=rocq rocq-released https://rocq-prover.org/opam/released --this-switch` | added to `rocq` only |
| `opam install --switch=rocq coq-itree coq-paco coq-ext-lib` | coq-itree 5.2.1; nothing removed |
| `opam switch create ctree ocaml-base-compiler.5.4.1 --repos=default,rocq-released=…` then `opam install --switch=ctree coq-ctree` | coq-ctree 2.0 on Coq 8.20.1, 12 minutes; 1.1 GiB |
| `bash docs/research/2026-10-16-itrees/reproduce.sh OUTDIR` | exit 0 in 60 s; every check of the logs below passes |
| `python3 scripts/check-language.py --strict docs/research/2026-10-16-itrees/README.md` | PASS, no finding |

What the final reproduction's logs hold:

| Log | Content |
| --- | --- |
| `logs/3-fixtures.log` | 7 to-do requests and 6 vessel runs read back exactly, programs re-encoded byte for byte |
| `logs/4-rocq.log` | 12 Rocq files compiled, each timed: 16 to-do checks and 7 vessel checks among them |
| `logs/5-assumptions.log` | the assumptions of 15 results |
| `logs/6-ctree.log` | the choice-tree files; the refinement's report; the import control |
| `logs/7-extracted.log` | 28 runs of the extracted tree under four hosts, each Lean's result; the timing |
| `logs/8-mutant.log` | the meaning with the option decision swapped fails the to-do checks |

Not run, by the brief: any Lean build. No `lake`, `make gen-*` or `make check-*` ran.

## Axiom output

No Lean declaration changed. The Rocq assumptions, from `logs/5-assumptions.log` and
`logs/6-ctree.log`:

| Result | Assumes |
| --- | --- |
| `TodoCheck.*`, `VesselCheck.*` (checked samples) | nothing: closed under the global context |
| `exit_not_divergence`, `frontier_not_divergence`, `tape_respects_equivalence`, `loop_diverges` | nothing |
| `study_checks_never_fire`, `raw_refuses` | nothing |
| `traces_iff_equivalent`, `assess_sound_every_host`, `assess_sound_every_stateful_host` | `eq_rect_eq` |
| `mock_meets` | nothing |
| `mock_answers_within_spec` | `eq_rect_eq` |
| `mock_refines_spec` | an unsafe universe hierarchy: ctrees' `Interp.FoldStateT` and `Interp.FoldCTree` |

Every result also assumes its translators: the LCNF route, `gen/split_types.ml` and rocq-of-ocaml
for the syntax, and Rocq's extraction for the extracted tree.

## Evidence

| Claim | Evidence |
| --- | --- |
| The Rocq meaning makes Lean's recorded calls and exits on 14 to-do runs and 6 vessel runs | tested, finite, by kernel computation |
| It tells another host's tape apart, waits on an empty tape, and fails with a swapped decision | tested |
| An `iterate` whose test is `true` has a divergent meaning | proved in Rocq |
| Exits and frontiers are not divergence; a tape cannot tell `eutt` trees apart | proved in Rocq |
| Every vessel verdict under every host satisfies `sound_verdict` | proved in Rocq, of the model, assuming `eq_rect_eq` |
| The untyped workflow's study checks never fire under a typed host | proved in Rocq, of the model |
| A mock FMI host refines the specification for every program | proved in Rocq modulo universe consistency |
| The extracted tree under the to-do lane's hosts gives Lean's results | tested, finite, 28 runs |
| The extracted tree costs 2.2 to 2.7 times less CPU per request than the engine | tested, three runs on one machine under load 6 to 15 |

## Landed theorems and their placement

No Lean theorem landed. The Rocq theorems live in the research folder and join no gate.

## Open obligations

1. The proposals of the note's README, items 1 to 7; items 1, 3 and 4 are for the math seat.
2. The switch `ctree` (1.1 GiB) and the switch `rocq` (now with coq-itree) stay installed. Run
   `opam switch remove ctree -y` to free the first.
3. The vessel's six runs are read from the Codex checkout that holds `apps/vessel/artifacts/`;
   `reproduce.sh` takes another location as its second argument.

## Proposed decisions rows (proposals only)

1. **Rocq results as research evidence.** A Rocq result names its translators, its axioms and its
   fragment, and it moves no number of the tree. The trace checks are finite tests, not
   theorems.
2. **Definitions in the call tree.** `denoteRows` and `denoteRowsB` gain the definition arms by
   budgeted unfolding; the Rocq meaning and its fixtures specify them.
