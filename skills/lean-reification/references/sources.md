# Source records

Research snapshot: 2026-09-02 UTC. These receipts identify what was read;
they do not certify a library build or import a source's axioms into Lean.
Paper files and downloaded proof sources were inspected in a temporary research
directory. They are not vendored or installed with the skills.

## Primary literature and documentation

| Source and resolved version | Bytes | SHA-256 of inspected artifact |
| --- | ---: | --- |
| [EffHOL, arXiv:2506.09458v1 (2025)](https://arxiv.org/pdf/2506.09458v1) | 777345 | `a493e698895878136a71e9ffdaaf9ece786cdd30864f853149cd69cec774ad0c` |
| [Interaction Trees, arXiv:1906.00046v2 (2019)](https://arxiv.org/pdf/1906.00046v2) | 554944 | `943dc278978b9d85f8957e9044ec2f571f315b43e98d58762dad3e08dca4934c` |
| [Choice Trees, arXiv:2211.06863v1 (2022)](https://arxiv.org/pdf/2211.06863v1) | 863779 | `87cae08d3a3c0156a38536ebefbf7bc179895a8b67759c277d474b71fad1d3a5` |
| [HITrees, arXiv:2510.14558v1 (2025)](https://arxiv.org/pdf/2510.14558v1) | 665188 | `86389e257dc4b0bd24ee838e40496f86bf4b65c5c71112db0664c6188cb3afc7` |
| [Dijkstra Monads for All, arXiv:1903.01237v1 (2019)](https://arxiv.org/pdf/1903.01237v1) | 1134244 | `8236fe3f4822d4ebec9e574d915743d46c2dae2c245b101e47877ef23ab02a12` |
| [Leroy, Formal verification of a realistic compiler (2009)](https://xavierleroy.org/publi/compcert-CACM.pdf) | 200102 | `5cfa2447db8dfa4400a43bb7e41e16f4787bf614e72bf0ffbf82f75d6824a137` |
| [Lean 4.33.0 reference: Axioms](https://lean-lang.org/doc/reference/4.33.0/Axioms/) | 309498 | `be43a0f1f89324682c15201cb6fa2da662b9e366e18adcab70dd54aa65325a46` |
| [Lean 4.33.0 reference: Recursive Definitions](https://lean-lang.org/doc/reference/4.33.0/Definitions/Recursive-Definitions/) | 3122484 | `1a8e5b80937e880304bd5239d0daa0090c6406378839fb0cd2af7701b96ae4f2` |
| [Loopy, arXiv:2311.07948v1 (2023)](https://arxiv.org/abs/2311.07948v1) | 805498 | `ec4197482a33bcaa5144f58e5df8d9b6a8c399504a53dcb892457b9fae8c66fa` |
| [LeanDojo, arXiv:2306.15626v2 (2023)](https://arxiv.org/abs/2306.15626v2) | 2967642 | `8eb0b3e351150d330202e30af528c9eb548a79905f52bdb0db04686a75b02649` |
| [Chockler et al., A Practical Approach to Coverage in Model Checking (2001)](https://doi.org/10.1007/3-540-44585-4_7) | 224906 | `9b293f2206b884b3a57f4716be847fdc96e2620e8fa3ae333162757fa056e055` |

EffHOL has 29 PDF pages; the inspected Dijkstra, ITree, Choice Tree, HITree,
and compiler papers have 30, 35, 32, 14, and 9 pages respectively. Page counts
are file-integrity checks, not statements that every proof was independently
verified.

Loopy, LeanDojo, and the coverage paper were read from Foldlab's
`.staging/model-guided-development/sources/`. Their local filenames are,
respectively, `kamath-et-al-2023-loopy-v1.pdf`,
`yang-et-al-2023-leandojo.pdf`, and
`chockler-kupferman-kurshan-vardi-2001-coverage.pdf`.

The three ITree/Choice Tree/HITree PDFs were absent at the paths recorded in
Foldlab's `papers.lock.json` on this machine. The exact recorded arXiv versions
were downloaded into temporary storage, and all three SHA-256 values matched
the lock. No Foldlab source record was changed. EffHOL's old staged provenance
row remains pending in that project; the receipt here is a separate research
record, not a promotion of the Foldlab packet.

The explanatory Lean page
[propositional large elimination](https://lean-lang.org/doc/reference/latest/Error-Explanations/About___--propRecLargeElim/)
was also read online on 2026-09-02. It is a rolling reference, not a pinned
artifact; the attempted 4.33.0 page could not be resolved through the browsing
tool. Use the target Lean toolchain for any implementation obligation. The
4.33.0 reference pages above are explanatory sources; Effect4's implementation
pin is 4.33.1, so examples and dependency behavior must be checked there.

## EffHOL proof artifact

Repository: [dominik-kirst/effhol at
163be012a13a0a6e408e7b41b25f1e059dcbdb0f](https://github.com/dominik-kirst/effhol/tree/163be012a13a0a6e408e7b41b25f1e059dcbdb0f).
The revision was resolved through the repository API; its commit date is
2025-06-25. The README names Coq 8.20.1. This task inspected source and did not
install Coq, run `make`, or collect `Print Assumptions` receipts.

| Inspected file | Bytes | SHA-256 |
| --- | ---: | --- |
| [README.md](https://raw.githubusercontent.com/dominik-kirst/effhol/163be012a13a0a6e408e7b41b25f1e059dcbdb0f/README.md) | 1034 | `2951677c67a06079695154b3a1dc263b5bf204165530b7a15aada6c5547df7db` |
| [EffHOL.v](https://raw.githubusercontent.com/dominik-kirst/effhol/163be012a13a0a6e408e7b41b25f1e059dcbdb0f/EffHOL.v) | 41780 | `06477db7cdbe3bab948f0e79c25cb0eb2e057fcd9cbf25677b0c10298dcd00fe` |
| [HOL_to_EffHOL.v](https://raw.githubusercontent.com/dominik-kirst/effhol/163be012a13a0a6e408e7b41b25f1e059dcbdb0f/HOL_to_EffHOL.v) | 18598 | `4c8f7937681fc93ec397b0b0a2a7a72e1e376e70aa1bdae8c4f66c196f10e26a` |
| [EffHOL_to_Fw.v](https://raw.githubusercontent.com/dominik-kirst/effhol/163be012a13a0a6e408e7b41b25f1e059dcbdb0f/EffHOL_to_Fw.v) | 23645 | `7f68646eefea521aa9f19f73682eea7ff6da21b908d300443940177852044f33` |
| [core_axioms.v](https://raw.githubusercontent.com/dominik-kirst/effhol/163be012a13a0a6e408e7b41b25f1e059dcbdb0f/core_axioms.v) | 1855 | `1081b16f1d054e18428d78474f171b6df7b1d881fc2086f5ed5047d67b4f6399` |
| [unscoped_axioms.v](https://raw.githubusercontent.com/dominik-kirst/effhol/163be012a13a0a6e408e7b41b25f1e059dcbdb0f/unscoped_axioms.v) | 3313 | `b1657cba577650bc007a67712cb09b26f74403488d16b3c2f03c980f646d8022` |

The inspected `core_axioms.v` imports functional extensionality. That source
fact is not a transitive dependency audit of `soundness`. The artifact's
simplifications and separate typing theorem are recorded in [effhol.md](effhol.md).
No proof source was copied into the skills, and no claim of an axiom-free
artifact is made.

## Local work reviewed

Effect4 baseline: `f4f55fae372be373465a9d7049f1c4721073f1ad`.
Foldlab baseline: `4005d34f249cda25134ac2bddff514e3a068bc1e`.
The following 24 tracked files matched their respective `HEAD` contents when
hashed. Other worktree changes were not evidence for this review. Paths are
relative to the named repository; [projects.md](projects.md) gives entry points.

| Repository | Path | SHA-256 |
| --- | --- | --- |
| effect4 | `AGENTS.md` | `e1202907874c6dbe0833283f4a9766221b31a73055f87b4e62d30710a534439c` |
| effect4 | `docs/ARCHITECTURE.md` | `8b140c510bcaaa98a6e84739d549764a5c30ab45710b185b17175ab9380a6029` |
| effect4 | `docs/DESIGN-BASIS.md` | `a8fe66bafe8654b08e50f3a93bfc040f9bb4bc219a2e7e92aa107c0d46425574` |
| effect4 | `docs/AGENT-ROUTING.md` | `a66e4ec24f2948670db3fd775304ec9861afd3847065110b9c304132527f04c6` |
| effect4 | `PORT-MANIFEST.md` | `9df6be60a4442278b94fa3e90b6c78ebcd9e832678fff2148cc52b9d48723983` |
| effect4 | `PLAN.md` | `2706f2d66c034d0a1f3911ff04964e789f8eec8097454ec22921ddeb37361dc9` |
| effect4 | `Effect4/Algebra/Program.lean` | `73a3c53d32bfd0b373d5853f4ec861943c387fe177e631e8aa814b2bd995a06b` |
| effect4 | `Effect4/Algebra/Handler.lean` | `930363b64967f7d98ae3f4f177fe46a5f1d1207faf3ba0a38ad865bd126cc2f0` |
| effect4 | `test/counterexamples/REGISTER.md` | `4674ff92f829858e73260f1483031bf4a9983e0c707dddfa95ea1f55293690f1` |
| effect4 | `docs/TYPESCRIPT-TARGET-DAG.md` | `4f469db86d2b426815923cedc2e20e3762bc16ca2c1ed4beae6ca57b415446e5` |
| effect4 | `docs/SCOPE-DAG.md` | `529c639970003ea940a46204ff8db61fa9f8c9d09e946d80aacff8f5a3c27214` |
| effect4 | `Effect4Test/Audit/AxiomGate.lean` | `1d426bd4e5e524d6af79d09b89d5649cdcd6e4a8512d6cfdce8ccbd7044ea53f` |
| effect4 | `scripts/test-trust-gate.sh` | `59a05c764de7193fe31c2ba016074e5f84e46bacaf8eeab568f92738bd6824cb` |
| foldlab | `.agents/skills/lean/SKILL.md` | `d74b967d69d2867894ed58d66c4ac368e7c95099e58f35f641e1a56b1de4e9f9` |
| foldlab | `.agents/skills/store-language/SKILL.md` | `0e7a7c78f4d65aac2be4ab56e1dcf8544372ab299bc305509b2988270fe7d943` |
| foldlab | `.staging/effect-core-v1/PLAN.md` | `2295a6e1bdb32366938347d18357bbc67a19ff629511a6a802668a61550ef96e` |
| foldlab | `.staging/effect-core-v1/ALGEBRA.md` | `e341698b699e65f2c7ec48bb3a31e92aa7a21b0391a849cb48784e5075978936` |
| foldlab | `.staging/effect-core-v1/COUNTEREXAMPLES.md` | `5562709dff0da37aedaadbf835e55bbeb563c16d4ed2246a7119eff1b7910216` |
| foldlab | `.staging/effect-core-v1/EXISTING-TYPES.md` | `9c98f17e02eaff47951561bbdbd61b1a25d420553edc8135648fbc9c6eafbb2a` |
| foldlab | `library/cas/Cas/Lang/Wp.lean` | `a90dec695e99187d2fdf62b25e406597989d0028aa1aae09571e44c411c2ad21` |
| foldlab | `.staging/operational-structure/LEAN-AGENT-SURFACE-PASS-A.md` | `0b65be0711f7f436ca99d20e07c70af12faafc0b10ed0f61dc4224cc79a926c4` |
| foldlab | `.staging/model-guided-development/SOURCE-STUDY.md` | `3811bedb7a4398d4e0d44e4ab9adfa32e15a003a3eec93d8b839026063ed5d36` |
| foldlab | `.reference/provenance/papers.lock.json` | `0eda34e3285c04c6884241763398cfbc0cad79f76caa365ed9a1d8f709885bd1` |
| foldlab | `docs/entity-store/research/lean-coinduction-realization-survey.md` | `8da29a3627ee1ffa1bc80a38d0294de80a8528977319e76f87f4c2cafda7e6e8` |

The existing Foldlab Lean stage entry points were also read for formation,
invariant modeling, algebraic systems, proof repair, and assurance review.
Their reuse is procedural; this pack is independently authored. The source
study's other empirical citations were treated as leads unless explicitly
listed above. Historical ecosystem surveys are not current compatibility tests.

## Reproduce the research boundary

Resolve the named repository commits and source paths; compare the file hashes.
For papers, retrieve the exact versioned URL and compare the SHA-256 before
using its claims. A mismatch requires a new source decision or an explicit
pending mark. Rebuilding a proof artifact or adopting a dependency is separate
work with its own toolchain, license, and trust review. Reading these sources
does not establish any source-to-Effect4 or Effect4-to-host theorem.
