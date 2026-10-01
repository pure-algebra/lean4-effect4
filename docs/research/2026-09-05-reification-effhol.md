# EffHOL and the local adaptation

Read this when choosing an effectful program logic, transporting a paper rule,
or attempting proof-to-program extraction. Source identities are in
[sources.md](sources.md); the skill procedures are engineering adaptations.

## What the paper establishes

EffHOL separates computational kinds, types, and programs from logical
indices, expressions, and specifications. Its Theorem 5 constructs typed
effectful realizers of HOL derivations. An instance must respect the required
typing, substitution, reduction, conversion, and deduction rules. The modality
has introduction, sequencing, monotonicity, and anti-reduction rules; the
sequencing rule is an implication. The paper permits a computation to satisfy
a false postcondition and does not thereby guarantee termination. Its
evidenced-frame result also carries instance conditions. Complex-language case
studies remain future work in this version. [EffHOL, Sections IV–V, VII, IX and
Appendix E](https://arxiv.org/html/2506.09458v1).

The authors' artifact uses Coq 8.20.1. Its README records simplified syntax and
an untyped deduction relation; typing is treated separately. The inspected
translation contains `soundness`, and `EffHOL.v` contains the modal constructors
`HOPL_MI`, `HOPL_ME`, `HOPL_MM`, and `HOPL_RED`. Source inspection is not a fresh
build or an axiom audit. [Pinned artifact](https://github.com/dominik-kirst/effhol/tree/163be012a13a0a6e408e7b41b25f1e059dcbdb0f).

## The adaptation to check

The following is a proposed work record for a Lean development, not an
additional theorem attributed to the paper. Fill it for the actual language.

| Component | Decision and required evidence |
| --- | --- |
| Program domain | Existing syntax/proof carrier, result and answer universes, admitted effects, and environments |
| Execution | Reduction or runs relation, evaluation strategy, values, state, history, choices, and observable outcomes |
| Specification | Predicates over which observations; whether failure and interruption satisfy or violate them |
| Computation modality | Its definition, universal/existential choice reading, and partial/total reading |
| Return | The local theorem connecting a returned value to the selected modality |
| Sequencing | The local theorem relating nested computation specifications to composition, with all state/history and domain premises |
| Monotonicity | The local postcondition order and the theorem transporting implication |
| Reduction | The permitted reduction steps and the direction in which satisfaction transfers; effectful steps cannot be erased without justification |
| Binding and typing | Capture avoidance, weakening/substitution, value restrictions, and preservation for the admitted syntax |
| Realization | The local relation between source formulas and program witnesses, if this is actually requested |

Do not strengthen a one-way rule into an equation or derive total correctness
from the notation for a modality. Do not infer an all-runs interpretation from
the mere presence of a monad. Distinct modalities can express different claims
about the same computation.

## Existing Effect4 and Foldlab decisions

Effect4's `docs/DESIGN-BASIS.md`, DB-06, assigns the future logic layer a
liberal-precondition reading and keeps total correctness separate. This is the
project's interpretation choice. It does not make every admissible EffHOL
instance that particular predicate transformer.

Foldlab already owns `WPre`, `WPost`, `wlp`, `wp`, `Triple`, and `PartialTriple`
in `library/cas/Cas/Lang/Wp.lean`. Its shipped `wp_iff_wlp_and_total` and
`wpAux_append` are the relevant reuse points. The latter requires
`env ≠ [] ∨ pre ≠ []` and passes
`env ++ PProg.answersFrom H env pre` into the suffix.

The staged Effect Core ruling `EC1-R31` specializes the logic to those owners.
Counterexamples `EC1-CE046` and `EC1-CE047` reject unconditional table append and
restarting the suffix with an empty answer history. The staged `EC1-T130`
specialization remains a separate obligation; the scratch `wlp_append` is not
a shipped theorem. Refresh these records before implementation. Do not create
a second public modality or discard the premises to match familiar notation.

## If actual proof extraction is requested

Separate object-language formulas and derivations from Lean's metatheory.
Record the admitted inference rules and a computational witness representation.
The desired interface computes a witness and supplies a proof of its relation
to the formula; an existential proposition alone does not provide a general
executable extraction interface. Ordinary Lean proofs in `Prop` are erased
during execution, and arbitrary proposition-to-data elimination is restricted.

State obligations for each translation and its binding/typing behavior, then
prove the conclusion for the admitted derivations. An extracted witness still
needs its own encoding, interpreter, and host connections if those are part of
the requested result. This route does not authorize translating arbitrary Lean
proofs, every classical principle, or unrestricted JavaScript closures.
