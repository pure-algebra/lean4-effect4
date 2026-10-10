# Comodel and runner papers, filed 2026-10-09

The owner's ruling of the coalgebra note's third question files these texts (decisions row
338). The coalgebra layer of `Effects` and the host laws of Effect4 cite them. The PDFs are
in `pdf/`, and their text, extracted with `pdftotext -layout` (Poppler), is in `text/`. Neither
folder is tracked; this note and `SHA256SUMS` are.

## Sources

| File | Document | Source | Bytes | Pages |
| --- | --- | --- | --- | --- |
| `plotkin-power-2008-tensors-comodels.pdf` | Plotkin and Power. *Tensors of Comodels and Models for Operational Semantics.* MFPS XXIV, ENTCS 218 (2008), 295–311 | `https://homepages.inf.ed.ac.uk/gdp/publications/Tensors_Comodels_Models.pdf` | 263016 | 20 |
| `uustalu-2015-stateful-runners.pdf` | Uustalu. *Stateful Runners of Effectful Computations.* MFPS XXXI, ENTCS 319 (2015), 403–421, open access | `https://cs.ioc.ee/~tarmo/papers/uustalu-mfps15.pdf` | 308674 | 19 |
| `ahman-bauer-2020-runners-in-action.pdf` | Ahman and Bauer. *Runners in Action.* ESOP 2020, arXiv 1910.11629 | `https://arxiv.org/pdf/1910.11629` | 702244 | 33 |
| `setzer-hancock-2005-interactive-programs-weakly-final.pdf` | Setzer and Hancock. *Interactive Programs and Weakly Final Coalgebras in Dependent Type Theory.* Dagstuhl Seminar Proceedings 04381 (2005) | `https://drops.dagstuhl.de/storage/16dagstuhl-seminar-proceedings/dsp-vol04381/DagSemProc.04381.2/DagSemProc.04381.2.pdf` | 284639 | 30 |
| `niu-spivak-2023-polynomial-functors.pdf` | Niu and Spivak. *Polynomial Functors: A Mathematical Theory of Interaction.* arXiv 2312.00990, a book | `https://arxiv.org/pdf/2312.00990` | 3400150 | 372 |

Hancock and Setzer's CSL 2000 paper, *Interactive Programs in Dependent Type Theory*, is
published by its authors only as DVI and PostScript. The 2005 paper above is its extended form.

## What each text gives the tree

Each locator below was read from the extracted text.

- **Hosts as comodels.** Plotkin and Power, Definition 3.1, defines a comodel of a countable
  Lawvere theory in a category. It is a functor from the theory's opposite category, and it
  keeps countable coproducts. Their section 4 defines the tensor of a comodel with a model. `Effects.Comodel` is
  the comodel of a signature with no equations, in `Set`, extended by `Option` failure.
- **Runners are comodels.** Uustalu, Proposition 3.1: monad morphisms from a theory's monad to
  the state monad of `C` are in bijection with comodels on `C`. His section 5 separates running
  from handling. `Comodel.handler` and `Comodel.ofHandler` are that bijection for a signature,
  into `StateT σ Option`.
- **Effectful runners.** Ahman and Bauer, section 2.2. Definition 1 gives a runner's
  co-operations, and Definition 2 a `T`-runner, whose co-operations land in a monad `T`.
  Proposition 3: monad morphisms from the free monad to `T` correspond one to one with
  `T`-runners. A comodel of `Effects` is a `T`-runner at `T = StateT σ Option`, and `Comodel.run`
  is the induced monad morphism.
- **Dependent interfaces.** Setzer and Hancock, section 3, defines a dependent interface. It
  has a set of states and the commands of each state. It has the responses to each command, and
  the next state after each response. `Effects.ISignature` (v0.10.0) is that interface, with worlds for states.
  Their section 3 also states bisimilarity of state-dependent interactive programs.
- **Polynomials and lenses.** Niu and Spivak, Definition 2.1 (a polynomial functor) and
  Definition 3.1 (a dependent lens). A signature of `Effects` is a polynomial, with operations
  for positions and answers for directions. `Signature.Hom` is a dependent lens: forward on
  operations, backward on answers. Their chapter 4 reads dynamical systems as dependent lenses.

## Not established

The table above maps definitions; it proves nothing. The statements of the tree are its own
theorems, and these texts are cited beside them.
