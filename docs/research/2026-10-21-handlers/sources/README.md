# Sources of the handlers note

`fetch.sh` downloads the open-access copies into `pdf/`, `pdftotext -layout` writes `text/`, and
`SHA256SUMS` fixes each copy. The PDFs and the texts stay on disk and out of git. This index is
tracked. Two copies are the view-graph note's (`docs/research/2026-10-21-view-graph/sources/`).

| Key | Source | Copy | What the note takes from it |
| --- | --- | --- | --- |
| Plotkin–Pretnar 2013 | G. Plotkin, M. Pretnar, *Handling algebraic effects*, LMCS 9(4), arXiv 1312.1399 | `pdf/plotkin-pretnar-2013-handling-algebraic-effects.pdf` | a handler as an algebra, handling as the fold of the free model; §3.3, the parameter-passing handlers, whose handling terms have the type `P → C` |
| Ahman–Bauer 2020 | D. Ahman, A. Bauer, *Runners in action*, ESOP 2020, arXiv 1910.11629 | `pdf/ahman-bauer-2020-runners-in-action.pdf` | Definition 1, a runner as a carrier with one co-operation per operation; Definition 2 and Proposition 3, the `T`-runner and its one-to-one correspondence with monad morphisms out of the free monad; Example 12, the pairing of runners on a product state |
| Wu–Schrijvers–Hinze 2014 | N. Wu, T. Schrijvers, R. Hinze, *Effect handlers in scope*, Haskell Symposium 2014 | `pdf/wu-schrijvers-hinze-2014-effect-handlers-in-scope.pdf` | §7 and §9: a scoped operation delimits a program it runs, so it is not algebraic; the higher-order syntax that carries the program |
| Hyland–Plotkin–Power 2006 | M. Hyland, G. Plotkin, J. Power, *Combining effects: sum and tensor*, TCS 357 | not vendored: both hosts refused the fetch on 2026-10-21 | the sum of theories adds no equation; the tensor adds the commutation of every left operation with every right one |
| Plotkin–Power 2008 | G. Plotkin, J. Power, *Tensors of comodels and models for operational semantics*, MFPS 2008 | not vendored: both hosts refused the fetch on 2026-10-21 | the tensor of two comodels on disjoint operations is their product state, each operation acting on its own component |

A locator in the note (a definition, an example, a section) is read off the copy in `text/`. A
source with no copy is cited by title alone.
