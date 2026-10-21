# Sources of the view-graph note

`fetch.sh` downloads the open-access copies into `pdf/`, `pdftotext -layout` writes `text/`, and
`SHA256SUMS` fixes each copy. The PDFs and the texts stay on disk and out of git. This index is
tracked.

| Key | Source | Copy | What the note takes from it |
| --- | --- | --- | --- |
| Mokhov 2017 | A. Mokhov, *Algebraic graphs with class (functional pearl)*, Haskell Symposium 2017 | `pdf/mokhov-2017-algebraic-graphs-with-class.pdf` | the four constructors, the eight axioms, the edge-set model (`tools/Tools/View/AlgGraph.lean` holds them) |
| Mokhov 2022 | A. Mokhov, *United monoids: finding simplicial sets and labelled algebraic graphs in trees*, arXiv 2203.05085 | `pdf/mokhov-2022-united-monoids.pdf` | labelled edges as a united monoid, the route to tags on wires |
| Fong 2015 | B. Fong, *Decorated cospans*, arXiv 1502.00872 | `pdf/fong-2015-decorated-cospans.pdf` | an open system as a cospan with a decoration; composition by pushout, the gluing of boundaries |
| Baez–Fong 2015 | J. Baez, B. Fong, *A compositional framework for passive linear networks*, arXiv 1504.05625 | `pdf/baez-fong-2015-passive-linear-networks.pdf` | the worked example of open graphs composed along their boundary wires |
| BSZ 2016 | F. Bonchi, F. Gadducci, A. Kissinger, P. Sobociński, F. Zanasi, *Rewriting modulo symmetric monoidal structure*, arXiv 1602.06771 | `pdf/bonchi-sobocinski-zanasi-2016-rewriting-modulo-smc.pdf` | string diagrams as hypergraphs; graph rewriting sound and complete for the monoidal equations |
| Selinger 2010 | P. Selinger, *A survey of graphical languages for monoidal categories*, arXiv 0908.3347 | `pdf/selinger-2010-string-diagrams-survey.pdf` | the string diagram of a symmetric monoidal category; the cartesian case, where copying is free |
| Plotkin–Pretnar 2013 | G. Plotkin, M. Pretnar, *Handling algebraic effects*, LMCS 9(4), arXiv 1312.1399 | `pdf/plotkin-pretnar-2013-handling-algebraic-effects.pdf` | a handler as an algebra; handling as the fold of the free model |
| Ahman–Bauer 2020 | D. Ahman, A. Bauer, *Runners in action*, ESOP 2020, arXiv 1910.11629 | `pdf/ahman-bauer-2020-runners-in-action.pdf` | a runner as a comodel with state; runners compose in sequence |
| Hasegawa 1997 | M. Hasegawa, *Models of sharing graphs*, PhD thesis, Edinburgh, ECS-LFCS-97-360 | not vendored: both hosts refused the fetch on 2026-10-21 | sharing graphs as the term graphs of a traced cartesian category |
| Joyal–Street 1991 | A. Joyal, R. Street, *The geometry of tensor calculus I*, Adv. Math. 88 | not vendored, paywalled | the origin of string diagrams |
| Fox 1976 | T. Fox, *Coalgebras and cartesian categories*, Comm. Algebra 4 | not vendored, paywalled | a symmetric monoidal category with natural commutative comonoids is cartesian |

A locator in the note (a section, a page, a figure) is read off the copy in `text/`. A source
with no copy is cited by title alone.
