# Program graphs, typing and event order

These original papers support the owner's program inspection and manipulation research.
They also support the design of visual explanations, session inspection and controllable clocks.
The collection contains references, not executable dependencies or new Effect4 proof claims.

The PDFs retain their original bytes, title pages and rights notices.
[manifest.json](manifest.json) records authors, versions, source URLs, retrieval times, page counts and SHA-256 hashes.
[SHA256SUMS](SHA256SUMS) supports an independent byte check.

## Papers

| Paper | Retained version | Main use |
| --- | --- | --- |
| [Bidirectional Type Slicing](bidirectional-type-slicing-2607.12197v1.pdf) | Carroll, Madhavapeddy and Omar, July 2026 preprint v1 | Explain inferred types, expected types and type disagreements. |
| [Time, Clocks, and the Ordering of Events in a Distributed System](lamport-1978-time-clocks.pdf) | Lamport, CACM, July 1978 | Separate causal dependencies, clock readings and chosen total orders. |
| [The Zipper](huet-zipper.pdf) | Huet, author manuscript of the 1997 paper | Select a subtree while retaining its reconstruction context. |
| [A Type and Scope Safe Universe of Syntaxes with Binding](allais-binding-universe.pdf) | Allais et al., ICFP 2018 | Share binding descriptions, traversals and their proof structure. |
| [Hazelnut](hazelnut-1607.04180v5.pdf) | Omar et al., POPL 2017, extended version v5 from February 2019 | Relate edit actions, cursor movement and typed editing states. |
| [Combinators for Bi-Directional Tree Transformations](foster-bidirectional-tree-transformations.pdf) | Foster et al., technical report MS-CIS-04-15, August 2004 | Relate a view update to its source tree. |
| [Interaction Trees](interaction-trees-author.pdf) | Xia et al., POPL 2020, author copy | Study effects, composition, iteration and behavior relations together. |
| [Choice Trees](choice-trees-2211.06863.pdf) | Chappe et al., November 2022 preprint v1, POPL 2023 publication | Study internal choices, scheduling and contextual restrictions on equations. |
| [Formal Verification of Translation Validators](tristan-leroy-2008-validation-scheduling.pdf) | Tristan and Leroy, POPL 2008, author copy | Validate proposed transformations against a named behavior relation. |

## Visual reading guide

Page numbers below count PDF pages from one.
[citations-audit.md](citations-audit.md) records how each locator was checked.

| Visual question | Paper and location | Candidate application |
| --- | --- | --- |
| Why does this expression have this type? | Type Slicing, pages 3–4, figures 1–3 | Highlight the selected expression and the context contributing to its type. |
| How can an explanation become more focused? | Type Slicing, page 10, figure 8 | Show query refinement and the information retained at each step. |
| Which events depend on which other events? | Lamport, pages 2–3, figures 1–3 | Draw fiber lanes with separately labeled program-order and communication edges. |
| What does an edit change? | Hazelnut, page 2, figures 1–2 | Show an edit action, its location and its resulting checked state. |
| How does a view update affect the source? | Tree Transformations, page 58, figures 8–9 | Show selected source content beside the corresponding view update. |
| How do sequences, branches and loops compose? | Interaction Trees, pages 12 and 18, figures 12–13 and 17 | Present straight composition and iteration within one explanation. |
| What does a scheduling choice expose? | Choice Trees, pages 8, 18 and 23, figures 3, 13 and 19 | Distinguish branching, internal steps and parallel behavior. |
| Where does transformation validation fit? | Translation Validators, pages 6–7, figures 1–3 | Separate a proposed change from its program admission and behavior checks. |
| How can binding proofs be shared? | Binding Universe, page 25, figures 46–47 | Organize reusable traversal proofs around their environment and binding premises. |

These applications are design proposals.
Type Slicing assumes a precision relation and holes that Effect4 does not currently provide.
Its minimal explanation is not necessarily a minimum-size explanation.
An accepted edit does not establish unchanged behavior.
A tree view is not automatically an editable view.
A later clock reading does not establish causality.
An execution journal does not contain every causal dependency.
Interaction Trees and Choice Trees supply semantic methods, not replacement stored syntax for `Eff`.

## Provenance notes

The manifest pins the returned bytes even when an author's URL has no version suffix.
The unversioned Choice Trees URL currently returns the same v1 bytes as the earlier local research copy.
The retained Interaction Trees author copy differs from the earlier arXiv copy.
The retained Tree Transformations report differs from the earlier local copy.
The manifest records those earlier paths and hashes without replacing them.

Huet's author PDF retains a 1993 template header.
The [publisher record](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/zipper/0C058890B8A9B588F26E6D68CF0CE204) identifies the published paper as September 1997.

The verification covers PDF validity, retained bytes, selected passages and the indexed visual pages.
It does not claim a full reading or independent proof audit of every paper.

## Verify the retained bytes

Run this command from the collection directory:

```sh
shasum -a 256 -c SHA256SUMS
```
