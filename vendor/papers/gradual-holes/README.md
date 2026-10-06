# Typed holes, the gap and its guarantees

These original papers support the study of a type gap with holes for Effect4 (decisions row
281). The owner asked for them on 2026-10-06, so that each term of a calculus and each
theorem is read from its page.
The collection contains references. It holds no executable dependency and no Effect4 proof
claim.

The PDFs keep their original bytes. Git tracks this index, the manifest and the checksums.
The PDFs stay on disk and are not tracked.
[manifest.json](manifest.json) records each paper's authors, version, source URL, retrieval
time, page count and SHA-256 hash.
[SHA256SUMS](SHA256SUMS) supports an independent byte check.
The neighbouring collection is [program graphs](../program-graphs/README.md). It holds
"Bidirectional Type Slicing", "Hazelnut" and "The Zipper", which this collection continues.

## Papers

| Paper | Retained version | Main use |
| --- | --- | --- |
| [Total Type Error Localization and Recovery with Holes](zhao-marking-popl24.pdf) | Zhao, Maroof, Dukkipati, Blinn, Pan and Omar, POPL 2024; the Hazel project's copy | The marking calculus: a total checker that marks each local failure. The type slicing paper builds on it. |
| [Live Functional Programming with Typed Holes](omar-live-typed-holes-1805.00155v4.pdf) | Omar, Voysey, Chugh and Hammer, POPL 2019; extended version, arXiv v4 | Running an incomplete program: evaluation around holes, and what a hole keeps of its environment. |
| [Refined Criteria for Gradual Typing](siek-refined-criteria-snapl2015.pdf) | Siek, Vitousek, Cimini and Boyland, SNAPL 2015 | The gradual guarantee. The slicing paper's graduality is its static, downward case. |
| [Gradual Typing: A New Perspective](castagna-gradual-new-perspective-popl19.pdf) | Castagna, Lanvin, Petrucciani and Siek, POPL 2019; the first author's copy, with appendices | Gradual types with subtyping, unions and intersections: the nearest published setting to Effect4's types. |
| [Abstracting Gradual Typing](garcia-abstracting-gradual-typing-popl16.pdf) | Garcia, Clark and Tanter, POPL 2016; the first author's copy | A recipe that derives the gap's rules from an existing static type system. |
| [The Derivative of a Regular Type is its Type of One-Hole Contexts](mcbride-derivative-regular-type.pdf) | McBride, extended abstract; the author's copy | One-hole contexts computed from a signature. |
| [Bidirectional Typing](dunfield-bidirectional-typing-1908.05839v2.pdf) | Dunfield and Krishnaswami, ACM Computing Surveys; arXiv v2 | The survey of synthesis and analysis that the slicing paper takes as its setting. |

## What was checked

Each file is a valid PDF, and its first page gives the title and the authors that the table
names. Nobody has read a paper in full for this index. A reader who cites one gives the
PDF page, and checks each formula against that page.

These papers are design references. A theorem of theirs is not an Effect4 theorem: each
transfer to Effect4's types and programs needs its own statement and its own proof.

## Verify the retained bytes

Run this command from the collection directory:

```sh
shasum -a 256 -c SHA256SUMS
```
