# Prompt: the research partner of seat SVG (the theory packet)

You are the research partner of seat SVG in `C:\Users\kokok\Dev\lean4-whatwg-svg`, branch
`html/svg`. You write only under `docs/research/2026-10-11-svg-theory/`. You run no `lake`, you
edit no Lean file, and you commit nothing: the seat commits your packet.

## Why

The seat's review is `docs/research/2026-10-11-svg-seat-review.md`. It sets the model of the SVG
package as nine points, T1 to T9, and the rules of its meta level as M1 to M8. Each point cites a
source. Your packet makes each source local, so the seat cites it from the page and never from
memory.

## What to collect

For each source below:

1. Find an open copy: the author's page, arXiv, the publisher's open access, or the proceedings.
2. Save it under `texts/`, with its SHA-256 and the date and address of the fetch.
3. Read the sections named below, and write what the package takes from them.

A book or a long survey is kept as its named chapter only. If no open copy exists, record the
full citation and the reason, and keep the closest open text instead. Never write a citation you
have not seen on the source itself.

| Group | Source | Read for | Serves |
| --- | --- | --- | --- |
| Trees | Murata, Lee, Mani, Kawaguchi, "Taxonomy of XML schema languages using formal language theory", ACM TOIT 2005 | local, single-type and regular tree grammars | T1 |
| Trees | Martens, Neven, Schwentick, Bex, "Expressiveness and complexity of XML Schema", ACM TODS 2006 | single-type grammars as top-down deterministic validation | T1 |
| Trees | Comon et al., *Tree Automata Techniques and Applications* (TATA), the chapter on unranked trees and hedge automata | hedge automata; closure under product | T1, T2 |
| Trees | Kilpeläinen, Wood, "SGML and XML document grammars and exceptions", Information and Computation 2001 | exclusions as a state that grows along a path | T3 |
| Trees | Boneva, Ciucanu, Staworko, "Schemas for unordered XML on a DIME", Theory of Computing Systems 2015 | disjunctive multiplicity schemas: unordered content with counts | T3 |
| Trees | Brüggemann-Klein, Wood, "One-unambiguous regular languages", Information and Computation 1998 | the ordered models that `seqOk` checks | T1 |
| Folds | Knuth, "Semantics of context-free languages", Mathematical Systems Theory 1968 | inherited and synthesized attributes | T5 |
| Folds | Fokkinga, Jeuring, Meertens, Meijer, "A translation from attribute grammars to catamorphisms", 1991 | an attribute grammar as one fold | T5 |
| Folds | Meijer, Fokkinga, Paterson, "Functional programming with bananas, lenses, envelopes and barbed wire", FPCA 1991 | the fusion law; the paramorphism | T5 |
| Embeddings | Foster, Greenwald, Moore, Pierce, Schmitt, "Combinators for bidirectional tree transformations", TOPLAS 2007 | the round-trip laws | T6, T7 |
| Embeddings | Kennedy, "Functional pearl: Pickler combinators", JFP 2004 | one description that writes a value and reads it back | T8 |
| Embeddings | Rendel, Ostermann, "Invertible syntax descriptions: unifying parsing and pretty printing", Haskell Symposium 2010 | partial isomorphisms; the invertible description | T8 |
| Embeddings | Danielsson, "Correct-by-construction pretty-printing", DTP 2013 | a printer whose output parses back, by construction | T7, T8 |
| Regular | Brzozowski, "Derivatives of regular expressions", JACM 1964 | the derivative | T8 |
| Regular | Owens, Reppy, Turon, "Regular-expression derivatives re-examined", JFP 2009 | a matcher by derivatives, with its correctness | T8 |
| Regular | Egolf, Lasser, Fisher, "Verbatim++: verified, optimized, and semantically rich lexing with derivatives", CPP 2022 (and the first Verbatim paper) | the longest-match rule, proved | T8 |
| Regular | Radanne, "Typed parsing and unparsing for untyped regular expression engines", PEPM 2019 | a typed regular expression that prints | T8 |
| Meta | Boutin, "Using reflection to build efficient and certified decision procedures", TACS 1997 | proof by reflection | M1, M4 |
| Meta | Gonthier, Mahboubi, "An introduction to small scale reflection in Coq", JFR 2010 | Boolean reflection | M1, M7 |
| Meta | Grégoire, Leroy, "A compiled implementation of strong reduction", ICFP 2002 | the cost of evaluation inside a kernel | M4 |
| Meta | Ullrich, de Moura, "Beyond notations: hygienic macro expansion for theorem proving languages", IJCAR 2020 (LMCS 2022) | Lean 4's macros and hygiene | M5 |
| Meta | de Moura, Ullrich, "The Lean 4 theorem prover and programming language", CADE 2021 | the elaboration of terms, the compiler and the kernel | M1, M4 |
| Meta | de Moura, Avigad, Kong, Roux, "Elaboration in dependent type theory", 2015 | what elaboration decides | M1 |

## Two facts about the toolchain

Read them in the Lean 4 sources at tag `v4.33.1`, the toolchain of this repository. Save each
excerpt with its path and the tag:

1. The list of `Nat` operations the kernel evaluates natively, in `src/kernel/type_checker.cpp`
   or the file that holds it at that tag. T4 and M4 rest on it.
2. The index function that Lean derives for an enumeration inductive (`toCtorIdx`, `ctorIdx` or
   another name), with `ofNat`. T4 uses it as the bit index.

## The packet

`docs/research/2026-10-11-svg-theory/README.md` holds:

1. One line per source: the citation, the address, the date of the fetch, the SHA-256 and the
   file under `texts/`.
2. Per source, three to six sentences on what the package takes, tied to T1–T9 or M1–M8. Quote
   at most one short definition or theorem per source, with its section.
3. Where a source contradicts the review, say so first, and name the point.
4. A reading order for the seat: the five sources to read before the plan revision.

The seat adds `docs/research/2026-10-11-svg-theory/texts/` to `.gitignore`. A `git add` of the
packet then commits the README and leaves the texts on disk.

Write the README to lean4-effect4's writing rules, as the seat's plan is written. Stop when the
README is done, and tell the seat in one paragraph what you found.
