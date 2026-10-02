# Sources for the semantics work (seat A, 2026-10-01)

Every chapter, section and page cited in `../citations-audit.md` is read off a file listed
here. New downloads sit in this folder (`fetch.sh` refetches them; `SHA256SUMS` checks them;
`text/` holds `pdftotext -layout` copies, poppler, `/opt/homebrew/bin/pdftotext`). Files that
were already on this Mac are linked, not copied, with their sha256 below. Nothing here was
downloaded from a mirror: every new file comes from an author's page, an institutional
repository (CWI), arXiv, or the book's own site.

**Do not force-add any PDF, `plf.tgz`, `plf/` or `text/` file.** The coordinator force-adds
only `README.md`, `fetch.sh` and `SHA256SUMS`. Two of the files carry terms that forbid
redistribution: Harper's abbreviated PFPL edition ("personal use of a single individual …
No unauthorized distribution of any kind is allowed", `text/pfpl-2nded-abbrev.txt:19-22`)
and ATTAPL's front matter ("All rights reserved", `text/attapl-frontmatter.txt:17-20`).

Short names used in the audit: [T] `text/tapl-contents.txt`, [A] `text/attapl-frontmatter.txt`,
[H] `text/pfpl-2nded-abbrev.txt`, [P] `plf/*.v`; the papers' short names are listed at the head
of the audit's §2.

## New downloads (this folder)

| File | Work | DOI or id; source URL | Terms | Pages | Text copy | Parse quality | Cited for (ours) |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `tapl-contents.pdf` | Pierce, *Types and Programming Languages*, MIT Press, 2002: contents pages v–xi | ISBN not printed in this file; downloaded from https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf | author's book page; the publisher's copyright applies; local reading copy, not to be force-added | 8 | `text/tapl-contents.txt` | good | the spine of Gemini's chapter table (TAPL chs. 3, 8, 9, 11, 13–16, 19, 20, 22, 23); system map §9 (TAPL ch. 15–16, §13.4, §16.3, ch. 16) |
| `attapl-frontmatter.pdf` | Pierce (ed.), *Advanced Topics in Types and Programming Languages*, MIT Press, ©2005: title pages, contents, preface | ISBN 0-262-16228-8 ([A]:36); downloaded from https://www.cis.upenn.edu/~bcpierce/attapl/frontmatter.pdf | author's book page; "All rights reserved" ([A]:17-20); local reading copy only | 12 | `text/attapl-frontmatter.txt` | good | Gemini's `attapl-03-effects`, `attapl-08-logical-relations` and the ch. 6/7 citations (all audited in §1a) |
| `pfpl-2nded-abbrev.pdf` | Harper, *Practical Foundations for Programming Languages*, 2nd ed., the author's "abbreviated online edition, with corrections" (© 2016; Cambridge University Press) | no DOI printed; downloaded from https://www.cs.cmu.edu/~rwh/pfpl/abbrev.pdf | author's terms ([H]:19-22): "made available for the personal use of a single individual. The reader may make one copy for personal use. No unauthorized distribution of any kind is allowed. No alterations are permitted." Keep the PDF and its text copy local; never force-add or share them | 228 | `text/pfpl-2nded-abbrev.txt` | fair: a diagonal PREVIEW watermark puts stray letters into lines and some page numbers on their own lines; the contents read correctly | `FrameAccepts`/`StackAccepts`/`SavedOk` and the machine (PFPL ch. 28, system map §9); Gemini's `machine-concurrency` and lemma-census rows (ch. 28, §28.2) |
| `plf.tgz` | Pierce et al., *Software Foundations* vol. 2, *Programming Language Foundations*, Version 7.1, 2026 (`plf/Preface.v:146-166`) | URL; downloaded from https://softwarefoundations.cis.upenn.edu/plf-current/plf.tgz | MIT-style licence, `plf/LICENSE` ("Permission is hereby granted, free of charge … to use, copy, modify, merge, publish, distribute …"); 17 chapters extracted to `plf/` | — | `plf/*.v` | source files, no extraction needed | the Coq twins of TAPL's lemmas in Gemini's lemma census (§3 of the audit); `References.v` for store typing |
| `plotkin-pretnar-2009-handlers-of-algebraic-effects.pdf` | Plotkin, Pretnar, "Handlers of Algebraic Effects", ESOP 2009, LNCS 5502, pp. 80–94 (as cited by [Pr15]:844-848) | 10.1007/978-3-642-00590-9_7 (as cited); downloaded from https://homepages.inf.ed.ac.uk/gdp/publications/Effect_Handlers.pdf | author-hosted copy | 15 | `text/plotkin-pretnar-2009-handlers-of-algebraic-effects.txt` | good | the free monad and `denote` (system map §9, "Plotkin and Pretnar §1, §5"); Gemini entry 29 |
| `pretnar-2015-introduction-to-algebraic-effects-and-handlers.pdf` | Pretnar, "An Introduction to Algebraic Effects and Handlers", invited tutorial, MFPS 2015 (ENTCS 319:19–35, as cited by [Scoped]:1531-1532) | 10.1016/j.entcs.2015.12.003 (as cited); downloaded from https://www.eff-lang.org/handlers-tutorial.pdf | author's language site (eff-lang.org) | 16 | `text/pretnar-2015-introduction-to-algebraic-effects-and-handlers.txt` | good | Gemini entry 31 (pedagogical basis of operations and handlers) |
| `bauer-pretnar-2015-programming-with-algebraic-effects-and-handlers.pdf` | Bauer, Pretnar, "Programming with Algebraic Effects and Handlers", arXiv:1203.1539v1 (2012); journal version JLAMP 84 (2015) 108–123 (as cited by [Pr15]:769-771) | arXiv:1203.1539; 10.1016/j.jlamp.2014.02.001 (as cited); downloaded from https://arxiv.org/pdf/1203.1539 | arXiv (author deposit) | 25 | `text/bauer-pretnar-2015-programming-with-algebraic-effects-and-handlers.txt` | good | Gemini entry 3 (handler execution, protocol-directed dispatch) |
| `castagna-2024-programming-with-union-intersection-negation-types.pdf` | Castagna, "Programming with Union, Intersection, and Negation Types", arXiv:2111.03354v4 (2024); published in *The French School of Programming*, Springer, 2023 ([Ca24]:52) | arXiv:2111.03354; downloaded from https://arxiv.org/pdf/2111.03354 | arXiv (author deposit) | 61 | `text/castagna-2024-programming-with-union-intersection-negation-types.txt` | good | `Ty`'s unions, `unknown`, `never`; `sub_not_complete` (Gemini entry 6, lemma census 107–108) |
| `leroy-2009-formal-verification-of-a-realistic-compiler.pdf` | Leroy, "Formal verification of a realistic compiler" (CompCert; venue not printed on the copy) | URL; downloaded from https://xavierleroy.org/publi/compcert-CACM.pdf | author-hosted copy | 9 | `text/leroy-2009-formal-verification-of-a-realistic-compiler.txt` | fair: two columns side by side | Gemini's `translation-simulation` (semantic preservation of lowering); system map §9's `HostSpec` (CompCert's external functions) |
| `ahmed-2004-semantics-of-types-for-mutable-state.pdf` | Ahmed, *Semantics of Types for Mutable State*, PhD thesis, Princeton University, November 2004 | URL; downloaded from https://www.ccs.neu.edu/home/amal/ahmedsthesis.pdf | author-hosted copy | 178 | `text/ahmed-2004-semantics-of-types-for-mutable-state.txt` | good | `Fits`, `World` (system map §9; DESIGN-BASIS DB-08); Gemini entry 1, lemma census 196 |
| `ahmed-dreyer-rossberg-2009-state-dependent-representation-independence.pdf` | Ahmed, Dreyer, Rossberg, "State-Dependent Representation Independence", POPL'09 | none printed; downloaded from https://www.ccs.neu.edu/home/amal/papers/sdri.pdf | author-hosted copy | 14 | `text/ahmed-dreyer-rossberg-2009-state-dependent-representation-independence.txt` | fair: two columns side by side | `Fits` and worlds (system map §9); Gemini entry 2 |
| `jung-et-al-2015-iris.pdf` | Jung, Swasey, Sieczkowski, Svendsen, Turon, Birkedal, Dreyer, "Iris: Monoids and Invariants as an Orthogonal Basis for Concurrent Reasoning", POPL '15 | 10.1145/2676726.2676980 ([Iris]:90); downloaded from https://iris-project.org/pdfs/2015-popl-iris1-final.pdf | project site (authors' copy) | 14 | `text/jung-et-al-2015-iris.txt` | fair: two columns side by side | world-indexed invariants by analogy (Gemini entry 4) |
| `meijer-fokkinga-paterson-1991-bananas-lenses.pdf` | Meijer, Fokkinga, Paterson, "Functional Programming with Bananas, Lenses, Envelopes and Barbed Wire" (FPCA 1991, LNCS 523, pp. 124–144, as cited by [Gi02]:2263-2265) | none printed; downloaded from https://maartenfokkinga.github.io/utwente/mmf91m.pdf | co-author Fokkinga's own page (the brief's lead, research.utwente.nl, answered 403) | 27 | `text/meijer-fokkinga-paterson-1991-bananas-lenses.txt` | good | `cataFam`, `cata_eff`, `hom_eq_cata_eff` (system map §9, "MFP 1991"); Gemini entry 24 |
| `rendel-ostermann-2010-invertible-syntax-descriptions.pdf` | Rendel, Ostermann, "Invertible Syntax Descriptions: Unifying Parsing and Pretty Printing", Haskell'10 ([RO10]:61) | none printed; downloaded from https://www.informatik.uni-marburg.de/~rendel/unparse/rendel10invertible.pdf | author-hosted copy | 12 | `text/rendel-ostermann-2010-invertible-syntax-descriptions.txt` | fair: two columns side by side | `printT`/`read`, `read_print` (system map §9); Gemini entry 32 |
| `lynch-vaandrager-1995-forward-and-backward-simulations.pdf` | Lynch, Vaandrager, "Forward and Backward Simulations I. Untimed Systems", Information and Computation 121, 214–233 (1995) | URL (CWI repository); downloaded from https://ir.cwi.nl/pub/1393/1393D.pdf | CWI institutional repository | 20 | `text/lynch-vaandrager-1995-forward-and-backward-simulations.txt` | poor: a scan with OCR errors ("C'OMPllTATION", "U ntimed"); read the PDF | the book's forward simulation, `bookMeans_obs` (system map §9); Gemini lemma census 241 |
| `de-vilhena-pottier-2021-separation-logic-for-effect-handlers.pdf` | de Vilhena, Pottier, "A Separation Logic for Effect Handlers", Proc. ACM Program. Lang. 5, POPL, Article 33 (January 2021) | 10.1145/3434314 ([dVP21]:25); downloaded from https://cambium.inria.fr/~fpottier/publis/de-vilhena-pottier-sleh.pdf | author-hosted copy | 28 | `text/de-vilhena-pottier-2021-separation-logic-for-effect-handlers.txt` | good | `TypedProg`, protocols (Gemini entry 8; system map §9 via the thesis) |
| `wadler-2012-propositions-as-sessions-icfp.pdf` | Wadler, "Propositions as Sessions", ICFP'12 | none printed; downloaded from https://homepages.inf.ed.ac.uk/wadler/papers/propositions-as-sessions/propositions-as-sessions.pdf | author-hosted copy | 13 | `text/wadler-2012-propositions-as-sessions-icfp.txt` | fair: two columns side by side | host session protocol (Gemini entry 35; domain-model-spec `host-session-protocol`) |
| `wadler-2014-propositions-as-sessions-jfp.pdf` | Wadler, "Propositions as sessions", JFP 24(2-3): 384–418, 2014 | 10.1017/S095679681400001X ([Wa14]:3); downloaded from https://homepages.inf.ed.ac.uk/wadler/papers/propositions-as-sessions/propositions-as-sessions-jfp.pdf | author-hosted copy | 35 | `text/wadler-2014-propositions-as-sessions-jfp.txt` | good | "Wadler 2014" in Gemini's note and lemma census |
| `mcbride-2008-clowns-to-the-left-of-me.pdf` | McBride, "Clowns to the Left of me, Jokers to the Right (Pearl): Dissecting Data Structures", POPL'08 | none printed; downloaded from https://personal.cis.strath.ac.uk/conor.mcbride/Dissect.pdf | author-hosted copy | 9 | `text/mcbride-2008-clowns-to-the-left-of-me.txt` | fair: two columns side by side | Gemini entry 23 (it says "ornamental structures"; the paper is about dissection; the system map's "McBride 2011" is a different work, not fetched) |
| `petricek-orchard-mycroft-2014-coeffects.pdf` | Petricek, Orchard, Mycroft, "Coeffects: A calculus of context-dependent computation", ICFP '14 | 10.1145/2628136.2628160 ([POM14]:63); downloaded from https://www.doc.ic.ac.uk/~dorchard/publ/coeffects-icfp14.pdf | co-author Orchard's page | 13 | `text/petricek-orchard-mycroft-2014-coeffects.txt` | fair: two columns side by side | requirement rows as a flat coeffect (system map §9 provision row; Gemini `context-requirements`) |
| `pickering-gibbons-wu-2017-profunctor-optics.pdf` | Pickering, Gibbons, Wu, "Profunctor Optics: Modular Data Accessors", The Art, Science, and Engineering of Programming 1(2), 2017, article 7 | 10.22152/programming-journal.org/2017/1/7 ([PGW17]:42); downloaded from https://arxiv.org/pdf/1703.10857 | arXiv; the journal is open access | 51 | `text/pickering-gibbons-wu-2017-profunctor-optics.txt` | good | `Canonical` as a lawful prism (system map §9); Gemini lemma census 213–214 |
| `gibbons-2002-calculating-functional-programs.pdf` | Gibbons, "Calculating Functional Programs", Chapter 5 of lecture notes on algebraic and coalgebraic methods (2002; volume not printed) | none printed; downloaded from https://www.cs.ox.ac.uk/people/jeremy.gibbons/publications/acmmpc-calcfp.pdf | author-hosted copy | 56 | `text/gibbons-2002-calculating-functional-programs.txt` | good | fold fusion and catamorphism uniqueness (Gemini entry 12) |

## Linked, already on this Mac (not copied)

Paths relative to `docs/research/` unless absolute. Text copies of these live beside them
(`2026-09-02-web-standards-sources/text/`, `2026-09-10-http-rest-formalisms/evidence/`,
`2026-09-05-effects-papers/text/`); their own `README.md`, `SOURCE-REGISTER.md`, `manifest.json`
and `SHA256SUMS` record how they were obtained, under what terms, and how well they parsed. The fold lab's other seven papers
(`~/Dev/foldlab/.reference/papers/*.pdf`: Gregory–Prest, Aeneas, Asperti et al., a lattice
hypothesis paper, a TPLP paper, AXLE, a compositional distributional semantics paper) are not
cited by Gemini and are not listed.

| Path | Work | Pages | sha256 (prefix) | Cited for (ours) |
| --- | --- | --- | --- | --- |
| `docs/research/2026-09-02-web-standards-sources/papers/02-interaction-trees.pdf` | Xia et al., "Interaction Trees", POPL 2020 (arXiv:1906.00046v2) | 35 | `943dc278978b9d85…` | `TypedProg`, `denoteR` (system map §9: Xia et al. §3.2, §7); Gemini entry 37 |
| `docs/research/2026-09-02-web-standards-sources/papers/05-handling-algebraic-effects.pdf` | Plotkin, Pretnar, "Handling Algebraic Effects", LMCS 9(4:23), 2013 | 36 | `d3835738a162c364…` | effect handlers (not cited by Gemini; the ESOP 2009 paper is a different work) |
| `docs/research/2026-09-02-web-standards-sources/papers/06-data-types-a-la-carte.pdf` | Swierstra, "Data Types à la Carte", JFP 18(4): 423–436, 2008 | 14 | `fdb9bdee98efbe21…` | signature coproducts (Gemini entry 34) |
| `docs/research/2026-09-02-web-standards-sources/papers/07-freer-monads-more-extensible-effects.pdf` | Kiselyov, Ishii, "Freer Monads, More Extensible Effects", Haskell 2015 | 12 | `e327cc2999680dee…` | free-monad programs without closures (Gemini entry 21) |
| `docs/research/2026-09-02-web-standards-sources/papers/08-koka-row-polymorphic-effect-types.pdf` | Leijen, "Koka: Programming with Row-Polymorphic Effect Types", MSFP 2014, EPTCS 153: 100–126 | 27 | `14b216f8441eb952…` | requirement rows (Gemini entry 22, lemma census 183) |
| `docs/research/2026-09-02-web-standards-sources/papers/16-defunctionalization-at-work.pdf` | Danvy, Nielsen, "Defunctionalization at Work", BRICS RS-01-23, June 2001 | 48 | `bdc7c8fff628d4e8…` | `RunMachine`, defunctionalized continuations (system map §9; Gemini domain-model-spec:114) |
| `docs/research/2026-09-02-web-standards-sources/papers/20-handlers-in-action.pdf` | Kammar, Lindley, Oury, "Handlers in Action", ICFP '13 | 14 | `a373e9f14e420acb…` | handler operational semantics (Gemini entry 20) |
| `docs/research/2026-09-02-web-standards-sources/papers/21-reasoning-about-effect-interaction-by-fusion.pdf` | "Reasoning about Effect Interaction by Fusion", ICFP 2021 copy (title and venue per the in-tree README) | 48 | `35efee1810b0ea4c…` | fusion; its reference list cites Gill, Launchbury, Peyton Jones 1993 (audit C20) |
| `docs/research/2026-09-10-http-rest-formalisms/sources/S05-tree-lenses.pdf` | Foster, Greenwald, Moore, Pierce, Schmitt, "Combinators for Bi-Directional Tree Transformations" (author version of TOPLAS 2007; this is the paper the brief asked about) | 93 | `1733a5e9e6dfedb3…` | the JSON codec and `Bridge.schema`/`ofSchema` as exact embeddings (system map §9); Gemini entry 11 |
| `docs/research/2026-09-10-http-rest-formalisms/sources/S06-profunctor-optics.pdf` | Clarke et al., "Profunctor Optics: a Categorical Update", Compositionality 6(1), 2024 (per the in-tree register) | 39 | `a1d66b669c73128a…` | optics background (not Pickering–Gibbons–Wu 2017) |
| `docs/research/2026-09-10-http-rest-formalisms/sources/S07-multiparty-sessions.pdf` | Honda, Yoshida, Carbone, "Multiparty Asynchronous Session Types", POPL 2008 (Imperial TR DTR07-5); not Honda–Vasconcelos–Kubo 1998 | 75 | `236f4f6742f42968…` | session types background |
| `docs/research/2026-09-10-http-rest-formalisms/sources/S09-concurrency-models.pdf` | Winskel, Nielsen, "Models for Concurrency", Handbook of Logic in Computer Science vol. 4, 1995 (DAIMI PB-429 draft) | 187 | `0e6f814f1621b109…` | transition systems; its reference list cites Milner 1989 and Manna–Pnueli 1991 (audit P25, C22) |
| `docs/research/2026-09-10-http-rest-formalisms/sources/S03-polynomial-interaction.pdf` | Niu, Spivak, *Polynomial Functors: A Mathematical Theory of Interaction* (2024 draft) | 375 | `7914f64eabdcadc0…` | interaction structures background |
| `docs/research/2026-09-10-http-rest-formalisms/sources/S04-seven-sketches.pdf` | Fong, Spivak, *Seven Sketches in Compositionality* (arXiv:1803.05316v3) | 353 | `f764f23020ee5ca4…` | background |
| `docs/research/2026-09-10-http-rest-formalisms/sources/S10b-rewriting-survey.pdf` | Meseguer, "Twenty Years of Rewriting Logic", JLAP 2012 (preprint) | 126 | `b6742a7b93e86b55…` | background |
| `docs/research/verification_with_effects.pdf` | de Vilhena, *Proof of Programs with Effect Handlers*, PhD thesis, Université Paris Cité, 2022 (HAL tel-03891381); text `2026-09-05-effects-papers/text/verification_with_effects.md` | 153 | `1f90dcc2e96741f6…` | `World`, `TypedProg` (system map §9: de Vilhena §4.3, Def. 2.2, 2.4–2.8); Gemini entry 9 |
| `docs/research/de-vilhena-thesis.pdf` | a second copy of a de Vilhena thesis PDF (different bytes from the one above; identity not re-checked here) | 152 | `b99b68f731d62e54…` | — |
| `docs/research/intro_coalgebar_mathematics_state.pdf` | Jacobs, *Introduction to Coalgebra. Towards Mathematics of States and Observations*, draft v2.00, 2012; text `2026-09-05-effects-papers/text/intro_coalgebar_mathematics_state.txt` | 190 | `c50b3a2b3bd20d34…` | `Beh`, `Obs` (Jacobs ch. 2), `World` (Prop. 6.2.4), iteration (Thm 5.3.4) (system map §9); Gemini entry 17 |
| `docs/research/from_partial_to_monadic_combinatory_algebra_effects.pdf` | Cohen, Grunfeld, Kirst, Miquey, "From Partial to Monadic: Combinatory Algebra with Effects"; text `2026-09-05-effects-papers/text/from_partial_to_monadic_combinatory_algebra_effects.md` | 29 | `e293e5cd3f9bf802…` | Gemini entry 7 |
| `docs/research/2026-09-11-protocol-projection-and-transport/sources/network-calculus.pdf` | *Network Calculus: A Theory of Deterministic Queuing Systems for the Internet*, Jean-Yves Le Boudec et al. (title page) | 265 | `4b822851782ca503…` | not cited by Gemini |
| `/Users/pooks/Dev/foldlab/.reference/papers/program_proofs.pdf` | Leino, *Program Proofs* (the fold lab's README names it) | 498 | `a14a98037799512e…` | not cited by Gemini |
| `/Users/pooks/Dev/jetstream-workflow-model/research/books/concrete-semantics.pdf` | Nipkow, Klein, *Concrete Semantics with Isabelle/HOL* (copy dated January 21, 2026) | 308 | `8c777db4673d7105…` | not cited by Gemini |

Full sha256 of the linked files (computed 2026-10-01 by seat A):

```
943dc278978b9d85f8957e9044ec2f571f315b43e98d58762dad3e08dca4934c  /Users/pooks/Dev/lean4-effect4/docs/research/2026-09-02-web-standards-sources/papers/02-interaction-trees.pdf
d3835738a162c364eb99f64304ef0a1b187f5af632a40acfd5648edf8e076f32  /Users/pooks/Dev/lean4-effect4/docs/research/2026-09-02-web-standards-sources/papers/05-handling-algebraic-effects.pdf
fdb9bdee98efbe21b7dab589a746b7f92edee91f6bd07f14cef2efa0022bd887  /Users/pooks/Dev/lean4-effect4/docs/research/2026-09-02-web-standards-sources/papers/06-data-types-a-la-carte.pdf
e327cc2999680dee37ee0626d89cbb19fcbc346b70cc768a7cd8608dbdce451e  /Users/pooks/Dev/lean4-effect4/docs/research/2026-09-02-web-standards-sources/papers/07-freer-monads-more-extensible-effects.pdf
14b216f8441eb952a9bcc5bf184de1c0a2448dbec22ee9aae407bf494e0b89bd  /Users/pooks/Dev/lean4-effect4/docs/research/2026-09-02-web-standards-sources/papers/08-koka-row-polymorphic-effect-types.pdf
bdc7c8fff628d4e8f5bff1d5d16054e3e71584075fb9e1d569e73159218728a8  /Users/pooks/Dev/lean4-effect4/docs/research/2026-09-02-web-standards-sources/papers/16-defunctionalization-at-work.pdf
a373e9f14e420acbb7a8fa22c0605858a99b51e2e0918eddda219090d9c8c40d  /Users/pooks/Dev/lean4-effect4/docs/research/2026-09-02-web-standards-sources/papers/20-handlers-in-action.pdf
35efee1810b0ea4c43771e42e3c3714574fb4f63b80c28eef66b5ac91b08436e  /Users/pooks/Dev/lean4-effect4/docs/research/2026-09-02-web-standards-sources/papers/21-reasoning-about-effect-interaction-by-fusion.pdf
1733a5e9e6dfedb391b7a4cb1d679ec231e72c47b1a96dc06a3d7693f0320a5b  /Users/pooks/Dev/lean4-effect4/docs/research/2026-09-10-http-rest-formalisms/sources/S05-tree-lenses.pdf
a1d66b669c73128a135b070f797a2651deb96bc31e3a6f0a714387e9abffe638  /Users/pooks/Dev/lean4-effect4/docs/research/2026-09-10-http-rest-formalisms/sources/S06-profunctor-optics.pdf
236f4f6742f42968b803dc876a38b60db3d509bb38d7aaa0d1642a1af9b023e2  /Users/pooks/Dev/lean4-effect4/docs/research/2026-09-10-http-rest-formalisms/sources/S07-multiparty-sessions.pdf
0e6f814f1621b1099b02169b46f54a14f76cea3b092fae13c72c79f6a927a28f  /Users/pooks/Dev/lean4-effect4/docs/research/2026-09-10-http-rest-formalisms/sources/S09-concurrency-models.pdf
7914f64eabdcadc054ffcc2784fc0c6fe3d96100e50abe82bd18c40e483b30f9  /Users/pooks/Dev/lean4-effect4/docs/research/2026-09-10-http-rest-formalisms/sources/S03-polynomial-interaction.pdf
f764f23020ee5ca45faa68b4e50257a7b5a69cb5e6baede696d2394baca33ce8  /Users/pooks/Dev/lean4-effect4/docs/research/2026-09-10-http-rest-formalisms/sources/S04-seven-sketches.pdf
b6742a7b93e86b557f7e1f754bc3c3305504cfcdf1c08b985559d1c407dda8c2  /Users/pooks/Dev/lean4-effect4/docs/research/2026-09-10-http-rest-formalisms/sources/S10b-rewriting-survey.pdf
1f90dcc2e96741f6d2c51981c319c69809aa2a4e8c20522c1cfe0d57d5cc022a  /Users/pooks/Dev/lean4-effect4/docs/research/verification_with_effects.pdf
b99b68f731d62e54597abaa88f7573a9ba711a76ae1cf5610e3e71b8600ee300  /Users/pooks/Dev/lean4-effect4/docs/research/de-vilhena-thesis.pdf
c50b3a2b3bd20d347ea471df5517689ed3e68a59a268d1d082d3d76b848e4852  /Users/pooks/Dev/lean4-effect4/docs/research/intro_coalgebar_mathematics_state.pdf
e293e5cd3f9bf80216b532f1f44cdc44dbdbe8fb153b52dde4fd43fc958b7a63  /Users/pooks/Dev/lean4-effect4/docs/research/from_partial_to_monadic_combinatory_algebra_effects.pdf
4b822851782ca5039a8b774f65f3a8809b48ed5e533d086cb82a6023405cd1ee  /Users/pooks/Dev/lean4-effect4/docs/research/2026-09-11-protocol-projection-and-transport/sources/network-calculus.pdf
a14a98037799512eb343bdfe8efa4ff2022b09b08446ba8205b5e995fcddf025  /Users/pooks/Dev/foldlab/.reference/papers/program_proofs.pdf
8c777db4673d7105a16dde2c5ebee2ef59fa50cf8ccc01269ed46a9f316f48c5  /Users/pooks/Dev/jetstream-workflow-model/research/books/concrete-semantics.pdf
```

## Not vendored (not free, or no legitimate free copy found)

| Work | Identifier (as printed in a vendored text, or as Gemini wrote it, unverified) | What the owner supplies |
| --- | --- | --- |
| Pierce, *Types and Programming Languages* (MIT Press, 2002), full text | ISBN not printed in the contents file | a copy, to check every theorem, lemma, definition, rule number and in-section page (audit rows T64–T116 marked unverifiable) |
| Pierce (ed.), *Advanced Topics in Types and Programming Languages* (MIT Press, 2005), full text | ISBN 0-262-16228-8 ([A]:36) | a copy, for ch. 3's and ch. 6's content claims (A19, A21, A25) and chapter end pages |
| Harper, *PFPL*, 2nd ed., Cambridge University Press printing | Gemini: DOI 10.1017/CBO9781316576892 (unverified) | the printed edition, if printed pages are to be cited instead of the author's abbreviated edition; bodies of chs. 39 and 41 |
| Milner, *Communication and Concurrency* (Prentice Hall, 1989) | as cited by [Jac]:35274 | a copy, if a chapter is to be cited |
| Sangiorgi, *Introduction to Bisimulation and Coinduction* (CUP) | Gemini: 2012, DOI 10.1017/CBO9780511777110 (unverified; the census says 2011) | a copy or the correct record |
| Jones, *Qualified Types* (CUP, 1994) | Gemini: DOI 10.1017/CBO9780511525902 (unverified) | a copy |
| Dolan, Mycroft, MLsub, POPL 2017 | Gemini: DOI 10.1145/3009837.3009882 (unverified); `cl.cam.ac.uk/~sd601/papers/` answered 403 | a copy |
| Honda, Vasconcelos, Kubo, ESOP 1998 | ESOP 1998, pp. 122–138 (as cited by [Wa14]:1925-1927); Gemini: DOI 10.1007/BFb0053567 | a copy |
| Hancock, Setzer, CSL 2000 | CSL 2000, pp. 317–331 (as cited by [ITree]:1605-1606) | a copy |
| Hinze, "Generic programming with adjunctions" | Gemini: LNCS 7470, 2012 (unverified; chapter-table.md:375 says 2013) | a copy or the correct record |
| Johann, Ghani, "Initial Algebra Semantics Is Enough!", TLCA 2007 | as cited by [DTalC]:553; the repository copy at `libres.uncg.edu` timed out twice | retry the lead, or a copy |
| Wright, Felleisen, "A syntactic approach to type soundness" | Information and Computation 115(1):38–94, November 1994 (as cited by [dV22]:3904) | a copy |
| Castagna, "Covariance and contravariance: conflict without a cause" (1995) | Gemini: SIGPLAN Notices 30(3), DOI 10.1145/202530.202538 (unverified) | a copy |
| Goguen, Thatcher, Wagner, Wright 1977 | JACM 24(1):68–95 (as cited by [Gi02]:2232-2234) | a copy, if cited beyond the name |
| Plotkin, "LCF considered as a programming language" | TCS 5(3):223–255, 1977 (as cited by [H]:9784-9785) | a copy |
| Milner, "A theory of type polymorphism in programming" | JCSS 17:348–375, 1978 (as cited by [H]:9709) | a copy, for the quoted phrase |
| Moggi, "Notions of computation and monads" | Information and Computation 93 (1991) 55–92 (as cited by [PP09]:651-652) | a copy |
| Katsumata, "Parametric effect monads and semantics of effect systems" | POPL 2014, pp. 633–646 (as cited by [POM14]:1396-1397) | a copy |
| Owicki, Gries 1976; Manna, Pnueli 1991; Wadler 1987 (Views); Gill, Launchbury, Peyton Jones 1993; Ahmed 2006 (ESOP); Petricek, Orchard, Mycroft 2013 (ICALP) | as cited (audit C20, C22, C38, C8) | copies if they are to be cited by section; the 2013 coeffects paper is free on the author's page (`tomasp.net/academic/papers/coeffects/`, `coeffects-icalp.pdf`) and was not fetched for time |
| Elgot 1975; Appel, McAllester 2001; "Birkhoff" | no vendored text cites them with a record | the records and copies |

## Regenerate and check

```
cd docs/research/2026-10-01-semantics/sources
sh fetch.sh                   # refetch the new downloads
shasum -a 256 -c SHA256SUMS   # check them (a site may have replaced a file: a mismatch is a review event)
for f in *.pdf; do pdftotext -layout "$f" "text/${f%.pdf}.txt"; done
tar xzf plf.tgz plf/LICENSE plf/Preface.v plf/Smallstep.v plf/Types.v plf/Stlc.v plf/StlcProp.v \
  plf/MoreStlc.v plf/References.v plf/Typechecking.v plf/Sub.v plf/Records.v plf/RecordSub.v \
  plf/Norm.v plf/Equiv.v plf/Imp.v plf/Hoare.v plf/Bib.v
```

`plf-current` moves with each release; the checksum pins Version 7.1 as fetched on 2026-10-01.
