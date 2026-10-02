# Citations audit of Gemini's four files (seat A, 2026-10-01)

Seat A, a bounded probe. Base: branch `refactor/phase1-phase3`, HEAD `198dd533` (no git command
run; the HEAD is the one the brief names). Audited files:
`gemini/note.md`, `gemini/domain-model-spec.md`, `gemini/chapter-table.md`,
`gemini/lemma-census.md` (paths below are relative to `docs/research/2026-10-01-semantics/`).
Sources are indexed in `sources/README.md`; every locator below is read off a file named there.

## The one thing to know

Gemini's ATTAPL chapter numbers are wrong where the semantics leans on them, and Codex was
right: in the publisher's own contents, ATTAPL **ch. 8 is "Design Considerations for ML-Style
Module Systems" by Robert Harper and Benjamin C. Pierce (p. 293)**, not logical relations and
not Dreyer–Crary–Harper; the logical-relations chapters are **ch. 6, Karl Crary, "Logical
Relations and a Case Study in Equivalence Checking" (p. 223)** and **ch. 7, Andrew Pitts,
"Typed Operational Reasoning" (p. 245; §7.6 "An Operationally Based Logical Relation", p. 266)**;
**ch. 3 is "Effect Types and Region-Based Memory Management" by Henglein, Makholm and Niss
(p. 87)**, and Walker's "Substructural Type Systems" is **ch. 1 (p. 3)**. So the chapter ids
`attapl-08-logical-relations` and every "ATTAPL ch. 8 / §8.4 / Thm 8.5.1" point into the
modules chapter. In TAPL, chapter numbers and titles hold (ch. 13 References p. 153, ch. 14
Exceptions p. 171, ch. 19 Case Study: Featherweight Java p. 247, ch. 20 Recursive Types p. 267;
**no "Generic Java" chapter exists**), but most of Gemini's page spans are off by a few pages,
and no theorem, lemma or rule number (e.g. "Thm 8.3.2, p. 96") can be checked without the full
text, which is not free: the owner must supply TAPL and ATTAPL for those rows. PFPL ch. 28 is
"Control Stacks" (p. 261, Part XII "Control Flow"); the concurrency part is chs. 39–41
(Process Calculus p. 373, Concurrent Algol p. 389, Distributed Algol p. 399), and Gemini cites
none of them for its `machine-concurrency` chapter.

## Sources used in this file (short names)

| Short | File (under `sources/`) | What it is |
| --- | --- | --- |
| [T] | `text/tapl-contents.txt` from `tapl-contents.pdf` | Pierce, *Types and Programming Languages*, MIT Press, contents pages v–xi, from the author's site. Lines cited as [T]:n. |
| [A] | `text/attapl-frontmatter.txt` from `attapl-frontmatter.pdf` | Pierce (ed.), *Advanced Topics in Types and Programming Languages*, MIT Press ©2005 ([A]:15), ISBN 0-262-16228-8 ([A]:36): title pages, contents v–viii, preface. |
| [H] | `text/pfpl-2nded-abbrev.txt` from `pfpl-2nded-abbrev.pdf` | Harper, *Practical Foundations for Programming Languages*, 2nd ed., the author's "abbreviated online edition, with corrections" (copyright 2016, [H]:12; terms at [H]:19-22); its contents print the page numbers of the whole book. Pages below are as that edition prints them; the Cambridge printing was not available to compare. |
| [P] | `plf/*.v` from `plf.tgz` | Pierce et al., *Software Foundations* vol. 2, *Programming Language Foundations*, Version 7.1, 2026 (`plf/Preface.v:160-166`). |

Status words: **verified** (read in the vendored text at the cited line and page);
**corrected** (Gemini's locator differs; the verified one is given); **unverifiable** (the
vendored text does not reach it; the missing source is named). A page span is "verified" when
its first page is the chapter's first page in the contents and its last page is the page before
the next chapter or part; a theorem, lemma, definition or rule number, or a page inside a
section, needs the book's body and is "unverifiable" here even when it falls inside the right
section (the section's span is given).

## 1. The flagged book claims (ATTAPL chs. 3, 6, 7, 8; TAPL chs. 13, 14, 19, 20; PFPL 28, 39–41)

### 1a. ATTAPL

Contents as printed ([A], PDF pp. 5–8, printed pp. v–viii): ch. 1 "Substructural Type
Systems", David Walker, p. 3 ([A]:55-56); ch. 2 "Dependent Types", Aspinall and Hofmann, p. 45
([A]:65-66); ch. 3 "Effect Types and Region-Based Memory Management", Fritz Henglein, Henning
Makholm and Henning Niss, p. 87 ([A]:82-83), sections 3.1 p. 87, 3.2 p. 90, 3.3 "Effects"
p. 102, 3.4 p. 106, 3.5 "The Tofte–Talpin Type System" p. 114, 3.6 p. 123, 3.7 p. 127,
3.8 p. 133 ([A]:85-93), Part II p. 137 ([A]:96); ch. 4 "Typed Assembly Language", Greg
Morrisett, p. 141 ([A]:97-98); ch. 5 "Proof-Carrying Code", George Necula, p. 177
([A]:109-110); ch. 6 "Logical Relations and a Case Study in Equivalence Checking", Karl Crary,
p. 223 ([A]:124-125), sections 6.6 "Logical Relations" p. 233, 6.7 "A Monotone Logical
Relation" p. 236, 6.9 "The Fundamental Theorem" p. 239, 6.10 Notes p. 243 ([A]:132-136);
ch. 7 "Typed Operational Reasoning", Andrew Pitts, p. 245 ([A]:138-139), 7.6 "An
Operationally Based Logical Relation" p. 266, 7.8 Notes p. 288 ([A]:146-148), Part IV p. 291
([A]:151); ch. 8 "Design Considerations for ML-Style Module Systems", Robert Harper and
Benjamin C. Pierce, p. 293 ([A]:152-153), 8.4 "Phase Distinction" p. 305, 8.5 "Abstract Type
Components" p. 307 ([A]:158-159); ch. 9 "Type Definitions", Christopher A. Stone, p. 347
([A]:170-171); Part V p. 387 ([A]:179); ch. 10 "The Essence of ML Type Inference", François
Pottier and Didier Rémy, p. 389 ([A]:180-181), 10.8 "Rows" p. 460 ([A]:190); Appendix A
p. 491 ([A]:193). No chapter is by Dreyer; no chapter title contains "Kripke" or "step".

| # | Where | As written | Verified locator | Status |
| --- | --- | --- | --- | --- |
| A1 | note.md:314 | "Chapter 3 (David Walker, Substructural Type Systems, pp. 3–44)" | Walker's "Substructural Type Systems" is ch. 1, pp. 3–44 (ch. 2 starts p. 45), [A]:55-56,65. Ch. 3 is Henglein, Makholm, Niss, "Effect Types and Region-Based Memory Management", p. 87, [A]:82-83. | corrected (chapter number; the span is ch. 1's) |
| A2 | note.md:314 | "Chapter 6 (Karl Crary, Logical Relations and Typed Assembly Language, pp. 205–244)" | ch. 6, Karl Crary, "Logical Relations and a Case Study in Equivalence Checking", pp. 223–244 (ch. 7 starts p. 245), [A]:124-125,138. Typed Assembly Language is ch. 4 (Morrisett, p. 141), [A]:97-98. | corrected (title, first page) |
| A3 | note.md:314 | "Chapter 7 (Andrew Pitts, Typed Operational Reasoning, pp. 245–289)" | ch. 7, Andrew Pitts, "Typed Operational Reasoning", p. 245, [A]:138-139; last section 7.8 starts p. 288 and Part IV starts p. 291, [A]:148,151. | verified (number, title, author, first page); the last page (289 or 290) needs the body |
| A4 | note.md:21 | "ATTAPL ch. 6 (Logical Relations, Crary, pp. 205–244)" | ch. 6, Crary, pp. 223–244, [A]:124-125,138 | corrected (first page 223) |
| A5 | note.md:66 | "`attapl-03-effect-rows` \| ATTAPL ch. 3 (§3.1–3.4, pp. 107–152)" | ch. 3 starts p. 87; §3.1–3.4 run pp. 87–113 (§3.5 p. 114); the chapter ends before Part II, p. 137, [A]:82-96 | corrected (pages) |
| A6 | note.md:67 | "`attapl-08-logical-relations` \| ATTAPL ch. 8 (§8.1–8.5, pp. 273–328)" | ch. 8 is Harper and Pierce, "Design Considerations for ML-Style Module Systems", p. 293, [A]:152-153. Logical relations: ch. 6 (Crary, p. 223) and ch. 7 §7.6 (Pitts, p. 266), [A]:124,146. | corrected (chapter) |
| A7 | note.md:353 | "accounted for across ATTAPL ch. 8 and TAPL ch. 8 & 13" | ATTAPL ch. 8 is the modules chapter, [A]:152-153; the logical-relations chapter meant is ch. 6, [A]:124 | corrected |
| A8 | domain-model-spec.md:40 | "ATTAPL ch. 6 Crary for logical relations" | ch. 6, Crary, p. 223, [A]:124-125 | verified |
| A9 | domain-model-spec.md:40 | "ch. 7 Pitts for operational reasoning" | ch. 7, Pitts, "Typed Operational Reasoning", p. 245, [A]:138-139 | verified |
| A10 | domain-model-spec.md:40 | "ch. 8 Dreyer–Crary–Harper for modules" | ch. 8 is by Robert Harper and Benjamin C. Pierce, p. 293, [A]:152-153 | corrected (authors) |
| A11 | domain-model-spec.md:40 | "All textbook citations are audited against official contents" | the spec's own ch. 6 span "pp. 205–244" (A13–A15) contradicts the contents, [A]:124,138 | corrected (the claim does not hold) |
| A12 | domain-model-spec.md:113 | "ATTAPL ch. 6 (Crary)" | ch. 6, Crary, p. 223, [A]:124-125 | verified |
| A13 | domain-model-spec.md:211 | `locator : String -- e.g. "ch. 6, pp. 205–244"` | ch. 6 is pp. 223–244, [A]:124,138 | corrected (example value) |
| A14 | domain-model-spec.md:427-429 | `"work": "ATTAPL"` … `"locator": "ch. 6 (Crary), pp. 205–244"` | pp. 223–244, [A]:124,138 | corrected |
| A15 | domain-model-spec.md:505 | "ATTAPL ch. 6 (Crary, pp. 205–244)" | pp. 223–244, [A]:124,138 | corrected |
| A16 | chapter-table.md:25 | "`attapl-03-effects` \| ATTAPL ch. 3, pp. 87–130" | ch. 3, Henglein, Makholm, Niss, starts p. 87; §3.8 starts p. 133 and Part II p. 137, so the chapter does not end at p. 130, [A]:82-96 | corrected (last page; it lies between 133 and 136) |
| A17 | chapter-table.md:26 | "`attapl-08-logical-relations` \| ATTAPL ch. 8, pp. 343–388" | ch. 8 is modules, p. 293; pp. 347–386 are ch. 9 (Stone, "Type Definitions"), [A]:152,170-171,179. Logical relations: ch. 6, p. 223. | corrected (chapter and pages) |
| A18 | chapter-table.md:302 | "ATTAPL Chapter 3: Effect Systems and Subeffecting (§3.1–§3.5, pp. 87–130)" | title is "Effect Types and Region-Based Memory Management"; §3.1–§3.5 run pp. 87–122 (§3.6 p. 123), [A]:82-90 | corrected (title, pages) |
| A19 | chapter-table.md:319 | "ATTAPL Chapter 3 studies effect systems tracking computational side-effects (read, write, alloc) with subeffecting." | ch. 3 has §3.3 "Effects", p. 102 ([A]:87); the preface says its types list "effects" such as mutations to the store and input/output ([A]:257-263). "Subeffecting" and "read, write, alloc" need the chapter body. | unverifiable (content; needs ATTAPL's body) |
| A20 | chapter-table.md:326 | "ATTAPL Chapter 8: Logical Relations and Kripke Models (Ahmed; Ahmed, Dreyer, Rossberg 2009; Birkedal et al. Iris)" | no chapter of that title; ch. 8 is modules, [A]:152-153; logical relations are ch. 6 and ch. 7 §7.6, [A]:124,146 | corrected |
| A21 | chapter-table.md:346 | "ATTAPL Chapter 8 uses step-indexed Kripke logical relations with an arrow clause" | ch. 8 is modules, [A]:152-153; ch. 6's sections name "Logical Relations" (6.6) and "A Monotone Logical Relation" (6.7), [A]:132-133; whether any chapter is step-indexed needs the body | corrected (chapter); the content is unverifiable |
| A22 | lemma-census.md:179 | "(ATTAPL ch. 3, pp. 87–130)" | as A16: starts p. 87, ends after p. 133, [A]:82-96 | corrected (last page) |
| A23 | lemma-census.md:192 | "(ATTAPL ch. 8, pp. 343–388)" | as A17 | corrected |
| A24 | lemma-census.md:196 | "Ahmed 2004; ATTAPL §8.4" | ATTAPL §8.4 is "Phase Distinction", p. 305, in the modules chapter, [A]:158. Ahmed 2004: see §2, row L1. | corrected (ATTAPL part) |
| A25 | lemma-census.md:202 | "ATTAPL Thm 8.5.1" | §8.5 is "Abstract Type Components", p. 307, [A]:159; the fundamental theorem of ch. 6 is §6.9 "The Fundamental Theorem", p. 239, [A]:135; theorem numbers need the body | corrected (section); the number is unverifiable |
| A26 | note.md:319 | "Pottier, François, and Didier Rémy. "The essence of ML." In *Advanced Topics …*, pp. 389–489, MIT Press, 2005." | ch. 10, "The Essence of ML Type Inference", p. 389; Appendix A starts p. 491; ©2005, [A]:15,180-181,193 | corrected (title); pages 389–489 consistent, last page needs the body |
| A27 | chapter-table.md:262 | "Pottier and Rémy (2005)" | ATTAPL ch. 10, p. 389, ©2005, [A]:15,180-181 | verified |
| A28 | lemma-census.md:159 | "Pottier & Rémy 2005" | as A27 | verified |
| A29 | note.md:313 (entry 27) | "Pierce, Benjamin C. (ed.). *Advanced Topics in Types and Programming Languages.* MIT Press, Cambridge, MA, 2005." | title page and imprint: "Benjamin C. Pierce, editor", The MIT Press, Cambridge, Massachusetts, ©2005, [A]:1-15 | verified |

### 1b. TAPL

Contents as printed ([T], PDF pp. 2–8, printed pp. v–xi). The chapters Gemini names, with
first pages and the next chapter's first page: ch. 3 "Untyped Arithmetic Expressions" p. 23,
next p. 45 ([T]:36,47); ch. 8 "Typed Arithmetic Expressions" p. 91, next p. 99 ([T]:71,76);
ch. 9 "Simply Typed Lambda-Calculus" p. 99, next p. 113 ([T]:76,85); ch. 11 "Simple
Extensions" p. 117, next p. 149 ([T]:92,106); ch. 13 "References" p. 153, next p. 171
([T]:110,118); ch. 14 "Exceptions" p. 171, Part III p. 179 ([T]:118,124); ch. 15 "Subtyping"
p. 181, next p. 209 ([T]:125,138); ch. 16 "Metatheory of Subtyping" p. 209, next p. 221
([T]:138,144); ch. 19 "Case Study: Featherweight Java" p. 247, Part IV p. 265 ([T]:165,176);
ch. 20 "Recursive Types" p. 267, next p. 281 ([T]:177,183); ch. 22 "Type Reconstruction"
p. 317, next p. 339 ([T]:199,209); ch. 23 "Universal Types" p. 339, next p. 363
([T]:209,226). A search of [T] for "Generic" finds nothing; "Java" occurs only in ch. 19's
title ([T]:165); "Nominal" only in §19.3 "Nominal and Structural Type Systems", p. 251
([T]:168); "variance" nowhere.

Spans used below (first page; the page before the next chapter or part): ch. 3 pp. 23–44
(§3.1 "Introduction" 23, §3.2 "Syntax" 26, §3.3 "Induction on Terms" 29, §3.4 "Semantic
Styles" 32, §3.5 "Evaluation" 34, §3.6 Notes 43; [T]:36-42); ch. 8 pp. 91–98 (§8.1 91, §8.2
"The Typing Relation" 92, §8.3 "Safety = Progress + Preservation" 95; [T]:71-74); ch. 9
pp. 99–112 (§9.3 "Properties of Typing" 104, §9.4 108, §9.5 "Erasure and Typability" 109;
[T]:76-83); ch. 11 pp. 117–148 (§11.1 "Base Types" 117, §11.2 "The Unit Type" 118, §11.3
"Derived Forms: Sequencing and Wildcards" 119, §11.4 "Ascription" 121, §11.5 "Let Bindings"
124, §11.6 "Pairs" 126, §11.7 "Tuples" 128, §11.8 "Records" 129, §11.9 "Sums" 132, §11.10
"Variants" 136, §11.11 "General Recursion" 142, §11.12 "Lists" 146; [T]:92-104); ch. 13
pp. 153–170 (§13.4 "Store Typings" 162, §13.5 "Safety" 165, §13.6 Notes 170; [T]:110-116);
ch. 14 pp. 171–178 (§14.1 "Raising Exceptions" 172, §14.2 "Handling Exceptions" 173, §14.3
175; [T]:118-121); ch. 15 pp. 181–208 (§15.1 "Subsumption" 181, §15.2 "The Subtype Relation"
182, §15.3 "Properties of Subtyping and Typing" 188, §15.4 "The Top and Bottom Types" 191,
§15.5 "Subtyping and Other Features" 193; [T]:125-133); ch. 16 pp. 209–220 (§16.1
"Algorithmic Subtyping" 210, §16.2 "Algorithmic Typing" 213, §16.3 "Joins and Meets" 218,
§16.4 220; ch. 17 starts 221, §17.3 "Typing" 222; [T]:138-147); ch. 19 pp. 247–264 (§19.3
"Nominal and Structural Type Systems" 251, §19.4 "Definitions" 254, §19.5 "Properties" 261;
[T]:165-172); ch. 20 pp. 267–280 (§20.1 "Examples" 268, §20.2 "Formalities" 275, §20.3
"Subtyping" 279; [T]:177-181); ch. 22 pp. 317–338 (§22.4 "Unification" 326, §22.5 329;
[T]:199-204); ch. 23 pp. 339–362 (§23.3 "System F" 341, §23.4 "Examples" 344, §23.5 353,
§23.6 354, §23.7 357, §23.10 "Impredicativity" 360; [T]:209-223).

| # | Where | As written | Verified locator | Status |
| --- | --- | --- | --- | --- |
| T1 | note.md:23 | "TAPL ch. 8 (§8.3) & ch. 13 (§13.5)" | §8.3 "Safety = Progress + Preservation", p. 95, [T]:74; §13.5 "Safety", p. 165, [T]:115 | verified |
| T2 | note.md:25 | "TAPL ch. 13 (§13.5)" | §13.5 "Safety", p. 165, [T]:115 | verified |
| T3 | note.md:54 | "TAPL ch. 3 (§3.1–3.5, pp. 31–46)" | ch. 3 "Untyped Arithmetic Expressions", pp. 23–44; §3.1–3.5 run pp. 23–42, [T]:36-47 | corrected |
| T4 | note.md:55 | "TAPL ch. 8 (§8.1–8.3, pp. 91–98)" | pp. 91–98, [T]:71-76 | verified |
| T5 | note.md:56 | "TAPL ch. 9 (§9.1–9.4, pp. 99–110)" | §9.1–9.4 run pp. 99–108 (§9.5 p. 109); the chapter runs pp. 99–112, [T]:76-85 | corrected |
| T6 | note.md:57 | "TAPL ch. 11 (§11.1–11.12, pp. 117–152)" | pp. 117–148 (ch. 12 starts p. 149), [T]:92-106 | corrected |
| T7 | note.md:58 | "TAPL ch. 13 (§13.1–13.5, pp. 153–178)" | §13.1–13.5 run pp. 153–169; the chapter runs pp. 153–170, [T]:110-118 | corrected |
| T8 | note.md:59 | "TAPL ch. 14 (§14.1–14.3, pp. 179–186)" | pp. 171–178 (Part III starts p. 179), [T]:118-124 | corrected |
| T9 | note.md:60 | "TAPL ch. 15 (§15.1–15.4, pp. 187–208)" | §15.1–15.4 run pp. 181–192; the chapter runs pp. 181–208, [T]:125-138 | corrected |
| T10 | note.md:61 | "`tapl-16-metric-subtyping` \| TAPL ch. 16 (§16.1–16.3, pp. 209–224)" | ch. 16 "Metatheory of Subtyping", pp. 209–220; §16.1–16.3 run pp. 210–219, [T]:138-144 | corrected |
| T11 | note.md:62 | "`tapl-19-nominal-types` \| TAPL ch. 19 (§19.1–19.4, pp. 251–264)" | ch. 19 "Case Study: Featherweight Java", p. 247; §19.1–19.4 run pp. 247–260, [T]:165-170 | corrected |
| T12 | note.md:63 | "`tapl-20-variances` \| TAPL ch. 20 (§20.1–20.3, pp. 265–274)" | ch. 20 is "Recursive Types", pp. 267–280; §20.1–20.3 run pp. 268–279; no section names variance, [T]:177-183 | corrected (chapter subject and pages) |
| T13 | note.md:64 | "TAPL ch. 22 (§22.1–22.8, pp. 317–338)" | pp. 317–338, [T]:199-209 | verified |
| T14 | note.md:65 | "TAPL ch. 23 (§23.1–23.6, pp. 339–362)" | pp. 339–362 is the whole chapter; §23.1–23.6 run pp. 339–356, [T]:209-220 | corrected (section range) |
| T15 | note.md:141 | `"locator": "ch. 13, pp. 153–170"` | pp. 153–170, [T]:110,118 | verified |
| T16 | note.md:311 | "Pierce, Benjamin C. *Types and Programming Languages.* MIT Press, Cambridge, MA, 2002." | title, author and imprint, [T]:1-12; the year from ATTAPL's preface, "Pierce [2002]—henceforth TAPL", [A]:207-208 | verified |
| T17 | note.md:312 | "Chapters 3, 8, 9, 11 … Subtyping ch. 15–16 … Type Reconstruction ch. 22" | ch. 15 "Subtyping", ch. 16 "Metatheory of Subtyping", ch. 22 "Type Reconstruction", [T]:125,138,199 | verified |
| T18 | note.md:312 | "References ch. 13, pp. 153–170" | [T]:110,118 | verified |
| T19 | note.md:312 | "Exceptions ch. 14, pp. 171–180" | pp. 171–178, [T]:118,124 | corrected |
| T20 | note.md:312 | "Featherweight Java ch. 19, pp. 251–266" | pp. 247–264 (Part IV p. 265), [T]:165,176 | corrected |
| T21 | note.md:312 | "Generic Java ch. 20, pp. 267–274" | ch. 20 is "Recursive Types", pp. 267–280; no chapter or section mentions Generic Java, [T]:165,177,183 | corrected |
| T22 | domain-model-spec.md:112 | "TAPL ch. 13 (pp. 153–170)" | [T]:110,118 | verified |
| T23 | domain-model-spec.md:117 | "TAPL ch. 15–16" | [T]:125,138 | verified |
| T24 | chapter-table.md:13 | "`tapl-03-evaluation` \| TAPL ch. 3, pp. 31–43" | pp. 23–44, [T]:36,47 | corrected |
| T25 | chapter-table.md:14 | "TAPL ch. 8, pp. 91–98" | [T]:71,76 | verified |
| T26 | chapter-table.md:15 | "TAPL ch. 9, pp. 99–112" | [T]:76,85 | verified |
| T27 | chapter-table.md:16 | "TAPL ch. 11, pp. 117–152" | pp. 117–148, [T]:92,106 | corrected |
| T28 | chapter-table.md:17 | "TAPL ch. 13, pp. 153–178" | pp. 153–170, [T]:110,118 | corrected |
| T29 | chapter-table.md:18 | "TAPL ch. 14, pp. 179–186" | pp. 171–178, [T]:118,124 | corrected |
| T30 | chapter-table.md:19 | "TAPL ch. 15, pp. 187–208" | pp. 181–208, [T]:125,138 | corrected |
| T31 | chapter-table.md:20 | "TAPL ch. 16, pp. 209–224" | pp. 209–220, [T]:138,144 | corrected |
| T32 | chapter-table.md:21 | "`tapl-19-nominal` \| TAPL ch. 19, pp. 245–259" | ch. 19 "Case Study: Featherweight Java", pp. 247–264; §19.3 "Nominal and Structural Type Systems", p. 251, [T]:165,168,176 | corrected |
| T33 | chapter-table.md:22 | "`tapl-20-recursive` \| TAPL ch. 20, pp. 261–280" | ch. 20 "Recursive Types", pp. 267–280 (Part IV's title page is p. 265), [T]:176-183 | corrected (first page) |
| T34 | chapter-table.md:23 | "TAPL ch. 22, pp. 317–338" | [T]:199,209 | verified |
| T35 | chapter-table.md:24 | "`tapl-23-prenex` \| TAPL ch. 23, pp. 339–358" | ch. 23 "Universal Types", pp. 339–362 (p. 358 is §23.8 "Fragments of System F"), [T]:209,221,226 | corrected |
| T36 | chapter-table.md:36 | "TAPL Chapter 3: Untyped Arithmetic Expressions (§3.1 Syntax, §3.2 Induction, §3.5 Evaluation, pp. 31–43)" | §3.1 is "Introduction" (23), "Syntax" is §3.2 (26), "Induction on Terms" §3.3 (29), §3.5 "Evaluation" (34); pp. 23–44, [T]:36-42 | corrected (section numbers, pages) |
| T37 | chapter-table.md:55 | "TAPL Chapter 3 formalizes evaluation via small-step inductive rewriting relations" | ch. 3, §3.5 "Evaluation", p. 34, [T]:41 | unverifiable (content; needs TAPL's body) |
| T38 | chapter-table.md:60 | "TAPL Chapter 8: Typed Arithmetic Expressions (§8.1–§8.3, pp. 91–98)" | [T]:71-76 | verified |
| T39 | chapter-table.md:79 | "In TAPL Chapter 8, Type Safety is stated on closed terms as Progress … and Preservation" | §8.3 "Safety = Progress + Preservation", p. 95, [T]:74 | verified (section); the statements' form is unverifiable |
| T40 | chapter-table.md:84 | "TAPL Chapter 9: Simply Typed Lambda-Calculus (§9.1–§9.4, pp. 99–112)" | chapter pp. 99–112; §9.1–9.4 alone end p. 108, [T]:76-85 | verified (chapter span) |
| T41 | chapter-table.md:102 | "TAPL Chapter 9 centers on arrow types …, and the substitution lemma" | §9.1 "Function Types", p. 99; §9.3 "Properties of Typing", p. 104, [T]:77,79 | unverifiable (content) |
| T42 | chapter-table.md:107 | "TAPL Chapter 11: Simple Extensions (§11.1 Base types, §11.2 Sequencing, §11.5 Pairs/Tuples, §11.6 Records, §11.7 Sums/Variants, §11.11 General Recursion, §11.12 Lists, pp. 117–152)" | §11.2 is "The Unit Type"; sequencing §11.3 (119); §11.5 "Let Bindings"; pairs §11.6 (126), tuples §11.7 (128), records §11.8 (129), sums §11.9 (132), variants §11.10 (136); §11.1, §11.11, §11.12 as written; pp. 117–148, [T]:92-106 | corrected (four section numbers, pages) |
| T43 | chapter-table.md:124 | "TAPL Chapter 11 uses general non-terminating recursion via fix or letrec" | §11.11 "General Recursion", p. 142, [T]:103 | verified (section); content unverifiable |
| T44 | chapter-table.md:129 | "TAPL Chapter 13: References (§13.1–§13.5, pp. 153–178)" | §13.1–13.5 run pp. 153–169; chapter pp. 153–170, [T]:110-118 | corrected |
| T45 | chapter-table.md:151 | "TAPL Chapter 13 defines locations … store typings Σ … including closures (which requires cyclic/step-indexed store typings)" | §13.4 "Store Typings", p. 162, [T]:114 | unverifiable (content) |
| T46 | chapter-table.md:156 | "TAPL Chapter 14: Exceptions (§14.1–§14.3, pp. 179–186)" | pp. 171–178, [T]:118-124 | corrected |
| T47 | chapter-table.md:172 | "TAPL Chapter 14 models simple exceptions (`error` or `raise t`)" | §14.1 "Raising Exceptions", p. 172, [T]:119 | unverifiable (content) |
| T48 | chapter-table.md:177 | "TAPL Chapter 15: Subtyping (§15.1 Subsumption, §15.2 Subtyping rules, §15.3 Top and Bottom, §15.4 Structural Subtyping, pp. 187–208)" | §15.1 "Subsumption" 181; §15.2 "The Subtype Relation" 182; §15.3 "Properties of Subtyping and Typing" 188; §15.4 "The Top and Bottom Types" 191; no section is called structural subtyping; pp. 181–208, [T]:125-138 | corrected |
| T49 | chapter-table.md:195 | "TAPL Chapter 15 includes the standard subsumption rule in the declarative judgment" | §15.1 "Subsumption", p. 181, [T]:126 | verified (section); the rule's form is unverifiable |
| T50 | chapter-table.md:200 | "TAPL Chapter 16: Metatheory of Subtyping (§16.1 Algorithmic Subtyping, §16.2 Completeness and Decidability, §16.3 Joins and Meets, pp. 209–224)" | §16.2 is "Algorithmic Typing" (213); pp. 209–220, [T]:138-144 | corrected |
| T51 | chapter-table.md:218 | "TAPL Chapter 16 develops algorithmic subtyping deductively …" | §16.1 "Algorithmic Subtyping", p. 210, [T]:139 | unverifiable (content) |
| T52 | chapter-table.md:223 | "TAPL Chapter 19: Case Study: Featherweight Java / Nominal Types (§19.1–§19.4, pp. 245–259)" | title is "Case Study: Featherweight Java"; §19.1–19.4 run pp. 247–260; chapter pp. 247–264, [T]:165-176 | corrected |
| T53 | chapter-table.md:239 | "TAPL Chapter 19 formalizes object-oriented classes with method suites and nominal subtyping hierarchies" | §19.3 "Nominal and Structural Type Systems", p. 251, [T]:168 | unverifiable (content) |
| T54 | chapter-table.md:244 | "TAPL Chapter 20: Recursive Types (§20.1 Examples, §20.2 Formalities, pp. 261–280)" | titles as written; pp. 267–280, [T]:177-183 | corrected (first page) |
| T55 | chapter-table.md:257 | "TAPL Chapter 20 treats recursive types via equi-recursive or iso-recursive μX.T terms" | ch. 20, p. 267; ch. 21 has §21.8 "µ-Types" (299) and §21.11 "Subtyping Iso-Recursive Types" (311), [T]:177,191,194 | unverifiable (content) |
| T56 | chapter-table.md:262 | "TAPL Chapter 22: Type Reconstruction (§22.1–§22.8, pp. 317–338)" | [T]:199-209 | verified |
| T57 | chapter-table.md:278 | "TAPL Chapter 22 presents algorithm W / Hindley-Milner unification" | §22.4 "Unification" 326, §22.7 "Let-Polymorphism" 331, [T]:203,206 | unverifiable ("algorithm W" needs the body) |
| T58 | chapter-table.md:283 | "TAPL Chapter 23: Universal Polymorphism (§23.1–§23.4 System F, pp. 339–358)" | title "Universal Types"; System F is §23.3 (341); §23.1–23.4 run pp. 339–352; chapter pp. 339–362, [T]:209-215,226 | corrected |
| T59 | chapter-table.md:297 | "TAPL Chapter 23 defines System F … impredicative universal types" | §23.3 "System F" 341, §23.10 "Impredicativity" 360, [T]:212,223 | verified (sections) |
| T60 | chapter-table.md:370 | "Standard TAPL does not formalize external syntax generation or serialization boundaries." | no chapter or section title in [T] names them, [T]:18-302 | unverifiable (an absence over the body) |
| T61 | chapter-table.md:392 | "In TAPL, inductive types are presented informal-syntactically …" | — | unverifiable (content) |
| T62 | chapter-table.md:418 | "Standard TAPL has no concurrency chapter" | no chapter or section title in [T] contains "concurren" or "process", [T]:18-302 | verified (contents only) |
| T63 | lemma-census.md:14 | "(TAPL ch. 3, pp. 31–43)" | pp. 23–44, [T]:36,47 | corrected |
| T64 | lemma-census.md:18 | "TAPL Thm 3.5.4, p. 38" | p. 38 lies in §3.5 "Evaluation" (pp. 34–42), [T]:41-42 | unverifiable (number; needs TAPL's body) |
| T65 | lemma-census.md:19 | "TAPL Thm 3.5.12, p. 41" | inside §3.5 (pp. 34–42) | unverifiable |
| T66 | lemma-census.md:22 | "TAPL §3.5 Definition 3.5.1" | §3.5 "Evaluation", p. 34, [T]:41 | verified (section); the definition number is unverifiable |
| T67 | lemma-census.md:27 | "(TAPL ch. 8, pp. 91–98)" | [T]:71,76 | verified |
| T68 | lemma-census.md:31 | "TAPL Lemma 8.2.2, p. 93" | inside §8.2 (pp. 92–94), [T]:73-74 | unverifiable |
| T69 | lemma-census.md:32 | "TAPL Lemma 8.3.1, p. 95" | p. 95 is §8.3's first page, [T]:74 | unverifiable |
| T70 | lemma-census.md:33 | "TAPL Thm 8.3.2, p. 96" | inside §8.3 (pp. 95–98) | unverifiable |
| T71 | lemma-census.md:35 | "TAPL Thm 8.3.3, p. 96" | inside §8.3 (pp. 95–98) | unverifiable |
| T72 | lemma-census.md:42 | "(TAPL ch. 9, pp. 99–112)" | [T]:76,85 | verified |
| T73 | lemma-census.md:46 | "TAPL Lemma 9.3.1, p. 104" | p. 104 is §9.3's first page, [T]:79 | unverifiable |
| T74 | lemma-census.md:47 | "TAPL Thm 9.3.3, p. 105" | inside §9.3 (pp. 104–107) | unverifiable |
| T75 | lemma-census.md:48 | "TAPL Lemma 9.3.6, p. 106" | inside §9.3 | unverifiable |
| T76 | lemma-census.md:49 | "TAPL Lemma 9.3.8, p. 106" | inside §9.3 | unverifiable |
| T77 | lemma-census.md:50 | "Soundness of Algorithmic Typechecker \| TAPL §16.1" | §16.1 is "Algorithmic Subtyping" (210); "Algorithmic Typing" is §16.2 (213), [T]:139-140 | corrected |
| T78 | lemma-census.md:51 | "Completeness of Algorithmic Typechecker \| TAPL §16.1" | as T77 | corrected |
| T79 | lemma-census.md:52 | "Decidability of Typing \| TAPL p. 110" | p. 110 lies in §9.5 "Erasure and Typability" (pp. 109–110), [T]:81-82 | unverifiable |
| T80 | lemma-census.md:57 | "(TAPL ch. 11, pp. 117–152)" | pp. 117–148, [T]:92,106 | corrected |
| T81 | lemma-census.md:61 | "TAPL §11.5–§11.11" | §11.5 "Let Bindings" (124) to §11.11 "General Recursion" (142), [T]:97-103 | verified (sections exist) |
| T82 | lemma-census.md:62 | "Subtyping Covariance for Products \| TAPL §15.2, p. 191" | §15.2 runs pp. 182–187; p. 191 is the first page of §15.4 "The Top and Bottom Types", [T]:127-129 | corrected (page and section disagree) |
| T83 | lemma-census.md:63 | "TAPL §11.11; Elgot 1975" | §11.11 "General Recursion", p. 142, [T]:103; Elgot 1975: §2 row E1 | verified (TAPL part) |
| T84 | lemma-census.md:64 | "Canonical Record Projection \| TAPL §11.6" | §11.6 is "Pairs" (126); "Records" is §11.8 (129), [T]:98,100 | corrected |
| T85 | lemma-census.md:66 | "General Non-Terminating Letrec \| TAPL §11.11" | [T]:103 | verified |
| T86 | lemma-census.md:71 | "(TAPL ch. 13, pp. 153–178)" | pp. 153–170, [T]:110,118 | corrected |
| T87 | lemma-census.md:75 | "TAPL Definition 13.5.1, p. 165" | p. 165 is §13.5's first page, [T]:115; T88 gives "Lemma 13.5.1" at the same page, so one of the two is wrong | unverifiable |
| T88 | lemma-census.md:76 | "TAPL Lemma 13.5.1, p. 165" | as T87 | unverifiable |
| T89 | lemma-census.md:78 | "TAPL Lemma 13.5.3, p. 166" | inside §13.5 (pp. 165–169); T90 gives "Thm 13.5.3" at the same page | unverifiable |
| T90 | lemma-census.md:80 | "TAPL Thm 13.5.3, p. 166" | as T89 | unverifiable |
| T91 | lemma-census.md:82 | "Cyclic / Higher-Order Store Typings \| TAPL §13.5, p. 164" | §13.5 starts p. 165; p. 164 lies in §13.4 "Store Typings" (pp. 162–164), [T]:114-115 | corrected |
| T92 | lemma-census.md:87 | "(TAPL ch. 14, pp. 179–186)" | pp. 171–178, [T]:118,124 | corrected |
| T93 | lemma-census.md:91 | "TAPL §14.2" | §14.2 "Handling Exceptions", p. 173, [T]:120 | verified |
| T94 | lemma-census.md:100 | "(TAPL ch. 15, pp. 187–208)" | pp. 181–208, [T]:125,138 | corrected |
| T95 | lemma-census.md:104 | "TAPL Rule S-REFL, p. 189" | p. 189 lies in §15.3 (pp. 188–190), [T]:128 | unverifiable (rule names need the body) |
| T96 | lemma-census.md:105 | "TAPL Rules S-TOP, S-BOTTOM, p. 189" | p. 189 lies in §15.3; §15.4 "The Top and Bottom Types" starts p. 191, [T]:128-129 | unverifiable |
| T97 | lemma-census.md:106 | "TAPL Rule S-JOIN" | — | unverifiable |
| T98 | lemma-census.md:109 | "TAPL Rule T-SUB, p. 189" | inside §15.3 | unverifiable |
| T99 | lemma-census.md:110 | "TAPL Rule S-RCDWIDTH, p. 189" | inside §15.3 | unverifiable |
| T100 | lemma-census.md:115 | "(TAPL ch. 16, pp. 209–224)" | pp. 209–220, [T]:138,144 | corrected |
| T101 | lemma-census.md:119 | "TAPL Thm 16.1.3, p. 212" | inside §16.1 (pp. 210–212), [T]:139 | unverifiable |
| T102 | lemma-census.md:120 | "TAPL §16.3; Birkhoff" | §16.3 "Joins and Meets", p. 218, [T]:141; "Birkhoff" names no work: §2 row E1 | verified (TAPL part) |
| T103 | lemma-census.md:122 | "TAPL §16.3, p. 222" | §16.3 runs pp. 218–219; p. 222 is §17.3 "Typing" in ch. 17, [T]:141-147 | corrected |
| T104 | lemma-census.md:123 | "TAPL Thm 16.1.6, p. 215" | p. 215 lies in §16.2 (pp. 213–217), while §16.1 runs pp. 210–212, so number and page cannot both hold, [T]:139-140 | corrected (which one needs the body) |
| T105 | lemma-census.md:124 | "TAPL §16.3, p. 222" | as T103 | corrected |
| T106 | lemma-census.md:129 | "(TAPL ch. 19, pp. 245–259)" | pp. 247–264, [T]:165,176 | corrected |
| T107 | lemma-census.md:133 | "TAPL §19.3" | §19.3 "Nominal and Structural Type Systems", p. 251, [T]:168 | verified |
| T108 | lemma-census.md:137 | "TAPL Thm 19.5.1, p. 256" | §19.5 "Properties" starts p. 261; p. 256 lies in §19.4 "Definitions" (pp. 254–260), [T]:169-170 | corrected |
| T109 | lemma-census.md:142 | "(TAPL ch. 20, pp. 261–280)" | pp. 267–280, [T]:177,183 | corrected |
| T110 | lemma-census.md:149 | "TAPL §20.2–§21.2" | §20.2 "Formalities" (275) to §21.2 "Finite and Infinite Types" (284), [T]:179,185 | verified (sections exist) |
| T111 | lemma-census.md:154 | "(TAPL ch. 22, pp. 317–338)" | [T]:199,209 | verified |
| T112 | lemma-census.md:158 | "TAPL Thm 22.4.2, p. 327" | inside §22.4 "Unification" (pp. 326–328), [T]:203-204 | unverifiable |
| T113 | lemma-census.md:161 | "TAPL Thm 22.4.3, p. 328" | inside §22.4 | unverifiable |
| T114 | lemma-census.md:166 | "(TAPL ch. 23, pp. 339–358)" | pp. 339–362, [T]:209,226 | corrected |
| T115 | lemma-census.md:173 | "TAPL Lemma 23.4.1, p. 347" | p. 347 lies in §23.4 "Examples" (pp. 344–352), [T]:213-214 | unverifiable |
| T116 | lemma-census.md:174 | "Impredicative Type Abstraction (ΛX. t) \| TAPL §23.4" | §23.4 is "Examples"; "System F" is §23.3 (341) and "Impredicativity" §23.10 (360), [T]:212-213,223 | corrected |

### 1c. PFPL (Harper, 2nd ed., author's abbreviated online edition)

Contents ([H], PDF pp. 10–13, printed pp. xii–xv): Part XII "Control Flow", p. 259
([H]:426); ch. 28 "Control Stacks", p. 261: §28.1 "Machine Definition" 261, §28.2 "Safety"
263, §28.3 "Correctness of the Stack Machine" 264, §28.4 Notes 267 ([H]:427-433); ch. 29
"Exceptions", p. 269 ([H]:435). Part XVI "Concurrency and Distribution", p. 371 ([H]:559);
ch. 39 "Process Calculus", p. 373, §39.1–39.8 pp. 373–386 ([H]:560-571); ch. 40 "Concurrent
Algol", p. 389, §40.1–40.5 pp. 390–398 ([H]:577-582); ch. 41 "Distributed Algol", p. 399,
§41.1 "Statics" 399, §41.2 "Dynamics" 402, §41.3 "Safety" 404, §41.4 Notes 404
([H]:584-593); Part XVII p. 407. Also ch. 6 "Type Safety", p. 51 (§6.1 "Preservation",
§6.2 "Progress"), and ch. 49 "Process Equivalence", p. 479 ([H]:672). The abbreviated PDF
carries the bodies of chs. 1–6, 9–11, 16, 19, 28, 29, 34, 35, 37 and 40 only (its "Chapter N"
headings); chs. 39 and 41 are in its contents but not its body.

| # | Where | As written | Verified locator | Status |
| --- | --- | --- | --- | --- |
| H1 | lemma-census.md:20 | "Harper PFPL §28.2; Owicki–Gries" | §28.2 "Safety", p. 263, in ch. 28 "Control Stacks", [H]:427-429 (body heading [H]:5824). Owicki–Gries: §2 row E1. | verified (PFPL part) |
| H2 | lemma-census.md:198 | "Stack Typing Monotonicity \| Harper PFPL ch. 28" | ch. 28 "Control Stacks", p. 261, [H]:427 | verified (chapter) |
| H3 | lemma-census.md:199 | "Stack Popping Typing Preservation \| Harper PFPL ch. 28" | as H2 | verified (chapter) |
| H4 | lemma-census.md:235 | "(Harper PFPL ch. 28; Wright 1994)" | as H2; Wright 1994: §2 row W1 | verified (PFPL part) |
| H5 | chapter-table.md:29 | "`machine-concurrency` \| Harper PFPL ch. 28; Wright 1994" | ch. 28 is "Control Stacks" in Part XII "Control Flow"; the book's concurrency chapters are 39–41 (Part XVI), [H]:426-427,559-584 | verified (locator exists); by its title and part it is about control flow, not concurrency |
| H6 | chapter-table.md:397 | "Harper (PFPL 2016, ch. 28, Abstract Machines)" | ch. 28's title is "Control Stacks" (§28.1 "Machine Definition"), [H]:427-428 | corrected (title) |
| H7 | domain-model-spec.md:114 | "PFPL ch. 28 (Control Stacks)" | [H]:427 | verified |
| H8 | note.md:287 | "Harper, Robert. *Practical Foundations for Programming Languages.* 2nd ed. Cambridge University Press, 2016. DOI: 10.1017/CBO9781316576892" | title, "Second Edition", Robert Harper, © 2016, published by Cambridge University Press, [H]:1-12,19-20; the edition prints no DOI (no "10.1017" in [H]) | verified (title, edition, year, publisher); DOI unverifiable |
| H9 | (brief's check) | PFPL chs. 39–41 | not cited anywhere in Gemini's four files (`rg -n "PFPL\|Harper"` finds only ch. 28 and §28.2); verified locators above | — |

## 2. The papers and the other books

Short names: new copies under `sources/text/` — [PP09] `plotkin-pretnar-2009-…`, [Pr15]
`pretnar-2015-…`, [BP12] `bauer-pretnar-2015-…` (arXiv:1203.1539v1, 2012), [Ca24]
`castagna-2024-…` (arXiv:2111.03354v4), [Le09] `leroy-2009-…`, [Ah04] `ahmed-2004-…`, [ADR09]
`ahmed-dreyer-rossberg-2009-…`, [Iris] `jung-et-al-2015-iris`, [MFP91] `meijer-fokkinga-paterson-1991-…`,
[RO10] `rendel-ostermann-2010-…`, [LV95] `lynch-vaandrager-1995-…`, [dVP21] `de-vilhena-pottier-2021-…`,
[Wa12] `wadler-2012-…`, [Wa14] `wadler-2014-…`, [McB08] `mcbride-2008-…`, [POM14]
`petricek-orchard-mycroft-2014-…`, [PGW17] `pickering-gibbons-wu-2017-…`, [Gi02] `gibbons-2002-…`.
Linked copies already in the tree — [ITree] `docs/research/2026-09-02-web-standards-sources/text/02-interaction-trees.txt`,
[DTalC] `…/06-data-types-a-la-carte.txt`, [Freer] `…/07-freer-monads-more-extensible-effects.txt`,
[Koka] `…/08-koka-row-polymorphic-effect-types.txt`, [Scoped] `…/12-a-calculus-for-scoped-effects-and-handlers.txt`,
[Latent] `…/13-latent-effects-for-reusable-language-components.txt`, [DN01] `…/16-defunctionalization-at-work.txt`,
[HiA] `…/20-handlers-in-action.txt`, [Fusion] `…/21-reasoning-about-effect-interaction-by-fusion.txt`;
[S05] `docs/research/2026-09-10-http-rest-formalisms/evidence/S05-tree-lenses.txt`, [S07]
`…/S07-multiparty-sessions.txt`, [S09] `…/S09-concurrency-models.txt`; [dV22]
`docs/research/2026-09-05-effects-papers/text/verification_with_effects.md`, [Jac]
`…/intro_coalgebar_mathematics_state.txt` and [Jac-md] `…/intro_coalgebar_mathematics_state.liteparse-interleaved.md`,
[CGKM] `…/from_partial_to_monadic_combinatory_algebra_effects.md`.

"As cited by X:n" means the detail is read in the reference list of another vendored text,
not in the work itself (a secondary reading; marked so in the status). Page spans and DOIs
of conference papers are rarely printed on author copies; where neither the copy nor a
vendored reference list prints them, they are unverifiable.

### 2a. Gemini's bibliography, `note.md` §6 (entry N is at line 259 + 2N)

| # | Where | As written (short) | Verified locator | Status |
| --- | --- | --- | --- | --- |
| P1 | note.md:261 | Ahmed, *Semantics of Types for Mutable State*, PhD thesis, Princeton, 2004 | title, author, Princeton, November 2004, [Ah04]:1-30 | verified |
| P2 | note.md:263 | Ahmed, Dreyer, Rossberg, "State-dependent representation independence and generational secrets", POPL '09, pp. 282–295, DOI 10.1145/1480881.1480917 | the title is "State-Dependent Representation Independence", [ADR09]:1; POPL'09, January 18–24, 2009, [ADR09]:60; the author copy prints no pages or DOI | corrected (title); pages and DOI unverifiable |
| P3 | note.md:265 | Bauer, Pretnar, "Programming with algebraic effects and handlers", JLAMP 84(1) (2015): 108–123, DOI 10.1016/j.jlamp.2014.02.001 | the copy is arXiv:1203.1539v1, 7 March 2012, [BP12]:3; journal 84 (2015), pp. 108–123, DOI as written, as cited by [Pr15]:769-771 | verified (as cited by [Pr15]); issue "no. 1" unverifiable |
| P4 | note.md:267 | Birkedal, Bizjak, Dreyer, Kaiser, Krebbers, "Iris: Monoids and Invariants …", POPL '15, DOI 10.1145/2676726.2676980 | authors are Ralf Jung, David Swasey, Filip Sieczkowski, Kasper Svendsen, Aaron Turon, Lars Birkedal, Derek Dreyer, [Iris]:3-9; POPL '15, [Iris]:87; DOI as written, [Iris]:90 | corrected (authors) |
| P5 | note.md:269 | Castagna, "Covariance and contravariance: conflict without a cause", ACM SIGPLAN Notices 30(3) (1995): 90–97, DOI 10.1145/202530.202538 | not vendored: no author- or publisher-hosted free copy found (the one free copy found is on a third party's course page); no vendored text cites it | unverifiable (the owner supplies the published copy) |
| P6 | note.md:271 | Castagna, Laurent, Nguyễn, Fluet, "Programming with Union, Intersection, and Negation Types", ACM Computing Surveys 56(3) (2024): 1–38, DOI 10.1145/3632297 | sole author Giuseppe Castagna, [Ca24]:1-4; "published in The French School of Programming, edited by B. Meyer, 2023, Springer", [Ca24]:52; arXiv:2111.03354v4, 27 March 2024, [Ca24]:12 | corrected (authors, venue, year) |
| P7 | note.md:273 | Cohen, Tate, Weirich, "From Partial to Monadic Combinatory Algebras for Effects", FSCD 2025 | authors Liron Cohen, Ariel Grunfeld, Dominik Kirst, Étienne Miquey; title "From Partial to Monadic: Combinatory Algebra with Effects", [CGKM]:1-11; the text copy prints no venue line | corrected (authors, title); venue unverifiable from the text |
| P8 | note.md:275 | de Vilhena, Pottier, "Verifying Concurrent Effectful Programs with Protocols", POPL '21, DOI 10.1145/3434301 | "A Separation Logic for Effect Handlers", Proc. ACM Program. Lang. 5, POPL, Article 33 (January 2021), 28 pages, DOI 10.1145/3434314, [dVP21]:3-6,23-25 | corrected (title, DOI) |
| P9 | note.md:277 | de Vilhena, *Specification and Verification of Effectful Programs with Protocols*, PhD thesis, Université Paris Cité, 2022 | *Proof of Programs with Effect Handlers*, Université Paris Cité, 2022, HAL tel-03891381, [dV22]:7-15 | corrected (title) |
| P10 | note.md:279 | Dolan, Mycroft, "Polymorphism, subtyping, and type inference in MLsub", POPL '17, pp. 60–72, DOI 10.1145/3009837.3009882 | not vendored (the author directory `cl.cam.ac.uk/~sd601/papers/` answers 403; the ACM copy is not free); no vendored text cites it | unverifiable |
| P11 | note.md:281 | Foster, Greenwald, Moore, Pierce, Schmitt, "Combinators for bidirectional tree transformations …", TOPLAS 29(3) (2007): 17-es, DOI 10.1145/1232420.1232424 | title and the five authors, [S05]:1-12; the copy is the author version, "ACM Transactions on Programming Languages and Systems, Vol. TBD, No. TDB, Month Year", [S05]:50 | verified (title, authors, journal); volume, article, year and DOI unverifiable |
| P12 | note.md:283 | Gibbons, "Calculating Functional Programs", LNCS 2297, pp. 149–201, Springer, 2002, DOI 10.1007/3-540-47797-0_5 | "Chapter 5", [Gi02]:1-2; running heads run from p. 149 ([Gi02]:45) to at least p. 203 ([Gi02]:2526); volume and DOI not printed | corrected (last page is at least 203); volume, year and DOI unverifiable |
| P13 | note.md:285 | Hancock, Setzer, "Interactive programs in dependent type theory", CSL 2000, LNCS 1862, pp. 315–329, DOI 10.1007/3-540-44622-6_23 | not vendored (Springer only); as cited by [ITree]:1605-1606: CSL, eds. Clote and Schwichtenberg, Springer, 2000, pp. 317–331 | corrected (pages, as cited by [ITree]); volume and DOI unverifiable |
| P14 | note.md:287 | Harper, PFPL, 2nd ed., CUP, 2016, DOI 10.1017/CBO9781316576892 | row H8 | see H8 |
| P15 | note.md:289 | Hinze, "Generic programming with adjunctions", LNCS 7470, pp. 47–129, 2012, DOI 10.1007/978-3-642-32202-0_2 | not vendored; no vendored text cites it. chapter-table.md:375 says "Hinze (2013)" for the same entry | unverifiable |
| P16 | note.md:291 | Honda, Vasconcelos, Kubo, "Language primitives and type discipline …", ESOP '98, LNCS 1381, pp. 122–138, DOI 10.1007/BFb0053567 | not vendored (S07 is Honda, Yoshida and Carbone's *Multiparty Asynchronous Session Types*, POPL 2008, a different paper, [S07]); as cited by [Wa14]:1925-1927: ESOP, 1998, pp. 122–138 | verified (venue, year, pages, as cited by [Wa14]); LNCS volume and DOI unverifiable |
| P17 | note.md:293 | Jacobs, *Introduction to Coalgebra: Mathematics of State and Observation*, CUP, 2016 | the vendored copy is the draft "Introduction to Coalgebra. Towards Mathematics of States and Observations", Version 2.00, September 27, 2012, [Jac-md]:1-13 | corrected (title, as the draft prints it); the 2016 CUP edition is unverifiable (not vendored) |
| P18 | note.md:295 | Johann, Ghani, "Initial algebra semantics is valid for inductive types", POPL '07, pp. 251–262, DOI 10.1145/1190216.1190255 | not vendored (the repository copy at libres.uncg.edu timed out twice). As cited by [DTalC]:553 and [Scoped]-family [11] (`…/11-syntax-and-semantics-for-operations-with-scopes.txt:1198`): Johann and Ghani (2007), "Initial algebra semantics is enough!", Typed Lambda Calculi and Applications | corrected (title and venue, as cited); pages and DOI unverifiable |
| P19 | note.md:297 | Jones, *Qualified Types: Theory and Practice*, CUP, 1994, DOI 10.1017/CBO9780511525902 | not vendored (a book); no vendored text cites it | unverifiable |
| P20 | note.md:299 | Kammar, Lindley, Oury, "Handlers in action", ICFP '13, pp. 145–158, DOI 10.1145/2500365.2500590 | title and authors, [HiA]:2-8; ICFP '13, September 25–27, 2013, [HiA]:56; DOI as written, [HiA]:59; pages not printed | verified (title, authors, venue, DOI); pages unverifiable |
| P21 | note.md:301 | Kiselyov, Ishii, "Freer monads, more extensible effects", Haskell 2015, pp. 94–105, DOI 10.1145/2804302.2804319 | title and authors, [Freer]:2-3; as cited by [Latent]:760-761: 8th Symposium on Haskell, pp. 94–105, ACM, 2015 | verified (as cited by [Latent]); DOI unverifiable |
| P22 | note.md:303 | Leijen, "Koka: Programming with row polymorphic effect types", MSFP 2014, DOI 10.4204/EPTCS.153.8 | MSFP 2014, EPTCS 153, 2014, pp. 100–126, doi:10.4204/EPTCS.153.8, [Koka]:2-5 | verified |
| P23 | note.md:305 | McBride, "Clowns to the left of me, jokers to the right: dissecting data structures", POPL '08, pp. 287–295, DOI 10.1145/1328438.1328474 | title "Clowns to the Left of me, Jokers to the Right (Pearl): Dissecting Data Structures", [McB08]:1-4; POPL'08, January 7–12, 2008, [McB08]:61; pages and DOI not printed. The entry says it is cited for "Ornamental structures"; the paper is about dissection, and its title and abstract do not mention ornaments | verified (title, venue); pages and DOI unverifiable |
| P24 | note.md:307 | Meijer, Fokkinga, Paterson, "Functional programming with bananas, lenses, envelopes and barbed wire", FPCA '91, LNCS 523, pp. 124–144, DOI 10.1007/3540543961_7 | title and authors, [MFP91]:1-3; as cited by [Gi02]:2263-2265: LNCS 523, Functional Programming Languages and Computer Architecture, pp. 124–144; year 1991 as cited by [DTalC]:567 | verified (as cited); DOI unverifiable |
| P25 | note.md:309 | Milner, *Communication and Concurrency*, Prentice Hall, 1989 | not vendored (a book); as cited by [Jac]:35274 and [S09]:6865: Prentice Hall, 1989 | verified (as cited) |
| P26 | note.md:311-312 | TAPL | rows T16–T21 | see T16–T21 |
| P27 | note.md:313-314 | ATTAPL | rows A1–A3, A29 | see A1–A3 |
| P28 | note.md:315 | Pierce, Azevedo de Amorim, Casinghino, Gaboardi, Greenberg, Hriţcu, Sjöberg, Yorgey, *Software Foundations, Volume 2: Programming Language Foundations*, electronic textbook, 2024 | the vendored copy's own citation lists those authors plus Andrew Tolmach, editor Benjamin C. Pierce, year 2026, "Version 7.1", `sources/plf/Preface.v:146-166` | corrected (author list, year and version, for the copy vendored today) |
| P29 | note.md:317 | Plotkin, Pretnar, "Handlers of algebraic effects", ESOP 2009, LNCS 5508, pp. 80–94, DOI 10.1007/978-3-642-00590-9_7 | title and authors, [PP09]:1-3; as cited by [Pr15]:844-848: ESOP 2009, York, LNCS 5502, pp. 80–94, DOI 10.1007/978-3-642-00590-9_7; [BP12]:1165-1166 also gives volume 5502, pages 80–94 | corrected (LNCS volume 5502, as cited twice) |
| P30 | note.md:319 | Pottier, Rémy, "The essence of ML", ATTAPL, pp. 389–489 | row A26 | see A26 |
| P31 | note.md:321 | Pretnar, "An introduction to algebraic effects and handlers: invited tutorial paper", ENTCS 319 (2015): 19–35, DOI 10.1016/j.entcs.2015.12.003 | the copy is the MFPS 2015 version, "Invited tutorial paper", [Pr15]:1-11,46; as cited by [Scoped]:1531-1532 (ENTCS 319:19–35, 2015) and by `…/09-generalized-evidence-passing-for-effect-handlers.txt:1638-1639` (same, DOI 10.1016/j.entcs.2015.12.003) | verified (as cited) |
| P32 | note.md:323 | Rendel, Ostermann, "Invertible syntax descriptions: unifying parsing and pretty printing", Haskell 2010, pp. 1–12, DOI 10.1145/1863523.1863525 | title and authors, [RO10]:1-3; "Haskell'10, September 30, 2010, Baltimore", [RO10]:61; pages and DOI not printed | verified (title, venue); pages and DOI unverifiable |
| P33 | note.md:325 | Sangiorgi, *Introduction to Bisimulation and Coinduction*, CUP, 2012, DOI 10.1017/CBO9780511777110 | not vendored (a book); no vendored text cites it. lemma-census.md:242 dates it 2011; the only nearby vendored citation is Sangiorgi and Rutten (eds.), *Advanced Topics in Bisimulation and Coinduction*, CUP 2011, [Jac]:35089-35091, a different book | unverifiable |
| P34 | note.md:327 | Swierstra, "Data types à la carte", JFP 18(4) (2008): 423–436, DOI 10.1017/S0956796808006758 | [DTalC]:2-3 | verified |
| P35 | note.md:329 | Wadler, "Propositions as sessions", ICFP '12, pp. 273–286, DOI 10.1145/2364527.2364568 | title, [Wa12]:1-3; ICFP'12, September 9–15, 2012, Copenhagen, [Wa12]:62; pages and DOI not printed | verified (title, venue); pages and DOI unverifiable |
| P36 | note.md:331 | Wright, Felleisen, "A syntactic approach to type soundness", Information and Computation 115(1) (1994): 38–94, DOI 10.1006/inco.1994.1093 | not vendored (no author-hosted copy found); as cited by [dV22]:3904: Information and Computation, 115(1):38–94, November 1994; also cited in [H]:9888 | verified (as cited); DOI unverifiable |
| P37 | note.md:333 | Xia, Zakowski, He, Hur, Malecha, Pierce, Zdancewic, "Interaction trees …", POPL '20, DOI 10.1145/3371119 | authors, title, Proc. ACM Program. Lang. 4, POPL, Article 51 (January 2020), DOI 10.1145/3371119, [ITree]:34-37 | verified |
| P38 | note.md:335 | TypeScript Team, handbook, Microsoft, 2024; tsgo 7.0.0-dev.20260629.1 | product documentation, not literature; not audited here | — |
| P39 | note.md:337 | Effect 4.0.0-rc.112 source, `vendor/effect-4.0.0-rc.112/src/` | in the tree; not literature; not audited here | — |

### 2b. Author-year citations in the tables and prose

| # | Where | As written | Verified locator | Status |
| --- | --- | --- | --- | --- |
| C1 | domain-model-spec.md:112 | "Ahmed (2004)" | P1 | verified |
| C2 | domain-model-spec.md:113 | "de Vilhena & Pottier (POPL '21); Xia et al. (POPL '20)" | P8 (venue only), P37 | verified |
| C3 | domain-model-spec.md:114 | "Danvy & Nielsen (2001, Defunctionalization)" | "Defunctionalization at Work", BRICS RS-01-23, June 2001, [DN01]:2,8-9 | verified |
| C4 | domain-model-spec.md:115 | "Lynch & Vaandrager (1995, Forward Simulations); Milner (1989); Sangiorgi (2012)" | "Forward and Backward Simulations I. Untimed Systems", Information and Computation 121, 214–233 (1995), [LV95]:1-7; Milner P25; Sangiorgi P33 | verified (Lynch–Vaandrager, Milner as cited); Sangiorgi unverifiable |
| C5 | domain-model-spec.md:116 | "Rendel & Ostermann (Haskell '10, Invertible Syntax); Foster et al. (TOPLAS '07, Lenses)" | P32; P11 | verified (Rendel–Ostermann venue; Foster journal); Foster year unverifiable |
| C6 | domain-model-spec.md:117 | "Dolan & Mycroft (POPL '17); Castagna (2024)" | P10; P6 (arXiv v4 2024, published 2023) | Dolan–Mycroft unverifiable; Castagna verified (year of the arXiv version) |
| C7 | domain-model-spec.md:118 | "Meijer, Fokkinga, Paterson (FPCA '91); Johann & Ghani (POPL '07)" | P24; P18 (TLCA 2007, as cited) | verified (Meijer et al., as cited); Johann–Ghani corrected (venue TLCA, as cited) |
| C8 | domain-model-spec.md:119 | "Petricek, Orchard, Mycroft (2013/2014, Coeffects); Leijen (MSFP '14, Koka)" | ICFP '14, DOI 10.1145/2628136.2628160, [POM14]:1-3,60,63; the 2013 paper is "Coeffects: Unified static analysis of context-dependence" (ICALP), as cited by [POM14]:1413-1414; Leijen P22 | verified (2014; 2013 as cited) |
| C9 | domain-model-spec.md:120 | "Honda, Vasconcelos, Kubo (ESOP '98); Wadler (ICFP '12)" | P16 (as cited); P35 | verified |
| C10 | domain-model-spec.md:121 | "Leroy (CACM '09, CompCert Semantic Preservation)" | "Formal verification of a realistic compiler", Xavier Leroy, [Le09]:1-3; "proof of semantic preservation", [Le09]:12; the copy prints no venue or year | verified (title, subject); "CACM '09" unverifiable |
| C11 | domain-model-spec.md:402 | `"work": "de Vilhena & Pottier"` | P8 | verified (authors) |
| C12 | domain-model-spec.md:453 | `"work": "Moggi / Xia et al."` | Xia P37; Moggi, "Notions of computation and monads", Information and Computation 93 (1991) 55–92, as cited by [PP09]:651-652 | verified (as cited) |
| C13 | chapter-table.md:27 | "Foster 2007; Rendel 2010" | P11 (year unverifiable); P32 | verified (Rendel 2010); Foster year unverifiable |
| C14 | chapter-table.md:28 | "GTWW 1977; Meijer 1991" | Goguen, Thatcher, Wagner, Wright, "Initial algebra semantics and continuous algebras", JACM 24(1):68–95, January 1977, as cited by [Gi02]:2232-2234; Meijer P24 | verified (as cited) |
| C15 | chapter-table.md:29 | "Harper PFPL ch. 28; Wright 1994" | H5; P36 | verified (as cited) |
| C16 | chapter-table.md:302 | "Plotkin & Pretnar, Bauer & Pretnar, Leijen (Koka)" | P29, P3, P22 | verified (works exist) |
| C17 | chapter-table.md:326 | "Ahmed; Ahmed, Dreyer, Rossberg 2009; Birkedal et al. Iris" | P1; P2 (POPL'09); Iris's first author is Ralf Jung, Birkedal is sixth of seven, [Iris]:3-9 | corrected ("Birkedal et al.") |
| C18 | chapter-table.md:351 | "Foster et al. (TOPLAS 2007, lenses); Rendel and Ostermann (POPL 2010, invertible syntax); Pickering, Gibbons, Wu (2017, profunctor optics / lawful prisms)" | Rendel–Ostermann appeared at Haskell'10, [RO10]:61, not POPL; Pickering, Gibbons, Wu, "Profunctor Optics: Modular Data Accessors", The Art, Science, and Engineering of Programming 1(2), 2017, article 7, doi 10.22152/programming-journal.org/2017/1/7, [PGW17]:1-4,36-46; Foster P11 | corrected (Rendel–Ostermann venue) |
| C19 | chapter-table.md:375 | "Goguen, Thatcher, Wagner, Wright (GTWW 1977); Meijer, Fokkinga, Paterson (FPCA 1991); Gibbons (2002); Hinze (2013); Johann and Ghani (2007)" | C14; P24; P12; Hinze: P15 (note.md says 2012); P18 | GTWW, Meijer verified (as cited); Gibbons verified (title); Hinze unverifiable; Johann–Ghani verified (year, as cited) |
| C20 | chapter-table.md:382 | "Wadler view and Gill–Launchbury–Peyton Jones build" | Wadler 1987, "Views: a way for pattern matching to cohabit with data abstraction", POPL, as cited by [S05]:3581-3582; Gill, Launchbury, Peyton Jones 1993, "A Short Cut to Deforestation", as cited by [Fusion]:1322 | verified (as cited) |
| C21 | chapter-table.md:397 | "Wright and Felleisen (1994); de Vilhena and Pottier (2021, 2022); Milner and Sangiorgi (bisimulation); Lynch and Vaandrager (forward simulations); Honda, Wadler (session types)" | P36; 2021 is P8; the 2022 work is de Vilhena's thesis alone, P9; P25, P33; C4; P16, P35 | corrected ("de Vilhena and Pottier 2022" is a single-author thesis); Sangiorgi unverifiable; rest verified |
| C22 | lemma-census.md:20,36,239 | "Owicki–Gries"; "Manna & Pnueli" | Owicki and Gries (1976), "An axiomatic proof technique for …", as cited by [LV95]:1281; Manna and Pnueli, *The Temporal Logic of Reactive and Concurrent Systems*, Springer, 1991, as cited by [S09]:6857-6858 | verified (as cited; Gemini gives no year) |
| C23 | lemma-census.md:21 | "Plotkin 1977 (Adequacy); Jacobs ch. 2" | Plotkin, "LCF considered as a programming language", TCS 5(3):223–255, 1977, as cited by [H]:9784-9785 and [dV22]:3841; Jacobs ch. 2 is "Coalgebras of Polynomial Functors", p. 25, [Jac]:377 | verified (Plotkin as cited; Jacobs chapter exists) |
| C24 | lemma-census.md:34,37,81,95,203,244 | "Wright & Felleisen 1994" | P36 | verified (as cited) |
| C25 | lemma-census.md:63 | "Elgot 1975" | no vendored text names an Elgot 1975 work ([Jac]:25660 mentions Elgot without a reference) | unverifiable |
| C26 | lemma-census.md:92 | "Milner 1978 ('well-typed programs cannot go wrong')" | Milner, "A theory of type polymorphism in programming", JCSS 17:348–375, 1978, as cited by [H]:9709 and [Koka]:997; the quoted phrase needs the paper | verified (as cited); the quotation is unverifiable |
| C27 | lemma-census.md:94 | "Plotkin 1977" | C23 | verified (as cited) |
| C28 | lemma-census.md:107,108 | "Castagna 2005 (Semantic Subtyping)" | the 2005 work is Castagna and Frisch, "A gentle introduction to semantic subtyping", PPDP '05 pp. 198–208 and ICALP '05 (LNCS 3580) pp. 30–34, as cited by [Ca24]:2998-3003 | corrected (co-author Frisch, as cited) |
| C29 | lemma-census.md:120 | "Birkhoff" | names no work | unverifiable |
| C30 | lemma-census.md:160 | "Jones 1994" | P19 | unverifiable |
| C31 | lemma-census.md:183 | "Leijen 2014 (Koka)" | P22 | verified |
| C32 | lemma-census.md:184 | "Katsumata 2014 (Coeffects)" | Katsumata, "Parametric effect monads and semantics of effect systems", POPL 2014, pp. 633–646, as cited by [POM14]:1396-1397; the title is about effect systems, not coeffects | verified (as cited); the label "Coeffects" does not match the title |
| C33 | lemma-census.md:185 | "Petricek et al. 2014" | C8 | verified |
| C34 | lemma-census.md:196 | "Ahmed 2004" | P1 | verified |
| C35 | lemma-census.md:197 | "de Vilhena 2022 §2.4" | the thesis's §2.4 is "Related work", p. 27, [dV22]:116,836 | corrected (section; the lemma's place needs a reading of ch. 2) |
| C36 | lemma-census.md:200 | "de Vilhena 2022" | P9 | verified (year) |
| C37 | lemma-census.md:202 | "Xia et al. 2020" | P37 | verified |
| C38 | lemma-census.md:204 | "Appel–McAllester 2001; Ahmed 2006" | Ahmed, "Step-indexed syntactic logical relations for recursive and quantified types", ESOP 2006, as cited by [ADR09]:1062-1063; no vendored text cites Appel and McAllester | verified (Ahmed 2006, as cited); Appel–McAllester unverifiable |
| C39 | lemma-census.md:209 | "(Foster 2007; Rendel 2010)" | C13 | as C13 |
| C40 | lemma-census.md:213,214 | "Pickering et al. 2017" | C18 | verified |
| C41 | lemma-census.md:215,218 | "Rendel & Ostermann 2010" | P32 | verified |
| C42 | lemma-census.md:216,217 | "Foster et al. 2007" | P11 | verified (work); year unverifiable |
| C43 | lemma-census.md:223,229 | "GTWW 1977"; "GTWW 1977; Johann & Ghani 2007" | C14; P18 | verified (as cited) |
| C44 | lemma-census.md:227 | "Meijer et al. 1991 (Bananas)" | P24 | verified (as cited) |
| C45 | lemma-census.md:228 | "Wadler 1987; Gill et al. 1993" | C20 | verified (as cited) |
| C46 | lemma-census.md:240 | "Honda 1998; Wadler 2014" | P16; "Propositions as sessions", JFP 24(2-3): 384–418, 2014, doi:10.1017/S095679681400001X, [Wa14]:1-3 | verified |
| C47 | lemma-census.md:241 | "Lynch & Vaandrager 1995" | C4 | verified |
| C48 | lemma-census.md:242 | "Milner 1989; Sangiorgi 2011" | P25; P33 (Gemini's bibliography says 2012) | Milner verified (as cited); Sangiorgi unverifiable |
| C49 | note.md:33 | "(Honda 1998, Wadler 2014)" | P16; C46 | verified |
| C50 | note.md:68 | "Literature (Meijer 1991, Johann 2007)" | P24; P18 | verified (as cited) |
| C51 | note.md:69 | "Literature (Foster 2005, Rendel 2010)" | Gemini's own entry 11 says 2007; the copy prints no year, [S05]:50; Rendel P32 | unverifiable (Foster's year; the file disagrees with itself) |
| C52 | note.md:70 | "Literature (Plotkin 2009, Xia 2020)" | P29; P37 | verified |
| C53 | note.md:233 | "(Honda et al. 1998, Wadler 2012)" | P16; P35 | verified |
| C54 | note.md:238 | "(Moggi 1991, Xia et al. 2020)" | C12; P37 | verified (Moggi as cited) |
| C55 | note.md:244 | "Castagna (2024) and Dolan & Mycroft (2017)" | P6; P10 | Castagna verified; Dolan–Mycroft unverifiable |

## 3. Software Foundations vol. 2 (PLF) chapter and lemma names

Read in `sources/plf/*.v` (Version 7.1, `plf/Preface.v:146-166`), searched with
`rg -n "^(Theorem|Lemma|Corollary|Definition) <name>\b" plf/*.v`. The distributed files leave
some proofs as exercises: the statement is there, the proof ends in `Admitted` (said below
where it applies).

| # | Where | As written | Verified locator | Status |
| --- | --- | --- | --- | --- |
| F1 | chapter-table.md:36 | "PLF *Smallstep*" | `plf/Smallstep.v` | verified |
| F2 | chapter-table.md:60 | "PLF *Types*" | `plf/Types.v` | verified |
| F3 | chapter-table.md:84 | "PLF *Stlc*" | `plf/Stlc.v` | verified |
| F4 | chapter-table.md:107 | "PLF *MoreStlc*" | `plf/MoreStlc.v` | verified |
| F5 | chapter-table.md:129; domain-model-spec.md:112; lemma-census.md:79 | "PLF *References*" | `plf/References.v` | verified |
| F6 | lemma-census.md:18 | "PLF *Smallstep* `step_deterministic`" | `Smallstep.v:269` (also `:464`, `:776` for later languages of the chapter); proved (`Qed` at `:292`) | verified |
| F7 | lemma-census.md:19 | "PLF *Smallstep* `normal_forms_unique`" | `Smallstep.v:1059`, `Qed` at `:1095` | verified |
| F8 | lemma-census.md:31 | "PLF *Types* `inversion`" | no declaration named `inversion` in any PLF file | corrected (absent) |
| F9 | lemma-census.md:32 | "PLF *Types* `canonical_forms`" | no such name; `Types.v` has `bool_canonical` (`:366`) and `nat_canonical` (`:376`); `StlcProp.v` has `canonical_forms_bool` (`:30`), `canonical_forms_fun` (`:40`) | corrected |
| F10 | lemma-census.md:33 | "PLF *Types* `progress`" | `Types.v:394`; an exercise (`finish_progress`), `Admitted` at `:417` | verified (statement) |
| F11 | lemma-census.md:35 | "PLF *Types* `preservation`" | `Types.v:463`; an exercise (`finish_preservation`, `:462`), `Admitted` at `:485` | verified (statement) |
| F12 | lemma-census.md:46 | "PLF *Stlc* `inversion`" | no declaration named `inversion` in `Stlc.v` or `StlcProp.v` | corrected (absent) |
| F13 | lemma-census.md:47 | "PLF *Stlc* `unique_types`" | `StlcProp.v:462` (chapter StlcProp, not Stlc); an exercise, `Admitted` at `:467` | corrected (chapter) |
| F14 | lemma-census.md:48 | "PLF *Stlc* `weakening`" | `StlcProp.v:193`, `Qed` at `:201` | corrected (chapter) |
| F15 | lemma-census.md:49 | "PLF *Stlc* `substitution_preserves_typing`" | `StlcProp.v:230`, `Qed` at `:311` | corrected (chapter) |
| F16 | lemma-census.md:50,51 | "PLF *Stlc*" (Gemini's two rows on the algorithmic typechecker) | `Typechecking.v:186` `type_checking_sound`, `:225` `type_checking_complete` | corrected (chapter) |
| F17 | lemma-census.md:76 | "PLF *References* `store_weakening`" | `References.v:1539`, `Qed` at `:1549` | verified |
| F18 | note.md:315 | the PLF bibliography entry | row P28 | corrected |

## 4. Book names without a locator (no row needed; listed so that every search hit is accounted for)

note.md:1, :14, :52 (column head), :229, :232, :251; domain-model-spec.md:19, :58, :209
(`work : String -- e.g. "ATTAPL", "TAPL", "PFPL"`); chapter-table.md:1, :3; lemma-census.md:5.
These name TAPL, ATTAPL, PFPL or PLF without a chapter, section or page; the titles they use
match [T]:1, [A]:1-3, [H]:1-5 and `plf/Preface.v:160`. note.md:14 and :355 also claim that
every open obligation "collapses onto" or "completely closes" by the TAPL/ATTAPL lemma lists;
that is a claim about the tree, not a locator, and is left to seat B.
Also matched by the brief's search but carrying no locator of their own: note.md:24, :26,
:27 (name "TAPL's standard Preservation theorem", "TAPL's store preservation lemma" and "TAPL
Type Safety" without a number; their locator is T1–T2); note.md:139 (the `"work": "TAPL"` field
of the JSON whose locator is T15); domain-model-spec.md:407 (a false match: "ch." in "match.").

## 5. Proposals for the coordinator (not rulings)

- Chapter ids. `attapl-08-logical-relations` points at the ML-modules chapter. The
  logical-relations sources in ATTAPL are ch. 6 (Crary, p. 223; §6.6–6.9 pp. 233–242) and
  ch. 7 §7.6 (Pitts, p. 266). `tapl-20-variances` (note.md:63) names a chapter that is "Recursive
  Types"; TAPL has no variance chapter. `tapl-19-nominal` is a section (§19.3, p. 251) of the
  Featherweight Java case study. A proposed decisions row: "the chapter skeleton takes its ids
  and spans from `sources/text/{tapl-contents,attapl-frontmatter}.txt`; a theorem or rule
  number enters only after it is read in the owner's copy".
- The `machine-concurrency` chapter cites PFPL ch. 28 (control stacks) only. If a PFPL locator
  is wanted for the fiber machine's concurrency, the candidates by title are chs. 39–41 (Part
  XVI) and ch. 49 "Process Equivalence" (p. 479) for the simulations; whether they fit is a
  reading for seat B, not settled here.
- Not in this brief's four files, and not audited: the system map §9's own literature marks.
  Three of them could be checked from the contents read tonight and hold: "TAPL §13.4" is
  "Store Typings", p. 162 ([T]:114); "TAPL §16.3" is "Joins and Meets", p. 218 ([T]:141);
  "Harper, PFPL ch. 28" is "Control Stacks", p. 261 ([H]:427). The others ("Jacobs Thm 5.3.4",
  "de Vilhena Def. 2.2, 2.4–2.8", "Xia et al. §3.2, §7", "Hinze §9–10", "McBride 2011", …) were
  not read.

## Receipt

**The one thing to know first:** ATTAPL ch. 8 is Harper and Pierce's ML-modules chapter
(p. 293), ch. 6 is Crary's logical relations (p. 223), ch. 3 is Henglein–Makholm–Niss effect
types and regions (p. 87), Walker is ch. 1 (p. 3); every theorem, lemma and rule number Gemini
gives for TAPL and ATTAPL is unverifiable until the owner supplies the books.

- Seat A, bounded probe. Branch `refactor/phase1-phase3`, HEAD `198dd533` as named by the
  brief; no git, lake, make or TypeScript command was run, so base and head are the brief's,
  not re-read. Nothing was committed.
- Files written (all under `docs/research/2026-10-01-semantics/`): `citations-audit.md` (this
  file); `sources/README.md`, `sources/fetch.sh`, `sources/SHA256SUMS`; the 21 PDFs and
  `plf.tgz` listed in `SHA256SUMS`; `sources/text/*.txt` (21 `pdftotext -layout` copies);
  `sources/plf/` (16 `.v` files and `LICENSE` extracted from `plf.tgz`). Scratch files stayed in
  the session scratchpad. No other file was touched.
- Commands: `curl -sS -fL --max-time … -o <file> <url>` (one per URL below);
  `pdftotext -layout <pdf> text/<name>.txt`; `pdfinfo` for page counts; `shasum -a 256 -c
  SHA256SUMS` (22 of 22 OK); `tar xzf plf.tgz plf/…`; `rg` over Gemini's four files
  (`rg -n "TAPL|ATTAPL|PFPL|PLF|pp\.|ch\."`: 175 hit lines; a script checked that every hit line
  is named in this audit, all 175 are, five of them in §4 as carrying no locator) and over the
  vendored texts for the secondary citations; `awk` for the PLF proof endings; `python3` to
  compute sums and build the README tables. The WebSearch tool was used twelve times only to
  find author pages; no search result is used as evidence for a locator.
- Rows: ATTAPL 29 (7 verified, 21 corrected, 1 unverifiable); TAPL 116 (32 verified,
  50 corrected, 34 unverifiable); PFPL 9 (7 verified, 1 corrected, 1 not cited); Gemini's
  bibliography 39 (16 verified, 12 corrected, 5 unverifiable, 6 pointers or not literature);
  author-year citations 55 (41 verified, 5 corrected, 4 unverifiable, 5 mixed); PLF 18
  (10 verified, 8 corrected). "Verified" includes rows marked "as cited", which are read in a
  vendored text's reference list rather than in the work itself.

URLs tried (result; bytes; sha256 of what was kept):

| URL | Result | Kept as | sha256 |
| --- | --- | --- | --- |
| https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf | 200, 46,663 B | `tapl-contents.pdf` | f34f69cea72c4a8676ca853925f1215005b8e8e6334a5283965c48f4dfd99834 |
| https://www.cis.upenn.edu/~bcpierce/attapl/frontmatter.pdf | 200, 73,315 B | `attapl-frontmatter.pdf` | db06766bdd0d9d8425dfc5664819e4ee5319b9f5382110b3ad00012ec91a59ba |
| https://www.cs.cmu.edu/~rwh/pfpl/2nded.pdf (the brief's lead) | 404 | — | — |
| https://www.cs.cmu.edu/~rwh/pfpl/ and …/pfpl.html (the author's page, one look) | 200, HTML; links "Abbreviated online edition, with corrections" | — | — |
| https://www.cs.cmu.edu/~rwh/pfpl/abbrev.pdf | 200, 789,843 B | `pfpl-2nded-abbrev.pdf` | 82aeead40e7d2160500c8f25612d4ec120c27454ae57619285345bae464ae94d |
| https://softwarefoundations.cis.upenn.edu/plf-current/plf.tgz | 200, 6,074,519 B | `plf.tgz` | 40d9f38757dd7b22ab54a867f684d4f22b18c7c5829334e5917d1158d1d318d0 |
| https://homepages.inf.ed.ac.uk/gdp/publications/Effect_Handlers.pdf | 200, 214,285 B | `plotkin-pretnar-2009-…` | 310e168be020973a1b7e43ffe4eac86ce4119a8c3cfe6a31b19c670a6c88da0e |
| https://www.eff-lang.org/handlers-tutorial.pdf | 200, 344,495 B | `pretnar-2015-…` | e4f65d819f7efa358b60af394dbfe065d2f49f2c04950aefc5a83aa05ba48c67 |
| https://arxiv.org/pdf/1203.1539 | 200, 242,279 B | `bauer-pretnar-2015-…` | 65c43ce564c5dfd6b0bb06a1d60a46c126a1ce08e67725e76ba93bc528726a7c |
| https://arxiv.org/pdf/2111.03354 | 200, 693,989 B | `castagna-2024-…` | c757fbf689e62ad58e7f15accb49b652227a5bd6d225c0ec2324ce69e049a3b1 |
| https://xavierleroy.org/publi/compcert-CACM.pdf | 200, 200,102 B | `leroy-2009-…` | 5cfa2447db8dfa4400a43bb7e41e16f4787bf614e72bf0ffbf82f75d6824a137 |
| https://research.utwente.nl/files/6142049/meijer91functional.pdf (lead) | 403 | — | — |
| https://maartenfokkinga.github.io/utwente/mmf91m.pdf (co-author's page) | 200, 253,662 B | `meijer-fokkinga-paterson-1991-…` | a37f101561101fc964448733ff3cda3714390da71be44d2713caeb5f5886c1e0 |
| https://www.ccs.neu.edu/home/amal/ahmedsthesis.pdf | 200, 1,469,000 B | `ahmed-2004-…` | e7ba0d520d51c99c20fbc834abf32f6cdae9065683ddd3c9b08611a98ac5dec6 |
| https://www.ccs.neu.edu/home/amal/papers/sdri.pdf | 200, 288,127 B | `ahmed-dreyer-rossberg-2009-…` | 95dc2c1d58456c9fb1fa4e42f3f5b97e14f741a6da3798b8c3d6299c43807c05 |
| https://iris-project.org/pdfs/2015-popl-iris1-final.pdf | 200, 424,926 B | `jung-et-al-2015-iris.pdf` | e661cd31d7a7a02df0262b7e1adda34ec84578d8a3864461593663979c9f2e98 |
| https://tomasp.net/academic/papers/coeffects/ (lead) | 200, HTML; lists the ICALP 2013 paper, not ICFP 2014 | — | — |
| https://www.doc.ic.ac.uk/~dorchard/publ/coeffects-icfp14.pdf (co-author's page) | 200, 522,022 B | `petricek-orchard-mycroft-2014-…` | 9645b0c4a32ef160b1210738c40728f92fd8284b96af54157ca77762e83b8bba |
| https://cambium.inria.fr/~fpottier/publis/ (lead, directory) | 403 | — | — |
| https://dl.acm.org/doi/pdf/10.1145/3434314 | 403 | — | — |
| https://gallium.inria.fr/~fpottier/biblio/pottier.html (author's list) | 200, HTML | — | — |
| https://cambium.inria.fr/~fpottier/publis/de-vilhena-pottier-sleh.pdf | 200, 739,831 B | `de-vilhena-pottier-2021-…` | 703085483ba6b4ed3d5d1704651f1c13234c07834a1014dbca34e3f1540023e6 |
| https://www.informatik.uni-marburg.de/~rendel/unparse/ (lead) | 200, HTML | — | — |
| http://www.informatik.uni-marburg.de/~rendel/unparse/rendel10invertible.pdf (redirects to https) | 200, 233,034 B | `rendel-ostermann-2010-…` | 65467791217ab45daf0979c7f560747df1a9ad400f1ee8a29522b83b0391b40f |
| https://www.cl.cam.ac.uk/~sd601/papers/ (lead) | 403 | — | — |
| https://www.cl.cam.ac.uk/~sd601/papers/mlsub-preprint.pdf | 403 | — | — |
| https://ir.cwi.nl/pub/1393 (lead) | 200, HTML | — | — |
| https://ir.cwi.nl/pub/1393/1393D.pdf | 200, 5,477,685 B | `lynch-vaandrager-1995-…` | fac099bf3462b90c58b8ed1077abef0808f5412f21879a5d1024ecdfdd5ff050 |
| https://homepages.inf.ed.ac.uk/wadler/ and …/topics/linear-logic.html (lead) | 200, HTML | — | — |
| https://homepages.inf.ed.ac.uk/wadler/papers/propositions-as-sessions/propositions-as-sessions.pdf | 200, 211,409 B | `wadler-2012-…` | 232aef383150dc2f92084631dfaf8b8fac8882cdc4c107c14d0893ea5cad316b |
| https://homepages.inf.ed.ac.uk/wadler/papers/propositions-as-sessions/propositions-as-sessions-jfp.pdf | 200, 296,606 B | `wadler-2014-…` | e40ce98626e32bfe53bb51980b850bfdd0c016464d73dc4b3cddc4184b06d670 |
| https://personal.cis.strath.ac.uk/conor.mcbride/Dissect.pdf | 200, 304,924 B | `mcbride-2008-…` | 5fb9105c41392baf1a0392cf87de942f060e55cbf827beb2660fb6570f89a0b5 |
| https://arxiv.org/pdf/1703.10857 | 200, 811,568 B | `pickering-gibbons-wu-2017-…` | c989594db24e9fa3d5d76de0263450d214eb9ee80363cc737a5d8cc8428d05bf |
| https://www.cs.ox.ac.uk/people/jeremy.gibbons/publications/acmmpc-calcfp.pdf | 200, 327,651 B | `gibbons-2002-…` | 3ff8d3fb3813327a676e0613f61fb3f9b09324283b3bfea96c5502ec31e1b121 |
| https://libres.uncg.edu/ir/asu/f/Johann_Patricia_2007_Intitial%20Algebra%20Semantics%20Is%20Enough.pdf (twice) | connection timed out (75 s, then 30 s) | — | — |

Not vendored, and what the owner must supply: the full texts of TAPL and ATTAPL (for the 34
TAPL rows marked unverifiable and the unverifiable parts of A3, A19, A21, A25 and A26, every theorem, lemma, definition and rule number,
and chapter end pages); the Cambridge printing of PFPL if printed pages are wanted; Milner 1989,
Sangiorgi, Jones 1994 (books); Dolan–Mycroft 2017, Honda–Vasconcelos–Kubo 1998,
Hancock–Setzer 2000, Hinze 2012, Wright–Felleisen 1994, Castagna 1995, GTWW 1977, Plotkin 1977,
Milner 1978, Moggi 1991, Katsumata 2014 (papers with no free author copy found, or not tried);
Johann–Ghani 2007 (lead timed out; retry). The table with identifiers is in
`sources/README.md`, "Not vendored".

Evidence class by section: §1a, §1b, §1c — reading of the book's own contents pages (and, for
PFPL ch. 28, one body heading), cited by file and line; §2a, §2b — reading of the vendored
copies' first pages and furniture lines, and secondary reading of vendored reference lists
where marked "as cited"; §3 — reading of PLF's `.v` files; §5 — proposals, not checked against
anything beyond the lines cited. Nothing here is proved or tested; all evidence is bounded to
the files named, and no row reads a book's body except PFPL ch. 28's heading.

Open: the PFPL page numbers are the author's abbreviated edition's; whether they equal the
Cambridge printing is unchecked. `docs/research/de-vilhena-thesis.pdf` and
`verification_with_effects.pdf` have different bytes; which document the first one is was not
checked. The system map §9's locators are outside this audit (§5). Minutes spent: about 25
(19:37–20:03 by the shell clock).
