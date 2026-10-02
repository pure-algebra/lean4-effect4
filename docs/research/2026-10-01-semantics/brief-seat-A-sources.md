# Brief for seat A: index the vendored sources, audit every citation (2026-10-01, ~45 minutes)

You are a bounded probe in `/Users/pooks/Dev/lean4-effect4` (branch `refactor/phase1-phase3`,
HEAD `198dd533`). The owner's rule tonight: no literature locator from memory; every chapter,
section and page cited in the semantics work is read off a vendored copy with a checksum. Most
of the literature is already vendored locally (below); your job is to index it in one place,
fetch only what is missing and free, record what is not free, and audit every citation Gemini
wrote against the vendored text. Stop after about 45 minutes at a coherent place and write the
receipt; a partial audit with a receipt beats a complete one without.

## Rules

- Write only under `docs/research/2026-10-01-semantics/sources/` and the one file
  `docs/research/2026-10-01-semantics/citations-audit.md`. Edit nothing else. Run no `git`
  command, no `lake`, no `make`, no TypeScript. (`docs/research/` is gitignored; the coordinator
  force-adds the index and the audit, never a PDF.)
- Refetch nothing that is already vendored: link it and record its existing sha256. Download
  only author-hosted, publisher open-access, or permissively licensed copies (an author's own
  page, HAL, arXiv, CWI/BRICS/university repositories, LMCS, a publisher's own free
  contents/frontmatter PDF). Never a pirate mirror. A work that is not free is `not vendored`
  with its DOI or ISBN and what the owner must supply.
- Tools: `curl`, `shasum -a 256`, `pdftotext` (`/opt/homebrew/bin`), `qpdf`, `python3` (no
  `pypdf`), `rg`. Precedents for the folder's shape: `docs/research/2026-09-05-effects-papers/`
  (`README.md`, `SHA256SUMS`, `text/`) and `docs/research/2026-09-02-web-standards-sources/`
  (`README.md`, `manifest.json`, `SHA256SUMS`, `retrieve.py`, `verify.py`, `text/`).
- Evidence words on every audit row: **verified** (read in a vendored text at a named page),
  **corrected** (Gemini's locator differs; the verified one given), **unverifiable** (no vendored
  source; which one is missing). Plain words; no "sound", "complete", "equivalent".

## Already vendored locally (index first)

- `docs/research/2026-09-02-web-standards-sources/papers/01…21-*.pdf` with `text/*.txt`,
  `SHA256SUMS`, `manifest.json` (download URLs) and a `README.md` table: interaction trees (02),
  Plotkin–Pretnar, Handling algebraic effects, LMCS 2013 (05), Swierstra (06), Kiselyov–Ishii
  (07), Leijen's Koka (08), effect handlers in scope (10), scoped operations (11, 12), hefty
  algebras (14), Danvy–Nielsen defunctionalization (16), rows and handlers (17, 18), retrofitting
  handlers onto OCaml (19), Kammar–Lindley–Oury handlers in action (20), fusion (21), and more.
- `docs/research/2026-09-05-effects-papers/` (`README.md`, `SHA256SUMS`, `text/`): de Vilhena's
  thesis (`../verification_with_effects.pdf`, also `../de-vilhena-thesis.pdf`), Jacobs'
  coalgebra, Cohen et al. FSCD 2025, Mattick.
- `docs/research/2026-09-10-http-rest-formalisms/sources/S01…S17-*.pdf` with
  `SOURCE-REGISTER.md` and `evidence/*.txt`: seven sketches (S04), polynomial interaction (S03),
  tree lenses (S05: check whether this is Foster et al. TOPLAS 2007), profunctor optics (S06),
  multiparty sessions (S07: check which Honda paper), concurrency models (S09), rewriting survey.
- `docs/research/2026-09-11-protocol-projection-and-transport/sources/network-calculus.pdf`.
- Outside the tree: `~/Dev/foldlab/.reference/papers/` (its `README.md` names them;
  `program_proofs.pdf` is Leino), `~/Dev/jetstream-workflow-model/research/books/concrete-semantics.pdf`
  (Nipkow–Klein). Link, do not copy.

Not found anywhere on this Mac by name, author metadata or full-text search (coordinator,
21:50): TAPL, ATTAPL, PFPL. If the owner drops a copy into `sources/` while you work, index it
(sha256, `pdftotext -layout`, the contents pages) and audit against it first.

## Produce

1. `sources/README.md`: one table row per source, vendored or linked (file or path; author,
   title, venue, year; DOI or URL; the terms it was downloaded under; pages; text copy; parse
   quality; the constructions of ours it is cited for, taken from Gemini's files,
   `docs/core/system-map.md` §9 and `docs/DESIGN-BASIS.md`'s literature marks); a second table
   `not vendored` (work, ISBN or DOI, what the owner supplies). `sources/fetch.sh` with one
   `curl -fL -o <file> <url>` line per new download so the folder is regenerable;
   `sources/SHA256SUMS` over the new files; `sources/text/<name>.txt` from `pdftotext -layout`.
2. `citations-audit.md`: one row per literature locator in Gemini's four files
   (`gemini/note.md`, `gemini/domain-model-spec.md`, `gemini/chapter-table.md`,
   `gemini/lemma-census.md`; find them with `rg -n "TAPL|ATTAPL|PFPL|PLF|pp\.|ch\."` and by
   author name): the sentence as written (file:line), the verified locator from the vendored
   text (chapter number, title, author, page span as the contents print them), the status word.
   First the flagged ones: ATTAPL chapters 3, 6, 7, 8 (Gemini: ch. 3 is Walker's substructural
   systems at "pp. 3–44", ch. 8 is Dreyer–Crary–Harper; Codex: ch. 3 is effect types and regions,
   ch. 8 is ML modules); TAPL chapters 13, 14, 19, 20 (titles and spans; whether a "Generic Java"
   chapter exists; Gemini's own ids say `tapl-19-nominal`, `tapl-20-recursive`); PFPL ch. 28 and
   39–41. For the books use the publisher-hosted contents PDFs (leads below). Then the papers,
   against the vendored texts.
3. At the end of `citations-audit.md`, the receipt: every URL tried with its result and sha256;
   what is `not vendored` and what the owner must supply; minutes spent; the evidence class of
   each section.

## Leads for what is missing (URLs as remembered by the coordinator; check each, none is a fact)

Books and free texts: TAPL contents `https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf`;
ATTAPL frontmatter `https://www.cis.upenn.edu/~bcpierce/attapl/frontmatter.pdf`; Harper, PFPL
2nd ed. online preview `https://www.cs.cmu.edu/~rwh/pfpl/2nded.pdf` (quote the author's terms in
the README); Software Foundations vol. 2 (PLF)
`https://softwarefoundations.cis.upenn.edu/plf-current/plf.tgz` (its `LICENSE` in the README;
`References.v` is the chapter we cite).

Papers likely missing: Plotkin & Pretnar, Handlers of algebraic effects (ESOP 2009)
`https://homepages.inf.ed.ac.uk/gdp/publications/Effect_Handlers.pdf`; Pretnar's tutorial (MFPS
2015) `https://www.eff-lang.org/handlers-tutorial.pdf`; Bauer & Pretnar, arXiv 1203.1539;
Petricek, Orchard, Mycroft, Coeffects (ICFP 2014, `https://tomasp.net/academic/papers/coeffects/`);
de Vilhena & Pottier, A separation logic for effect handlers (POPL 2021; HAL or
`https://cambium.inria.fr/~fpottier/publis/`); Rendel & Ostermann (Haskell 2010,
`https://www.informatik.uni-marburg.de/~rendel/unparse/`); Foster et al. (TOPLAS 2007,
`https://www.cis.upenn.edu/~bcpierce/papers/lenses-toplas-final.pdf`) unless S05 is it; Dolan &
Mycroft, MLsub (POPL 2017, `https://www.cl.cam.ac.uk/~sd601/papers/`); Castagna, arXiv
2111.03354; Leroy (CACM 2009) `https://xavierleroy.org/publi/compcert-CACM.pdf`; Lynch &
Vaandrager (1995) `https://ir.cwi.nl/pub/1393`; Meijer, Fokkinga, Paterson (FPCA 1991)
`https://research.utwente.nl/files/6142049/meijer91functional.pdf`; Johann & Ghani (TLCA 2007,
Strathclyde eprints); Ahmed's thesis (2004) `https://www.ccs.neu.edu/home/amal/ahmedsthesis.pdf`;
Wright & Felleisen (1994, author copy); Honda, Vasconcelos, Kubo (ESOP 1998, Vasconcelos's
page) unless S07 is it; Wadler, Propositions as sessions (ICFP 2012,
`https://homepages.inf.ed.ac.uk/wadler/`); Hancock & Setzer (CSL 2000). Books not free: Milner
1989, Sangiorgi 2012, Pierce's TAPL and ATTAPL full texts: `not vendored`.
