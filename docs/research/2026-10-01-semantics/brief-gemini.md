# Brief for Gemini: the language described by TAPL chapter (a read-only probe, 2026-10-01)

You are probing the Effect4 repository at `/Users/pooks/Dev/lean4-effect4` (branch
`refactor/phase1-phase3`), a Lean 4 reification of Effect's fiber machine in which programs are
typed first-order data, with a type language `Ty`, a program language `Eff`, a term language
`Term`, a value language `Store.Val`, a Schema data plane, a proof graph (`Effect4.Laws`) and a
ledger of declared obligations. The owner wants the language's semantics categorized and
organized formally against Benjamin Pierce's *Types and Programming Languages* (TAPL; with
*Advanced Topics in Types and Programming Languages* ch. 3 for effect types and ch. 8 for logical
relations), so that the proof obligations are bounded by the chapters' standard lemma lists, the
documentation becomes one consistent language description, and the proof graph takes its direction
from it. Your job is the analysis and the draft; the coordinator verifies and lands.

## Rules

- Read only. Edit no tracked file, run no `git add`, `git commit`, `git checkout`, `git merge`
  or `git reset`, change no branch. Write everything you produce under
  `docs/research/2026-10-01-semantics/gemini/` (that folder is untracked; the coordinator tracks
  what matters). Do not write under `/tmp`.
- You may read any file. Run no build and no generator (four merges are landing; one compiler
  at a time is the rule). If you need to check that a name exists, use `grep`; if you run
  anything TypeScript-related, it is tsgo 7 (`ts/eff/node_modules/@typescript/native-preview`)
  and you name its version; `tsc` and `typescript@5.x` are never run.
- Evidence words on every claim: **proved** (a kernel theorem you located, file:line, with its
  statement quoted), **tested** (a finite check someone ran, cited), **reading** (read in code or
  a document), **assumed** (not checked). Cite `file:line` for every theorem or definition you
  name, and `vendor/effect-4.0.0-rc.112/src/...:line` for every rc.112 behaviour you mention.
  Never name a theorem you have not found with `grep`.
- Plain words. No "sound", "complete", "equivalent", "preserves" or "fully reified" without
  the exact judgment, theorem, assumptions and remaining boundary. Nothing you write is a
  decision: the decisions register (`docs/core/decisions.md`) is the coordinator's; you propose
  rows, you do not rule them.

## Read first, in this order

1. `AGENTS.md` (the operating rules, the vocabulary bullets, the trust ceiling).
2. `docs/STATE.md` (what is true at HEAD; what is next; the owner's instruction of this evening).
3. `docs/research/2026-10-01-landing/status-2026-10-01-evening.md`, especially §7, §7b, §7c:
   the plan this brief serves (the chapter skeleton, the chapter attribute and census, the map's
   chapter section, the Schema-document form of the meta-documentation).
4. `docs/core/system-map.md`: §4–§5 (the sorts, the arrow kinds, the vocabulary tables), §8 (the
   requirements R1–R13), §9 (the glossary with literature marks), §10 (the five constructions,
   the stability criteria S1–S8, the outcomes).
5. `docs/core/decisions.md`, rows 111–184 (the open and ruled decisions of the typed state and
   the data wave; each row names its evidence).
6. `docs/DESIGN-BASIS.md` (the representation decisions DB-01…DB-17 with their literature marks),
   `docs/core/coherence-principle.md` (every traversal an algebra of one fold),
   `docs/core/traversal-census.md` §7.12 (the families of `Ty`), `docs/core/host-boundary.md`,
   `docs/core/machine-state.md`.
7. The code, by area: types `src/Effect4/Program/Ty.lean`, `Program/Typing/Rules.lean`,
   `Program/Typing/*.lean`, `Program/Checker.lean`, `Program/Refs.lean`; programs
   `src/Effect4/Program/*.lean` (`Eff`, the free monad), `Laws/Program/DenoteR.lean` (the
   denotation), `Laws/Program/InterpR.lean`, `Laws/Program/Simulation/*.lean`; the typed state
   `src/Effect4/Laws/Program/Typed/{Membership,Residual,Admission,Assembly,Adequacy,Contracts,
   Sources,World,Validity}.lean`, `Typed/Commands/*.lean`, `Typed/Edits.lean`; the machine
   `src/Effect4/Machine/*.lean`, `Laws/Machine/*.lean`; values `src/Effect4/Store/**`; the Schema
   plane `src/Effect4/Schema/*.lean`, `Laws/Schema/*.lean`; the ledger commands
   `src/Effect4/Laws/Auto/Obligations.lean`, `Laws/Auto/Census.lean`; the architecture map's
   inputs `tools/Tools/ArchitectureRoles.lean`, `tools/Tools/Architecture.lean`.
8. The probes' notes under `docs/research/2026-10-01-type-language-probe/{T,R,S,P,Q,U}/note.md`
   and the receipts under `docs/research/2026-10-01-landing/receipt-*.md` for what landed today
   and what is open (M5's denotation lemma, M6's eight refuted goals, M7's route).

## Produce (one note, `gemini/note.md`, with tables as separate files if large)

1. **The chapter table.** One row per chapter of the language description, in the order of the
   status note's §7: id (`tapl-03-evaluation`, `tapl-08-typed-arith`, `tapl-09-stlc-cut`,
   `tapl-11-extensions`, `tapl-13-references`, `tapl-14-exceptions`, `tapl-15-subtyping`,
   `tapl-16-metatheory-subtyping`, `tapl-19-nominal`, `tapl-20-recursive`, `tapl-22-reconstruction`,
   `tapl-23-prenex`, `attapl-03-effects`, `attapl-08-logical-relations`, `boundary-embeddings`,
   `initial-algebra`, `machine-concurrency`; add or split as the book and the tree justify, and
   say why), the book chapter and section, the title, the judgment(s) of ours it instantiates
   (name, file:line, the statement in words), the theorems (name, file:line, proved/open), the
   ledger scopes (`M3bWorld`, `M3bAdequacy`, `M3bAssembly`, `M6Ledger`, `M6Edits`, `M7`, and the
   others the tree has: find them with `grep -rn "#typed_state_obligations\|#obligation_audit"`),
   the decisions rows it cross-indexes, the modules it covers. Where the tree differs from the
   book by design, say so as the cut: no function values (row 163), first-order references with
   worlds as store typings, prenex templates only, effect rows, the fiber machine instead of a
   term rewriting relation.
2. **The standard lemma list per chapter, with status.** For each chapter the lemmas TAPL (or
   ATTAPL) proves for that system: inversion, canonical forms, weakening, substitution,
   permutation, progress, preservation, uniqueness of types, decidability, transitivity and
   antisymmetry of subtyping, soundness and completeness of the algorithmic relation, store
   typing monotonicity, and the rest as the chapter has them. For each: present by name
   (file:line), open as a declared goal (the ledger line), or absent, in which case say whether
   it is needed here (a proposed row) or does not apply (why). This list is the bound the owner
   wants: an obligation off every chapter's list is a design finding, not a theorem to prove.
3. **The annotation schema.** The documentation-class annotation keys for the chapter tags, in
   rc.112 Schema terms (an annotations record: key, value type, example), following the
   principle of decisions row 179 (a documentation annotation changes no decoding and is erased
   by the normaliser): at least `effect4/chapter`, `effect4/lemma`, `effect4/status`,
   `effect4/row`, `effect4/theorem`; say which of rc.112's own annotation keys
   (`title`, `description`, `documentation`, `examples`, `identifier`, …) the meta-documentation
   reuses and which are ours. Give the `Representation` shape of one chapter's document node and
   one theorem's node as they would be emitted (JSON), so the emitter can be written from it.
4. **The tagging plan.** Which modules map to which chapter by default (the chapter attribute's
   module-level default), and the declarations that need an explicit tag because their module
   spans two chapters; the count of theorems in the Laws graph you expect to be left unplaced,
   with the list if small.
5. **The prose draft of `docs/core/semantics.md`**, by chapter: what the judgment says in words,
   what the chapter demands, what our cut is, the theorems that instantiate it (names only, no
   proofs), the open obligations and the rows they wait on. Short paragraphs; one owner per fact
   (nothing that `system-map.md` or `decisions.md` already owns is restated; point to it).
6. **Gaps and misplacements.** Anything the tree claims that the chapter does not support, any
   chapter the tree needs that nobody named, any obligation named in two chapters, any theorem
   whose statement is weaker than the chapter's standard lemma (say exactly how). Each as a
   proposed decisions row with the evidence words.

## What not to do

Do not propose changing a definition or a statement in the tree; do not propose new theorems
beyond a chapter's lemma list; do not restate decisions; do not write prose that duplicates the
system map. If you find a theorem whose name suggests more than its statement delivers, quote the
statement and say what it delivers.

Write incrementally (the note's head first: the one thing you found, then the tables), so that
a partial result is useful, and end with a receipt: what you read, what you ran (if anything),
and the evidence class of every section.
