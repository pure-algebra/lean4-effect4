# The site's written copy

This folder holds the words of the documentation site that a writer adds by hand. Every
`make site` reads it, so a file saved here is on the next build of the site. The site is at
`https://effect4-docs.pages.dev`, and a local build at
`http://localhost:8783/.lake/gen/site/`.

The pages of evidence (claims, statuses, statements, the plan) are generated from the Lean tree.
This folder explains them in plain words. It never restates what the tree measures.

## Where a file goes

- `landing.md`: the site's first page.
- `guides/NN-name.md`: a guide, a page of its own under `/guides/name/`. The two digits order the
  guides; the page that lists them shows each guide's title and first paragraph.
- `concepts/ID.md`: what one concept means, shown on the concept's page under its summary.
  The ten ids are `store-typing`, `residual-program-typing`, `scope-lifetime-finalization`,
  `reactive-scheduling`, `exact-codecs`, `subtyping-algebra`, `initial-algebras-folds`,
  `context-requirements`, `host-session-protocol` and `translation-simulation`.
- `requirements/RN.md`: what one requirement asks, shown on its page under its summary. The ids
  are `R1` to `R14`.

A file for an id that no page has is refused by the build.

## The subset of Markdown

- The first line of text is `# Title`.
- `## Heading` opens a part, and `###` a part inside it. A heading may end in `{#key}`.
- A paragraph is a run of lines. A list is a run of lines that open with `- `.
- Code is a span in backticks, or a block between two lines of three backticks with a language.
- `[label](#key)` refers to a part of the same page; `[label](../semantics/)` links to a page.
- A status word in braces draws its mark: `{proved}`, `{modulo}`, `{goal}`, `{open}`,
  `{refuted}`, `{absent}`, `{assumed}`.

The build refuses, at its line: a table, a quotation, raw HTML, an image, and emphasis with `*`
or `_`. Write a list in place of a table and plain words in place of emphasis.

## How to write

The writing rules are `docs/core/controlled-english.md`, and a file here passes its check:

    python3 scripts/check-language.py --strict docs/site/FILE.md

- One idea per sentence: a description has at most 25 words, an instruction at most 20.
- The active voice; the present tense for facts; the imperative for a procedure.
- Each word of the dictionary (§3) in its one meaning, and never a word of its avoid column.
- Lead with the answer: a page's first paragraph says what the page is for, and the site shows it
  wherever it lists the page.

What a page may say:

- Explain meaning, purpose and how to read. Ground each fact in its source, cited: a core
  document (`docs/core/semantics.md`, `docs/core/system-map.md`, `docs/core/machine-state.md`), a
  decisions row, or a declaration by name in backticks.
- Never write a count, a status or a date that the tree measures. Link to the page that shows it.
- Never write that a claim holds. Name the claim, and link to its page.

Leave out the habits of machine-made prose:

- the words `welcome`, `simply`, `just`, `powerful`, `seamless`, `robust`, `leverage`, `delve`,
  `comprehensive`, `cutting-edge`, `unlock` and `journey`;
- the phrases `it is worth noting` and `in conclusion`;
- a question put to the reader, three adjectives in a row, an exclamation mark, an emoji.

## What a writer edits

Only the files of this folder. A writer never edits Lean, the Makefile, the registers or a
generated file. A writer never runs `lake` or `make`: the coordinator builds. A writer never
commits: the coordinator reads the folder at each landing and commits it.
