#!/usr/bin/env python3
"""Promote Gemini's reviewed draft (gemini/semantics-v1.md) to docs/core/semantics.md (coordinator,
2026-10-01). Kept: the overview, each concept's parts 1-4, the glossary, the bounds. Dropped: each
concept's part 5 (what is next belongs to docs/STATE.md and the registers) and every hand-written
status phrase (the generated report owns status). Links become `path:line`, the authorities' form."""
import pathlib, re

SRC = pathlib.Path('docs/research/2026-10-01-semantics/gemini/semantics-v1.md')
DST = pathlib.Path('docs/core/semantics.md')
t = SRC.read_text()

HEADER = """# Semantics: the language's judgments, their literature and their obligations

The authority for what Effect4's semantic judgments mean, which literature each adopts or adapts,
where the language cuts away from that literature, and which properties each must have. Ten
concepts, each in four parts: what the literature defines; our adaptation, assumptions and
exclusions; the definition and judgment in the tree; the required properties.

What this document does not own, and who does:

- **Status.** Whether a property is proved, wanted, refuted, absent or assumed is measured, never
  written here: `generated/semantics.json` and `generated/semantics.md` (`make gen-semantics`;
  `docs/GENERATED.md`, group `semantics`), produced from the registry
  `tools/Tools/SemanticsRegistry.lean` and the loaded environment, every status derived through
  `ProofRef.validate` and `ProofGraph.check`.
- **Decisions.** `docs/core/decisions.md`; the cuts below cite its rows by number.
- **The goal, the sorts, the arrows and the requirements.** `docs/core/system-map.md`.
- **What is next.** `docs/STATE.md`.
- **Counterexamples.** `Test/Counterexamples/REGISTER.md`.
- **The sources.** `docs/research/2026-10-01-semantics/sources/README.md` (vendored with
  checksums) and `docs/research/2026-10-01-semantics/citations-audit.md` (every locator read off a
  vendored page). A theorem, rule or in-section page number of TAPL or ATTAPL is not verified
  until the owner's copies are vendored; those references are marked as cited.

Drafted by Gemini from the semantics pass of 2026-10-01 (concept-first after Codex's review),
reviewed against the tree by the coordinator and checked mechanically (every declaration named
with a `path:line` locator is declared within three lines of it:
`python3 docs/research/2026-10-01-semantics/check-gemini-drafts.py docs/core/semantics.md`).

---

"""
# the preamble up to the first horizontal rule is replaced
first_rule = t.index('\n---\n')
t = HEADER + t[first_rule + len('\n---\n'):].lstrip('\n')
# part 5 of every concept, from its heading to the next concept or section heading
t = re.sub(r'#### 5\. Next Bounded Coding Task.*?(?=\n### |\n## )', '', t, flags=re.S)
# hand-written status phrases at the end of a property
t = re.sub(r'\s*(Proved witness(?:es)?|Required work|Required absent obligations?|Planned feature claims?|Open ledger goals?|Refuted claims?|External assumptions?)\.(?=\s*$)', '', t, flags=re.M)
# the property lists name each property and its declaration; the exact statement is printed
# from the environment in generated/semantics.md, never written here
out, part4 = [], False
for line in t.split('\n'):
    if line.startswith('#### 4. Required Properties'):
        part4 = True
    elif line.startswith(('#### ', '### ', '## ')):
        part4 = False
    if part4:
        line = re.sub(r'`[^`]*(?:→|↔|∀|∃|=)[^`]*`\s*(?=\(\[`)', '', line)
        line = re.sub(r':\s*$', '.', line) if line.rstrip().endswith(':') and line.lstrip().startswith('- **') else line
    out.append(line)
t = '\n'.join(out)
t = t.replace('explicit compatibility lemmas (`seq_typed`, `onFailure_typed`).',
              'explicit compatibility lemmas: `guardBind_typed`, the general form, and its shapes `seqGuard_typed`\n'
              '  (`onSuccess`), `catchGuard_typed` (`onFailure`), `allGuard_typed` (`all`, `onExit`), `onExit_typed`\n'
              '  and `seq_typed` (seat D2, `src/Effect4/Laws/Program/Typed/Seq.lean`).')
t = t.replace('Compatibility lemma for error recovery bracket `onFailure`\n  (decisions row 148, M5).',
              'Compatibility lemma for the error recovery bracket `onFailure` (decisions row 148), proved by\n'
              '  `catchGuard_typed` (`src/Effect4/Laws/Program/Typed/Seq.lean:123`).')
# links: [`name`](file:///path#Lnn) -> `name` (`path:nn`); [text](file:///path#Lnn) -> `path:nn`
t = re.sub(r'\[`([^`]+)`\]\(file:///(?:Users/pooks/Dev/lean4-effect4/)?([^#)\s]+)#L(\d+)(?:-L\d+)?\)', r'`\1` (`\2:\3`)', t)
t = re.sub(r'\[[^\]]*\]\(file:///(?:Users/pooks/Dev/lean4-effect4/)?([^#)\s]+)#L(\d+)(?:-L\d+)?\)', r'`\1:\2`', t)
t = re.sub(r'\[([^\]]*)\]\(file:///(?:Users/pooks/Dev/lean4-effect4/)?([^)\s]+)\)', r'\1 (`\2`)', t)
# the axiom sentence, stated as the policy actually is
t = t.replace('All theorems cited in this document are held to the strict repository axiom\n'
              '   ceiling: `[propext, Quot.sound]`. Any use of `Classical.choice` is rejected by the axiom gate\n'
              '   (`Test/Audit/AxiomGate.lean`).',
              'Every theorem the registry cites is checked by the producer at `[propext,\n'
              '   Quot.sound]`; the whole-library gate (`Test/Audit/AxiomGate.lean`) holds every declaration\n'
              '   there too, except the rendering and instrumentation modules it admits by name.')
t = t.replace('The checked executable report currently covers strictly residual program typing (the 4-claim\n'
              'slice); it does not yet execute checks for the other nine concepts in Lean. Those nine concepts\n'
              'are authored registry entries awaiting adoption.',
              'The generated report checks every concept\'s selected claims in the loaded environment. A\n'
              'concept\'s claims are a selection, not a complete inventory: an owed property is made visible as\n'
              'an `absent` claim, and a ledger goal the registry does not name is not in the report.')
t = t.replace('(D5 / decisions row 180)', '(seat D5; decisions rows 134, 139 and 181)')
t = re.sub(r'\n{3,}', '\n\n', t)
DST.write_text(t)
print(f'{DST}: {len(t.splitlines())} lines; part 5 sections left: {t.count("Next Bounded Coding Task")}; '
      f'file:/// links left: {t.count("file:///")}; status phrases left: '
      f'{len(re.findall(r"Proved witness|Open ledger goal|Refuted claim", t))}')
