# Gemini: a consolidation and review round in Effect4 (2026-10-13)

Status: prompt (history, not authority). From the coordinator, for Gemini 4 Argon. Worktree
`~/Dev/lean4-effect4-gemini`, branch `gemini/consolidation`, base: the coordinator's head when the
worktree was made.

## A word before you start

Treat this the way I would treat a doctoral student's first serious term in my group. You are
capable, and that is exactly why I will not accept work that only looks finished.

I have read many reviews that list fifty "issues" and fix none of them. I do not want that from
you. I want fewer findings, each one true, each with its evidence, and the ones that matter fixed,
built and audited. Three consolidations that land cleanly are worth more to me than fifteen
proposals. If you are unsure, check. If you cannot check, say so plainly and move on.

Read before you write. This tree has strict rules, and they exist because each one cost someone a
day. When a rule surprises you, assume it is right until you can show me otherwise.

## What to read first

1. `AGENTS.md` in your worktree, in full: the trust rules, the proof rules, the writing rules.
2. `docs/core/controlled-english.md` §2: every Markdown file you write follows it.
3. `docs/STATE.md`, item 0000 (the vertical slice), and decisions row 378 in
   `docs/core/decisions.md`: what the group is building now, and why.
4. `docs/research/2026-10-13-seat-address-receipt.md`, the section "Duplicates found and not
   gathered". It is your main assignment.

## Part 1: consolidation, the main job

Seat ADDRESS measured seven families of duplicated declarations in the law graph and left them,
for two reasons. Another seat owned some of the files then, and that seat has finished. The
rebuilds were too wide for six seats sharing two build slots. Now three seats run, and the
families sit outside their files. So these are yours.

For each family:

- **Verify the claim before you act.** The table is a lead, not a fact. An earlier census in this
  group named lemmas that did not exist. Confirm that the home and each copy state what the table
  says, and count their users yourself.
- **Keep one home.** Rewrite each copy's users to name the home, then delete the copy. Where the
  copy is a special case, its users apply the home at the instance; they do not keep a wrapper.
- **Stop where equality is not definitional.** The table already warns about one family: `Path.lt`
  and `Field.ltKey` agree only extensionally, so `rfl` fails. Do not force it with a pile of
  `simp`. Decide whether one should become the other's definition, write the reason in your
  receipt, and land it only if the proofs stay short.
- **Order by cost.** The dead lemmas and the moves inside one module first. The edit of
  `src/Effect4/Program/Refs.lean` (a core module) last, because it rebuilds the most.
- **One commit per family**, with what you verified, what you built, and the axiom audit, in the
  commit message.

## Part 2: review of today's landings

The group landed the second slice of the vertical slice today: the application emitted as an
Effect service, its rows as services, and the first banked module. The merges on
`refactor/phase1-phase3` are `6f32c88cd`, `9cff5c7cf`, `0c1760dd9`, `45761a86a`, `c4f56a879`,
`23f95aac2`, `d2d10b383`, `f463ee53b` and `60f10bc4c`. Their receipts are under `docs/research/`,
named `2026-10-13-seat-{svc,rows,bank}-receipt.md`.

Today I caught three duplicates at merge time. There were two decoders of a key's text, two readers
of a requirement row, and the same operation-renaming fold written twice. I want to know what I
missed. Look for:

- a definition or lemma that already exists elsewhere in the tree, under another name;
- a traversal written by hand where a fold or a generated function exists (AGENTS.md, the
  vocabulary);
- two folds proved to agree pairwise, where the agreement of their algebras would do;
- a docstring that says "sound", "complete", "equivalent" or "exact" without naming the theorem,
  its observation and its fragment;
- a helper lemma in the wrong module. Seat BANK named three, in its receipt's open obligations.

A finding is a declaration's name, its path, and the evidence: the other declaration, the
`#check` or the proof that shows they coincide, or the sentence and the theorem it lacks. A
finding without evidence is gossip. Leave it out. Fix what lies outside the files fenced below. Rank
the rest, and give me the fix you would make.

## The fence

Three seats are working, and Codex works on the PC. Do not edit their files:

- seat SVC: `src/Effect4/Codegen/Checked.lean`,
  `src/Effect4/Program/Authoring/ApplicationService.lean`,
  `Test/Dogfood/Scenario/TodoService.lean`, `harness/truth/service/`,
  `scripts/check-host-protocol.py`;
- seat READ: `src/Effect4/Codegen/{Read,Classes,Types}.lean`,
  `src/Effect4/Laws/Api/ModuleReadable.lean`, `ts/eff/read.ts`;
- seat IMPOSE: `src/Effect4/Program/Authoring.lean`, `src/Effect4/Program/Authoring/Application.lean`,
  `src/Effect4/Codegen/Print.lean`, `Test/Dogfood/Scenario/Todo.lean`,
  `src/Effect4/Library/Ref/`, `src/Effect4/Laws/Library/Ref/`, `src/Effect4/Laws/Program/Block.lean`;
- Codex: `tools/Tools/View/`, `tools/view/`;
- the coordinator's: `lakefile.toml`, `docs/core/decisions.md`, the root imports except by
  appending at the end.

A finding in a fenced file goes into your receipt for me to route.

## How to work

- Build only through `~/Dev/lean4-effect4/scratch/lean-slot.sh lake build <Module>`. It shares two
  build slots with the seats. Never run a bare `lake build`, and never `lake build Test`. For one
  test file, run `~/Dev/lean4-effect4/scratch/lean-slot.sh lake env lean <file>`.
- A narrow build is the modules you edited and their direct importers.
  `grep -rln "import <Module>$" src Test tools` finds those importers.
- Audit every module you touch with `#axiom_audit` (`tools/ProofGraph/AxiomAudit.lean`): put it in a
  scratch file under `scratch/` and run it with `lake env lean`. Expect
  `[propext, Quot.sound]` and nothing more.
- Proofs follow AGENTS.md:
  - aesop and its banks where they close, and `simp only [...]` otherwise;
  - never `simp_all`, `first` or `try`;
  - no `sorry`, `partial`, `native_decide` or `axiom`.

  Every warning is an error.
- Commit on `gemini/consolidation` by named paths (`git add <path>`; research notes need
  `git add -f`). Never `git add -A`, never push, never rewrite a commit you did not make.
- No downloads, no bun, no npm. Never `2>/dev/null`.

## What I expect back

A receipt at `docs/research/2026-10-13-gemini-consolidation/README.md`, force-added and committed.
It starts with the one thing I must know before I merge. Then, in this order:

1. each family: verified or refuted, landed or stopped, its commit, the users rewritten, the
   build and the audit;
2. the review's findings, ranked, each with its evidence, marked fixed (with the commit) or
   routed (with the fix you propose);
3. what you could not check, and why.

Write it in the house style, and keep it short. When you are done, stop and tell me. I will read
every commit.
