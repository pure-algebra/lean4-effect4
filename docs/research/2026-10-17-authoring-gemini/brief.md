# 2026-10-17 brief: the authoring slices, for the Gemini seat

Status: brief (history, not authority). Base: the commit that adds this file, on
`refactor/phase1-phase3`. The coordinator (Claude) reviews each commit and merges.

**The one thing to know first.** You implement the remaining slices of the authoring plan,
`docs/research/2026-10-17-proof-scout/README.md`. Land them in its order, one commit per slice, in your
own worktree. The plan says what each slice holds; this brief says how to work. At any stop rule
(§6), stop and hand back.

## 1. Where you work

- Worktree `/Users/pooks/Dev/lean4-effect4-gemini`, branch `gemini/authoring`. The coordinator makes it
  and builds it once before you start.
- Check the base first: `git log --oneline -1 -- docs/research/2026-10-17-authoring-gemini/brief.md`.
- Run every `lake` and `lean` command through the shared slot:
  `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh lake …`.
- Commit by named paths. Force-add files under `docs/research` with `git add -f`.
- Never push, merge, rebase, reset, stash or check out another branch.

## 2. Read first, in this order

1. `AGENTS.md`, whole: the trust rules, the proof-obligation rule and the working rules bind you.
2. The plan: §6 (module plan), §7.0 (landing cadence), §7.1 to §7.6 (the slices), §8, §9 and §12.
3. The plan's probes, `docs/research/2026-10-17-proof-scout/probes/<A|B|C|D|E>.lean`. They hold the
   definitions and the proved theorems you port.
4. The final review, `docs/research/2026-10-17-authoring-model-review/final-review.md`, and its
   controls `evidence/final/probes.lean` and `evidence/final/handles.lean`. Slices B, D and P flip them.
5. `docs/core/controlled-english.md` §2, for the receipt.

## 3. The slices

| Order | Slice | Plan section | New modules | Existing files edited | Not yet probed |
| --- | --- | --- | --- | --- | --- |
| 1 | A, the tool part | §7.1 | `Effect4.Laws.Program.SketchAdmission` | `Tools.Session`, `Tools.Query`, `Tools.Session.Snapshot` | none |
| 2 | B, inspection and atomic edits | §7.2 | `Effect4.Program.Typing.SourceDocument` and its law module | `Tools.Session`; `Test/Program/SessionToolControls.lean` and `Test/fixtures/session/requests.jsonl` move | none |
| 3 | E, persistent keyed live sessions | §7.5 | `Effect4.Run.LiveRecord`, `Effect4.Laws.Api.LiveRecord` | `Tools.Session` | none |
| 4 | P, the preview profile | §7.6 | `Effect4.Run.Preview`, `Effect4.Laws.Api.Preview` | `Tools.Session` | the `externalValue` lemma |
| 5 | C, catalogue and verdict cache | §7.3 | `Effect4.Program.Typing.CheckCache` and its law module | `Tools.Session` | none |
| 6 | D, fixed-base fills | §7.4 | `Effect4.Program.Typing.FillSet` and its law module | `Tools.Session` | the construction invariant |

Not yours:

- slice A′, which waits on the owner's decisions row 5;
- slices F to H;
- the semantics registry;
- `docs/core/decisions.md`.

The emission guard of slice A is already landed (`c43f8b3aa`).

## 4. How to land one slice

1. Port the probe's definitions and proofs into the modules that plan §6 names.
2. Open no new module with `module`: plan §6 gives the reason (decisions row 200).
3. Give each theorem a docstring placement: concept, proposed claim, reach, exclusions, consumer.
4. Take each placement from the plan's §3.7 node.
5. Iterate one file at a time: `lean-slot.sh lake env lean -DwarningAsError=true <file>`.
6. Wire each new module into its root, below the previous slice's line:
   - a core module into `src/Effect4.lean`, after `import Effect4.Schema.Prepare`;
   - a law module into `src/Effect4/Laws.lean`, after `import Effect4.Laws.Schema.DocumentJson`;
   - a battery into `Test/All.lean`, after `import Test.Api.TargetSupport`.
7. Put the slice's acceptance controls in one new battery under `Test/`, named for the slice.
8. Build narrowly: `lean-slot.sh lake build` of the new modules, the edited modules and their direct
   dependents.
9. Run `lean-slot.sh make batteries-touched BASE=<the slice's base commit> > <log> 2>&1`, and read the
   whole log.
10. Audit the axioms: a scratch Lean file, one `import` per line, then
    `#axiom_audit <every new and edited module>`.
11. The audit must read `within [propext, Quot.sound]`, with 0 planned goals.
12. Commit the slice by named paths. The message states the change, the checks and their results.
13. Add the slice's section to the receipt (§7).

No gate is owed: no slice here touches a gate input (plan §7.0).

## 5. Rules

- Edit no module that plan §7.0's table marks "nothing".
- Edit no other module with more than 20 dependents: stop instead. Count with
  `python3 docs/research/2026-10-17-proof-scout/probes/revdeps.py <Module>`.
- Add no constructor to an existing type: plan §7.0 says what one reaches.
- Edit no `src/Effect4/Api` module, no `Run.Kit` and no `Program.Compile`: they are gate inputs.
- Run none of `make build`, `make check*`, `lake build Test`, `Test.All` or a whole-tree build.
- Install nothing. Run `bun` with `--no-install` outside `ts/eff` and `harness/truth`.
- Write no `sorry`, `proof_goal`, `axiom`, `partial`, `unsafe`, `native_decide` or `implemented_by`.
- Write no `simp_all`, `first | …` or `try`. A hand-written `simp` is `simp only [...]`.
- Search with `aesop` in `src/Effect4/Laws/**`, as `AGENTS.md` says. Every warning is an error.
- Each battery line is a reader, a control or a finite evaluation. A battery restates no theorem.
- Change an existing battery's guard only as the plan says. Name each changed guard in the commit.
- A scout probe's red guard records the base. When a slice flips it, the battery states the new
  behaviour.
- Edit none of `docs/core`, `lakefile.toml`, `tools/ProofGraph/Registry.lean` or `generated/`.
- The shell is zsh: it does not split a variable into words. Spell lists out.
- Never send a Lean command's errors to `/dev/null`: a hook refuses it.

## 6. Stop rules

Stop, commit what is green, write the receipt and hand back when:

- a probed theorem needs a changed statement to port;
- an unprobed lemma (§3) does not close by a direct proof;
- a change needs an edit that §5 forbids;
- `#axiom_audit` names any other axiom;
- a battery outside the slice turns red, and the plan names no such move;
- the disk holds less than 8 GB free (`df -h /System/Volumes/Data`);
- a question needs the owner, such as the restoration policy beyond plan §7.5.

## 7. Hand-back

Write `docs/research/2026-10-17-authoring-gemini/receipt.md` and force-add it. In order:

1. The one thing the coordinator must know before merging.
2. The base and head commits.
3. Per slice:
   - its commit and changed files, from `git show --stat`;
   - each command with its result, copied from the log;
   - the `#axiom_audit` line;
   - each red control that flipped;
   - each proposed decisions row.
4. The open obligations, and what you did not run.

Check every file name, count and statement against the tree before you write it (`git show`, `grep`,
`wc`). Earlier receipts named files that did not exist. Run
`python3 scripts/check-language.py --strict` on the receipt.
