# Brief for Gemini, part three: prove what the report says is open (2026-10-01, late)

You now implement and land Lean proofs. The documentation is in and the tree is merged and green;
you build off it. The order of work below is the record's (decisions rows, receipts D2 and D3,
brief D5), and every slice ends with the generated report showing the change.

## Base, worktree, rules

- **Base:** the head of `refactor/phase1-phase3` that contains this brief (its parent is
  `d6e5862b`). It holds every merge of 2026-10-01 (seats D3, D4, D2, W1, W2, J2; Codex's
  metaprogramming branch), and the sweep passes there: `lake build` 758 jobs, the trust gate 536
  modules and 75 032 declarations at the policy; `python3 scripts/check-semantics.py` PASS.
- **Worktree:** `/Users/pooks/Dev/lean4-effect4-gemini`, branch `gemini/proofs`, created from the
  base (`git worktree add -b gemini/proofs /Users/pooks/Dev/lean4-effect4-gemini <base>`). Clone the
  build cache so nothing rebuilds from zero: `cp -c -R /Users/pooks/Dev/lean4-effect4/.lake
  /Users/pooks/Dev/lean4-effect4-gemini/` (APFS clone, copy on write). A worktree has no
  `docs/research` (2 GB, gitignored); read this folder's files at their absolute paths in the main
  checkout, and write your receipt there.
- **AGENTS.md, all of it**, and in particular: no `sorry`, `partial`, `unsafe`, `native_decide`,
  `axiom`, `extern`, `implemented_by`; every warning is an error; in a new or touched proof no
  `simp_all`, no `first | …`, no `try`; a hand `simp` is `simp only [...]`; proof search is
  `aesop` with the named banks (`src/Effect4/Laws/Auto/RuleSets.lean`), induction hypotheses
  introduced by hand and handed to the call; take a proof's case list from the definition
  (`fun_induction`/`fun_cases`); no case analysis on `Ty` outside `Typed/Membership.lean`;
  `#print axioms` of every new theorem at or below `[propext, Quot.sound]`.
- **One `lake` at a time** in your worktree; this machine has 16 GB. Narrow builds before each
  commit: `lake build <the modules you touched and their direct dependents>`, `lake env lean
  -DwarningAsError=true <file>` for a test. No `make check`, `make check-full`, `make gen` or full
  `lake build`: the coordinator's sweep at the merge.
- **Commits** by explicit paths (`git add <path> …`, never `-A`); read `git status` first. You
  never edit `docs/core/decisions.md`, `Test/Counterexamples/REGISTER.md`, `lakefile.toml`, or the
  axiom gate; you propose rows and register lines in your receipt. A new module goes into the
  root import at the line after the module it extends (`src/Effect4/Laws.lean`, `Test/All.lean`),
  named in the commit message.
- **Never weaken a statement.** A goal you find false as stated is a finding: a kernel-checked
  refutation in a test file, the proposed repair as a decisions row in the receipt, the goal left
  open with its exact obstacle. This is how seats D3 and D2 found rows 134, 170, 175, 176 and 183.

## The loop, every slice

1. Pick the next item below. Find its claim in `generated/semantics.md` (the status and the
   exact printed statement), its concept in `docs/core/semantics.md` (what the property means,
   the literature, the cuts), and the decisions rows the concept cites.
2. Prove it under the rules. A ledger goal closes through the ledger: `#obligation_proved <goal>
   := <term>` or the scope's `#typed_state_obligations … ceiling n using aesop …`, and its
   `#proof_wanted` marker is removed in the same commit (the ledger refuses a proved goal that
   still has a placeholder, and a goal with neither); lower the scope's ceiling by the goals you
   closed.
3. If a claim's pointer changes (a new witness, an `absent` claim now proved) edit
   `tools/Tools/SemanticsRegistry.lean`; then regenerate and check:
   `python3 scripts/check-semantics.py --generate generated` and `python3 scripts/check-semantics.py`
   (they refuse a stale artifact and print the `lake build` to run first). The regenerated
   `generated/semantics.{json,md}` go into the same commit as the proof: the report's diff is the
   completion evidence.
4. If the property's text in `docs/core/semantics.md` changes, edit it there (never a status, never
   a hand-typed statement; a declaration named with its `path:line`), and run
   `python3 /Users/pooks/Dev/lean4-effect4/docs/research/2026-10-01-semantics/check-gemini-drafts.py docs/core/semantics.md`
   from your worktree's root: it must print PASS.
5. Commit, then the next item. Stop at a coherent place (a slice that builds) rather than mid-proof.

## The order of work

**M5, the denotation lemma (`denote-typed`, `M3bAssembly.denoteR_typed`).** Seat D2 proved arm
groups 1–3 (`src/Effect4/Laws/Program/Typed/Denotation.lean`) and wrote the rest as plans with
their obstacles: `docs/research/2026-10-01-landing/receipt-D2.md`, "What is owed, with the exact
obstacles". In order:

1. `M3bAssembly.evalTerm_fits`: D2's receipt names the adapter, `fun table _ _ _ _ _ _ hty henv hev
   => evalTerm_fits_native table henv hty hev` (the statement matches `TermFits` up to the order of
   two premises). The smallest slice; it also checks your loop end to end.
2. Group 4 (store rows, services, `exit`): no obstacle found by reading. D2's receipt lists every
   lemma with its proof plan (`fits_refTy_inv`, `syncRow_typed`, the host row through
   `fits_instantiate` and the template bridge already in Membership, `service_arm`,
   `provideService_arm`, `inlineYield_typed`, `exit_arm`). The draft D2 mentions was never committed;
   work from the receipt's plan.
3. Group 6 (the assembly) for programs without a layer: `denoteR_typed` by induction on fuel
   (zero by `denoteR_zero_typed`; each arm with `ChildDenotes` from the hypothesis), landed as D2
   planned: `denotesTyped_of_provideLayer : ProvideLayerArm root → DenotesTyped root` (`ProvideLayerArm`
   is yours to define: the layer family's arm stated as a hypothesis; it does not exist yet) and the named
   open goal `M3bAssembly.denoteR_typed_provideLayer`, so M5 holds for layer-free programs and the
   layer family stays one named goal. Then the controls D2 lists flip (the typed corpus at a starting
   world, `AwaitLoad.loadsTyped`, the CE-021/022 flips) and `M3bAssembly.typedState_load` follows
   from `loadsTyped_of_denotesTyped`.
4. Group 5 (the layer family) is **blocked on the owner**: decisions row 176 (the type of a built
   layer context). Do not start it; if you meet it, write the measurement row 176 asks for.

**M6, the step goals (`step-loop-preserves`, `step-deliver-preserves` and the ledger's other seven
open goals in `M6Ledger`, plus `M6Edits.clockSome`).** These are false as stated until five
clauses are added to the typed state: decisions row 134 (a)–(e), ruled. The work is written in full
as seat D5's brief, `docs/research/2026-10-01-landing/brief-D5.md`, which was to be dispatched once
D4 and D2 merged; they have. Take it as written, from its step 1 (the five clauses, each where seat
D3 named it, with the field census of decisions row 181 beside them), through the eight goals
re-proved, M6b and M6c, to row 180 (a), which closes `M7.exitHandles_valid`. Its rules are this
brief's rules; its base is this brief's base.

**M7 (`m7-exits-typed`, `m7-stores-typed`, `m7-never-halts`).** After M5 and M6 close their
premises, through `m7_of_ledger` (proved: M7 from the ledger's hypotheses). Plan it from the
docstrings at `Assembly.lean`'s `M7` namespace when you get there; nothing here is ready before.

**Not yours, and why:** row 183 (host adequacy at a template row: the coordinator's repair is
recommended; group 4's host-row arm closes meanwhile through the template bridge, as D2 did); row
184 (the gate's exact admission of the `semantics` attribute's handle, for the owner's ratification);
the fairness claim (`fair-scheduling`, R12) and the two planned data-wave claims (`record-codec-layout`,
`record-app-subtyping`), which are the data path's (seats W4, W5).

## One small tooling slice, any time

The 14 paper keys in the registry (`Ahmed2004`, `LynchVaandrager1995`, …) resolve to nothing: the
source index has no key column. Add a `Key` column to
`docs/research/2026-10-01-semantics/sources/README.md` (both tables and the not-vendored table;
`TAPL`, `ATTAPL`, `PFPL`, `PLF` included; force-added, it is tracked), make the producer refuse a
`work` it cannot find there (`tools/Tools/Semantics.lean`, beside the relation check; the README goes
into `SEMANTICS_INPUTS` and the script's `INPUTS`), and add one refusal control to
`tools/Drivers/SemanticsControls.lean`. A key in the not-vendored table stays legal, and the claim's
relation then reads as cited, not verified.

## The receipt

`/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-01-semantics/gemini/receipt-proofs.md`,
written as you go. AGENTS.md's format: first the one thing the coordinator must know before
merging; base and head; the commits, each with its files and the narrow builds it ran (command, exit,
seconds); `#print axioms` of every theorem you added; the report's status counts before and after
each slice (`43 proved, 7 wanted, 5 absent, 1 refuted, 1 assumed` at the base); the ledger's counts
per scope; every finding with its kernel-checked control and the proposed decisions row; what is
open, with its exact obstacle. Nothing in it is a statement you did not run or read: evidence words
as in the earlier briefs (proved, tested, reading, assumed).
