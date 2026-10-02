# Review of what Codex and Gemini produced (coordinator, 2026-10-01 ~22:30; review only, nothing merged)

Codex: branch `codex/metaprogramming` at `d595eda3`, eleven commits on `8c9be258`, worktree
`~/.codex/worktrees/metaprogramming-audit/lean4-effect4`, still working when this was written.
Gemini: three untracked files under `docs/research/2026-10-01-semantics/gemini/` (21:51–21:53),
no branch. Everything below was read from the branch (`git show`, `git diff`) or the files; I ran
no build (Codex's worktree is live; one compiler at a time) and changed nothing.

## The one thing to know first

HEAD does not build the Laws root. Codex's receipt records that a full `Effect4.Laws` preparation
at `8c9be258` fails in `src/Effect4/Laws/Program/Typed/Commands/Bookkeeping.lean`
(ScopeStateOk/FinNameOk mismatches: D4's merge made `ScopeStateOk` a pair and Bookkeeping was not
updated). The repair is the owner's uncommitted edit to that file in the main checkout
(`finalizerTyped_mono … , finNameOk_world …` pairs, `scopeStateOk_typed`). Until it lands,
"roots build at the merge" cannot be met for any branch, and the gate entry Codex added is
unverified. Commit the repair first.

## Codex: what the branch is

Two things. (1) The metaprogramming audit and three narrow cleanups, as briefed. (2) The semantics
report's first slice C1–C5, which part one of Gemini's brief described; Codex's `plan.md` says the
owner authorized it after the two Sol reviews. Fine; it voids Gemini's part one and leaves part two.

Checked against the brief and `AGENTS.md` (reading):

- `readGoal` moved from `Laws/Auto/Obligations.lean` to `ProofGraph.readGoal` (`Ledger.lean`);
  the ceiling filter written once as `ProofGraph.disallowedAxioms` (`Proof.lean`), used by Ledger,
  Proof and Search. Messages unchanged.
- `Laws/Machine/Handles.lean:1114-1184`: the five hand-copied simp-argument grammars replaced by
  `Lean.Parser.Tactic.simpArg,*`; bodies untouched.
- `Program/Authoring/Sugar.lean`: `getDoSeqElems` delegates to `Lean.Parser.Term.getDoElems`;
  `unnestElems` matches a typed `(doElem| do $seq:doSeq)` quotation instead of `getKind` strings.
  Needs `import Lean.Parser.Do` in the runtime root, released by the DI-18 re-ruling.
- No theorem statement changed; the fallback macros (A3) untouched; no unexpander (A5); no module
  moved (A7). The three coordinator-owned choices stay choices.
- The slice: `Laws/Auto/Semantics.lean` (a parametric attribute under the non-reserved keyword
  `&"semantics"`, one concept per declaration, current module only; `#semantics_census`;
  `semanticsTheorems` excluding noise, goal markers and their `.checked` witnesses);
  `tools/Tools/SemanticsRegistry.lean` with spec v3's types and the four claims (the absent one is
  the `onFailure` lemma, as ruled; `denoteR_typed` carries `contestedBy` CE-020/021/022; the
  refutation cites `E4-TYPED-CE-030`); cuts 163 and 117; `tools/Tools/Semantics.lean` deriving
  every status through `ProofRef.validate`, `ProofGraph.readGoal` and `ProofGraph.check`, refusing
  a RETIRED id, a duplicate contest, a disallowed axiom, an unloaded module, a blank reason;
  anchors exactly where spec v3 named them (Laws root after `Auto.Obligations`, `Test/All.lean`
  after `Audit.Obligations`, the gate's `auditImplementationModules` after `AnswerGate`);
  `Test/Audit/SemanticsCensus.lean` with `#guard_msgs` positives and refusals; `ts/eff/semantics.ts`
  and `check-semantics.ts`, 50 reader tests; `scripts/check-semantics.py`; Makefile and
  `docs/GENERATED.md` rows.
- `generated/semantics.json` and `.md`: no commit, wall clock or machine path in the bytes (grep);
  statements printed from the environment with `pp.fullNames`. The printed `seq_typed` carries the
  world, `leHost`, the `Fits` premise and `root`, the four things v2's hand-typed judgment dropped.
  The design does what it was for.
- Codex's receipt: narrow builds of its five targets exit 0; `make gen-semantics` 41 s and
  `make check-semantics` 114 s pass; tsgo 7.0.0-dev.20260629.1, bun 1.4.2; `close_typed` and
  `seq_typed` stay at `[propext, Quot.sound]`; the attribute module reaches `Classical.choice`
  (meta code, admitted by the module list, as spec §4.1 said). Tested by Codex, not by me.

Findings, in order:

1. **`FORCE` on both make targets** (`$(GEN)/semantics: FORCE …`, `$(CHK)/semantics: FORCE …`).
   Every `make gen` reruns the producer and every `make check-full` the 114 s check whether or
   not an input changed. The owner's rule: gates are incremental. Codex's reason (an imported
   source edit must not hide behind an unchanged Lake trace) is met by `SEMANTICS_INPUTS` and
   `SEMANTICS_TRACES`, which the rules already list, plus the script's own hash preflight. Drop
   `FORCE` before merge.
2. **The placement universe is two modules.** "unplaced: 0" is relative to `Residual.lean` and
   `Seq.lean` (2 tagged, 36 inherited). The report says so in words; it is not yet §7b's coverage
   number over the Laws graph. Right for the slice; say it when the number is quoted.
3. **A second noise filter.** `semanticsNoise` copies `Tools.Architecture.isNoise` because the
   executable cannot be imported. Codex's own A4 argued the censuses' universes differ on purpose
   and should not share one `isNoise`; this one is an exact copy, so it is the first candidate for
   the shared helper module when A4's home is chosen.
4. **"At the ceiling: yes" on a wanted goal** reads as if the goal were proved. It means the marker
   and placeholder are within the ceiling. Rename the column "evidence at the ceiling".
5. Codex's coherence review item 3 (an out-of-ceiling marker beside clean evidence) is resolved in
   the final driver: `declaration` refuses a disallowed axiom and the renderer prints the measured
   Boolean.
6. **A3 measured, ruling owed by the owner** (`evidence-A3/RESULTS.md`): all six `hops_leaf` arms
   fire; `hops_observers` arm 2, `hops_loop` arm 1 and `queue_hops` arm 1 never fire at the nine
   call sites. Proposal: keep `hops_leaf`, `hops_cmd`, `queue_hops` as named selectors (banks when
   ruled), inline `hops_observers`, an explicit `drive_extends` hop for `hops_loop`. A5: no
   unexpander (a prototype changed one of two fixtures in TypedProgBindRed, little value). A6:
   the pinned compiler has no `ToExpr Expr`; `quoteClosed` stays. A7: 475 project modules
   measured; functional ownership, no file moves without a dependency graph.
7. Codex wrote `codex-implementation/brief-gemini-next.md`, a brief for Gemini. It agrees in
   substance with `brief-gemini-documentation.md` (fix the registry, reconcile prose); Gemini
   follows the coordinator's brief, with Codex's REG-1…REG-5 as the concrete checklist, which
   Gemini has already applied (below).

## Gemini: the three files

`registry-content.lean` (520 lines). Imports only `Lean` (REG-5 fixed). Redeclares the model
types; they match Codex's `SemanticsRegistry.lean` field for field, so only the `registry` value
slots in. Mechanical checks tonight: 74 distinct qualified names, all 74 resolve by leaf-name grep
(the fifteen of REG-1 are fixed; the producer is the real check); 12 register ids, all in
`REGISTER.md`; 19 decisions rows cited as cuts, all exist; 17 `work` keys: `TAPL`, `ATTAPL`,
`PFPL` resolve, the 14 paper keys (`Ahmed2004`, `LynchVaandrager1995`, …) appear nowhere in
`sources/README.md`, which has file names and prose but no key column. Locators are audit row ids
(`audit C4`), which is right; the key scheme into the source index is undefined, so C6 needs one
line of design first: a key column in `sources/README.md` (the audit's `[Ah04]` style or the file
name) and the producer refusing an unknown key. The receipt says 45 claims; the file has about 50
(60 `id :=` minus 10 concepts). The producer will count.

`semantics-v1.md` (774 lines). Concept-first, ten sections with the five subsections; Codex's §7
corrections visibly applied (weakest precondition an analogy, "no step index for this membership
relation", invariant not progress, small step on a configuration); no hand-written status words;
a glossary (§3) with the right shape, whose "same thing or not" column is the useful half (merge
with Codex's glossary, whose "boundary" column is the other half). Statements appear as 23 copied
source snippets with `file:line` comments: quotes, not printed; acceptable in prose if the
promoted document points at the generated statements instead.

Mechanical check of the 56 distinct `file:line` locators across the receipt and the prose: 48
right, 8 wrong, all eight in the glossary and definitions tables: `MachineTyped` is at
`Assembly.lean:251`, not 257; `Term` is not at `Machine/Term.lean:14` (declarations at 100, 119);
`printModule` is not at `Templates.lean:612`; `readEff` is at `Read.lean:736`, not 240;
`readModule` at 758, not 715; `Ty.render` is not at `Ty.lean:124`; `Atom.render` is not at
`Atoms.lean:45`; `AxiomGate.lean:55` holds no declaration. The receipt's first sentence ("no
statement typed from memory") is true of the registry and false of these table cells. Not
promotable until every locator passes a mechanical check (the script is in this session's
scratchpad; it should become a check of the document, like the citations audit).

`receipt-documentation.md` (298 lines). §2 still lists the pre-REG-1 names while §6.1 lists the
corrections: inconsistent, fix. §4 (bibliography from the registry's keys) is right in principle
but proposes a second hand-written metadata table; the source index is the one table, keyed.
§5's definitions pass has sixteen proposals; the ones worth the coordinator's pass are #2
(`run_eq_ref` on `M7Fragment` with answer-free tapes), #7 (`TypedProg` not a weakest
precondition), #8 (`MachineTyped` an invariant, `machineTyped_not_halted` not progress), #9
(`denoteR` a translation, not an elaboration), #15 (exactness modulo `normS` on closed
`reservedFree` types). §4.2's "verified" literature marks verify that a work exists in the
vendored copy, not the section marks; label them "as cited".

## Landing order, when the owner says go

1. The owner commits the Bookkeeping repair; `lake build Effect4.Laws` green at HEAD.
2. Codex's branch: drop `FORCE` (finding 1), rename the column (4), merge onto the repaired HEAD;
   roots build at the merge; the gate runs once since a new implementation module was admitted.
3. Gemini's registry value as C6 after the key scheme exists and the producer accepts it; the
   prose after the eight locators are fixed and a mechanical locator check passes; the glossary
   merged from both halves; the definitions pass as the coordinator's edits to `AGENTS.md` and
   the system map.

## Addendum (~22:45): Gemini's second round (Codex's `brief-gemini-next.md`)

Files (all under `gemini/`, 22:15–22:19): `implementation-inventory.md` (346 lines, new),
`semantics-v1.md` (677, restructured), `registry-content.lean` (475, now the `registry` value
only, `import Lean` only), `receipt-documentation.md` (421, §7 added). Nothing tracked touched.

Checked mechanically (the scratchpad scripts; a leaf-name grep is not the producer):

- Registry: 73 qualified names resolve; 12 register ids and 19 cut rows exist; 51 claims as the
  report says (39 witness, 4 goal, 1 refutedBy, 6 absent, 1 assumed); no duplicate ids; roots
  `Assembly`, `TypedProgBindRed`, `ProtocolPosts`. The counts in the receipt now match the file.
- **One wrong pointer of 51.** `.goal `Effect4.Program.Typed.M7Exits`` names a `def`
  (`Assembly.lean:1500`, the proposition), not a ledger goal. The M7 goals are
  `Effect4.Program.Typed.M7.exits_typed`, `M7.stores_typed`, `M7.never_halts`,
  `M7.exitHandles_valid` (`Assembly.lean:1771-1789`; markers at `:1854-1857`). The producer would
  refuse it ("not an obligation"), which is the design working; the receipt presents it as a goal.
- **Unchanged from round one:** the 14 paper `work` keys (`Ahmed2004`, …) key into nothing in
  `sources/README.md`, which has no key column. One line of design before C6.
- **Wrong decisions row, twice.** The inventory attributes `Val.int64`/`float64` ("data-wave
  values") and part of store safety to decisions row 180. Row 180 is "Registered handle bytes (seat
  D3, M7)" and never mentions integers or floats; the signed-integer and binary64 decisions are
  rows 109 (FloatLib) and 121 (`int` and numbers).
- **Locators.** Receipt: 48 distinct, 46 right; wrong: `MachineTyped` at `Assembly.lean:257` (it is
  251; carried over) and `HostProtocol` at `HostProtocol.lean:48` (the structure there is
  `Protocol`; nothing is named `HostProtocol`). Inventory: 13, all right. Prose: the glossary table
  kept all eight wrong locators from round one (`Term.lean#L14`, `Templates.lean#L612`,
  `Read.lean#L240`, `Read.lean#L715`, `Ty.lean#L124`, `Atoms.lean#L45`, `AxiomGate.lean#L55`,
  `Assembly.lean#L257`), now as `file:///src/…` links. Gemini did not see this review; the fix list
  stands.
- Prose: no status words; ten code blocks; the glossary and the three senses of "elaborate" kept.

Two design points for the promotion, not defects of the draft:

1. **Part 5 of every concept ("Next Bounded Coding Task") and the inventory's "two tracks" make
   the semantics document a second owner of what is next.** `docs/STATE.md`'s "Next, in order"
   and the registers own that. The promoted `docs/core/semantics.md` keeps parts 1–4 and drops
   part 5; the inventory stays a research note.
2. **The inventory's categories (Open Goal, Required Work, Planned Feature, Intentional
   Exclusion, External Assumption) are the registry's `goal`, `absent`, `assumed` pointers and
   cuts, written by hand a second time.** After C6 the generated report is the one owner of that
   list; the inventory's value tonight is as Gemini's worksheet for the registry, not a document
   to keep in step.

The restructure into "what the literature defines / adaptation and exclusions / definition and
judgment / required properties / next task" is a reasonable shape and close to the brief's; parts
1–4 can be promoted after the locators are fixed and the `M7Exits` pointer corrected.

## Addendum 2 (~22:50): Gemini's third round (its reconciliation against this review)

Checked with `docs/research/2026-10-01-semantics/check-gemini-drafts.py` (new; untracked; exit 0
only when everything passes) and by reading each claimed repair at its line. Nothing tracked
touched; Codex's branch has moved to `845ce06e` and was not re-reviewed.

**Landed and right:** the M7 pointer is now `M7.exits_typed` (`Assembly.lean:1774`, a theorem
concluding `ProofGraph.Obligation`); all eight glossary locators are fixed and each declaration
is at its stated line (`Term.lean:100`, `Print.lean:142`, `Templates.lean:438`, `Read.lean:736`,
`:758`, `Ty.lean:756`, `Atoms.lean:64` `renderAll`, `Assembly.lean:251`; `AxiomGate.lean:376` is
the gate command); the definitions row now names `Protocol` at `HostProtocol.lean:48`; the
inventory cites rows 109 and 121 for the numbers. The registry value still passes: 73 names, 12
register ids, 19 cut rows, 51 claims, no duplicates, all four goal pointers obligation theorems.

**New errors (the checker's 16 failure lines, 10 distinct):** the "fully qualified names" cleanup of
receipt §2 replaced real names with names that exist nowhere in the tree, at the same locators
where round one had them right, and five carried into the prose:

| Written | The declaration at that locator |
| --- | --- |
| `fits_of_subN` (`Membership.lean:1261`) | `fits_subN` |
| `Effect4.Machine.DriveState.lift` (`Lift.lean:56`) | `driveState_lift` |
| `sub_antisymm_on_canonical` (`TypeAlgebra.lean:1092`) | `sub_antisymm_canonical` |
| `Effect4.Api.HostSession.Step.allowsAnswer_inv` (`Run.lean:289`) | `allows_answer` |
| `awaitHost_inv`, prose `frontier_awaitHost` (`Frontier.lean:41`) | `awaitHost_mem` (`Frontier.lean:8`) |
| `M6bLoopStep.stepLoopPreserves`, `M6cDeliverStep.stepDeliverPreserves` (`Assembly.lean:1843-1844`) | the goals `M6Ledger.step_loop`, `step_deliver` (`:1668`, `:1679`); `:1843-1844` are their `#proof_wanted` markers |

Also in the prose: `decode_iff`, `decode_encode` cited at `src/Effect4/Schema/Codec.lean` (they are
in `src/Effect4/Laws/Schema/Codec.lean:1052`, `:1065`); `m7_of_ledger` at `Assembly.lean:1555`
(it is `:1580`). The report's "All mechanical checks pass" is not so; no check was shipped with it.

**Smaller:**

- The proposed key mapping (receipt §8.4) leaves two registry keys unmapped (`Leijen2014`,
  `XiaEtAl2020`) and maps two keys the registry does not use (`AhmedDreyerRossberg2009`,
  `PlotkinPretnar2009`). `WrightFelleisen1994` maps to the audit, not a source: the paper is in
  `sources/README.md`'s not-vendored table, so its references are `assumed`. `FosterEtAl2007` to
  `S05-tree-lenses.pdf` is right (the README identifies it as the TOPLAS 2007 author version).
- `m7-capstone-goals`'s title promises typed exits, typed stores and non-halting; its pointer is
  `M7.exits_typed` alone. One claim per goal (`exits_typed`, `stores_typed`, `never_halts`,
  `exitHandles_valid`), or a title that says exits.

**Structural (for Codex and the coordinator, not Gemini):** the typed-state ledger scopes hold 19
open goals (`M3bAdequacy` 2, `M3bAssembly` 3, `M6Ledger` 9, `M6Edits` 1, `M7` 4; counted from the
`#proof_wanted` lines); the registry names four. A hand-picked selection is how the bound leaks.
Proposal: a pointer kind naming a whole ledger scope, so the producer enumerates its goals from
the environment the way `#typed_state_obligations` does and the report shows every open goal of
the scope with no registry edit when a goal is added. Measured, never drawn.

**The pattern across three rounds:** each round fixes the listed errors and adds new ones wherever
nothing mechanical checks the text. The fix is procedural: Gemini runs the checker before
reporting and pastes its output into the receipt; a draft is reviewable when it exits 0 with only
the PENDING line.
