# Seat W6: the record term forms (commit 6; rows 165, 166, 167, 131)

Written 2026-10-01 by the coordinator from probe R's paste-ready text (its note, "Brief text for
the data wave's commits 6, 7 and 8"; `docs/research/2026-10-01-type-language-probe/R/note.md`).
Base: main after commit 4 (the `Ty` append) merges; the coordinator names the commit and the
worktree at dispatch. Read first: `README.md` here; rows 119 (as amended by 165), 165, 166, 167,
131 in `docs/core/decisions.md` (read-only); probe R's note Q1 (both routes, "The reason as a
theorem shape"), Q2, "The forms table"; the packet draft
`docs/research/2026-10-01-type-language-probe/R/contracts/record-terms.contract.md` with its
falsifiers 001–012; probe R's models `R/probes/Q1Named.lean`, `Q1Positional.lean`, `Q1Bill.log`.
Rules: `2026-10-01-landing/plan.md` §4; `AGENTS.md` (DI-78: the packet before the code; one
TypeScript compiler, tsgo 7).

**The one thing.** Row 165 is ruled: a record value carries its canonical names,
`ctor 0 [list names, list values]`. With that, a name-only projection is sound with the untyped
evaluator (R's `Named.sound`), and the two forms are `Term` constructors, not atoms (row 166): a
label is type-level data printed as syntax. Freeze the contract first, write its battery red, then
land the forms by explicit paths.

## The work, in order

1. **Freeze the packet.** `Test/contracts/record-terms.contract.md` from R's draft, amended to
   row 165 (a) (its §6 "if positional values stand" becomes history); its battery red:
   `Test/Program/RecordTermContract.lean` (reachable from `Test/All.lean` at the anchor after
   `Test.Program.H2PartOne`) with falsifiers 001–012 as fixtures: the model theorems that refute
   the atom route and the positional reader stay compiling theorems over local copies (history);
   the refusals as `#guard_msgs (error)` fixtures. Commit.
2. **`Machine/Term.lean`:** append `record (labels : List String) (args : Terms)` and
   `field (target : Term) (name : String)` to the mutual block (un-nested, so `DecidableEq`
   derives; the nested spelling is pinned refused, falsifier 011); `evalTerm`'s arms over the
   named value (`getField` by name search in the canonical name list); `tools/Effect4Gen/wire-tags.json`:
   `Effect4.Program.Term` gains `record: 3`, `field: 4`; regenerate the reached groups in the fixed
   order (`derived`, then `lcnf` by name, `eff`, `wire`, `cas`, `ts`) and nothing else,
   `LEAN_NUM_THREADS=1`, outputs committed never hand-edited.
3. **`Program/Typing/Rules.lean`:** the two `argTy` arms (record fields typed at flag `false`; the
   field arm reads `lookupName n (canon fs) = some τ`), the located refusals `notARecord`,
   `unknownName`, `arity`, `repeated` in the checker (`Program/Checker.lean`); `Program/Authoring.lean`:
   the builders `record` and `field` beside `app`. The theorem shape (R):
   `argTy sig Γ c (.field t n) = some τ ↔ ∃ fs, argTy sig Γ false t = some (.record fs) ∧
   lookupName n (canon fs) = some τ`.
4. **The hand traversals the append forces** (`#exhaustive_gate Effect4.Program.Term`: 29 matches
   with no catch-all at `bff50631`, 34 in all): `Term.scoped`, `Terms.scoped`, `Term.weaken`,
   `Terms.weaken`, `Terms.toList`, `Terms.names?`, `noRow`, `argTy`, `argsTy`, `evalTerm`,
   `evalTerms`, `printTerm`, `printTerms` (the printer arms are commit 8's; here they refuse the
   new forms by name until then); review the five with a catch-all (`pairArgs?`, `readLiteral`,
   `tagTest?`, `tupleRequestReadable`, `TestClock.dilateAlgebra`): none may treat a record term as
   an application. `make check-cases` after the match on the policy family.
5. **Laws:** the packet's L1–L8 in the tree (`Laws/Program/Typed.lean` and the term laws: L5 is
   row 148's `evalTerm_fits` with its two new arms, in seat A's `EnvTyped` form; L8 the weakening
   lemmas); the fold generator needs no change (R's bill). `#print axioms` on each.
6. **Number-to-text** (row 131): the atom over every number type of the wave, by DI-89's atom
   route, with its contract line in the packet.
7. **Final:** `LEAN_NUM_THREADS=4 lake build Effect4.Laws Test.All` green with both gates; the
   admission census; the conservativity check (`make check-gen`, the goldens byte-identical except
   the regenerated groups named above, corpus verdicts unchanged).

Stop rules: a classifier that puts a record term in a positive class by a catch-all; a generated
path outside the named groups; any existing golden that changes bytes or corpus verdict that
changes; a form the dependency bump does not bring is refused by name at formation (row 167),
never worked around in the faces.

## Receipt

`docs/research/2026-10-01-data-wave/receipt-W6.md` (force-added): the one thing first; base and
head; every changed path, the generated files with their producer commands and exit codes; the
laws (name, file:line, axioms); the controls that flipped; what is owed; the proposed lines for
rows 131, 166, 167 and the register (`E4-RECORD-CE-001`–`005`, `-011` repaired by the battery).
