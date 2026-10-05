# T3b implementation audit

No new actionable defect is verified in the inspected A–D changes.
The T3b worktree remains clean at `44960c5b`, which merges the rulings at `632265fd`.
No E/F implementation delta is present during this reading.
The main checkout is `5ebacecc`.

Evidence status: source inspection only. No build, test, generator, or repository mutation occurs.
Scope: the committed `917d4b5d..15ee58c8` changes, their commit receipts, the current worktree, and the T3b design.
The current rulings retain the bounded assignment under row 228.

## What the comparison establishes

- `compileEff` in `src/Effect4/Program/Compile.lean` passes `p.env` to `NativeOp.syncOpOf`.
  The denotations and agreement statements pass their corresponding environment.
  The existing name rows lower with an empty environment.
  The slice A commit defers use of the supplied environment until the cutover.
  This retains the old names' meaning and is not evidence of a lost capture in a term row.
- `ScopedOp.mapTerm` in `src/Effect4/Program/ScopedOp.lean` reaches the generated `frontierMap` and `Eff.weaken` in `src/Effect4/Program/Fold.lean`.
  `mapOf` and `weakenOf` in `tools/Effect4Gen/Fold.lean` emit those operation transformations.
  `Signature.WeakenNatural` and `Signature.termUse_weaken` in `src/Effect4/Program/Typing.lean` account for the inserted environment slot and appended current value.
- `Signature.termUse` in `src/Effect4/Program/Typing/Rules.lean` types the term at `env ++ [A]`.
  `bindTerm` matches the raw result type, after matching the request.
  `Checker.rowCheck` and the `HasTy.perform` premise both consume that term use.
  The widened request and term bindings remain distinct in the updated `rowTy_fits` statement.
- `Signature.opAtLevel` reaches the printer, reader, and readable-domain row-call cases.
  `readPerform_exact` and `readRow_rowCall_print` use `LawfulSpelling.opAtLevel_symm` to recover the operation at its original level.
  Native hooks remain defaults during A–D; the native image implementation belongs to E.
- `refStep` in `src/Effect4/Machine/Stores.lean` still evaluates a modify term before returning its first component and storing its second.
  The OCaml `sh_ref_step` also keeps those two components separate.
  Neither changes in A–D. This reading does not establish the future native term row's typed connection to those operations.

## Cutover boundaries already owned by the design

Design sections P4 and P6 assign capture transport and `TermMaps` discharge to E.

The existing `syncOpOf_keys` statement omits environment keys because the name rows currently discard that argument.
E must widen that statement and connect `Point.env_keys_subset` when native terms retain captures.
The engine's environment carrier also remains an E obligation, as slice A's receipt states.
These are planned changes, not newly discovered failures.

P11 already requires outer captures, current-value scope, an out-of-scope negative control, and weakening with its broken-map control.
It also requires `B` different from `A`, image round trips at several levels, and refusal of unsupported captured terms in the faces.
No additional test request follows from this inspection.
Those controls must exercise the actual native cutover before E can claim their results.

The design explicitly leaves operation annotations and integer scanning to T5 under row 212.
This audit does not reclassify that accepted boundary as an E defect.

## Commands and limits

Read-only commands include `git rev-parse HEAD`, `git status --short`, `git diff --stat`, and scoped `git diff 917d4b5d..15ee58c8`.
The review reads the full messages for `e757a2f4`, `c7afee00`, `5abdb76f`, and `15ee58c8`.
It reads current `AGENTS.md`, decision rows 43, 210–213 and 228–234, the T3b brief, and relevant design sections.
It also reads the landing review's A–D receipt summary.
No independent claim about successful compilation follows from those receipts.
The source may change after this snapshot; E/F require another bounded review once their delta exists.
