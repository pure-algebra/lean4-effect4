# 2026-10-07 chunk 3b: a correction of stage F2, from the coordinator

Status: a research note (history, not authority). It is for the implementer of chunk 3b. Read
it before stage F2. It replaces section 4 of `docs/research/2026-10-07-chunk-3b-brief.md`
where the two differ. Stage F1 stands as the brief gives it.

## 1. What the brief had wrong

A research probe drafted the repair and compiled it, after the brief was written. It found two
facts that the brief did not hold.

1. **`add` stays refused, for a second reason.** A module that the TypeScript printer writes
   has no import of its own. A lane writes the imports above it, and it imports each atom by name
   (`harness/truth/module-imports.ts`). So an export named `add` meets the import of the atom
   `add`. The brief asked for a green control of `add`: write none.
2. **Today's test also refuses too little.** It accepts `eq`, `get`, `some`, `Effect` and
   `Data` as export names. Each is a name that the imports bind.

And one fact that makes the stage smaller.

3. **A row's spelling keeps today's rule.** `rowNamesSafe` keeps its test of the first byte.
   Three proofs read that byte (`Var.name_ne`, `src/Effect4/Laws/Codegen/ReadLeaf.lean`), and
   a row spelled `a0.get` would print as a call on a binder. Do not touch `rowNamesSafe`. The
   brief asked for one predicate for all three places: do not write that.

## 2. The stage, as it is now

**The draft is `docs/research/2026-10-07-chunk-3b-names-draft.lean.txt`.** The coordinator ran
it on the landed tree, and it compiles with no error.

- `binderNamed` decides whether a name is a printed binder: the byte `a`, then the decimal of
  a position. It decodes the bytes and compares one string (`Effect4.Data.NatDecimal`).
- `exportNameFault` answers why a name is no export name, as one of six words, or nothing.
- `exportNameSafe` becomes "no fault".

**No probe note is owed.** The draft answers the probe's questions. Its two declarations stand
at `[propext, Quot.sound]`.

**Land it so**:

- in `src/Effect4/Codegen/PrintLeaf.lean`: `binderNamed`, `importedNames`, `ExportFault`,
  `exportNameFault`, and `exportNameSafe` as "no fault". The list `effectNamespaces` moves
  there from `src/Effect4/Codegen/ClassTable.lean`, since `PrintLeaf.lean` stands below it;
- **do not land the theorem `binderNamed_iff`.** It has no consumer in the law graph. The
  controls hold the test;
- the docstring of `Api.printModule` (`src/Effect4/Api.lean`) names `Api.emitModule` and
  `exportNameFault` for the reason. `PrintRefusal.unsafeName` keeps its one field;
- the header of `Test/Dogfood/Scenario/Todo.lean` says the finding as it is now: `add` is
  refused because a module imports the atom `add`.

**Controls** (`Test/Codegen/PrintContract.lean`):

- one green line: `all` and `answer` are export names;
- one red line for each new reason: `a0` and `a12` are binders, and `add`, `eq` and `Effect`
  are imported;
- the five lines that pin `main`, `a0`, `Effect.succeed`, `L_0` and `export` stay as they are.

**One thing to report, and not to repair.** The lane's import list holds three names that no
list of Lean holds: the adapters `Host`, `Sql` and `Kv`. Say in the hand-back where their
list stands in Lean, if one stands. If none stands, the test still accepts them.

**The stage owes**, as in the brief: `make corpus` with the diff of the corpus index,
`make check-truth` and `make check-target`. It owes the build of `Test` too. No law opens
`exportNameSafe` by a search of the sources, and the build confirms it.

## What this does not establish

- That tsgo refuses an export named like an atom. The conflict is a reading of the lane's
  import list, and no compiler ran on it.
- That the to-do application prints as one module under its own names. `add` stays refused.
