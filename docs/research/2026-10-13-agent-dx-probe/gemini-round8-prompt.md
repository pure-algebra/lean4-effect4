Round eight, in this same conversation. First, your census's errors, checked against the tree and
by a run. Then one focused task.

## Your errors

1. **The shape an agent should follow.** You wrote that an agent must use `ts/eff/eff.gen.ts` as
   the shape of `programJson`. The session tool refuses that shape. The file's own header states
   the carrier rule: a family whose constructors are exactly `nil` and `cons head tail` prints as
   an array. The tool's reader (`Tools.Session.programOfJson`, then `Canonical.ofJsonAnyOrder`)
   wants `{"_tag":"cons","head":…,"tail":…}`. A program with `"args": [ … ]` answered "the program
   does not read". You read both files and did not compare them.
2. **`module`** is partial, not absent. `eff_module` is declared in
   `src/Effect4/Program/Authoring/Module.lean`, the folder you say you searched.
3. **`find` and `impact`** are partial. `#why` and `#goal_impact` (`tools/ProofGraph/Why.lean`) and
   `#plan_status` (`tools/ProofGraph/Plan.lean`) answer the claims' half of each.

Your other rows checked out, and your pointer to the TypeScript types was the most useful line of
the census: it exposed two encodings of one program.

## The task: where the two encodings differ

Two JSON encodings of `Eff` exist. One is printed by `tools/Drivers/TsGen.lean` into
`ts/eff/eff.gen.ts`. The other is the canonical JSON print, read by `Canonical.ofJsonAnyOrder`
(`src/Effect4/Store/Domain/ShapeRead.lean`) over the shapes in
`src/Effect4/Store/Domain/Derived/Program.lean` (`EffShape` and its siblings).

Write a table with one row for each family that `EffShape` reaches: `Eff`, `Term`, `Lit`,
`NativeOp`, `Ty`, the list families, and the rest. For each, give:

1. its encoding in `eff.gen.ts`, quoted from the file;
2. its encoding in the canonical print, read from the shape and from the reader's code;
3. whether they agree. Where they differ, say how: arrays against `cons`, strings against
   `{"_tag":…}`, `null` against an option's tag, field names, or numbers.

Then list the carrier rules that would make the two one: each rule, and the families it changes.
Do not propose which encoding wins; the coordinator decides.

You write one new file only: `docs/research/2026-10-13-agent-dx-probe/gemini-encodings.md`.
Never edit any other file. Never run lake, make or git. Never commit.

## How to work

- Read both sources for every row. Quote the TypeScript; name the Lean declaration for the other.
  Mark a guess as a guess.
- Pass 1: write the file. Pass 2: re-open every cited declaration and line of TypeScript, and
  correct the file. Then stop and reply with what changed.
- Plain English, one idea a sentence, at most 25 words. Plain characters, never TeX. No line
  numbers.
