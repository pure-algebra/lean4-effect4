# 2026-10-07 chunk 2, steps A and B: the coordinator's first review

Status: a research note (history, not authority). It rules nothing. It is written for the
implementer of chunk 2 (`docs/research/2026-10-06-chunk-2-brief.md`), at the owner's request:
"start reviewing landed work so far".

**What was read.** The working tree of branch `chunk-2` over `de7b4044`, on 2026-10-07. No
stage of the chunk is a commit, so the review reads files. Step C was in flight, and a build
held the tree. So the review ran no Lean command. Each finding is a reading, except the one
run of tsgo in section 2.

**Verdict.**

- **Step A (QUERY): not ready to land.** The function's design holds. Its acceptance tests
  almost nothing, and one recorded answer is wrong for the program that it names.
- **Step B (the probe of the TypeScript printer): lands after its table is corrected.** The evidence is
  good. The note reports five verdicts that the evidence does not hold.
- **Step C (MATCH): not reviewed.** Section 3 lists four questions for its receipt.

## 1. Step A: QUERY

### What stands

- One pure function, `Tools.Query.answer`, and a thin driver. No theorem, and no executable
  entry in `lakefile.toml`.
- The eight law names resolve to theorems of the tree.
- The input is canonical bytes, by `decodeProgram`.
- Four lines of the battery are real controls. They read the addresses, the focus at no
  address, the empty list of refusals, and a slot that a node does not have.

### What must change, and the rule behind each

1. **Six lines of the battery test a flag that is always `true`.** `answer` sets `ok := true`
   at `check`, `focus`, `table`, `refusals` and `slots`, whatever the checker answers. So
   `(answer { op := "check", … }).ok = true` holds for a refused program too. The two lines at
   `omit` and `fill` show only that the edit exists. No line reads a type, an environment, an
   entry of the table, or a refusal's path.
   - **Rule**: the brief's acceptance. For each request, compare the answer with the value
     that `Test/Program/FocusControls.lean` or `Test/Program/TableControls.lean` guards.
     Compare `result`, never `ok`.
   - **Rule**: a red control for each `none`. Add three: bad bytes, an unknown operation,
     and a filling at no address.
2. **The transcript is not replayed, and the driver cannot read it.** The battery counts ten
   lines and reads the first key of each. It parses no request and calls `answer` on none. A
   scratch file wrote the fixture (`scratch/gen_transcript.lean`). It names the operation
   `request`, and `Request.fromJson?` reads `op`. So each line of the fixture is a request
   that the driver refuses. The receipt records no run of the driver.
   - **Rule**: a fixture is the tool's own output. Write a file of requests, run the driver
     on it, and file both. The battery parses each request, calls `answer`, and compares the
     answer with the recorded one inside one `#guard`.
3. **The recorded answer for `slots` at `update` is wrong for that program.** `update` reads
   two variables, so it has a type only in an environment. `TableControls` guards its slot at
   the environment `[.refOf .nat]`: the slot's environment is `[.refOf .nat, .nat]`, and the
   term's type is `.nat`. `answer` asks at the empty environment. The fixture records
   `"env": null` and `"termTy": null`, under the law `hasTy_extSlotEnv`. That law speaks of a
   typed node, and this node is not typed there. The battery line passes, since it reads `ok`.
   - **Repair**: put the operation under its binders in a closed program, and guard the
     answer. `original` holds reference operations at depth: use one of them.
   - **Rule**: the battery applies a law at each place where a receipt says that it holds.
     Step C rewrites the slot of an operation's own term, so that slot needs a true control.
4. **An answer names a law whose premises the function does not decide.**
   - `omit` names `Sketch.check_omit_focusAt` always, also on a failure. The law asks six
     things: the sketch is admitted, two columns are closed, two are normal, and the hole row
     is formed. The docstring of the law says that a tool can decide each. Decide them, and
     name the law only then. Otherwise the answer is a new check, and it names none.
   - `fill` decides the filling's type, and not that the sketch is admitted.
   - `check` names `holes_conservative`. The request carries no hole table, so the law that
     applies is `Sketch.check_program`. The brief's table has this error, and it is the
     coordinator's. Follow this note.
   - **Rule**: a named law is a claim. Name it where its premises hold, and nowhere else.
5. **A second writer of one type.** `Tools.Query.effTyJson` writes a requirement key as its
   service number alone. `Tools.ProfileJson.keyJson` writes the name and the service, and
   `effTyJson` of `src/OCaml5/Eff/Metadata.lean` uses it. Two keys of one service now print
   the same. Move the one writer to `Tools.ProfileJson`, and let both callers read it.
   - **Rule**: one name for one thing.
6. **A wrong field is read as an absent field.** `Request.fromJson?` turns a `path` that is
   no list of numbers into the root's path, and a `slot` of an unknown name into every slot.
   A client's error then gets a confident answer for another question.
   - **Rule**: the reader reads an input or refuses it. Refuse a field of the wrong type,
     and an unknown slot name, with the field's name in the error.
7. **The term writer is a hand match with an arm that no input reaches.** `termJson` and
   `termsJson` recurse by hand, and `termsJson` has a last arm for a tail that is no array.
   The tree has the fold: `TermAlgebra` and `cata_term` (`src/Effect4/Program/Fold.lean`).
   The writer also drops the first field of `record`, `field` and `fold`.
   - **Rule**: a traversal is a fold. State in the docstring which fields the form omits.
8. **Three copies of the list of slots**: `parseExtSlot`, `extSlotToString` and the literal
   `allSlots`. A sixth slot would change one and miss two, in silence. Keep one list, derive
   the reader from the writer, and guard the round trip once.
9. **The receipt's counts are not measured.** It gives 224 lines for `tools/Tools/Query.lean`.
   The file has 282, and it is older than the receipt. Take a count from `wc`.

### One limit that the receipt names, and its consequence

A request carries no hole table. So the program that `omit` returns cannot be sent back: its
hole row is gone, and a `check` of it would refuse an unknown row. `omit` is a dead end until
a sketch has a codec. Say so in the answer, in a field, and not only in the receipt.

## 2. Step B: the probe of the TypeScript printer

### What stands

- Each probe imports the real `effect` package and the real prelude, and declares no stand-in.
- Each evidence file holds tsgo's version (7.0.0-dev.20260629.1), its exit code and its text.
- The counts hold: 44 forms, 44 green files with exit 0, 44 red files with exit 1.
- The module folder of the probe is a link to `ts/eff/node_modules`. Nothing was installed.

### What must change

1. **Five cells of the verdict column are not in the evidence.**

| Form | The note says | The evidence file records |
| --- | --- | --- |
| the Boolean test of `select` | `TS1005` | `TS2635` |
| the native field read | `TS1005` | `TS2635` |
| the native record update | `TS1005` | `TS2635` |
| the native tuple index | `TS1005` | `TS2365` and `TS2693` |
| `Ref.modify`, the red control | `TS2345` | `TS2322` |

   `TS1005` stands in the probe's own comments and in no output of tsgo. The six first rows
   also cite the green file for a verdict that the red file holds.
   - **Rule**: a verdict is copied from the tool's output, with the file that holds it.
2. **Three green probes hold no union of two members.** The native field read, the record
   update and the tuple index run at one record or tuple with a union inside. The brief asks
   for a term with two union members. The file declares `rec1`, `rec2`, `tup1` and `tup2`,
   and uses none.
   - The coordinator ran the three forms at a union of two members. The compiler and the
     flags are the probe's. tsgo accepts each form with no type argument, and the result is
     the union. The red control fails with `TS2322`. The files are
     `docs/research/2026-10-07-chunk-2-review-evidence/union_green.ts.txt` and
     `union_red.ts.txt`.
3. **The note does not say what its finding means.** A form with no place for a type argument
   matters only where tsgo needs one. The evidence answers that for all six forms: each is
   accepted with no type argument. State it as the first line of the findings. PRINT, step 2,
   reads that line.
4. **Four rows are true at the prelude of `de7b4044` only.** Step C changes the declarations
   of `cons`, `get`, `append` and `mapFromEntries`. Run those rows again after step C, and
   any atom that takes the whole form after them. Mark each row with the prelude that it ran
   against.
5. **The receipt gives no command.** The runner is `scratch/print_probe/run_probe.py`, and it
   is not filed. File it as text beside the evidence, and write the flags in the receipt. The
   probes import by an absolute path of this machine: say so, or import by a relative path.

## 3. Step C: four questions for its receipt

This is no review. The tree was in flight when it was read.

1. **The goal gate's pin moved from 12 to 19**, and the diff adds one planned goal,
   `closedSubst_matchArgsB`. So seven more declarations rest on a goal. Rule 4 of the brief
   holds: say which law one level higher was tried, and how it failed. Name the seven.
2. **`getOrElse` and `ite`.** `Scheme.poly` has lost its `join` flag, so both atoms now bind
   by bounds. The working prelude still declares `getOrElse` with `NoInfer<A>`, and `ite` with
   one plain parameter. Give one table for the fourteen template atoms. A row holds the
   checker's answer at two members, and tsgo's verdict on the printed call.
3. **The eight other template atoms.** The brief asks the design note why each keeps its
   declaration. The note of step C does not name them.
4. **Stage C0 did not land alone.** The tree holds four changed declarations of the prelude
   at once, and no commit. Say in the receipt which run of `make check-target` saw `cons`
   alone, or that none did.

## 4. Process

- **Commit each stage, or say first that you cannot.** A message file for step A stands in
  `scratch/`, and no commit was made. A review of a moving tree costs more than a review of a
  commit, and it cannot tell one stage from the next.
- **Steps A and B are independent of step C.** Repair them while step C builds.

## What this does not establish

- That any file of the chunk compiles. No Lean command ran.
- That the ten recorded answers are what `answer` gives. The review compared one of them with
  a guarded value, by reading.
- Anything about the 78 theorems of `src/Effect4/Laws/Program/Bounds.lean`. They were counted
  and not read.
- That tsgo accepts the six forms at the truth lane's own flags. The probe's flags are the
  runner's, and the review used the same.
