# 2026-10-06 seat TAPE: filed evidence

Status: evidence of a receipt (history, not authority). The receipt is
`docs/research/2026-10-06-seat-TAPE-receipt.md`. The base is `4ff42e89`. The probes of
the statements, of the kernel's terms, of the root and of the report ran at the sources of
`05768d17`. They ran again at `aac8b509`, with the same bytes.

| File | What it is | Evidence |
| --- | --- | --- |
| `names.txt` | the short names of the 44 declarations that left `Test/Dogfood/Scenario.lean` | — |
| `check.lean.txt` | the statement probe at the head: `#check` of each name, `#print` of each definition, and `#print axioms` of each name. The base's probe holds the same lines under `Test.Dogfood.Scenario` | a finite probe |
| `base-check.out.txt`, `head-check.out.txt` | the probe's output at the base and at the head | tested |
| `normalize.py.txt` | it joins the lines of one message, so that two outputs compare where only the line breaks differ | — |
| `dump-base.lean.txt`, `dump-head.lean.txt` | the probe of the kernel's terms, as it ran at the base and at the head | a finite probe |
| `dump.diff.txt` | the base's output against the head's | tested |
| `dump.sha256.txt` | the sums of the four outputs that are not filed | — |
| `names.lean.txt`, `names.diff.txt` | the declarations of the base's support file against those of the four modules after step 1, by name and kind | tested, with the base's file as a scratch copy |
| `helper.out.txt` | the type and the value of the matcher's helper, equal at the base and at the head | tested |
| `union.lean.txt`, `union.diff.txt` | the declarations of the four run modules before step 2 against after it; each line is cut at 220 characters | tested |
| `root-probe.lean.txt`, `root-probe.out.txt` | a file that imports the `Effect4` root alone and reads a tape; its red control asks for a law | tested |
| `report-probe.lean.txt` | the semantics report's own function, called in scratch on two values of the semantics registry | a finite probe |
| `report-stale.out.txt` | the refusal of the semantics registry as it stands | reproduced |
| `semantics-report.diff.txt` | the committed `generated/semantics.md` against the scratch report with the three pointers moved | reproduced: no tracked file is written |
| `cases.out.txt` | the summary line of `make check-cases` at three states | tested |
| `fixtures.sha256.txt` | the sums of the nine engine fixtures, equal before the slice and after each step | reproduced |

No Lean file here is a module of the tree, and no gate runs one. To run one again, copy it to
a file with the ending `.lean` outside the tree, and run `lake env lean` on it from the
repository's root. `report-probe.lean.txt` takes `--run` and one folder for its output.

## The statements

`check.lean.txt` sets `pp.fullNames` and turns field notation off. So each constant of a
statement stands under its full name. The comparison takes three steps.

1. Write `Effect4.Run.` for each `Test.Dogfood.Scenario.` of the base's output.
2. Run `normalize.py.txt` on both outputs.
3. Compare the two results with `diff`.

The comparison finds no line that differs: 130 messages on each side. The last 44 messages
are the axioms: 40 declarations at `[propext, Quot.sound]` and 4 at `[propext]`, equal on both
sides.

## The kernel's terms

`dump-base.lean.txt` writes each declaration's type in full. It writes a definition's value in
full, and a hash of each value. It does the same for each declaration that Lean's elaborator
made under one of the 44 names. The base's probe writes each moved name under `Effect4.Run`.

The head's probe hashes each term in the base's name form. It maps back two kinds of names
that Lean's elaborator makes.

- **A module-private auxiliary.** A matcher's splitter and its equation lemmas are private
  to the module that asks for them, and the module's name is part of their names. The four
  proofs that use one are `submit_inert`, `receive_receiptRows`, and the equation lemmas
  `decisionOf.eq_3` and `tapeFrom.eq_def`.
- **The helper of `decisionOf`'s matcher.** The base took it from the reader `applications`
  (`applications._sparseCasesOn_2`). The head has its own (`decisionOf._sparseCasesOn_3`).
  `helper.out.txt` is the type and the value of both.

`dump.diff.txt` then holds two differences. The head has seven lines more: its new helper and
the lemma `else_eq`. The value of `decisionOf.match_1` is written with that helper's name on
each side, and it differs in that name alone. Each of the base's 102 hashes is the head's. A
hash has 32 bits, so an equal hash is a test and no proof. Each type and each definition's
value is compared as text.

`names.diff.txt` gives the count of step 1. The four modules hold four declarations more than
the base's support file. The helper, its lemma and three private helpers of the matcher's
splitter come. One lemma of the base's helper goes. The base's side is a scratch copy of
the base's file, since the base's build was gone when the probe ran.

`union.diff.txt` gives the count of step 2. `runOf` (`src/Effect4/Laws/Run.lean`) calls a
matcher of its own, where it called `machineOf.match_1`. The new matcher and its four private
lemmas come, and nothing goes. The two matchers are equal up to their binder names: `m` in
the one, `machine` in the other.

## The root probe

`root-probe.lean.txt` imports `Effect4` and nothing of the law graph. Each of the sixteen
definitions of `src/Effect4/Run/Tape.lean` resolves there.

- Green: a small program's started run is funded and at rest. Its tape holds one decision, and
  the raw replay of that tape shows the run's machine view.
- Red: at a command budget of zero the same run is not funded.
- Red: `Effect4.Run.tape_replays` is an unknown constant there. The probe pins the message.

## The report

`report-probe.lean.txt` calls `loadReport` (`tools/Tools/Semantics.lean`) twice. It writes
into a scratch folder, and `make gen-semantics` did not run.

- On the semantics registry as it stands, the function refuses: three findings, one for each
  pointer.
- On the semantics registry with the three pointers at `Effect4.Run`, it accepts. The probe also names
  the new file of `funded` in one open part of R12.

`semantics-report.diff.txt` has 57 lines of the committed report and 54 of the scratch one.
They are the three pointers and the statements of the three claims, as the report writes them.
The nodes of R6, R8 and R13 also change their order, in the rows and in the diagrams. A node's
name now sorts under `Effect4.Run`. No status differs, and no count of a node differs.
