# 2026-10-06 seat WORKQ: filed evidence

Status: evidence of a receipt (history, not authority). The receipt is
`docs/research/2026-10-06-seat-WORKQ-receipt.md`.

| File | What it is | Evidence |
| --- | --- | --- |
| `search.lean.txt` | the bounded search of the four planned goals of `Test/Dogfood/Scenario/QueueWorkers.lean`, as it ran | a finite probe |
| `search.out.txt` | its output: one line for each start state, with the counts of the states that it judged | tested, on the Lean machine |
| `sweep.lean.txt` | the budget sweep: the battery's 22 scripts on the crew, each at the command budgets 1 to 160 | a finite probe |
| `sweep.out.txt` | its output: one line for each script, then the totals | tested, on the Lean machine |
| `cut.lean.txt` | one script at five command budgets: the verdicts and the whole observation at each | a finite probe |
| `cut.out.txt` | its output: one line for each budget | tested, on the Lean machine |
| `left.lean.txt` | the same script at seven command budgets: the commands that the command loop leaves at the stopped row | a finite probe |
| `left.out.txt` | its output: one line for each budget | tested, on the Lean machine |
| `rows.lean.txt` | the least command budget of each row of eight scripts, read at the funded run's machine | a finite probe |
| `rows.out.txt` | its output: one line for each row that gives the machine a decision | tested, on the Lean machine |
| `after.lean.txt` | the run `dropped`, then seven continuations by a host's acts | a finite probe |
| `after.out.txt` | its output: one line for each continuation | tested, on the Lean machine |
| `continue.lean.txt` | the run `dropped`, then every script of 29 moves up to length 3 | a finite probe |
| `continue.out.txt` | its output: one line of counts | tested, on the Lean machine |
| `onerow.lean.txt` | a budget for one row: nine middle rows, each at every fuel below its least one | a finite probe, outside the goals' domain |
| `onerow.out.txt` | its output: one line for each row | tested, on the Lean machine |
| `host-evidence.md` | the keyed lane's table of each entry's source of evidence, as the check wrote it in its work folder | tested, on rc.112 under bun 1.4.2 |
| `semantics-report.diff.txt` | what the semantics report gains at its next writing: the committed `generated/semantics.md` against the report tool's output in a scratch folder | tested: one run of the report tool; the committed file is not written |

The eight Lean files are not modules of the tree, and no gate runs them. To run one again,
follow these steps from the repository's root.

1. Build `Test.Dogfood.Scenario.QueueWorkers`.
2. Copy the file to a file with the ending `.lean`, outside the tree.
3. Run `lake env lean` on that file.

The search takes about eleven minutes.

## The search

The search judges the four goals' observations on every script of an alphabet up to a length,
from named states. It computes `funded` row by row along a script, by the test of `tapeFrom`
(`Test/Dogfood/Scenario.lean`). The test: a row ends at no frontier, and its decision is taken
at a live machine with enough command fuel. The output's first line compares that reading with
`funded` itself on four samples.

| Word | Meaning |
| --- | --- |
| `nodes` | the states that the search visited from one start state |
| `funded` | the states whose run is funded |
| `atRest` | the funded states at rest |
| `judgedAtRest` | the funded states at rest on which the two goals at rest were judged |
| `bad` | the first scripts, by the moves' indexes, where a goal's observation fails on a funded run |
| `cut` | the states whose run is not funded |
| `cutAtRest` | the states at rest whose run is not funded |
| `cutBad` | the first scripts where a goal's observation fails on a run that is not funded |

Part D starts each search from a run whose last reply application a small budget cut. So no
state of that part has a funded run.

## The sweep

The sweep plays each script of the battery's first 22 named runs at each command budget from 1
to 160, at the battery's compile budget. A line gives one script's facts.

| Phrase | Meaning |
| --- | --- |
| `funded from N` | the run is funded at `N` and at each larger budget to 160, and at no smaller one |
| `cut and at rest` | the budgets at which the run is not funded and the machine is at rest |
| `cut, at rest, the root has no exit` | the part of those budgets at which the root has no exit |
| `FAIL funded …` | the budgets at which a goal's observation fails on a funded run |
| `cut … fails` | the budgets at which a goal's observation fails on a run that is not funded |

A run that is not funded and at rest is one of two kinds. At the budgets just below the least
funded one, the stopped row's step did its whole work: the root has its exit. At the other
budgets the step lost work: the root has no exit, and nothing will run it.

## The one script at five budgets

The script is `[running, cancelWaiting, afterWaiting]`, the script of the named runs
`cancelled-waiting-closed`, `starved` and `dropped`. In a line's `verdicts`, a letter stands for
one row's verdict.

| Letter | Verdict |
| --- | --- |
| `c` | a control that progressed |
| `F` | a frontier |
| `b` | a held call |
| `p` | a reply receipt |
| `A` | a reply application |
| `r` | a refused row |

## The commands that the command loop leaves

`left.out.txt` reads the stopped row of the same script at seven command budgets. At six of
them the journal has a stopped row, the same reply application. At 119 the run is funded. The
probe runs the command loop of the row's answer
decision (`driveState`, `src/Effect4/Machine/Fibers.lean`) and prints the commands that it
returns. `stepDecisionState` keeps the loop's machine and its receipt, and it does not keep those
commands. So the printed commands are the work that the budget's cut loses.

## The least command budget of each row

`rows.out.txt` plays a script at the battery's budget. Before each row that gives the machine a
decision, it asks `Run.enoughFor` at each command budget from 1 to 200. A line gives the least
sufficient one. The answer is monotone in the budget at each row: no line says otherwise.

## The run that lost its work, continued

`after.out.txt` plays the run `dropped` and then seven continuations.

1. No more row.
2. Five flushes.
3. A clock step of 10 ms, then a flush.
4. A held call at each selector, a reply receipt and two reply applications, then a flush.
5. A cancellation of each crew member, then a flush.
6. A cancellation of the root.
7. A cancellation of the root, then a flush.

A line gives the verdicts of the added rows and the root's exit. It also says whether the
machine's view is still the view of `dropped`.

## The run that lost its work, under every short script

`continue.out.txt` plays the run `dropped` and then every script of an alphabet up to length 3.
The alphabet has 29 moves: the search's 28 with raw controls and raw rows, and the root's start.
The line gives three counts. The first is the scripts. The second is the scripts after which
the root has an exit. The third is the scripts after which the machine's view has moved.

## A budget for one row

The goals range over runs with one command budget. `onerow.out.txt` is outside that domain. The
probe plays a script at the battery's budget, and it sets the run's command fuel for one row.
It plays that row at each fuel from 1 to 69. A line reads the fuels below the first one at
which the row's view is the whole run's. It gives the fuels at which the machine is at rest
and those at which an observation fails. Then it gives the same after two more flushes at the
battery's fuel.

## The semantics report

`semantics-report.diff.txt` is the output of `diff` on two files. The first is the committed
`generated/semantics.md` at the seat's head `e1e3959c`. The second is the file that
`lake exe semantics-report` wrote into a scratch folder there. The seat did not run
`make gen-semantics`, and it did not write the committed file. The coordinator wrote the report
again at the merge `c67fa03c`. A second scratch run at the merged head gives the committed
file's bytes.
