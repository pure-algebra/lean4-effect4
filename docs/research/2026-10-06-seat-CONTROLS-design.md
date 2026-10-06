# 2026-10-06 seat CONTROLS design: a scenario lists its runs, and a control names the runs it reads

Status: a design note (history, not authority). Brief:
`docs/research/2026-10-05-claude-lead/briefs/seat-controls-brief.md`, under decisions rows 254
and 266. Base: `1e280f24`. Written on 2026-10-06, before the first Lean commit of the seat.

## 1. The fault, on the base

A battery holds a control's script inside a Boolean expression, so the host driver writes each
script again. Two finite probes of 2026-10-06 ran the driver on scratch copies of the workers
battery. Each copy keeps its gate green. Evidence word: tested.

| Change in the copy | The driver's fixtures (`Keyed.lean scenarios`) |
| --- | --- |
| One inline script of one control: the two reply applications of `between`, swapped | The base's bytes. The host would perform the old script. |
| One named part: a flush after `lowest` | Two runs change: `workers/lowest` and `workers/twice`. |

## 2. The records (`Test/Dogfood/Scenario.lean`)

A **named run** is one script on one program: a name, the built program opened for a run, and a
`List Move`. A scenario's record lists each named run once, and a control names the runs that
its comparison reads.

```lean
structure NamedRun where
  name : String
  opened : Run
  moves : List Move

structure Control where
  clause : String
  isRed : Bool
  name : String
  reads : List String        -- the named runs that the comparison reads, in order
  holds : List Run → Bool    -- the comparison, over those runs as played

structure Scenario where     -- its other fields stay
  runs : List NamedRun := [] -- each script of the scenario, once
  controls : List Control
```

The brief describes the named runs inside each control. I put the list at the scenario. A name
then has one script by construction, and a script that two controls read is one entry. The gate
plays each run once. The list's order is the order of the lanes' runs.

## 3. The gate

`Scenario.problems` plays each named run once, with `play`. It hands each control the played runs
that the control names, and it judges the comparison. It refuses what it refuses today. It
refuses two things more: a control that names a run which the record does not list, and a name
listed twice. `Test/Dogfood/Scenario/Gate.lean` keeps its nine fixture records in the new form.
It gets a red control for each new refusal, and one fixture whose control reads a played run.

The gate allows a named run that no control reads. Section 6 reports the one that stands today.

## 4. The host driver (`harness/truth/session/Keyed.lean`)

The driver maps each scenario's `runs` to its host runs. A host run's name stays the scenario's
name, a slash and the run's name. The driver keeps the lane's own parts: each observation's
wire, the readers that a scenario asks for, and the rule `performable`. It keeps one stated
reason, by the run's name: tsgo 7 refuses the printed TypeScript module of `routing/exact-escape`.
It holds no list of moves.

Each battery lists its runs in the driver's order of today. So the fixtures that the driver
writes must be the base's bytes, and the lane's evidence table with them.

## 5. The controls that have no script of their own

| Control | How it is written |
| --- | --- |
| The frontier control (timeout) | It reads the run `received`. Its comparison sets the budget's fuel to zero and plays one reply application. That move stays in the comparison: no lane has an act for a budget. |
| The journal controls (workers, timeout) | Each reads one run. Its comparison plays that run's journal again from the opened program, whole or without one row. |
| The run of `P3WorkerQueue.drive` (workers) | It reads the run `lowest`. Its comparison makes the driven run, and compares the two journals and the two observations. |
| The straight clause (atomic) | It reads no run. It runs the request alone with `Api.run`, at a bound. |
| Routing's program pin, atomic's two typed-row controls, each battery's build control | Each reads no run. |

## 6. The engine's lane, and three findings

`Test/Dogfood/Scenario/Tape.lean` holds the runs of the generated OCaml engine, and it restates
scripts too. A scratch probe compared its 19 runs with the driver's 55, on the base: tested.
Twelve are a control's script on that control's program. The lane takes those twelve from the
records, by name. Seven are the lane's own scripts, each written once. The engine's fixtures
must not move.

- **A run that no control reads.** The host driver lists `timeout/parked`, and no control of the
  timeout battery plays it alone. I keep it as a named run, so the lane's runs stay the same.
- **One name, two scripts.** Five names carry one script on the host lane and another on the
  engine's lane: `atomic/interrupted`, and timeout's `late`, `kept`, `404` and `four`.
- **A stale copy.** The engine's `timeout/four` was the battery's script until the retry repair
  (`0f76dd2a`). The repair changed the battery's delays, and the engine's copy kept the old
  ones: reading. The engine's `timeout/kept` ends with the old first delay.

A repair of the last two changes a committed fixture, so it is not in this slice. I report them
to the coordinator.

## 7. What this does not establish

The slice states no theorem and moves no status. A played run is a finite probe: one script on
the Lean machine. The gate cannot see a move that a comparison plays by itself. Section 5 names
the one that stays.
