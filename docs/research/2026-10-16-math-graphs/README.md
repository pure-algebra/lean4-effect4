# 2026-10-16 The call tree, the session and the program graph: one structure, a working interaction-tree reading, and graph laws

Status: research note (history, not authority). Base: `b3453c241` on `claude/math-d3`, itself on
`81f9a4354` (`refactor/phase1-phase3`). Role: the math seat, the one Lean seat, second task of
2026-10-16. The receipt is `docs/research/2026-10-16-seat-math2-receipt.md`.

The owner, by voice, asked for three things:

- model the math "with a focus on what we prove … to build powerful abstractions";
- look into "graph semantics, call tree, other stuff about the session";
- make "the mechanization of things like interaction trees realized" as engineering wins.

## The one thing to know first

The structure under the session exists, for one fiber, and it is one object read four ways:

- **the call tree** is the free monad over the stores and the host rows (`denoteRows`);
- **a host** is a comodel of the row signature (`RowSig`), and the session's meaning is the host's run;
- **a reply tape** is a path through the tree, and a reactor is a strategy with memory;
- **the journal** is a word acting on runs, and its decision tape is the word's projection.

A loop makes the tree infinite. This seat reads it as a **call chain**: the budgeted call trees
(`denoteRowsB`), each below the next. Three new modules make that reading work:

- `src/Effect4/Laws/Program/CallChain.lean`. A chain has three outcomes under a host: it
  finishes, waits or diverges, and they persist and exclude one another. `Chain.Equiv` is the
  interaction-tree library's weak equivalence, read on approximants. `RProgram` is stated as the
  finite, silent-free part of an interaction tree.
- `src/Effect4/Laws/Run/Outcome.lean`. A driven session's exit is its chain's finish, and a
  frontier is its chain's wait. A diverging chain has neither. The converse is a planned goal
  at R12.
- `src/Effect4/Laws/Run/CallMap.lean`. Every host request of a run is performed at a site of its
  program: the law a generated call map rests on.

## 1. Questions

1. Four readings: is the call tree the unfolding of the program's coalgebra, and the session a
   path in it? Is the journal a word acting on the run, and a decision tape a strategy? What
   is the one free object, and which pairwise lemmas would it replace?
2. Which carrier gives a working interaction-tree reading in Lean, and how does `Eff` relate to
   it? Can the dictionary's analogy between `RProgram` and interaction trees become a relation?
3. Which laws of the program graph would let a generator compute what is written by hand?
4. What do these semantics say about the vessel dogfood, and where does its author meet friction?

## 2. What was read or run

| Item | Evidence | Result |
| --- | --- | --- |
| `Effects/Coalgebra/{Step,System,Bisim,Comodel,Run,Protocol,Sat,Indexed}.lean` (package `effects`) | reading | systems, simulations, hosts, protocols, typed handlers, indexed signatures |
| `src/Effect4/Laws/Run/{CallTree,Journal,JournalPrefix,Frame,Tape,Rows}.lean` | reading | §3 |
| `src/Effect4/Laws/Api/{SessionMeaning,SessionMeaningLoop,SessionRef,HostDrive,Live}.lean`, `src/Effect4/Laws/Program/{HostRuns,DenoteRows,DenoteRowsB}.lean` | reading | §3, §4 |
| `docs/research/2026-10-09-host-coalgebra.md`, `docs/research/2026-10-14-view-from-semantics.md`, `docs/DESIGN-BASIS.md` DB-03 | reading | what was planned and landed |
| `Test/Dogfood/Scenario/Vessel/*.lean`, `apps/vessel/{README,PLAN}.md` on `codex/vessel-dogfood` | reading, by `git show` | §6 |
| The partner seat's `docs/research/2026-10-16-itrees/rocq/{Denote,Run}.v` (work in progress, `modest-sammet-90f7b7`) | reading | §4.6 |
| The three new modules, built with `lake build` | proved | §4.2, §5 |
| `#axiom_audit` over the three modules | proved | 64, 6 and 6 declarations within `[propext, Quot.sound]`; one planned goal |

## 3. One structure under the session

### 3.1 The objects, each with one representation

| Object | Representation | How it is made |
| --- | --- | --- |
| call tree | `Effects.Program (RowsSig table) ExitV` (`denoteRows`) | a fold of `Eff` (K1) |
| call chain | `Chain (RowsSig table) ExitV` (`effChain`, new) | the budgeted call trees (`denoteRowsB_approx`) |
| host | `Effects.Comodel (RowSig table) σ` | a reactor read as a host (`reactorHost`), or any construction of `Effects.Comodel` |
| meaning under a host | `hostRun`, `hostRunB` | the host's run of the tree, routed beside the stores (`rowsHost`) |
| reply tape | `ReplyTape := List ExitV` | the exits of a run's applied replies (`appliedExits`) |
| journal | `List Command` | the rows a run played; `play` folds them (K5) |
| decision tape | `List Api.Decision` | the journal's projection (`tapeOf`) |
| machine | `RunMachine`, stepped by decisions | `replayEval`, a function of the tape (DB-03) |
| session system | `Effects.System (RowSig table) …` (`sessionSystem`) | the call tree with its stores hidden (`Effects.System.peel`) |

### 3.2 The four readings

- **The call tree is the unfolding of the session's coalgebra: yes, on one fiber.** The session
  system is the call tree with its stores hidden. Its unfolding at enough depth is the session's
  observation, both ways (`sessionSystem_finished`, `sessionSystem_finishes`).
- **The session is a path: yes.** A finished run's reply tape is the branch it took. Following a
  branch is running the tree against the reply host (`tapeHost`, `Effects.Comodel.replies`). So H8
  (`denoteRows_eq_session`) is H9 (`denoteRows_eq_session_host`) at that host.
- **The journal is a word acting on the run: yes.** `play` is a fold, so a journal splits anywhere
  (`journal_play`, `replay_append`). Its decision tape is the projection `tapeOf`, and the action
  commutes with it (`tape_replays`).
- **A decision tape is a strategy: no, it is a play.** A strategy answers from a state of its own:
  a reactor, read as a host (`reactorHost`). A tape is what a strategy wrote. Recording a host's
  answers and replaying them is the same run (`Effects.Comodel.run_record_replies`).

### 3.3 The one free object

The free object is the free monad `Effects.Program (StoreSig ⊕ RowSig table)`, and its chains for
loops. Every other object of §3.1 is a fold of it, an unfolding of it, or a path through it.

What is not yet such a reading is the session of the whole machine. Its positions are the work a
run offers (`Run.work`), and its directions are decisions. The coalgebra note drew it
(`docs/research/2026-10-09-host-coalgebra.md` §2). It is not built: the landed session system
covers one fiber, at the machine's settled forms.

### 3.4 The pairwise lemmas one simulation would replace

One relation, a simulation of the session by the call tree (`Effects.IsSim`), gives each row below
by a theorem of `Effects` proved once. The coalgebra note named it `rows-next-call`.

| Pair | Today | From one simulation |
| --- | --- | --- |
| session, tree under the reply host | `denoteRows_eq_session` (H8) | H9 at `tapeHost` (already so) |
| session, tree under any host | `denoteRows_eq_session_host` (H9), through `tape_holds_host` | `Effects.Program.run_of_sim_program` |
| drive, tree | `runWith_denotes`, `runWith_denotesB`, the guarded, host and layer forms | H9 at `reactorHost`, `hostGuard`, `Effects.Comodel.through` |
| system, session | `sessionSystem_finished`, `sessionSystem_finishes` | the simulation's unfolding |
| recorded call, tree | `request_in_tree`, `bound_in_tree`, with their own invariant (`CallTree.lean`, 2942 lines) | `Effects.unfold_approx_of_sim`: a call the machine reaches is a node of the tree |
| frontier, tree wait | `rows_loop_frontier`, `rows_loop_frontier_host` | `Chain.Waits` (§4) |
| loops, tree | `h8_loopedRows`, `denoteRowsB_eq_session_host` | `Chain.Finishes` (§4) |

Today H8, H9 and the driver theorems share one induction (`tape_holds_host`). The call-tree prefix
law is a separate route. The simulation would make it a corollary, and it would reach unsettled
prefixes, which the settled-form route does not.

## 4. An interaction-tree reading that works

### 4.1 Three carriers

| Carrier | What it unlocks | What it costs |
| --- | --- | --- |
| The `Effects` coalgebra: `System`, `IsSim`, `IsBisim`, `Comodel` | landed; one simulation gives every host; hosts compose with a law each; no new dependency | behaviour is no object: a system is read by its finite unfoldings |
| Coinductive trees of polynomial functors (QPF, `PFunctor.M`) | a limit object; equality is bisimilarity | Mathlib, which this tree does not depend on; an axiom gate risk; no generator runs an M-type |
| Finite approximants: chains of trees, or prefix-closed trace sets | the budget and frontier rules already work this way; every judgment is a statement about finite trees | infinitely many answers (`ExitV`) make depth unbounded across branches, so a limit is per path |

**Chosen: chains of finite trees over the `Effects` coalgebra.** The judgments are observational,
under hosts, so infinite branching costs nothing. The budgeted call tree is a chain already
(`denoteRowsB_approx`). The partner seat's Rocq reading counts the same three outcomes
(`observe_n`: `Done`, `Waiting`, `Unfinished`).

### 4.2 What landed (`CallChain.lean`)

| Declaration | Statement | Status |
| --- | --- | --- |
| `Chain`, `Chain.ofSystem`, `Chain.ofProgram`, `effChain` | a chain; a system's unfoldings; a finite program; a program of `Eff` by `denoteRowsB` | definition |
| `run_approx_none` | a host that leaves a call of an approximant unanswered leaves it unanswered above | proved |
| `Chain.Finishes`, `Chain.Waits`, `Chain.Diverges` | finishes or waits at some budget; reaches a cut at every budget | definition |
| `Chain.finishes_le`, `Chain.waits_le` | a finish and a wait persist at every larger budget | proved |
| `Chain.Finishes.not_diverges`, `Chain.Waits.not_diverges`, `Chain.Finishes.not_waits`, `Chain.Finishes.unique` | the outcomes exclude one another; a finish is unique | proved |
| `Chain.Refines`, `Chain.Equiv` | every finish and wait of one, under every host, is the other's; both ways | definition |
| `Chain.Refines.diverges`, `Chain.Equiv.finishes_iff`, `waits_iff`, `diverges_iff` | `Chain.Equiv` chains have one outcome under every host, divergence included | proved |
| `Chain.refines_of_sim`, `Chain.equiv_of_bisim` | a simulation gives refinement; a bisimulation gives `Chain.Equiv` | proved |
| `Chain.ofSystem_program_equiv`, `Chain.ofProgram_not_diverges` | a finite program's coalgebra reading is itself; it never diverges | proved |
| `effChain_bind_succeed` | closing a body with a term is the body at the extended environment | proved, R6 |
| `EffEquiv`, `EffEquiv.hostRunB_iff` | program equivalence at a table; it keeps every finish under every row host | defined; proved, R6 |

### 4.3 How `Eff` relates to the carrier

- **Denotation.** `effChain table e env` is the chain of `denoteRowsB`. On `StraightRows` it is
  constant, `denoteRows` finished (`denoteRowsB_straight`).
- **An equivalence like `eutt`.** A call tree has no silent node: internal steps are no nodes, and
  the stores are hidden by their handler. So `Chain.Equiv` on approximants plays the part of weak
  bisimilarity. `EffEquiv` lifts it to programs at a table.
- **`interp` is host handling.** A handler that implements rows by programs over other rows, with
  a host for those, is a host (`Effects.Comodel.through`, `run_through`). Typed handlers compose
  (`Effects.Handler.Typed.through`). The driver already uses it (`runWith_layer_denotes`).
- **The session is an `interp`.** The session's meaning is the host's run of the call tree (H9).
  Its outcome is the chain's (`runWith_finishes`, `frontier_waits`, §4.5).

### 4.4 `RProgram` and interaction trees: a stated relation

`RProgram` is `Effects.Program RSig ExitV`, an inductive tree over `SyncOp ⊕ FiberOp`.

1. It is the finite, silent-free part of an interaction tree: its coalgebra reading is itself
   (`Chain.ofSystem_program_equiv`), and it never diverges (`Chain.ofProgram_not_diverges`).
2. Divergence enters only through a budget, as a chain: `denoteR`'s fuel and `denoteRowsB`'s `k`.
3. The `interp` reading covers `SyncOp` (the store handler) and the host rows. It does not cover
   `FiberOp`: its handler is a total stand-in that is no semantics (`fiberRefusal`), and the
   scheduler is the decision tape. So the comparison holds for the store and the hosts, and the machine owns the fibers.

Proposed dictionary edit, not made. In the row "residual program", this relation and its two
pointers replace "interaction trees (Xia et al. 2020), by analogy".

### 4.5 The three judgments DB-03 asks for

`docs/DESIGN-BASIS.md` DB-03 asks for explicit trace, divergence and equivalence judgments.

- **Trace.** A run's trace is its path: the reply tape, written by a recording host
  (`Effects.Comodel.record`) and replayed by the reply host.
- **Divergence.** `Chain.Diverges`: a cut at every budget. A frontier is a wait, which excludes it
  (`Chain.Waits.not_diverges`). So "a frontier at every budget" is now told apart from divergence.
- **Equivalence**: `Chain.Equiv`, observational under every host.

At the session (`Outcome.lean`): an exiting drive is the chain's finish (`runWith_finishes`), so a
diverging chain has no exiting drive (`runWith_exit_of_diverges`). A frontier is the chain's wait
(`frontier_waits`), so a diverging chain leaves no awaited call unanswered
(`frontier_of_diverges`). The converse is the planned goal `rows_divergence_adequate`. Its route
needs the open claim `embedded-budget-sufficient`.

### 4.6 What it unlocks

- **Rewrites that keep the session theorems.** A rewrite of `Eff` shown `EffEquiv` carries a
  driven run's exit to the new program (`effEquiv_runWith`). The first instance is closing an
  entry with its request (`effChain_bind_succeed`), the vessel's `programFor`.
- **Frontier against divergence at R12.** The three outcomes are a statement now.
- **Hosts for free.** A generated host is a comodel. Routing, renaming, layers, guards, recording
  and replay each come with one law, so a generated test harness inherits record and replay.
- **A meeting point with the Rocq seat.** Its `observe_n` outcomes are this module's three. An
  extracted OCaml run and a Lean chain can be compared outcome by outcome. Its recursive
  definitions (`mrec`) suggest the next Lean item: definitions in the chain, by budgeted
  unfolding, monotone as loops are.

## 5. Graph semantics

The program graph is the address table of a program (`Node.addresses`). A site census is a
`filterMap` over it: `HeapSites.performSites` (each `perform`), `programCalls` (each call with its
checked instance), and the write sites behind `heap_sites_keep`. The call graph is the call
tree's paths. One law joins the two (landed): `request_performed`, built on
`origin_addresses_call`. Every host request a recorded, funded run holds is a `perform` site's.

| A generator computes | From | Law | State |
| --- | --- | --- | --- |
| the call map, dogfood friction F10 | `HostSession.callTable` with each row's name | `lookup_programCalls`, `reached_callInstance`, `request_performed` | the laws exist; `Built.calls` is one function in `Api/Built.lean`, a D2 file, so it is proposed |
| the rows a host must answer | the rows of `performSites` | `request_performed`: no run asks another row | proved; an over-approximation, since a site may be dead |
| the services a program reaches | the requirement row of its type (`EffTy.requires`) | the checker's typing; the typed state's M7 | exists; the vessel guards it by `#guard` |
| two calls that commute | the binder table (`tools/Effect4Gen/binders.json`): a request term that reads no earlier answer | a call independent of an earlier answer commutes with it under a routed host (`Effects.Comodel.route`) | proposed, not stated |
| the score's join to the program | the call's origin (`originOf`) on a journal's `bind` | `request_performed` | the view note's gap G1; proposed |

## 6. The vessel dogfood

The workflow (`Test/Dogfood/Scenario/Vessel/Workflow.lean`) is one straight program with two host
calls, geometry then simulation, and a check after each. It is in `StraightRows`, so H8, H9, the
call-tree prefix law, the session system and the new outcome laws all reach it.

What the semantics says, and where the author meets friction:

- **V1, study identity is checked by hand.** Each reply must echo the request's vessel, revision
  and input digest (`sameStudy`), written as `require` checks. A row's operation carries its
  request value (`RowSig`'s `Op` is a row and a request). So a protocol of the row signature can
  say that an answer echoes its request (`Effects.Protocol`). `Effects.Comodel.guard` enforces it
  at the boundary, and `Effects.Program.Sat` proves that the workflow never refuses a foreign
  study under such a host. The checks then become a typed fact instead of runtime code.
- **V2, the browser re-implements the session's ledger.** `Reactive.update` is a total comodel of
  its event signature, a Mealy machine. Its stale-token rule (`stale_ignored`) restates the
  session's key discipline (`session_keys_once`, `stale_never_applies`). A generator could derive
  the browser's request control from the session protocol.
- **V3, the two calls are independent in data.** The simulation's request reads no geometry
  reply, so the two calls could run together. The order is control: the simulation runs only if
  geometry passes. The commutation law of §5 would let a generator offer that choice with a proof.
- **V4, closing the entry.** `programFor` binds the request before the open body;
  `effChain_bind_succeed` says its chain is the body's at the extended environment.

## 7. Placement of every obligation

| Obligation | Question: concept, role, pointer | Reach | Does not establish | Unlocks |
| --- | --- | --- | --- | --- |
| The outcomes of a chain | `translation-simulation`, the proposed claim `call-chain-outcome`; `Chain.Finishes.not_diverges` and its kin (proved) | every signature, host, start and chain | anything of the machine | R12's frontier against divergence |
| `Chain.Equiv` of chains | `translation-simulation`, `call-chain-equivalence`; `Chain.Equiv.diverges_iff` (proved) | every chain and host | that two programs need one budget | rewrites of `Eff` |
| `RProgram`'s behaviour | `initial-algebras-folds`, `program-behaviour`; `Chain.ofSystem_program_equiv` (proved) | every finite program | the fibers' meaning | the dictionary row's relation |
| Closing an entry | `translation-simulation`, R6; `effChain_bind_succeed` (proved) | every table, term and body | a session of the closed program | the vessel's `programFor` |
| `EffEquiv` keeps finishes | `translation-simulation`, R6; `EffEquiv.hostRunB_iff` (proved) | every table and row host | equal budgets | `effEquiv_runWith` |
| A drive's exit is the chain's finish | `host-session-protocol`, `rows-loop-outcome`, R6; `runWith_finishes` (proved) | loops, a reactor in the envelope | that the drive finishes | the two R12 laws below |
| Divergence excludes an exit and a frontier | `host-session-protocol`, R12; `runWith_exit_of_diverges`, `frontier_of_diverges` (proved) | loops, every budget | divergence itself | R12's divergence adequacy |
| A rewrite carries the drive | `host-session-protocol`, R6; `effEquiv_runWith` (proved) | loops, `EffEquiv` | a session of the rewritten program | authored rewrites |
| Divergence adequacy | `host-session-protocol`, `rows-divergence-adequate`, R12; the goal `rows_divergence_adequate` | loops, a reactor in the envelope, fixed rounds | progress, fairness | R12 closed at the driver |
| The call map | `host-session-protocol`, `performed-rows`, R6; `request_performed` (proved) | recorded, funded runs | that a site is reached | F10, a host restricted to its rows |

## 8. Proposed edits to files of the coordinator's D2 slice (not made)

1. `Api/Built.lean`: `Built.calls`, each call's address, row name and checked instance (F10).
2. After D2, the three new modules take `{app : SigApp}` where the session laws do.
3. `docs/core/controlled-english.md`, the row "residual program": the relation of §4.4.
4. The simulation of §3.4, then `CallTree.lean`'s prefix law as its corollary.
5. A request-indexed protocol of a table's rows, for V1, beside `RowProtocol.lean`'s.

## 9. What this does not establish

- The session of the whole machine: §3.3's system is drawn, not built.
- The simulation of §3.4 is a proposal. Today's theorems keep their own proofs.
- Divergence adequacy is a planned goal, and its route needs `embedded-budget-sufficient`.
- `EffEquiv` quantifies over every host of the row and store signature. A rewrite that holds only
  under the real store needs a narrower relation.
- The graph laws of §5 beyond `request_performed` are proposals.
- The vessel reading is by source reading; no vessel run was made.
- The three modules use the session laws before D2. After D2 they need its index.
- The build covered the three modules and their imports, not a root or a battery.
