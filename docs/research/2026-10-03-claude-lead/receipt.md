# Receipt: slice T-LOW (2026-10-03, Claude lead)

**First, the one thing to know before merging.** `M7.exitHandles_valid` is proved as stated, with no
contract change. No proof of M5 or M6 reads the lawful-signature or closed-row premise, so `J` holds
on every checked program, and the goal follows from `J` and capability membership. With it the M7
ledger is closed (4/4), and T1 lands: every exit the frame machine records satisfies the meaning
layer's judgment, on every fragment. One store invariant of the simulation (`StoresOk`) gained a
field; the whole law graph was rebuilt green.

- **Base:** `d673a246`.
- **Head:** the commit carrying this receipt, on `claude/proofs`, fast-forwarded to
  `refactor/phase1-phase3`.
- **Notes:** the foundations note `docs/research/2026-10-03-claude-lead/foundations.md`:
  - §11, the concrete definitions the owner asked about;
  - §12, this slice.

## Changed files

| File | Change |
| --- | --- |
| `src/Effect4/Laws/Machine/Book.lean` | `book_replayEval_ok`: the left instance's invariant at the end of any replay |
| `src/Effect4/Laws/Program/Simulation/Hooks.lean` | `StoresOk.externals` (no external handle allocated); the frame-rule guard updated (7 theorems, 11 reused, 3 premises); five construction sites |
| `src/Effect4/Laws/Program/Simulation/{Actions,Deliver,Drive,Evaluate}.lean` | the field at the scope-link, scope-close, finalizer-drop and scoped-entry sites; `scopeLinkFiber_externals` |
| `src/Effect4/Laws/Machine/StoresLaws.lean` | `syncOpStep_memoGet_families` also gives `externals` |
| `src/Effect4/Laws/Program/RuntimeR.lean` | `replay_ok`, `replay_externals`, `replayR_externals` |
| `src/Effect4/Laws/Program/Typed/Assembly.lean` | `load_typed_of_denotesTyped` (premise-free; replaces `loadsTyped_of_denotesTyped`); `AdmittedTape`, `admittedTape_of_noHostAnswer`, `admitted_typed`; `reachable_of_ledger` derived; `obsTyped_admitted` (replaces `m7_of_capstone`); `m7_of_ledger` derived; the `#proof_wanted M7.exitHandles_valid` removed; docstrings |
| `src/Effect4/Laws/Program/Typed/Commands/Finish.lean` | `load_typed_of_denotesTyped_typed`; `loadsTyped_of_denotesTyped_typed` derived |
| `src/Effect4/Laws/Program/Typed/LayerArm.lean` | `load_typed` |
| `src/Effect4/Laws/Program/Typed/Commands/Clauses/All.lean` | `reachable_typed`, `obs_typed`, `exitHandles_valid`; M7 report at ceiling 0 |
| `src/Effect4/Laws/Program/Typed/Results.lean` (new) | `exitHasTy_of_exitOk`, `exits_hasTy` (T1), `root_exit_hasTy`; ledger `M7Results` |
| `src/Effect4/Laws.lean` | imports `Typed.Results` |
| `src/Effect4/Laws/Program/Typed/Edits.lean` | cut: `HandlesRegistered`, `validIn_of_ok`, `answersValid_of_noHostAnswer`, `exitHandles_valid_of_registered` (superseded) |
| `src/Effect4/Laws/Program/Typed/ExitConnector.lean`, `Handles/Term.lean` | stale docstrings repaired |
| `Test/Program/{RawHandleTerms,LayerRefs,TypedDenotation,TypedSplit}.lean` | renamed or cut declarations |
| `tools/Tools/ProofMapSelection.lean` | two renamed declaration names |
| `docs/core/system-map.md` | M7 status lines |
| `docs/research/2026-10-03-claude-lead/{foundations,receipt}.md` | §11, §12; this receipt |

## Commands and results

- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.RuntimeR`: green after two repairs. The
  first was an `Eq.trans` at the wrong level; the second, a `rw` against `replayR`'s unfolded form,
  was replaced by rewriting the hypothesis.
- `LEAN_NUM_THREADS=3 lake build Effect4.Laws`: **green, 579 jobs.** Ledger reports:

  | Ledger | Proved |
  | --- | --- |
  | `M7` | 4/4 |
  | `M7Results` | 1/1 |
  | `M6Ledger` | 20/20 |
  | `M6Clauses` | 2/2 |
  | `M6Edits` | 13/13 |
  | `M3bAssembly` | 5/5 |
  | `Sched.M1Hooks` | 4/4 |

- `lake build` of the 31 test modules that import a changed module, plus
  `Test.Program.CapabilityMembership`: **green, 446 jobs.**
- **Axioms** (`lake env lean` on a scratch file): `[propext, Quot.sound]` for all of
  - `exits_hasTy`, `root_exit_hasTy`, `exitHasTy_of_exitOk`;
  - `exitHandles_valid`, `reachable_typed`, `obs_typed`, `admitted_typed`, `load_typed`;
  - `replay_externals`, `replayR_externals`, `replay_ok`;
  - `book_replayEval_ok`.

No full battery or `make check` was run; the owner runs sweeps.

## Placement of each landed theorem

| Theorem | Concept | Question | Reach | Not established | Unlocks |
| --- | --- | --- | --- | --- | --- |
| `exitHandles_valid` | 10 (and 4) | `M7.exitHandles_valid` | lawful, checked, `RReachable` (as stated) | host answers; the native registered-byte fact (no longer needed) | the M7 ledger closed |
| `reachable_typed`, `admitted_typed` | 4 | serves `M6Ledger.typedState_reachable` (derived from it) and T4 | every checked program, every `AdmittedTape` | executable admission (`admit_sound`, row 97); a table-aware machine | T4 reduced to `admit_sound` |
| `obs_typed`, `obsTyped_admitted` | 10 | serves M7a–c (`m7_of_ledger` derived) | the frame machine at its empty row table, every admitted tape | DI-57 | M7 over ghost-admitted host answers |
| `load_typed`, `load_typed_of_denotesTyped` | 3 | serves `M3bAssembly.typedState_load` (derived) | every checked program | the closed row stays part two's premise (row 117) | the open-row forms above |
| `replay_externals`, `book_replayEval_ok` | 10 | a step of `M7Results.exits_hasTy` | every tape, the frame machine at the empty row table, the reference | nonempty row tables | the connector's allocation premise |
| `exits_hasTy` (T1), `root_exit_hasTy` | 10 | `M7Results.exits_hasTy` (declared and proved, `Typed/Results.lean`) | every checked program, every admitted tape, observation `obs` | `missingService` on closed rows (row 117); progress; the OCaml engine | the quotable claim: a checked program's recorded result has its checked type, every fragment |

## Proposals for the coordinator (not edited here)

Not edited because the main checkout holds uncommitted changes to `docs/core/semantics.md` and
`generated/semantics.*`, and `decisions.md` is the coordinator's.

**Decisions rows.**
- **Row 180:** superseded. `M7.exitHandles_valid` is proved by the typed route; the native
  registered-byte invariant has no consumer, and its route was cut.
- **Row 117:** record that `LoadsTyped`'s closed-row premise is unread by any proof. `J` holds on
  open rows; the premise is kept for part two (the presence clause).
- **Rows 138 and 139:** the M7 ledger closed, 4/4.
- **Rows 97–99:** T4's typing half is proved over ghost admission (`reachable_typed`,
  `obs_typed`). What remains is `admit_sound`.

**Registry claims** (`tools/Tools/SemanticsRegistry.lean`):

| id | Concept | Role | Pointer |
| --- | --- | --- | --- |
| `load-typed-checked` | residual-program-typing | preservation | witness `load_typed` |
| `typed-state-admitted` | reactive-scheduling | preservation | witness `reachable_typed` |
| `obs-typed-admitted` | translation-simulation | adequacy | witness `obs_typed` |
| `m7-results-exit-hasty` | translation-simulation | adequacy | goal `M7Results.exits_hasTy` |
| `replay-externals` | translation-simulation | preservation | witness `replay_externals` |

`m7-exit-handles-valid` flips to proved on the next regeneration.

## Open, and bounded evidence

- **Open from the foundations note's §7:** T3, T4's remainder (`admit_sound`), T6, T7, T8 and T9
  (sized in §12 of the note).
- **Bounded:** every result here is about the frame machine at its empty row table and the term
  reference. Nothing is host-only, and nothing is a finite probe.
