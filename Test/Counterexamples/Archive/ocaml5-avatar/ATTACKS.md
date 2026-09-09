# The avatar's attacks

Packet: the OCaml avatar (`git:14e6835:ocaml/avatar/README.md`), the daemon `effect4d`
(`git:14e6835:ocaml/server/README.md`) and the Lean descriptions, derived twins and
projection guard under `git:14e6835:src/OCaml5/Avatar/Check.lean`.

Archived 2026-09-08 on the local branch `archive/ocaml5-avatar` at `14e6835`, on the
owner's word, under the engine brief's ruling that one OCaml engine (`ocaml/gen`) is the
machine's OCaml and the avatar is retired estate. The two gates that held the avatar to the
Lean machine, `avatar-witnesses` and `armmap-citations`, had been declared red since
`62c04d9` because the hand-written avatar predated the join, the scheduler and the timer;
they left with it.

These are durable semantic attacks. They are retained because they transfer from the
avatar to any host that answers the machine.

## Exit-only answers — `E4-D6-CE-002`

A host that answers a parked fiber with an exit alone cannot express the second
completion the machine admits (`Completion.ofRefGet`, `src/Effect4/Machine/Completion.lean`).
The avatar's hand description of `Fibers.runDecision` carried an exit-only answer while the
description derived from the environment carried a `Completion`, and the projection guard
named the mismatch rather than papering over it. The same attack applies to the engine's
answer facade (`ocaml/engine/e4_engine.mli`, `answer_async_success`) and to the tape's
`E4_diff.decision`: an answer must carry a `Completion`, and a facade that narrows it to a
natural number or an exit is the mismatch this ID names.
