# Typed-state admission audit (2026-09-23)

Status: findings recorded with checked witnesses; the repair is proposed and **not landed**. The
owner asked for this audit before any repair lands. Decision row 89 carries the choice.

## 1. The finding

The typed-state invariant's program judgment, `TypedProg` (`Typed/Residual.lean`), refuses
most programs the checker admits. A protocol row whose postcondition is `True` demands a typed
continuation for every answer, including answers of the wrong type. When generated code feeds
that answer into its result, no type satisfies the demand. The loaded code of a checker-typed
`sleep(1)` is such a program: `E4-SCHED-CE-013`,
`Test/Counterexamples/Machine/Semantics/TrivialPosts.lean`.

The same defect in the guard row meant that, from the M3a landing (`ef38bf11`, 2026-09-21)
until the contract ruling (`5f81d35f`, 2026-09-23), the judgment refused **every program
containing a `bind`**: `denoteR` compiles each bind through an `onSuccess` guard. No control
noticed, because every positive control was a hand-written program. Generated code first met
the judgment in the slice 5 preflight.

## 2. What this does and does not reach

Not affected. These are proved and do not mention `TypedProg`:

- the checker against the typing relation (`check_sound`, `Typing/CheckSound.lean`, and its
  completeness companion);
- meaning soundness on the straight fragment (`sound`, `Laws/Program/MeaningSound.lean`) and
  the looped fragment (`soundB`, `Laws/Program/LoopSound.lean`);
- runtime agreement of the compiled and reference machines (`run_eq_ref`), and the truth
  harness's agreement with the pinned host.

Affected: type soundness for everything outside the straight and looped fragments. `Straight`
(`Program/Fragment.lean`) excludes forks, joins and races, performed effects other than `sync`
(so sleep, deferreds and host rows), scopes, resources, layers, services, masks, yields,
generators and conditional catches. For that part of the language the typed-state milestone
(M3–M7) is the only route to a proof, and today nothing is proved there: the judgment the proof
rests on refuses those programs. `E4-SCHED-CE-008` shows the pinned rc.112 runtime itself breaks
typing in that fragment, which is why the divergence `U-01` exists.

So the language's checker is not broken. The claim "a checked program's run respects its
types" is proved only for sequential, effect-free-apart-from-stores programs, and the work
meant to extend it was not yet able to state its first case.

## 3. Audit

Checked means a kernel-checked witness or `#guard` in the tree; reading means the cited code.

| # | Class | Finding | Evidence | Consequence |
| --- | --- | --- | --- | --- |
| A1 | trivial post, fiber | `async`, `awaitAll`, `awaitAllFailFast`, `snapshotChildren`, `awaitNewChildren`, `raceAll`, `raceRegister`, `gen`, `loop`, `scoped`, `forkScoped`, `getContext`, `frontier` have `True` posts and generated code feeds their answer into a result | checked: `async` (the loaded sleep code), `awaitAll`, `frontier`; reading: `DenoteR.lean:176-195, 229-254, 262, 297, 538, 639-659`, `InterpR.lean:320-323` | every program using sleep, deferreds, host rows, joins, races, generators, loops, scopes, services or layers is untypable; a program at the compile-fuel bound is untypable |
| A2 | trivial post, store | `refModify`, `refModifySome`, `deferredPoll`, `memoGet`, `memoBuild` | checked: `refModify` in the shape `denoteR`'s `.perform` arm emits (`DenoteR.lean:594-601`); reading: `memoizeR` (`DenoteR.lean:376-390`) | performed modify/poll rows and every memoized layer are untypable |
| A3 | precondition too strong | `PointTyped` checks a body under `nativeSignature []`: no host rows, default services | checked: `E4-SCHED-CE-014`, a host-row body the checker admits under its table and refuses under `[]`; services by reading (`nativeSignatureWith`) | forked, scoped, masked and resource bodies that use host rows (and likely services) are refused |
| A4 | missing law | no world-weakening law for `TypedProg`, `StrongValue` or `StrongExit`; the hook clauses are stated at one world and consumed at later ones | reading: no such theorem in `src/`; the controls use clean causes to avoid it | if the law fails, the invariant cannot be assembled; it is required before `deliver_*` and assembly |
| A5 | expectation | defensive `badShapeExit` branches are typable, because a defect fits every type | reading: `memoizeR`, the `.perform` arm | "no bad shape" (M7) cannot follow from typing; it rests on the M6 adequacy of the posts |
| A6 | adequacy | none of the 71 posts is proved true of the machine; the repair makes posts stronger | ledger: no M6 obligation declared yet | a post the machine does not satisfy makes the judgment unsound; each strengthened post needs its declared adequacy obligation |
| A7 | coverage | frame and hook contracts are checked against one generated stack (the sleep cleanup) | `Test/Program/TypedControl.lean` | iterator, loop, finalizer, mask-restore and race-cleanup stacks have no positive control |
| A8 | to check | the join row types its answer at the fiber table's entry, not at the program's expected type | reading: `fiberPost` `.await` | typable only if world validity ties the table to fork certificates; unverified |
| A9 | to check | `construction` (post `True`) answers the completed exits, which callbacks may inline as results | reading: `constructR`, `prepareR` | may be a further A1 case |
| — | not affected | `suspend` (the continuation ignores the answer), `refuse` (precondition `False` by design), `closeIter` (post pins the answer), the unit-answer rows | reading | none |

## 4. Why it was missed

The frozen statements were reviewed by reading, and their positive controls were written by
hand. The coordinator's ruling today repeated the pattern: it fixed the guard row, deferred the
rest to M6 without checking which rows generated code uses, and listed the rows by shape (with
`closeIter` wrongly in and `scoped`, `forkScoped`, `getContext` and the five store rows missing).
The corrected list is §3.

## 5. Deeper dive: recommended before any more hard proofs

- **D1, generated-code admission census.** A battery that, for every source constructor, loads a
  minimal checker-typed instance and either proves its loaded code (and its parked stacks under a
  small canonical tape family) typed, or retains a checked refusal. Gated like the answer gate:
  every constructor accounted for. It is the finite preview of M5's "the denotation is typed" and
  would have caught A1–A3 and the bind case. A slice of its own: the census command and roughly
  one probe per constructor.
- **D2, dynamic soundness lane.** Over the corpus's well-typed programs, run the reference machine
  under the same tape family and check every exit fits its checked type. Empirical and bounded,
  for the fragment with no proof; `U-01` is the kind of hole it finds. A driver and a make target.

## 6. The repair (proposed, not landed)

1. Each A1/A2 row certifies the type of its answer, ties it to the source in its precondition (a
   scoped or forked body checked at it, a race's entrants, a join's targets through the fiber
   table, a generator or loop body), and answers a typed value or exit at it, in the guard row's
   shape. `frontier`'s post admits nothing: running out of fuel is never an answer.
2. `PointTyped` checks under the program's row table and services, carried by the root.
3. The world-weakening law is stated as an obligation.
4. Each strengthened post gets its M6 adequacy obligation, declared, not proved.

Order: D1 first, so the repair is known complete when it lands; then the repair with D1 green;
then slice 5's assembly. Slice 5's generic stack proofs do not depend on the rows and can proceed.

## 7. Errata to the 2026-09-23 contract ruling

- Its list of affected rows is replaced by §3 A1–A2.
- `docs/STATE.md` said nothing blocks the packet. Slice 5's assembly is blocked on §6.
