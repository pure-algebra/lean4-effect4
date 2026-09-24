# Slice 5 contract ruling (2026-09-23)

Ruling on [the proposed amendment](2026-09-23-foundations-slice5-contract-amendment.md) after
the coordinator's review. The owner approved landing it in the coordinator session on
2026-09-23. It governs slice 5 from here and amends the
[slice 5 brief](2026-09-21-codex-brief-foundations-slice-5.md) §2, §3.2, §3.3 and §3.6.
Runtime code, stored syntax, decision tapes, the world order, the axiom ceiling, `U-01` and its
signed host exception are unchanged. The hard proofs keep `InterruptProvenance` and `HookLaws`
as their only premises.

## What was established

The three counterexamples are checked and reachable (`E4-SCHED-CE-010/011/012`,
`Test/Counterexamples/Machine/Semantics/AsyncHookContract.lean`, rebuilt by the coordinator:
every theorem at `[propext, Quot.sound]` or less). One finding is wider than the proposal
said. Under the protocol judgment a postcondition is a demand on the program: every answer
it admits needs a typed continuation. A `True` post on a row whose answer flows into a leaf
therefore makes the program untypable. The guard row is one case. The join-all park code
`interpR` installs is another: `joinAll_untypable` in
`2026-09-23-foundations-slice5-ruling-evidence/TruePostProbe.lean` proves it untypable at
answer `nat`, at `[propext, Quot.sound]`. The same holds of every row that answers an exit or a
value straight into `pure` under a `True` post: `awaitAll`, `awaitAllFailFast`,
`snapshotChildren`, `awaitNewChildren`, `raceAll`, `raceRegister`, `async`, `gen`, `loop`,
`closeIter`, `frontier`.

## The ruling

1. **Async hook premise (proposal item 1): approved as written.** The concrete clause in
   `frameProtocols root` is
   `tin = tout ∧ ∀ cause, StrongExit w tin (.failure cause) → cause.hasInterrupts = true →
   TypedProg root w tout ((interpR root).cancelThenFail name cause)`. `popR` holds that
   `StrongExit` at the arm; the `HookLaws` field in `Typed/Stack.lean` takes the same text.
2. **Guard row (item 2): approved.** `FiberCert (.guard_ kind) = EffTy`, the guard's
   intermediate type. `fiberPost` at `none` is `True` (body entry); at `some ex` it is
   `kind.hasExitArm ex = true ∧ StrongExit w' cert ex`. No other row is opened. The rows
   listed above keep their `True` posts in this slice; §3.6 of the brief now makes each
   M6 declaration for them state its strengthened post in the guard row's shape, with the
   adequacy obligation "the machine's actual answer satisfies it". Installing those posts is
   the M6 slice.
3. **Control admission (item 3): approved, in a different shape.** The proposal kept two
   judgments over one program, each choosing its own certificate per operation. When they
   choose differently, the machine's actual answer satisfies the post at one certificate
   while the continuation is admitted only under the other. The certificate must be shared.
   `TypedProg` is now one inductive (`Typed/Residual.lean`) and `ControlAdmitted` is retired:
   - `pure`: `StrongExit` at the current type;
   - `store`, `fiber`: one certificate from `Ψ_S`/`Ψ_F`, its precondition, and a continuation
     for every answer the postcondition admits at every later world; the fiber arm excludes
     the four markers by name;
   - `guard`: a certified intermediate type `mid`; the body typed at `mid`; `run` for every
     exit the guard row's post admits at `mid`; `skip`: an exit at `mid` that the arm does not
     take fits the outer type;
   - `unguard`, `finishFinalizer`: the payload at the current type, and no continuation. The
     reference machine never resumes either continuation (`evaluateFiberR` hands the payload
     to `deliverR`; `popR`'s answer glue passes it to the next frame), so none is typed;
   - `scopeExit`: the payload and a continuation for every answer, as before.

   The review said the protocol-only judgment would be proved as the erasure of the merged
   one. That is false as stated: the merged judgment does not type a marker's continuation,
   so it does not imply the protocol judgment. `Typed` stays the Effects library's judgment;
   `Ψ_S` and `Ψ_F` stay the manifest that the answer gate and M6 read.
4. **The R3 frame contract lands with this ruling**, because the repaired controls need it:
   `FrameAccepts` takes the exit judgment as a parameter (`Exits`), `resume.skip` is
   guard-miss-only, and `frameProtocols root` carries the async clause above with the
   iterator and loop protocols from Codex's checked attempt (mutually inductive step
   witnesses, the strictly positive form of the brief's existential clause).
5. **Organization.** `ExitFits` moves from `Typed/Contracts.lean` to `Typed/World.lean`
   beside `CompletionOk`, which it restates. `Contracts` becomes a parametric interface that
   imports only the world; `Validity` and `Admission` no longer import it. `cleanExit` and
   `strongExit_of_clean` land in `Typed/Admission.lean` beside `StrongExit`, instead of
   `Typed/Stack.lean`. The payload inversions and their obligations move with `TypedProg`
   into `Typed/Residual.lean`, under their existing names, so the ledger is unchanged.
   `Typed/Admission.lean` drops four imports it no longer uses (the source admission check,
   the program handle laws, the protocol and the ledger); `Typed/Residual.lean` imports the
   protocol and the ledger it uses directly.
6. **Layering, measured.** Regenerating the architecture map at this landing found three
   imports against the register's direction that arrived after the 2026-09-20 map, two of
   them making area pairs that import each other. None came from this ruling; all three are
   repaired here, with declaration names unchanged:
   - `Laws/Auto/AnswerGate.lean` (instruments) imported `Laws.Program.Sched` only to find the
     fiber alphabet; it now looks the name up in the invoking file's environment, and
     `Test/Audit/AnswerGate.lean` imports the scheduler;
   - `Laws/Program/Guard/TraceOrigin.lean` declared API-namespace obligations over API
     supervision facts and imported `Laws.Api.Supervision`; it moves to `Laws/Api/`;
   - `Laws/Effects/ProtocolObligations.lean` registered the protocol's laws in the ledger and
     imported `Laws.Auto.Obligations`, against its area's rule (the pinned `Effects` only); it
     moves to `Laws/Program/Typed/`, beside the ledger's users.

   The regenerated map reports no import against the direction beyond the two accepted by
   `docs/ARCHITECTURE.md`, and no area pair that imports each other.

## Controls

`Test/Program/TypedControl.lean`. Positive: the sleep cancellation with an interrupt-only
cause; the exact reachable sleep stack under the landed contracts; a `Nat`-removing catch in
the shape `denoteR` gives `catchCause`; an `onSuccess` guard that changes the value type.
Negative: the wrong guard arm; the cancellation with a typed `Fail` at `unit`/`never`; an
`onSuccess` guard whose body fails at an error the outer type forbids, rejected at every
middle type; an ill-typed top-level `unguard` payload. `AsyncHookContract.lean` keeps its
refutations: CE-010 against the landed judgment (the refuted object is the old clause,
already local), CE-011 and CE-012 against local copies of the old guard row and the old
`ControlAdmitted` (`Reviewed…`).

## What slice 5 does next

Codex resumes the brief from `Typed/Stack.lean`: `HookLaws` with item 1's field,
`sanitize_clean_exit`, `popR_typed`, `saveAnswerR_typed`, `deliver_active`, `deliver_stale`,
then assembly, the M6 declarations under the amended §3.6, and the `Keeps` ladder. The
guard arm's `run` and `skip` are exactly `FrameAccepts.resume` at the saved frame; the new
inversion lemmas (`TypedProg.pure_inv`, `guard_inv`, the two payload inversions) are the
entry points.
