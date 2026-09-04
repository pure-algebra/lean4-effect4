# Stress and spam testing: the runtime must not break

Date: 2026-09-04. Ruling: "we should be stress and spam testing our shit; our runtime must
be unbreakable." Status: plan; S1 is the first piece.

Today's finding (the `Iterator` frame cannot carry a second `yield*`, caught by writing a
program as data, not by any test) is the shape of what this lane exists to catch: every
battery in the tree checks a handful of hand-written programs at one tape. Nothing
enumerates programs, tapes or store histories, nothing runs the machine at volume, and
nothing measures how the executable model behaves at depth. Three targets, in the order
they can be built.

## S1. Enumerated invariants over the reference machine (Lean, `#guard`)

`Effect4Test/Deep/Fuzz.lean` (lib `Effect4TestDeep`): a bounded enumerator of programs over
the stores' alphabet (`Deep.Stores.ProgName`, depth ≤ 3, every constructor reachable), a
bounded enumerator of tapes (`RunDecision` lists over the fibers the program can mint,
length ≤ 4, every decision kind), and one runner `replayEval` per pair. Invariants, each a
Boolean over the final machine and its trace, checked by `#guard` over the whole corpus
(thousands of runs; `#guard` evaluates compiled code, so the cost is seconds, and no
`native_decide` enters the tree):

1. `traceWellFormed` and `noNotImplementedDefect` (already witnesses on 13 programs).
2. **Exit once.** At most one `exited` event per fiber; a fiber with an exit has an empty
   stack, no pending parks, no observers, no children, and the empty context.
3. **Observers fire once.** Every `observerFired` is for an observer the fiber held, and
   no observer fires twice.
4. **Finalizers once.** Each `OnExit`/scope finalizer runs at most once (`finalizerRuns`).
5. **Interrupt monotone.** Once `interruptedCause` is `some`, it stays `some` until exit,
   and an exit after a recorded interrupt carries an interrupt reason unless the fiber was
   masked into completion (the M2 witnesses' shape).
6. **Determinism.** The same program and tape yield the same machine (run twice, `==`).
7. **Fuel is a frontier.** A run that stops with fuel exhausted is `running`, never an
   exit; with fuel doubled the trace of the shorter run is a prefix of the longer.
8. **Stuck only by unknown ids.** `Stuck.unknownFiber`/`unknownScope` names an id the
   program never minted (the enumerator's programs name only ids they minted, so the
   corpus must produce no stuck machine at all).
9. **Store conservation.** Ref heap length only grows; a Deferred completes at most once;
   a closed scope stays closed; `due` is empty after every `drainDue`.

The report is data (`FuzzReport`: runs, failures with the program, tape and invariant
index); the battery `#guard`s `report.failures = []` and pins the run count, so a shrink of
the corpus is visible. An `#eval` prints the first failure when one exists.

## S2. The frame machine and the stores under random histories

Same shape for `FrameFiber.run` over enumerated `Prim` trees with a small interp (push/pop
balance in the event stream, `interrupt_skips_every_handler` as a Boolean, termination
with an exit or fuel-out), and for the stores under enumerated operation sequences (Ref
read-after-write, Deferred single completion and one resume per waiter, scope LIFO close
and exactly-once finalizers).

## S3. Spam: volume and depth

The executable model must survive the sizes the host survives. `drive` recurses on every
command and `run` on every step; a 100,000-iteration `whileLoop`, 10,000 forks, 10,000
yields and a 1,000-deep `bind` chain are the probes. Failures here are Lean stack
overflows (the `0xC0000409` fast-fail seen today while building `Deep.Clauses` under load)
or quadratic traces. Fixes are structural: a command loop with an explicit stack instead of
recursion in `drive`'s `finished` arm, traces as difference lists, fuel as the only bound.
Measured, then fixed, then pinned by a `#guard` at the size that used to fail.

## S4. The host at volume (after the host loop)

Once `print` and the run-loop hook exist (lanes A2 and A6), the same enumerated corpus is
printed and run on rc.112 with the `TapeScheduler`, thousands of programs per run, and the
frame streams and outcomes compared with the machine's. This is R4 at scale and the only
place the model's fidelity, not just its consistency, is stress-tested.

## Order and ownership

S1 first (Opus, mechanical once the invariants above are written as Booleans over
`Deep.Witnesses`' helpers), S3's measurement beside it (Opus: the probes and the numbers),
S2 next, S4 with the traces phase. Every finding is a register row with the attack that
found it and the clause that closes it.
