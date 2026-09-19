# The language, as cut: every alphabet against Effect (2026-09-18)

What the stored-program language can and cannot say, read off its inductives at HEAD, and what
each gap costs against Effect 4.0.0-rc.112. Three columns matter: whether the gap is a
**profile decision** the owner ruled (DI-20, DI-28, DESIGN-BASIS "designs excluded"), a **cut**
nobody decided (a first slice never widened), or a **deferral** named in a note. Nothing here is
"a separate issue": a program that cannot say what an Effect program says is not a working
system, and this is the list.

## 1. Terms: first order, twenty atoms, positional binders

`Term := var (index) | lit | app (atom : String) args` (`Program/Eff.lean:254-261`); literals
`unit | nat | bool | str` (`:235`). The atom alphabet (`NativeAtom`): `succ pred isZero not add
lt eq pair fst snd strings causeIsFail causeError causeIsDie causeIsInterrupt or and tagIs
isSome getOrElse`. There is no lambda and no function value.

What the language *does* have is **positional binding**: `bind` extends the environment by the
result, and `iterate`'s `test`/`step`/`result` terms are evaluated at `env ++ [cursor]`
(`InterpR.lean:283`, `:293`), `select`'s arms at the scrutinee's parts, `acquireRelease`'s
release at `env ++ [a, exit]` (`Checker.lean:203`). A function of one argument is a term over
an extended environment. That device exists; it is simply not offered to the rows.

| gap | kind | cost against Effect | the honest fix |
| --- | --- | --- | --- |
| no function-valued arguments to rows: `Ref.update/modify/…` take a `FnName` from `incr double zeroWhenPositive noChange takeAndBump` (`Stores.lean:109-117`) | cut | `Ref.update(r, n => n + x)` with a runtime `x` is unsayable; every `modify` is one of five number functions | rows take a **binder-carrying term** evaluated at `env ++ [current]`, exactly as `iterate` does; `FnName` retires. No closures, no new value kind, the term typer already types it |
| twenty atoms: no subtraction beyond `pred`, no multiplication, no string operations beyond `strings`, **no list atom at all** (no length, head, cons, map), no option constructor, no bytes operation, comparison only `lt`/`eq` on numbers | cut | most data-shaping code in an Effect program is unsayable; lists can be awaited but not built or read | grow the atom alphabet by families with their typing rows (list, string, arithmetic); each atom is one row and one `evalTerm` arm; the typer is the fold |
| no functions as **values** (nothing stores or passes a function) | profile (DI-20/28 refuse polymorphic syntax in a stored program; DESIGN-BASIS refuses storing closures) | `Effect<A>` is a first-class value in Effect; here a program cannot be held in a `Ref` or passed to a service | the basis's own direction is content-addressed programs: a program as a value is a `Val.ref` to its digest, run by a row. Not designed; the profile's answer, not a hole in it |

## 2. Types

`Ty := never unit nat int string bool handle(string) option list prod except exitOf causeOf
fiberOf union lit refOf deferredOf var unknown` plus `scope` (`Ty.lean`; `refOf`, `deferredOf` and the
template parameter `var` since rows 42/43 step 1; `unknown`, the top, since L5). Variance follows rc.112's declarations
(decisions row 55): `fiberOf` covariant (`Fiber<out A, out E>`), `refOf` and `deferredOf`
invariant (`Ref<in out A>`, `Deferred<in out A, in out E>`).

| gap | kind | cost | fix |
| --- | --- | --- | --- |
| `Ref` and `Deferred` are `handle "Ref.Ref<number>"` / `handle "Deferred.Deferred<number, number>"` (`Native.lean:138-150`); rows fix `refGet : nat`, `deferredAwait : nat / nat` | cut | every `Ref<A>`, `Deferred<A, E>` with `A ≠ number` is refused by the checker; the machine runs them (`RefHeap := List Val`) | decisions row 42: `Ty.refOf a`, `Ty.deferredOf a e`, rows with type variables instantiated from the request; before S1 |
| ~~no top (`unknown`)~~ landed 2026-09-18 (L5): `Ty.unknown`, the top of `sub`, inhabited by every value; `Exit<unknown, unknown>` types the release's parameter (row 47) and `Fiber<unknown, unknown>` the children snapshot | — | — | rows 46, 47 |
| no records or variants: only `prod` and untagged `union` (DI-15 gave `tagIs` and subsumption) | deferred (row 2) | Effect programs are records everywhere; a struct is a nested pair with positional access | row 2(b) `Ty.record`/`Ty.variant` before the first foreign consumer; the authoring layer already models tagged tuples |
| `int` has no inhabitant (`TYPED-FB-INT`); no float, no bigint | cut | negative numbers and decimals are unsayable; `Float64` exists only in the JSON carrier | add `Val.int`/`Val.float` with their atoms, or refuse them by name in the printed profile |
| no type variables anywhere; no `Ty.app` (row 3) | profile (DI-20, DI-28) | generic combinators are written per instantiation by a builder | the basis: Lean/OCaml/TS builders are polymorphic, the stored program is closed. Keep, and say it on the surface |
| no function types | profile | follows from §1 | as §1 |

## 3. Values and errors

`Val := unit bool nat str bytes list pair none some ctor(index, args) ref(kind, digest)
handle(kind, key)`. Handles carry a kind byte and no type (DI-17, row 44).

`Err := boom | tag (code : Nat) | tagged (tag message : String) | text (message : String)`
(`Machine/Alphabets.lean`, since L1 of the push; this section first read the S5 spike's stale copy in
`Machine/Context.lean`, which said `boom | tag` and had no consumer — deleted at L1). `Err.value (v : Val)`
is **refused** by the basis (`DESIGN-BASIS.md:640`).

| gap | kind | cost | fix |
| --- | --- | --- | --- |
| an error is a numbered tag, a text, or a tag with a message; no structured payload | profile (DESIGN-BASIS) | `Effect.fail(new NotFound({ id }))` becomes `fail (tag 7)`; a handler cannot read `id` | a ruling: admit `Err.value` with the error column's type, or keep tags and say so on the surface. The typing proofs (`causeAdmits`, DI-62) are stated over the error column and survive either |
| defects are an alphabet (`Defect`) | cut | `Effect.die(anything)` is one of a few names | grows with rows |

## 4. Programs: 25 constructors, 16 actions, 10 layer forms

`Eff`: `succeed fail failCause sync suspend perform bind gen catchCause matchCause onExit exit
uninterruptible interruptible yieldNow awaitFiber withFiber scoped acquireRelease provideLayer
service provideService catchIf select iterate`; `gen` statements: `bindYield yieldDiscard ret
ifElse whileTrue breakLoop`; actions: `fork forkIn forkScoped runIn interrupt interruptScoped
interruptAll awaitAll awaitAllFailFast snapshotChildren awaitNewChildren raceAll setContext
getContext getId closeScope`; layers: `succeed effect effectDiscard provide provideMerge merge
fresh orDie ref mergeAll` (`Program/Eff.lean:304-455`).

What Effect has that no constructor, action, row or atom spells:

| Effect module | status | note |
| --- | --- | --- |
| `Queue`, `PubSub`, `Mailbox`, `Semaphore`, `Latch` | absent | the store has the generic waiter list (`Machine/Wake.lean`) they would sit on; each is a store family plus rows, and the position census then demands their typing source |
| `Stream`, `Channel`, `Sink` | ruled as design only (DI-11: an external handle answering `pull` in a scope) | nothing landed |
| `STM`, `TxRef` | absent | — |
| `Schedule`, `Effect.retry`, `Effect.repeat`, `Effect.timeout` | absent | `iterate` + `sleep` + `raceAll` can encode fixed cases by hand; no schedule value |
| `Config` | absent (a design note of 2026-09-10 with decisions D1–D5 pending) | — |
| `Cache`, `Effect.cached`, `memoize` | absent (layer memoisation exists) | — |
| `Logger`, `Metric`, `Tracer`, `Random` | absent | — |
| `FiberRef` | partly: `setContext`/`getContext` carry the fiber's context | no per-fiber typed reference beyond the context map |
| `Effect.map`/`flatMap` with a computed function | partly: `bind` binds the result positionally; the continuation is a program, not a function value | §1 |
| `Option`/`Either`/`Exit`/`Cause` combinators | four cause predicates, `isSome`/`getOrElse`, `tagIs` | §1's atoms |
| user-defined services | only six carriers by type code: `nat bool unit Ref<number> SqlClient KvStore`, plus `Scope` (`Native.lean:287-293`) | a service is one of six shapes; no service record |
| `acquireRelease` release typing | wrong against rc.112 (row 47) | — |

## 5. Runtime and faces

| item | kind | note |
| --- | --- | --- |
| compile budgets: a program at insufficient fuel stops as a residual (`pending .compileFuel`), never an exit | cut (the basis names it a frontier, not a failure) | correct for a reified engine, invisible in Effect; the surface must say what budget a run had |
| `.program`-kind rows stop at `pending .unsupported` (`DenoteR.lean:603`) | cut | which rows: to list mechanically, the same way as the positions |
| external rows are answered by a tape; the proofs run at the empty table (DI-57) | deferral (row 54) | — |
| the clock is logical | design | matches `TestClock`; a real clock is the engine's |
| `getId` answers a number | cut | Effect's `FiberId` is a value with structure |

## 6. What this means for "fully functioning"

The profile is a **closed, first-order, monomorphic stored-program language** by two rulings
of 2026-09-09 (DI-20, DI-28) and the basis's exclusion list; polymorphism and functions were
placed in the builders on purpose. Within that profile the cuts that stop real programs are, in
order of how often an Effect program hits them: records (row 2), error payloads (§3),
polymorphic `Ref`/`Deferred` (row 42), function-taking rows by binder terms (§1), the atom
alphabet (§1), user service carriers (§4), then the absent modules of §4 in whatever order the
dogfood programs demand. None of them changes the machine; all of them change the checker, the
rows, the printer and the reader, and each lands as rows the position census and the
traversal census already know how to gate.
