# Effect4

Effect4 makes Effect-style computations explicit, inspectable **program data**. Lean
defines their structure, execution rules and construction checks. Effect TypeScript
rc.112 is the first target profile and the behavioural reference for that profile,
never the semantic owner; OCaml is an authoring and execution test bed. Host
connections supply real services while keeping their values, errors, lifetimes and
scheduling choices visible at defined boundaries, each held by a named grade of
evidence.

Concretely, the product is **Effect codegen**: a first-order program syntax (`Eff`)
that prints as Effect TS and reads back, a compiler to the rc.112 frame machine, a
reference fiber machine (`Machine`) that runs those frames the way rc.112's run loop
does, and the Effect Schema data plane with its TypeScript generation, optics and
surface carriers beside it.

```text
 Effect TS text  ⇄  Eff program  →  rc.112 frames  →  Machine
   print / read      compile                          replay / runSync

 Schema document ⇄  representation  →  Schema.Struct({…}) syntax, JSON Schema
```

## The application face

Import `Effect4.Api` (`src/Effect4/Api.lean`). It is the program interface:
`typeOf`, `print`, `printDecl`, `compile`, `replay`, `run`, `runSync`,
and the Schema syntax (`schemaDocument`, `schemaRepresentation`, `jsonExpr`).
Its program printers answer TypeScript **syntax**; the explicit `render` operation
crosses from a codegen artefact to bytes, and
`Test/Api/ApiContract.lean` is the receipt that crosses it the way a
caller does.

The same import exposes concrete value images, typed effectful transformations,
multi-tier cascading CAS stores, and checked schema endpoints.

The library lives under `src/Effect4`, its batteries under `Test/`, and its
generators and drivers under `tools/`. The OCaml estate spans `src/OCaml5` and
the dune workspace `ocaml/`; the TypeScript reader lives in `ts/eff`.
[Architecture](docs/ARCHITECTURE.md#source-tree) owns the source-tree table
and the dependency boundaries.

The earlier Flow route is retained in git history and on branch `archive/flow-route`.
The earlier Surface library is preserved on branch `archive/surface`.

## Records in authored programs

A record declaration retains required and optional fields, including fields whose values are absent.
Use the existing authoring functions through `Effect4.Api`:

```lean
import Effect4.Api
open Effect4.Program

def person : Authoring.TermSrc :=
  Authoring.record [("name", false, .string), ("nickname", true, .string)]
    [("name", Authoring.str "Ada")]

def nickname : Authoring.Src NativeOp :=
  Authoring.bind "person" (Authoring.succeed person)
    (Authoring.succeed (Authoring.optionalField (Authoring.var "person") "nickname"))
```

`Effect4.Api.author nickname` checks the program and returns its certificate.
Its answer type is `option string`; execution returns `None` because `nickname` is absent.
`Authoring.field` reads a required field.
`Authoring.recordSet` inserts or replaces a field in a new record, retaining the original record.
It makes the supplied field required and can change its type.

Every string field name is supported, including `__proto__` and names outside the TypeScript identifier profile.
An optional read distinguishes absence from a present `undefined` or a present `Option.none`.
The checked example and overwrite controls are in `Test/Api/RecordAuthoring.lean`.
Schema descriptions and JSON codecs include records, string maps and fixed-size tuples.
JSON decoding refuses duplicate keys, unknown record fields and missing required fields.
An absent optional field differs from a present field containing an optional value.
Type support and value-level codec admission remain separate checks.
The codec laws describe exact recovery under the named JSON normalizer; host execution remains a separate check.

## Maps in authored programs

`Authoring.mapEmpty` constructs an empty string map.
`Authoring.mapSet` inserts or replaces a value and retains the original map.
The checked result type retains the old and new value types.
`Authoring.mapGet` returns an outer option for own-key presence.
A missing key differs from a present unit or empty option.

`Authoring.mapKeys` and `Authoring.mapEntries` return entries in UTF-8 key order.
`Authoring.mapFromEntries` constructs a map from ordinary pairs and retains the last value for each repeated key.
The application examples and execution controls are in `Test/Api/MapAuthoring.lean`.

## Tuples and record tags

`Authoring.tuple` constructs a tuple at any fixed arity.
`Authoring.tupleAt value index` reads a statically known position and retains its declared type.
The checker refuses an index missing from any possible tuple alternative.
Two-item tuples share the existing product type after normalization.

```lean
def entry : Authoring.TermSrc :=
  Authoring.tuple [Authoring.nat 7, Authoring.str "ready", Authoring.bool true]

def selected : Authoring.Src NativeOp :=
  Authoring.bind "entry" (Authoring.succeed entry)
    (Authoring.succeed (Authoring.tupleAt (Authoring.var "entry") 1))
```

`Effect4.Api.author selected` checks this program at the literal answer type `"ready"`.
The application example in `Test/Api/TupleAuthoring.lean` constructs, selects, checks, prints and executes a three-item tuple.

`Authoring.selectRecordTag` branches on a required literal `_tag` field.
Each branch receives the whole narrowed record, including its field names.
`Test/Program/RecordTag.lean` checks branch typing and impossible branches.

## Folds over lists

`Authoring.fold acc item accTy list init body` folds a list from its head.
The body sees the accumulator under the name `acc` and the element under the name `item`.
It also reads every name that is in scope at the fold.
`accTy` states the accumulator's type where it is wider than the initial value's type.
An accumulator that starts as the empty list needs it.

```lean
def total : Authoring.Src NativeOp :=
  Authoring.bind "base" (Authoring.succeed (Authoring.nat 100))
    (Authoring.succeed (Authoring.fold "total" "x" none
      (Authoring.app "cons" [Authoring.nat 1, Authoring.app "cons" [Authoring.nat 2, Authoring.app "nil" []]])
      (Authoring.nat 0)
      (Authoring.app "add" [Authoring.var "total",
        Authoring.app "add" [Authoring.var "x", Authoring.var "base"]])))
```

`Effect4.Api.author total` checks this program at the answer type `nat`, and its run answers `203`.
A fold is pure, so a `Ref.modify` whose term holds one stays one step of the store.
The atoms `take` and `drop` split a list at a count.
The atom `sameHandle` compares two `Ref` handles, or two `Deferred` handles, by identity.
A fold in a term position prints as `fold(list, init, (acc, x) => body)` and reads back.
A fold with a stated type is printed and not read.
The printer refuses a fold inside an operation's term by the row's name.
`Test/Program/FoldContract.lean` holds the checked examples and the refusals.

`Authoring.foldWith list init (fun acc item => body)` is the same fold with its two names minted.
A helper that places its caller's term in the body uses this form.
With fixed names, a caller's variable of the same name would read the folded element.
`Test/Program/FoldHygiene.lean` holds that capture as a control.

Three more builders mint the name that they bind, for the same reason.
`Authoring.Ref.modifyWith cell (fun current => body)` mints the name of the cell's current value.
Each row that carries a term has this second wrapper, named with the suffix `With`.
`Authoring.selectOptionWith` mints the payload's name, and `Authoring.onExitWith` the exit's name.
`Test/Program/AuthoringContract.lean` holds one capture under a written name, and each minted form's reading.

## A bounded queue

`Queue.bounded A capacity` makes a queue of messages of the type `A`, at a positive capacity.
Its handle is the `Ref` of the queue's cell.
`Queue.offer`, `Queue.take`, `Queue.poll` and `Queue.size` are library programs over that handle.
An offer waits while the queue is full, and a take waits while it is empty.
`Queue.poll` and `Queue.size` never wait.

```lean
import Effect4
open Effect4 Effect4.Program Effect4.Program.Authoring

def handoff : Src NativeOp := eff do
  let q ← Queue.bounded .nat 2
  let worker ← fork (Queue.take .nat q)
  let _ ← Queue.offer .nat q (nat 7)
  let x ← join worker
  return x
```

`Effect4.Api.author handoff` checks this program at the answer type `nat`, and its run answers `7`.
The worker waits first, and the offer's posted helper wakes it.
An operation mints the name of each of its binders, so it captures no name of its caller.
Each operation prints as its expansion over `Ref.modify`, `Deferred` and `Effect.forkDetach`, and reads back.
The printed program agrees with Effect 4.0.0-rc.112 on its exit and on its compared schedule rows.
That run is the program `pQueueWake` of `harness/truth/Truth.lean`.
`Test/Program/QueueOps.lean` holds this example, and `Test/contracts/queue.contract.md` states what is proved and what is open.

## A semaphore

`Semaphore.make permits` makes a semaphore with a positive total of permits.
Its handle is the `Ref` of the semaphore's cell.
`Semaphore.take`, `Semaphore.release` and `Semaphore.withPermits` are library programs over that handle.
A take waits while its count does not fit, and it answers the count.
A release answers the free count, and its posted helper visits the waiters in the order of enrolment.
`Semaphore.withPermits handle count body` runs the body with the permits, and it releases them at every exit of the body.
`Semaphore.takeIfAvailable` and `Semaphore.withPermitsIfAvailable` never wait.

```lean
import Effect4
open Effect4 Effect4.Program Effect4.Program.Authoring

def handoff : Src NativeOp := eff do
  let gate ← Semaphore.make 1
  let _ ← Semaphore.take gate (nat 1)
  let worker ← fork (Semaphore.withPermits gate (nat 1) (succeed (nat 7)))
  let free ← Semaphore.release gate (nat 1)
  let x ← join worker
  return tuple [free, x]
```

`Effect4.Api.author handoff` checks this program at the answer type of a pair of numbers, and its run answers `[1, 7]`.
The worker waits first, and the release's posted helper resumes it.
The protected form is one mask over the take, the hook and the body.
An operation mints the name of each of its binders, so it captures no name of its caller.
Each operation prints as its expansion over `Ref.modify`, `Deferred` and `Effect.forkDetach`, and reads back.
The printed program agrees with Effect 4.0.0-rc.112 on its exit and on its compared schedule rows.
That run is the program `pSemaphoreHandoff` of `harness/truth/Truth.lean`.
`Test/Program/SemaphoreOps.lean` holds this example, and `Test/contracts/semaphore.contract.md` states what is proved and what is open.

## A pool

`Pool.make A size acquire` makes a pool of `size` resources of the type `A`, at a positive size.
It runs the acquisition `size` times before it answers, and a failed acquisition fails `make`.
Its handle is the `Ref` of the pool's cell.
`Pool.use A pool body` borrows one item, runs the body with its resource, and returns the item at every exit of the body.
A borrower waits while every item is borrowed.
A pool is made inside a scope: `make` registers the close there, and its type requires the scope.
The close refuses new borrowers, waits for every borrowed item, and then lets each resource's finalizer run.
A borrow at a closed pool interrupts the borrower itself, and its body does not run.

```lean
import Effect4
open Effect4 Effect4.Program Effect4.Program.Authoring

def handoff : Src NativeOp := scope (eff do
  let pool ← Pool.make .nat 1 (succeed (nat 7))
  let worker ← Pool.use .nat pool fun _ =>
    fork (Pool.use .nat pool fun resource => succeed resource)
  let x ← join worker
  return x)
```

`Effect4.Api.author handoff` checks this program at the answer type `nat`, and its run answers `7`.
The root borrows the one item, and the worker waits for it.
The root's return posts a helper, which wakes the worker, and the worker gets the same resource.
The protected form is one mask over the lease, the hook and the body.
An operation mints the name of each of its binders, so it captures no name of its caller.
Each operation prints as its expansion over `Ref.modify`, `Deferred` and `Effect.forkDetach`, and reads back.
Ten cases over these operations agree with Effect 4.0.0-rc.112 on their exits and on their compared schedule rows.
They are the programs `pPoolReuse` to `pPoolClosing` of `harness/truth/Truth.lean`, and this example is not one of them.
The close of the pin's own `Pool` does not wait for a borrowed item: decisions row 268 signs that difference.
`Test/Program/PoolOps.lean` holds this example, and `Test/contracts/pool.contract.md` states what is proved and what is open.

## Building

The toolchain is pinned by `lean-toolchain`. Dependencies are pinned by exact
commit in `lakefile.toml`: `effects` (the portable effect algebra),
`typescript` (target syntax and rendering), `hash` (a proved SHA-256).

```text
lake build Effect4       # API and functional utilities
lake build Effect4Laws   # proof graph
```

build the two library roots; a bare `lake build` builds both and `Test`, the
green battery, whose root runs the module-closure and axiom gate: every
declaration under `Effect4.*` and `Test.*` is audited at
`[propext, Quot.sound]` with a short list of exact, named rendering
exceptions, and every battery file must be reachable from `Test/All.lean`.
Every library file must be reachable from one of the two roots, and `Effect4` must
never reach `Effect4.Laws`. Config, ConfigValue and Provision remain functional
utilities in `Effect4`.
The five area targets are `TestSchema`, `TestMachine`, `TestStore`,
`TestProgram`, and `TestCodegen`. A single battery builds by its module name,
for example `lake build Test.Api.ApiContract`. Run one `lake` at a time. `lake build OCaml5`
builds the Lean half of the OCaml estate; the OCaml half is `dune build` in
`ocaml/` under the `effect4` opam switch (`ocaml/README.md`). `lake build Tools`
type-checks the `--run` drivers under `tools/Tools/`; one runs as
`lake env lean -M4096 --run tools/Tools/<Driver>.lean …`.

The gates beyond the build (bash; on Windows run them through WSL):

```text
make check-tools                                 # the checkers' own self-tests (planted defects must be refused)
make check-roots                                 # the module-closure, library-root and axiom gates, freshly
make check-docs                                  # every path, link, citation and make target in the documents resolves
make status                                      # one screen, measured: HEAD, build and check freshness, claims, registers, stale references
make check-census                                # the rc.112 mechanism census join
npm ci --prefix harness/schema-host # pinned Schema host and compiler integrations
make check-gen                                   # every generated file is what its generator emits
make check-ts-reader                             # the TypeScript reader = Lean's reader over the printed corpus (bun)
make check-truth                                 # bounded Lean/rc.112 differential (bun)
make check-schema-codec                          # fresh type-directed JSON vs rc.112 (bun)
make check                                       # the per-change tier (make help lists the rest)
make check-full                                  # the outside oracles: truth, T0, the OCaml tests
```

The TypeScript gates use the dependencies pinned in `ts/eff/package.json`; install them
with `bun install --frozen-lockfile --cwd ts/eff`. The truth lane selects its pinned
host through `EFFECT4_EFFECT_NODE_MODULES`. The OCaml lane (`make check-ocaml`) runs
under the `effect4` opam switch (`opam exec --switch=effect4`) and is local until the CI
runner has one. Archived receipt paths are checked against their recorded git history;
this does not refresh their original verdicts.

`docs/ARCHITECTURE.md` owns module boundaries and dependency direction,
`docs/DESIGN-BASIS.md` the representation decisions, `docs/RUNTIME-COVERAGE.md`
the one coverage report format, and `Test/Counterexamples/REGISTER.md` the
stable IDs of every declaration-changing counterexample. `AGENTS.md` is the
router for agents working in this tree.
