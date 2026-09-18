# The position census: obligations derived from the types (design, 2026-09-18)

Step 0 of the typed-state milestone (row 41). Three probes built and run tonight against HEAD
(`01ff4ec8`) carry the design: `docs/research/probes/2026-09-18-Q1_protocol.lean` (the generic
predicate), `Q2_positions.lean` (positions from the types), `Q3_writes.lean` (writes from the
constructor sites, closed over the call graph). Every number below is a probe's output, quoted
in the appendix. The composed graph this feeds is
`docs/research/2026-09-18-typed-state-composed-graph.md`.

## 0. What it is for

The owner's requirement: every Effect semantic accounted for, no surprises found mid-proof.
Tonight's two surprises (memoised builds share the deferred store; the release's exit parameter
is typed at the wrong exit) came from one cause: the invariant's fields were enumerated by
reading operations. The instrument below makes the invariant **total over the data by
construction**: the positions come from the types reachable from the reference state, the
obligations come from the constructor sites each step reaches, and a position without a named
typing source is a refusal that fails the build, exactly as a traversal without a fold is a
census row. It is the coherence census pointed at data instead of traversals, and it is reused
by every later addition to the alphabet.

## 1. What exists and is reused

| piece | where | what the design takes from it |
| --- | --- | --- |
| `#traversal_census` | `Laws/Auto/Traversals.lean` | the shape of a census command over the environment: rows, `definitionsUnder`, `moduleOf`, the manifest-aware `generated` kind, the `under` scoping |
| `#auto_census` | `Laws/Auto/Census.lean` | the rolled-back attempt harness: the obligation gate reuses it to report which generated statements `aesop` already closes |
| `fold_of` | `Program/FoldOf.lean` | reading a definition's unfold equations and matchers; the write census reads constructor applications the same way |
| the generator | `tools/Effect4Gen/{Driver,Authoring,Fold}.lean`, `manifest.json` | `readCtor`/`readFamilies` (constructor arguments with kinds), the `Pos` vocabulary for container positions, the group mechanism (`Imports`, `Out`, `Guards`), `make gen-<group>` and `check-gen` drift |
| the coverage join | `Test/Audit/RuntimeCoverage.lean` | a frozen row list with disposition, state and witness theorems, failing the build on a missing witness: the obligation ledger's shape |
| the unary ladder | scout §A.3 item 1, `Laws/Machine/Keeps.lean` (to write) | the statement shape every per-definition lemma instantiates |
| the axiom gate's meta list | `Test/Audit/AxiomGate.lean` | the new meta module joins the four already exempt |

Nothing in the Effects package changes.

## 2. The instrument: three censuses, one table, one generator, one join

```
types reachable from the roots ──#position_census──▶ positions.tsv      (A)
                                                          │
hand: one Source row per position  ◀── totality gate ────┘              (B)
                                                          │
step roots ──#write_census / #read_census (closure)──▶ sites.tsv         (C)
                                                          │
(A)+(B) ──generator──▶ Typed/State.lean (the skeleton, aesop rules)      (D1)
(A)+(B)+(C) ──generator──▶ typed-state-obligations.tsv + the join module (D2)
```

### A. `#position_census` — positions from the types

`#position_census R₁ R₂ … carriers c₁ … wrappers w₁ …` walks the types reachable from each
root. A root is a type constant or an abbreviation (`RState`, `RCmd`, `RInterp`, `RIter`,
`Stores`). The walk (probe Q2, `walkType`):

- `whnf` the type at default transparency, so abbreviations (`RProgram`, `ExitV`, `ValU`) and
  `def`-headed types (`Env.Ctx := Context ValU`) unfold; a head that is neither an inductive
  nor unfoldable is a **refusal** when a carrier occurs in its arguments;
- a **carrier** head stops the walk and reports the position (`Store.Val`, `Exit`, `Cause`,
  `Reason`, `Effects.Program`, `Machine.Program`, `Prim`); the list is a parameter;
- a **wrapper** head (`List`, `Option`, `Prod`, `Array`, `Except`) is seen through and recorded
  in the shape;
- a **function** type records its domain and continues into the codomain (a continuation
  position, `ExitV → RProgram`, or a hook, `ParkKind → RProgram`);
- a structure or non-recursive inductive is entered once per type constant, its constructor
  types instantiated with the root's arguments (`instArgs`), each field or constructor argument
  a sub-walk labelled `Owner.field` or `Owner.ctor.arg`;
- a recursive inductive over a carrier is a refusal (none today: `Program` and `Prim` are
  carriers, `Cmd`/`Observer`/`Task` do not recurse).

Output: `generated/positions.tsv`, one row `owner  field  shape  carrier`, and the same as a
Lean list the totality gate reads. Measured tonight:

| root | positions | of note |
| --- | --- | --- |
| `RState` | 26 | `RSaved.current`, the two continuation slots, `ScopeFrame.loop.cursor`, `Pending.collected`, `RunFiber.exit`/`.finalizing`, `Task.resume.answer`, `RaceAllState.{failures,winner,accepted}`, `WaitState.result`, `Race.programs`, the store's seven, five `RunEvent` payloads |
| `RCmd` | 3 | `Cmd.resume.answer`, `Cmd.finish.exit`, `Cmd.observe.exit` |
| `Ctx` | 1 | `Env.Service.value` (found only once `def`-headed types unfold) |
| `RInterp` | 51 | every code- or value-valued hook, `IterStep`/`LoopNext`/`WithFiberAction` payloads: the `InterpTyped` field list, mechanically |
| `RIter` | 31 | the step result: the fiber, the machine, the outcome's exit, the nested commands |

Six of the 26 state positions were not in any hand list before tonight. Two cosmetic fixes
before landing: a hygienic constructor-argument name (`Except.error.a._@…`) prints by index,
and `Except` joins the wrappers.

### B. The source table — one row per position, by hand, gated for totality

`Laws/Program/Typed/Positions.lean` holds the only hand-written input: for every position, its
typing source.

```lean
/-- Where a position's expected type comes from. -/
inductive Expected
  | fiber (id : Term)          -- the fiber table Γ at this id
  | promise (cell : Term)      -- the promise table Π at this cell
  | refColumn                  -- the heap column (nat at this cut)
  | row (op : Term)            -- the signature row's answer/error
  | checker (point : Term)     -- the checker at this point of the root
  | same (position : Name)     -- the type another position carries
  | const (ty : Term)          -- a fixed type (unit, nat)

/-- What the invariant says at a position. -/
inductive Source
  | program (e : Expected)       -- TypedProg w e p
  | continuation (e : Expected)  -- ∀ w' ≥ w, ∀ ex, ExitOk e ex → TypedProg w' (next ex)
  | value (e : Expected)         -- hasTy ∧ validIn
  | exit (e : Expected)          -- ExitOk
  | cause (e : Expected)         -- causeAdmits
  | hook (consumer : Name)       -- InterpTyped: typed at what `consumer` installs it as
  | column (name : Name)         -- a store column carried separately (HeapNat, Π)
  | journal                      -- written, never read back (checked by the read census)
  | custom (pred : Name)         -- StackOk, ParkedOk: a hand predicate over the position
  | refused (reason : String)    -- named debt; must be a decisions/DI row

def sources : List (Name × Source) := [
  (`Effect4.Program.Sched.RSaved.current, .program (.fiber `f.id)),
  (`Effect4.Program.Sched.ScopeFrame.answer.next, .custom `StackOk),
  (`Effect4.Machine.DeferredCell.completion, .column `PromiseTable),
  (`Effect4.ScopeState.closed.exit, .refused "the release's exit parameter, DI pending"),
  (`Effect4.Machine.RunEvent.exited.exit, .journal),
  … ]
```

The **totality gate** (`Test/Audit/PositionCensus.lean`): every position of (A) has exactly
one source row; every source row names a position that exists (staleness); every `journal` row
has no read site in (C); every `refused` row is cited by a decisions or DI row. Adding a field
to any state structure makes the build fail here until it is sourced. That is the property the
owner asked for.

### C. `#write_census` / `#read_census` — sites from the bodies, closed over the call graph

For a definition, the write census (probe Q3, `collect`) lists every constructor application
of an owner type in its body and, per site, the fields whose argument is not a projection of a
source value (both spellings: `Expr.proj` and the projection function applied to the
structure's parameters plus the value). The read census lists projections and matches on owner
types. Both close over the constants the definition uses within `Effect4.*` (`closure`), so
a step's writes are attributed to the helper that performs them, and a body that structural
recursion compiled into an auxiliary is reached (`popR` writes nothing; `popR._f` writes 17
sites).

Output: `generated/sites.tsv`, rows `step  definition  owner  fields`. Measured tonight:

| step root | definitions reached | with write sites | examples |
| --- | --- | --- | --- |
| `driveStep` | 374 | 21 | `RunFiber.publish ← frame, running, parked, pending, finalizing, exit`; `interruptRecord ← frame` (three sites); `RunFiber.cleared ← frame, observers, children, context`; `spawn ← fibers, nextId`; `exitFiber.exitInterruptChildren ← frame, running, finalizing`; `settle ← parked, pending`; `injectYield ← frame, yieldOverride`; `linkScope ← state, observers` |
| `popR` | 174 | 1 (`popR._f`, 17 sites) | `current`, `stack`, `interruptible` in every combination |
| `evaluateFiberR` | — | 6 own sites | `context, maxOpsBeforeYield, preventYield` (`scoped`), `state`, `nextToken`, a `Pending`, `RSaved ← stack, interruptible` (`mask`), `frame`; the rest through `answerR`/`pushR`/`saveAnswerR` and the `FiberAction` helpers |

The **obligation matrix** is (C) restricted to the typed positions of (A): one row per
(definition, owner, written typed field). Its unit is the *definition*, not the arm: `answerR`
gets one lemma, `RunFiber.publish` one, `interruptRecord` one, and `driveStep`'s eighteen arms
are then applications of those. That is the honest replacement for "65 arms".

### D. The generator — the skeleton, the aesop rules, the ledger

A new manifest group `TypedState` (`tools/Effect4Gen/TypedState.lean`, `make gen-typed-state`,
in `HERMETIC_GROUPS`, `check-gen` drift) emits:

**D1 `src/Effect4/Laws/Program/Typed/State.lean`** — per owner type a `structure <Owner>Ok
(w : World) (x : Owner) : Prop` with one field per typed position, its proposition from the
source row (`program` → `TypedProg w (expected) x.field`; `continuation` → the ∀-clause;
`value` → `Val.hasTy ∧ validIn`; `exit` → `ExitOk`; `custom` → the named predicate applied;
`column`/`journal`/`refused`/`hook` → no field here), each field's docstring the source row's
text; `TypedState w m` as the conjunction over the roots plus the coverage clause and the
columns; `InterpTyped i` as the structure over the 51 `RInterp` positions with `hook` sources;
and the registrations `attribute [aesop safe forward] <Owner>Ok.<field>` for every generated
accessor. The carrier predicates themselves (`TypedProg` from layer 0/1, `StackOk`,
`ParkedOk`, `ExitOk`) are hand-written and imported; the generator only applies them. The
guards file pins the field count against `positions.tsv`.

**D2 `generated/typed-state-obligations.tsv`** and `Test/Audit/TypedStateObligations.lean`
(the join, in `RuntimeCoverage`'s shape): one row per definition of the obligation matrix with
the typed fields it writes, the expected witness name `keeps_<definition>`, and a status
(`open`, `proved`, `by_frame` when the definition writes no typed field and the frame lemma
covers it). The join fails the build when a `proved` row's witness is not a theorem, or when a
theorem's conclusion is not the owner's `Ok` for every field the row lists (a head check on the
statement, not a defeq: the statement's exact hypotheses are the implementer's). `#auto_census`
over the module of witnesses reports which the rule set closes.

Statements are **generated as templates, proved by hand**: for a definition `f` whose result
contains owner-typed components, the template is the unary-ladder shape "for all arguments,
each owner-typed argument `Ok` at `w`, each program argument `TypedProg` at its expected type,
each answer-function argument typed as a continuation, then each owner-typed result component
`Ok` at some `w' ≥ w`". The template is emitted as a comment above the row's witness slot in a
scaffold file the implementer fills; it is never a `sorry` in `src/`.

## 3. Where it lives

```
src/Effect4/Laws/Auto/Positions.lean          the three censuses (meta; joins the gate's list)
src/Effect4/Laws/Program/Typed/Positions.lean  the source table (hand, ~90 rows)
tools/Effect4Gen/TypedState.lean               the generator; manifest group TypedState
src/Effect4/Laws/Program/Typed/State.lean      generated: the Ok structures, TypedState, InterpTyped, aesop rules
generated/positions.tsv, sites.tsv, typed-state-obligations.tsv
Test/Audit/PositionCensus.lean                 the totality gate (positions ⇔ sources; journal ⇔ unread)
Test/Audit/TypedStateObligations.lean          the join (rows ⇔ witnesses)
```

Import discipline: `Positions.lean` imports `Lean` and the roots' modules only; the source
table imports `InterpR` (the roots) and nothing of `Simulation/*`; the generated `State.lean`
imports the hand predicates of layers 0–2 and the table. The scout's placement (§D.2 of the
scout note) holds: no `Simulation`/`Book` import before `Typed/Transfer.lean`.

## 4. How it lands the milestone, in order

| step | artefact | gate |
| --- | --- | --- |
| 0a | `Positions.lean` + `positions.tsv` from the four roots | the census builds; refusals: none today, two cosmetic fixes |
| 0b | the source table, with the three rulings as rows (`Γ` for fibers, `Π` for promises, `HandlesFit` for handles) and the release parameter as `refused` until its DI is ruled | totality gate green |
| 0c | `sites.tsv` for the step roots (`driveStep`, `evaluateFiberR`, `evaluateRawR`, `popR`, `prepareIterR`, `fireObserver`, `exitFiber`, `stepDecisionState`, `replayEval`) and `typed-state-obligations.tsv` | the ledger exists; every row `open` |
| 1 | layer 0 (`Laws/Effects/Protocol.lean`, from probe Q1) and layer 1 (`TypedProg`, `OpOk`/`AnswerOk`, the world with `Γ`, `Π`, the heap column) | narrow builds |
| 2 | `make gen-typed-state`: `State.lean`, `InterpTyped`, the aesop registrations | `check-gen` |
| 3 | `Keeps.lean`; `StackOk`/`ParkedOk`; `popR_typed` (the first hard witness; `popR._f`'s row) | its row `proved` |
| 4 | S1 `denoteR_typed` by combinator lemmas; the four hook bodies; `InterpTyped (interpR root)` | the 51 hook rows `proved` |
| 5 | S2 = the ledger, definition by definition, frame rows first (`by_frame`), then delivery helpers (`answerR`, `publish`, `interruptRecord`, `join`, `countdown`…), then the step roots | rows turn `proved`; `#auto_census` names what the rules close |
| 6 | S3 through `BMeans.exitOf` | the corollaries |

Progress is the ledger's `proved` count, printed by the join; the owner reads one file.

## 5. Reuse beyond this milestone

- **A new primitive** (a queue, a semaphore, a pub-sub): its store structure adds positions;
  the totality gate refuses until each is sourced; its step helpers add rows to the ledger.
  Nothing is enumerated by hand.
- **The compiled machine**: the same censuses at `FMachine`/`FRun` if a typed invariant is ever
  wanted there; today the transfer through `BMeans` makes it unnecessary.
- **The bytes boundary**: `positions.tsv` at `Stores` is the list of what the OCaml schema and
  the runner's bytes must encode (the player/schema plan), read from the same file.
- **The table-aware slice**: `Stores.externals` is already a position; its source row changes
  from `refused` to the typed-tape hypothesis when that slice lands.
- **Every future census**: `#position_census` is generic over roots, carriers and wrappers;
  `#write_census` over owner types. They are two more instruments beside `#traversal_census`
  and `#auto_census`, in the same module family.

## 6. Sizes and risks

Meta: `Positions.lean` about 300 lines (probes Q2 and Q3 are 90 and 110 today), the generator
about 250, the two audit modules about 150; the source table about 90 rows. Two to three days
for step 0 including the generated skeleton, before any proof.

Risks, named: (1) `whnf` at default transparency could unfold a type further than its author
means; the carrier stop and the visited set bound it, and a refusal is loud. (2) A write through
a container helper (`List.set`, `updateEntry` with a lambda) is attributed to the helper's
lambda site, which is inside the caller's body: correct, but the row names the caller, so the
lemma unit is the caller. (3) The generated `Ok` structures must stay readable: one per owner,
docstrings from the source rows, no nesting deeper than the position's own shape. (4) The
statement template is a scaffold, not a pinned statement; the join checks conclusions, not
hypotheses, so a weak witness is possible and is caught only by S3's use of it. (5) The
generator runs with the `Laws` environment loaded (`Imports` names `InterpR`); the group is
hermetic but slower than the others.

## Appendix: probe receipts

Q2 (`#positions`, after `whnf` and the refusal rule): `RState` 26, `RCmd` 3, `Ctx` 1,
`RInterp` 51, `RIter` 31; one warning `skipped Eq` (a proof field, to filter by `Prop`).
Q3 (`#writes`): `driveStep` 16 own sites with the fields as listed in §2C;
`FiberAction.join` 5; `fireObserver` 9; `evaluateFiberR` 6; `deliverR` 4; `answerR` 2
(`RunFiber ← frame`, `RSaved ← current`); `pushR` 2 (`RSaved ← stack`); `popR` 0 and
`popR._f` 17. Q3 (`#writes_closure`): `popR` 174 definitions reached; `driveStep` 374 reached,
21 with write sites, the list in §2C. Q1: `Typed.mono`, `.bind`, `.inl`, `.inr_inv` with no
axioms.
