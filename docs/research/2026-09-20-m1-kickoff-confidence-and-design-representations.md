# M1 kickoff: the state decisions checked, the design representations organized, and the research behind the lowering API

Written 2026-09-20 at `f9d3112b` (`refactor/phase1-phase3`), in answer to the forward scout
brief of the same date and to the owner's two asks: give confidence that the decisions on
types, world data, stores, heaps and the promise table are right so M1 can start, and organize
the compiled research (this tree and foldlab) into design representations that later slices
and the lowering-module API can draw on. Codex takes M1–M2; the design focus stays here.

Everything checkable below was checked against the tree by command at `f9d3112b`; nothing was
built, and no proof was run. Where a claim is another note's, the note is named.

## 0. Verdict

**M1 can start.** The four decisions M1 rests on are either ruled by the owner or proved in the
tree, and the three refutations that reshaped the design since 2026-09-18 all landed in the
plan before the brief was written:

| decision | standing | evidence |
| --- | --- | --- |
| handle types are coarse in values and typed by the world (row 44) | ruled 2026-09-19 | `Program/Typed.lean:50-61` (`Val.hasTy` on `.refOf`/`.deferredOf` reads the kind byte only) |
| the promise table is per cell, both populations (row 45) | ruled 2026-09-19 | `memoBuild` allocates from the same store (`Stores.lean`), `Completion` already carries the stored alphabet (`Machine/Completion.lean:28`) |
| the world order is table extension ∧ allocation growth ∧ typed-cell compatibility | refuted-and-amended | `heapNotMonotone`, `[propext]` (`2026-09-19-landed-architecture-review/Boundaries.lean:31`) |
| a store step's contract is `progress` (pre) and its conclusion (post) | proved | `Progress.lean:345-358` |

What M1 changes is a **deletion**: two `Program`-typed positions leave the store, a duplicated
field leaves the memo entry, and a shape invariant with no content goes with them. No theorem
about the machine's behaviour changes, because every writer of those positions already stores
the image of a `Completion` (stores map F1). The one thing M1 must not delete is the
reference-validity boundary `E4-STORES-CE-003`, and §3.5 explains why that boundary is not a
defect in the data type.

The brief is right in substance and wrong in six details (§1). The larger point the brief does
not make, and this note does, is that the design is now one shape at four levels (§3): a
comodel for the stores, a Hazel-style protocol for the operations, an interaction-tree predicate
for typing, and a data-refinement interface for the lowering. Each level has a named prior art
whose implementation can be taken (§4), and the same shape is what a lowering-module API has to
expose (§5).

## 1. The scout brief, checked

| brief says | disposition |
| --- | --- |
| commit 1 (`65b143a2`) installed a parser-based gate scanner | **True on 2026-09-19, retired the same night** in `243ca0dd` (the brief's own item 3). The gate reads the compiled environment only; there is no source scan at HEAD. |
| `lake build Test.All` is 652/652 jobs | The test root alone, at `3cb5805e`. The whole tree at `f9d3112b` is 735 jobs, zero warnings, `-DwarningAsError=true` in all 13 libraries. |
| `Stores.lean:1079` `DeferredCell.completion`, `:1089` `DeferredStore.due`, `:551` `MemoEntry` | **Confirmed** at `f9d3112b`. |
| `completionPrim` at `Stores.lean:2220` | **`:1813`.** `denoteCompletion` at `InterpR.lean:128` is right; `answerCode := denoteCompletion` at `:352`. |
| `poll` returns `Option (Option Completion)`; the sync row answers `Val.bool slot.isSome` | **Confirmed** (today `Option (Option Program)`, `:1115`). DI-97 stands as a signed exception. |
| delete `CompletionShaped`, `DeferredOk` whole, `StoredCodeNoRace`, `DeferredCodes`; `StoresOk` keeps `ScopeKeysFresh` | **Confirmed**: both conjuncts of `DeferredOk` are `CompletionShaped` (`Simulation/Hooks.lean:33-35`); `StoresOk := DeferredOk s.deferreds ∧ s.ScopeKeysFresh` (`:41`). |
| "delete row 61, update rows 59–60 to `Completion`" in `Typed/Sources.lean` | **Half right.** Rows are keyed by field name (`"Effect4.Machine.DeferredCell.completion"`, `"Effect4.Machine.Owed.code"`), and the field names do not change, so rows 59–60 need no edit. Row 61 (`MemoEntry.effect`) goes with the field. Row 62 (`Completion.ofExit.exit`) stays. What changes is the *census*: `#position_gate`'s count lines and the `#typed_state` skeleton, so the controls in `Test/Audit/` re-pin. |
| regenerate with `python3 scripts/generate.py --only lcnf,cas` or `make gen-lcnf && make gen-cas` | **The second form is right, the first is not.** `--only` takes one family (`generate.py:161`); `make gen-lcnf` and `make gen-cas` both exist (`make -n` at HEAD: `lake build` then `generate.py --only lcnf`). This corrects the deep-dive review §10, which said there was no `make gen-lcnf`. The lcnf cut is minutes; run it once at the end. |
| M2: "register order theorems into the `Effect4.World` rule set" | **No such bank.** The declared banks are `Effect4.{Inversion, TyOrder, TypedState, Rows, Atoms, Reader, Checker}` (`Laws/Auto/RuleSets.lean:22-25`). M2 registers into `Effect4.TypedState`, or declares a bank there first; the name is Codex's, the file is that one. |
| M2: prune five `Expect` constructors (`promise`, `refColumn`, `row`, `checker`, `const`) | **Confirmed**: their only uses are the generator's own emitter arms (`TypedStateDecl.lean:70-75`); nothing in the skeleton reaches them. |
| M2's order law and `PromiseTable` formula | **Confirmed** against deep-dive review §3 and plan §14. |
| M3: 40 `FiberOp` arms; `#answer_gate` | **40 confirmed** (`Sched.lean:96`). The gate does not exist; the map's role register reserves `Laws/Auto/AnswerGate` and `Typed/Residual` for it. |
| "26 upward imports across 3 primary cycles" | The map at HEAD reports 26 imports against the direction and 164 area edges; the M1 specification counted 10 mutual area cycles and said clearing the fold connectors clears 3. The brief's "3 primary" is that grouping. |
| design area 1: "formally adopt Option A (finite replay contract)" | **Not ruled, and not the only option.** Deep-dive review §10: `driveState` keeps the command residue and the critique's own witness resumes it; replay and a retained suspension are both row 80 options. Under the proved bound plus the connector (row 84), a straight body needs neither. The design work is the connector; the replay/suspension choice is row 80 and stays the owner's. |
| design area 2: `Arena` with five laws; no Lean `Array` | **Confirmed** as row 85's proposal; the brief now carries the follow-up's correction (`E4_table` is `Map.Make(Int)`, `e4_table.ml:21-28`; `Array.push` lowers to `@ [x]`, `Translate.lean:241`). |
| design area 3: the placement moves "prior to M2/M3" | **Accepted moves, but not inside M1's window.** They are import-only refactors across dozens of files; running them while Codex holds M1's 38 files invites conflicts. Order proposed in §6. |
| design areas 4 and 5 (Latch, `BehaviorRef`) | Consistent with rows 81 and 82 as recorded; both open. |

The brief's execution sequence for M1 (types, denotation, laws, simulation, census,
generation) is the M1 specification's, accepted in deep-dive review §10. Its radius is 38
files, measured there; my narrower grep at HEAD (files naming a deleted or retyped artifact
directly) finds 24, the difference being consumers of `Owed Program` and the registers.

## 2. The decisions, one by one, and what each stands on

This is the confidence section. For each object M1 and M2 touch: what is decided, who decided
it, what refuted the alternative, and what is still open.

### 2.1 Values: coarse handles, no runtime tags (row 44)

`Val.hasTy v (.refOf _)` and `(.deferredOf _ _)` check the handle's kind byte and nothing else
(`Program/Typed.lean:50-61`). That is Effect's erasure: a `Ref<A>` at run time is a cell
index. The alternative, tags on values, was rejected because it changes `Val`, the bytes
boundary, the printer and the OCaml engine for a fact the world can carry for free.
**Ruled 2026-09-19.** Nothing in M1–M3 revisits it.

### 2.2 The world: one record, three tables, one store

```
World := ⟨ Γ : FiberId → Option EffTy,          -- what each fiber was forked at
           Π : DeferredKey → Option (Ty × Ty),  -- what each promise cell holds, per cell
           Ρ : RefKey → Option Ty,              -- what each heap cell holds
           s : Stores ⟩
```

Extended at `fork` (Γ), `deferredMake` and `memoBuild` (Π), `refMake` (Ρ). The three tables
are logical: they exist only in `Laws`, are never in the runtime closure, and `Prop`-erasure
keeps them out of the OCaml (LCNF note §2.4). A first version of this record already exists for
handle *existence*: `Laws/Machine/Handles.lean:812` (`World := ⟨ids, state⟩`, `Handle.existsIn`,
`World.le`). M2's record is that one plus the three typing tables, and its existence checks
are the same six arms.

**The order.** `w ≤ w'` is pointwise table extension ∧ `Stores.le` ∧ typed-cell compatibility.
The third conjunct was forced: `Stores.le` compares lengths, domains and counters only
(`StoresLaws.lean:46-53`), so `[nat 0]` may become `[bool false]` under it, and
`heapNotMonotone` proves `HeapNat` is not upward closed along it (`Boundaries.lean:31`,
`[propext]`). The deep-dive review had claimed "nothing else is owed for weakening"; that
claim is withdrawn in its §9. The reason it matters: layer 0's `Typed.mono` needs the
protocol's demands and the result predicate to be `Mono` along the order
(`Laws/Effects/Protocol.lean:45-56`). With compatibility in the order, weakening is one
`cases`; without it, it is false. **Settled by refutation; not an owner ruling.**

What the order does *not* say, on purpose: that cell contents are immutable (they are not:
`refSet`), or that the store's own invariants (`WF`, `ScopeKeysFresh`) are part of the
monotone demand (they are handler-preservation premises, the landed-architecture review §2).

### 2.3 The stores: seven fields, one growth order, one observation

`Stores` (`Stores.lean:1719-1733`): `refs : RefHeap`, `deferreds : DeferredStore`,
`scopes : ScopeStore`, `memo : MemoWorld`, `timers : TimerStore`, `nextName : Nat`,
`externals : ExternalStore`. Each transcribes a named rc.112 object; the stores map §2 gives
origin, writers, readers, typing source and OCaml carrier per field.

- **Growth**: `Stores.le` (`StoresLaws.lean:46`), proved for every `syncOpStep`
  (`syncOpStep_le`, `:800`). Allocation only; contents excluded (§2.2).
- **Well-formedness**: `Stores.WF` (`:218`): every heap value valid, every closing exit valid,
  `MemoValid` (each entry's cell and scope exist), `timers.WF`. Proved preserved
  (`syncOpStep_wf`, `:1411`).
- **Observation**: `Obs := ⟨exits, stores⟩` with `Obs.le` (`Laws/Machine/Behaviour.lean:29-45`).
  The whole concrete `Stores` value is observed; the trace is not. Plan §3: any container swap
  or hidden buffer therefore needs a named projection and a connector, not an assertion.
- **The one counter**: `nextName` mints scope keys, finalizer keys and memo-map ids, by ruling
  (identity is the only fact read off them). Distinct *types* for those spaces are R5 (stores
  map §6), a free change; the shared *counter* stays.

**Confidence**: the store record is the most exercised object in the tree (the census's green
witnesses, the OCaml property tests ST1–ST8, `Obs` in every correctness theorem). M1 changes two
field types inside it and deletes one field; it does not change the record's shape, `le`, `WF`
or `Obs`. Nothing here is open.

### 2.4 The heap: a list, a kernel, and a column that becomes a table

`RefHeap := List Val`, `refPeek`/`refPoke`, and every row but `refMake` is one instance of
`refStepOf cell k heap` (read, kernel, write back; `RefKernel.lean:30-52`), with
`refStep_eq_refStepOf` proving the table is the machine and `refStepOf_keeps` proving the
frame once. `HeapNat` (`Progress.lean:72`) is the current column: every cell a `nat`.

- M2 restates the column as `∀ i v, s.refs[i]? = some v → ∀ ty, Ρ ⟨i⟩ = some ty → Val.hasTy v ty`,
  with `HeapNat` the instance `Ρ ≡ nat`. The proof pattern (`answer_typed`, `step_heapNat`)
  carries over row by row because the kernel table is the only place the heap is written.
- Row 85 (open, proposed): `Arena σ α` with `peek`, `poke`, `alloc`, `size` and five laws;
  `refStepOf` restated over any arena; `RefHeap` the list instance; the OCaml `E4_store` the
  trusted instance with `prop_store.ml` as its evidence; no Lean `Array` instance while the
  translator lowers `Array` to a list. **Nothing in M1–M3 depends on row 85**; it is P2.

**Confidence**: high. The kernel already decouples the rows from the representation, which is
exactly the seam a refinement needs (§4.4).

### 2.5 The promise store: data, not code (M1's content)

Today `DeferredCell.completion : Option Program` and `DeferredStore.due : List (Owed Program)`.
Every writer stores `completionPrim c` for some `c : Completion` (stores map F1:
`deferredCompleteWith`, `deferredInterruptWith`, `memoComplete`); the reference reads it back
through `denoteStored`, a partial decoder whose fall-through is `pending .unsupported`
(`InterpR.lean:133-137`), unreachable only because `CompletionShaped` says so.

After M1: `completion : Option (Completion Val Err Defect FiberId Ann)`,
`due : List (Owed (Completion …))`. `Completion` is `ofExit exit | ofRefGet cell`
(`Machine/Completion.lean:28`), derives `DecidableEq`, and is the instantiation `Stores.lean:279`
already uses in `SyncOp.deferredCompleteWith`. `Owed κ` is parametric (`Wake.lean:97`). The
code is minted at the two consumers that exist: `completionPrim` for the compiled machine,
`denoteCompletion` (total) for the reference; `answerCode` already is `denoteCompletion`.

What this buys, each a deletion: `CompletionShaped`, `DeferredOk`, `StoredCodeNoRace`,
`DeferredCodes`, `denoteStored` and its five call sites, `STORES-FB-COMPLETION`. What it
changes in the typed world: `Π` can type an exit per cell (`CompletionOk w (Π ⟨i⟩) x`), which
is the column the composed graph §9 asked for and could not state over code.

**Two populations, one table.** User cells are made at the row's `⟨nat, nat⟩` today;
memoised layer builds allocate a cell from the same store (`memoBuild`) and complete it with
the layer's exit (`memoComplete`). A constant column is therefore wrong, and `Π` is per cell,
extended at both sites. **Ruled** (row 45).

**`ofRefGet` stays data.** A completion may be a deferred ref read, evaluated when the
receiver resumes, not when written. `poll` therefore cannot answer an `Exit` without a heap
read at the wrong time; it answers the slot, and the sync row answers `isSome` (DI-97). The
plan §4 says this in one line: narrowing the carrier does not turn poll into a stored-exit
query.

**Confidence**: this is the best-evidenced change in the whole plan. It was found by reading
(map F1), confirmed by two reviews, and its radius was measured. The only correction across
three notes was the deletion list's edge (§3.5).

### 2.6 The memo entry: delete the copy

`MemoEntry.effect : Program` is rc.112's `effect` field, which rc.112's hit path runs. This
machine's hit path answers the entry's *promise* (`memoGet`), so `effect` is either "await the
cell" or "the exit", and the cell already knows which. Only `Handles.lean:747` (a key set) and
two `StoresLaws` theorems read it. **The two conditions** the stores map attached
(`docs/core/machine-state.md` §4) are part of M1: the census witnesses of
`layer.memo-build-once` restate against the cell, and the representation connector says what
the new memo observation retains. The brief omits both; they are the reason M1 is 38 files and
not six.

### 2.7 Waiting: one protocol, one owed-resume carrier

`WakeList π` (waiters in registration order, an optional captured batch, a phase) with
fifteen proved laws (`Wake.lean` header), and `Owed κ` (waiter, token, code, mode). Deferred is
the broadcast-inline instance, the timer the second. The park handshake (a waiter is recorded
in the store *and* as a guard token on the fiber; a resume for the wrong token is inert,
`drive_resume_wrong_token`) is the generation-index pattern and is correct; its two-sided
statement is `ResumeOk` in the skeleton and is owed before S2. **Latch** (row 81) is the
`Unit`/broadcast/scheduled instance and needs its four controls before landing. Nothing in
M1–M3 depends on it.

### 2.8 The position census and the skeleton: ownership per occurrence

`#position_gate` walks every type reachable from the state roots and refuses a value-,
exit-, cause- or program-bearing field with no typing source; `#typed_state` emits the
predicate skeleton from the source table (`Typed/Sources.lean`). Since `243ca0dd` the
accounting is per field occurrence (`Emit.covered` on keys; `columnKeysUnder`), with the
follow-up's two probes as controls. The real skeleton is 16 predicates, 11 carrier
predicates, 2 refusals. M1 moves three rows' *types* and deletes one row; the gate forces the
edit and the controls re-pin.

## 3. The design, as one shape at four levels

The pieces above are not seven designs; they are one shape seen at four levels, and each level
has a name in the literature the tree already cites. Stated once here so later slices reuse
the vocabulary instead of re-deriving it.

```
level 0  the free monad         Program S A := pure a | vis op k        (Effects.Algebra.Program)
         and its typing         Typed o Ψ w Q p                          (Laws/Effects/Protocol.lean)
                                  pure: Q w a
                                  vis:  Ψ.pre w op ∧ ∀ w' ≥ w, ∀ ans, Ψ.post w' op ans → Typed … w' Q (k ans)

level 1  the world              World := ⟨Γ, Π, Ρ, s⟩; w ≤ w' := ext ∧ s.le s' ∧ compat
         the store protocol     Ψ_S.pre  = progress's hypotheses (WF, column, typed valid request)
                                Ψ_S.post = its conclusion (typed valid answer, WF, column)
         the fiber protocol     Ψ_F = OpOk (40 arms) / AnswerOk (40 arms), tables read in ∀-form
         the columns            HeapOk (Ρ), PromiseTable (Π), both over data

level 2  the typed stack        StackOk w ty stack; ParkedOk; TypedFiber (running | parked | exited)
         one delivery lemma     popR_typed (seven slot cases) → the nine delivery sites + the sink

level 3  the machine invariant  TypedState m := ∃ w, fibers ∧ races ∧ residue ∧ coverage ∧ columns
         the store as comodel   syncOpStep : SyncOp → Stores → Option (Stores × Val)
         the observation        Obs := ⟨exits, stores⟩, ordered by allocation
         the boundary           Completion (data in), Externs rows (carriers out)
```

Reading the levels with their prior art:

- **Level 0 is an interaction tree** (`Ret`/`Vis`, no `Tau`; foldlab `EFFECTS-BACKEND.md` R1)
  **with a Hazel protocol** on it: `Protocol.pre`/`post` is de Vilhena's send/receive protocol
  `! x (v) {P}. ? y (w) {Q}` (papers review §1.3, Definition 2.2), and `Typed.mono` is his
  Monotonicity rule, which is why the demand and the result predicate must be upward closed
  (Definitions 2.6, 2.7). The tree took the first-order relational route rather than Iris
  (Hazel notes §5); the protocol shape survived the translation intact.
- **Level 1's order is the Iris split between persistent and exclusive resources.** Table
  extension and allocation growth are persistent facts ("the promise map only grows", de
  Vilhena §4.3, `isPromise` persistent); a cell's *content* is not, which is exactly what
  `heapNotMonotone` says. Typed-cell compatibility is the ghost points-to for a mutable cell:
  the type is persistent, the value is owned. This is the same condition three papers state
  (papers review A3: MCA §4.1.1, de Vilhena §4.3, Jacobs 6.2.4), and the tree's `Stable`
  sketch there is `Mono` in `Protocol.lean`.
- **Level 3's store is a comodel and `Api.run` is a runner** (Plotkin–Power 2008;
  Ahman–Bauer 2020; core-math note §7): `syncOpStep` is the co-operation, `meaning` is the
  tensor, finalizers are the runner's `finally`. Both machines use the very same comodel,
  which is the design principle behind "the same store on both sides".
- **The machine is CESK with defunctionalized continuations** (Reynolds; Danvy; Van Horn and
  Might; stores map §5). M1 is the last place a store slot held code instead of a value.
- **The observation follows CompCert's contract shape**: a named source semantics, target
  semantics and observation, allowed behaviours explicit (plan §3). `Obs` is the final state;
  the trace is not yet split into observable and silent labels (R3, later).

## 4. What to take, from whom, and for which object

The owner's steer: steal implementations, data structures and abstractions from every verified
implementation we can find. Organized by the object it serves, with the note in this tree or
foldlab that already read the source.

| object | take | from | where it is already read |
| --- | --- | --- | --- |
| world order, columns | persistent vs owned resources; `Stable` predicates; monotone-store invariant theorem | Iris / Hazel (de Vilhena 2022); MCA (Cohen et al. 2025); Jacobs 2012 | papers review §1.3, A3; `Protocol.lean` |
| typing judgement | ITree predicate with protocol; inversion per node | Xia et al. 2020; Hazel Fig. 2.3–2.5 | composed graph §4; foldlab `EFFECTS-BACKEND.md` R1–R3 |
| stores | comodel + runner; finalization as the runner's `finally` | Plotkin–Power 2008; Ahman–Bauer 2020 | core-math §7 |
| store validity | **legal states defined by reachability; invariants are theorems, not assumptions** | foldlab `entity-store/STORE-MODEL.md` §3 (WF1–WF3 over `Reachable`), `MACHINE-ALGEBRA.md` §4 | this note §3.5 |
| heap, cells, tables | data refinement: abstract interface with laws, list as proof instance, fast carrier as refinement | Hoare 1972; Isabelle Refinement Framework / Autoref (Lammich); seL4's three layers | stores map §5, R4; plan §5 (the `alpha` shape) |
| container laws | index each law by its hidden parameters (key relation, duplicate policy, projection, ownership) | the critique's six counter-models | critique response §6 |
| park handshake | generation-indexed handles; stale resume inert | Eio `sem_state.ml` cancelled-waiter clause | `Wake.lean` header; stores map §2.1 |
| logs | state is the truth, log is write-only; observable vs diagnostic alphabets | event sourcing; CompCert labels; CakeML FFI oracle | stores map F3, R3 |
| in-place update | why Lean `Array` does not cross to OCaml | Counting Immutable Beans (2019); Perceus (2021) | LCNF note references; stores map §5 |
| stuttering simulation | fuel as the up-to measure; relation on whole machine states | Milner; Sangiorgi; Pous 2016; Hur et al. 2013 | core-math §8 |
| composed modules | histories and rely/guarantee before proof technique; count-only invariants are not a semaphore | linearizability literature via the critique | critique §7; catalogue §3 |
| transactions | one owner record, ordered accesses, own-write reads; wake-on-access; no versions | rc.112 `TxRef`; GHC STM; ZIO STM | stm-scout §1.3–1.5, §3 |

Foldlab's `formal/effect-core-v1` is a scaffold (its `Stateful/*.lean` and `Concurrency/*.lean`
are 11-line placeholders); there is no implementation to take from it. What foldlab contributes
is the store-model *method* (§3.5 below), the effect-replay vocabulary (`docs/effect-replay/
CONTEXT.md`: histories as under-approximations, no live fallback, the direction law), and the
research sweeps §5 draws on.

### 3.5 The one method to take now: validity by reachability

`E4-STORES-CE-003` says: a valid Deferred can store `Completion.ofRefGet ⟨9⟩` while reference 9
does not exist, and `Stores.WF` still holds (`StoresLawsContract.lean:80-84`). The follow-up
rightly stopped M1 from deleting it. The brief calls it "a property of the whole-machine typed
invariant (M2)". Sharper: it is a **reachability** property, and the tree already proves
those the right way.

Foldlab's store model does not axiomatize well-formed stores; it defines legal stores
inductively (`Reachable ∅`; `Reachable σ ∧ legalInsert σ b → Reachable (σ ∪ …)`) and proves
WF1–WF3 as theorems over `Reachable`. This tree's `MachineOk`/`TypedState` are the same move:
`StoresOk` holds at every *reachable* registration because it is carried through `spawn`,
`evaluatePrim`, `driveStep`, `flushAll` and `replayEval` (`Simulation/Hooks.lean:36-40` says
exactly this for `ScopeKeysFresh`). A completion with a dangling cell cannot be *written* by
a step, because `deferredCompleteWith`'s request is checked by `SyncOp.validIn` at every
reachable step (`syncOpStep_answer_valid`, `syncOpStep_wf`). So the boundary CE-003 marks is
closed not by widening `WF` or by a new conjunct on `Completion`, but by the preservation
theorem of M6 over the world of M2: **no reachable world stores an invalid reference**. Until
then the counterexample stays, translated to the data representation, as the follow-up ruled.

Consequence for M2's `PromiseTable`: state it over the data (`CompletionOk w (Π ⟨i⟩) x`), and
let `CompletionOk` for `ofRefGet cell` say only "`Ρ cell` is `some ty` and `ty` fits the
column"; existence of the cell is then `Handle.existsIn`, the six arms that already exist,
carried by reachability. Do not put "the cell exists" into `Completion`'s type.

## 5. Verified language abstractions, for the lowering-module API

The owner's mid-turn ask: the research on verified language abstractions is key to a robust
Lean API for plugging in lowering modules in LCNF (and not hand-written OCaml). This section
organizes what the tree and foldlab have read, and states the API shape it implies. The rule
in force is "OCaml only from LCNF".

### 5.1 What the lowering estate is today

- `src/OCaml5/Lcnf/Translate.lean` (1,132 lines): one `ReaderT TCtx (StateM St)` action over
  `Code .pure`, carrying five concerns (naming, carriers, list literals, join-point seeding,
  wrapper folding). No theorem can be stated about it directly (LCNF note §2.6).
- `src/OCaml5/Lcnf/Externs.lean` (510 lines): the `Extract Constant` of the route. Seven row
  kinds (`fn`, `fn?`, `type`, `field`, `elem`, `ops`, `carg`); a row changes a *type*, so a
  wrong rewrite is an `ocamlopt` error; an unused `fn` row is a fatal stale ledger; "the table
  is complete iff the generated file compiles". What is missing is the fidelity obligation per
  row.
- `src/OCaml5/Ml/Profile.lean:297`: `Profile` = admitted constructs, admitted library modules
  (each with an optional Lean carrier), banned modules (`Obj` outright).
- `tools/Conform/Lcnf/{Semantics,SemanticsTarget}.lean`: two Lean evaluators (LCNF; emitted
  OCaml syntax), 1,167 lines, **zero theorems**; `Rules.lean` holds structural summaries and
  policy joins, not preservation proofs. The 20,387-vector differential between them was
  produced once and no lane re-runs it.
- `ocaml/engine/externs.txt` and the hand prelude: about twenty store operations
  re-implemented by hand (`sh_*`), property-tested law by law against the Lean lists
  (`prop_store.ml` ST1–ST8), stated nowhere in Lean (stores map F4).

### 5.2 The research, and what each piece gives the API

| source | what it establishes | what the API takes from it |
| --- | --- | --- |
| **CompCert** (Leroy 2009), **CakeML** (Kumar et al. 2014) | per-pass forward simulation between two formal semantics, composed; the observation named once | the theorem's shape: `eval f v = some a → evalT (lower f) (Rv v) = some (Ra a)` by induction on a *reference fragment*, never on `Code .pure` (LCNF note §2.6 Tier 3) |
| **Fiat Crypto**, **Bedrock2**, **Everest/HACL\*** (foldlab ecosystems note) | proved and unproved backends are labelled distinctly; a deep narrow slice beats a broad unlabelled promise | every lowering module carries an **evidence tier** as data: stamped (goldens), tested (differential), proved (simulation) |
| **Coq extraction** (Letouzey 2002) | `Extract Constant` is an unchecked axiom about the target; `Obj.magic` voids the target's types | the mono-LCNF route already avoids `Obj.magic` structurally; an `Externs` row is an `Extract Constant` and must name its **obligation**: the Lean model operation it replaces, the property test that checks it, the refinement lemma when one exists |
| **LLVM CodeGenerator**, **MLIR dialect conversion** (owner's steer, `lcnf-route.md` §7; LCNF note §2.2) | a target is data (`TargetMachine` + `DataLayout` mandatory, the rest tables); legalization = promote/expand/custom, each rule with a preservation obligation; `TypeConverter` is its own object; verify after every step | `Target.Layout` as the one reader of the environment both pipelines project (LCNF note §4(ii)); a `Legalization` rule = source pattern, target pattern, side condition, obligation, tier; `Ml.checkModule` fatal |
| **MLIR Transform dialect** (foldlab frontier) | an optimization *schedule* is itself IR with explicit effects and failure modes | the lowering pipeline as a list of named passes with declared inputs and outputs, inspectable, not a monolithic action |
| **data refinement** (Hoare 1972; Autoref/Refinement Framework; seL4) | write the algorithm over an abstract container, prove each concrete operation commutes with `alpha` once | the plug-in point is an **interface with laws** (`Arena`, keyed table, ordered work, append sequence, path, derived view; plan §5); a module is an instance plus its tier; the machine is written once against the interface (stores map R4) |
| **DimSum** (foldlab frontier) | independently defined language modules as LTSs linked by events, with proved wrappers; no shared heap or global syntax | several targets (OCaml, TypeScript, Wasm) share one **event boundary** (R3's observable alphabet), not one memory model; a wrapper per target, related by refinement |
| **handler fusion, "From High to Low"** (Schrijvers 2015; 2025) and **evidence passing** (Xie–Leijen 2021) | lowerings of state and control are meaning-preserving handler transformations; an effect calculus and its runtime representation are different objects with a proved relation | the store comodel's lowering (list → arena → OCaml table) is a handler transformation with its laws; the fiber machine's is the second (defunctionalized continuations are already the evidence-passing form) |
| **Alive2**, **Cranelift ISLE/Crocus** (LCNF note references; foldlab frontier) | candidate producer → semantic validator → independent checker; prove rewrite rules one at a time, fuzz differentially meanwhile | gate the differential (Tier 2) *now* and wide; prove legalization rules one by one (Tier 3 per rule); the validator is independent of the producer |
| **WasmCert**, **Miri / mir-opt** | prefer a target whose semantics is mechanized; an interpreter for your own IR is the oracle; golden IR dumps are regression tests | `SemanticsTarget` is *our* model of OCaml, a cost of the target; run `Conform.Lcnf.Semantics` as the oracle; commit the closure manifest (`declHash`, construct census) per root set |
| **relational separation logic for handlers** (2026, Iris artifact; foldlab frontier §3) | relate a direct specification to a continuation-bearing implementation without identifying the two | the reference machine vs the compiled machine (`run_eq_ref`) is that relation in first-order form; keep it, do not import Iris |

### 5.3 The API shape this implies

Three objects, each already half-present, and one ledger:

```
Carrier interface (plan §5, row 85 first):
  class Arena (σ : Type) (α : Type) where
    empty : σ ; size : σ → Nat ; peek : σ → Nat → Option α ; poke : σ → Nat → α → σ ; alloc : σ → α → Nat × σ
    peek_alloc / peek_poke_same / peek_poke_diff / size_alloc / size_poke
  instances: List α (proof); E4_store (trusted; evidence = prop_store.ml ST1–ST8, tier: tested)

Layout (LCNF note §4(ii)): one reader of the environment, both pipelines project it
  Layout := builtin ty | alias ty | record fields | variant ctors | carrier chain | placeholder
  FieldInfo := ⟨leanName, ocamlName, relevant, ty, carrier?⟩     -- mutability has one home: a carrier

Legalization rule (lcnf-route §7; MLIR):
  ⟨ source : Frag-pattern, target : Ml.Expr-pattern, side : Prop, obligation : Prop, tier : Tier ⟩
  Tier := stamped | tested | proved
  an Externs row is a Legalization whose obligation names the model operation and the test
```

The ledger: every `Externs` row and every legalization rule has a tier; a row with no
evidence is a ceiling that may only rise, checked the way the stale-`fn`-row check already is
(`LcnfGen.lean:201-215`). The order the LCNF note already set: `Frag` and `ofCode` (the
reference fragment and its checked reader, Tier 3 pieces 1–2) now, because they turn the
accepted fragment from prose into a decidable gate whether or not the theorem lands; `Layout`
(A2) as a strict refactor with `make check-gen` as the receipt; `Arena` (P2) as the first
refinement consumer; the simulation theorem last, and only with the `Nat < 2^62` side condition
threaded or a `Nat` carrier chosen first. **And not**: no second IR, no checker in the OCaml
closure, no hand-written OCaml in the load path (LCNF note §5.2 names the three files that
still are).

## 6. The kickoff checklist for Codex (M1), and the order around it

1. Types first, narrow builds: `DeferredCell.completion`, `DeferredStore.due`, delete
   `MemoEntry.effect`; `lake build Effect4.Machine.Stores`. Then `InterpR` (`denoteStored` →
   `denoteCompletion`, five sites), then `StoresLaws`/`Handles`, then `Simulation/*` and
   `Guard/*`, then the census (`Test/Audit/*` re-pin), then `make gen-lcnf` and `make gen-cas`
   once at the end. Radius 38 files (deep-dive review §10 lists them).
2. Delete: `CompletionShaped`, `DeferredOk` (whole; `StoresOk` keeps `ScopeKeysFresh`),
   `StoredCodeNoRace`, `DeferredCodes`, `denoteStored`, `STORES-FB-COMPLETION`.
3. Keep, translated to the data: `E4-STORES-CE-003` (§3.5). Keep DI-97's `poll` shape.
4. The memo deletion's two conditions: census witnesses of `layer.memo-build-once` restated on
   the cell; the representation connector for the memo observation.
5. `Typed/Sources.lean`: delete row 61 only. `#position_gate` and `#typed_state` will report the
   new counts; re-pin the controls, deliberately, in the same commit.
6. Do not start the placement moves (fold connectors, Tools split, Store bisect, `Arch` →
   `Data`/`Schema`, `ModuleReadable` → `Laws/Api`) inside M1. Proposed order: M1 lands; the moves
   as one import-only commit, verified by `make check` and a `make gen-architecture` diff that
   shows the 26 falling; then M2 (`Typed/World.lean`, the instruments moved under `Typed/`).
7. Standing rules: one Lean compiler process at a time; commit by explicit paths; nothing
   pushed; the owner's `README.md` untouched; research notes force-added.

### 6a. How the proofs are done: the graph is attacked with the instruments, not by hand

Measured at `c57b1821`: 493 `aesop` calls under `src/` against about 50 registered rules (25
in the default inversion bank, 16 in `Effect4.Checker`, 6 in `Effect4.Atoms`, 3 generated into
`Effect4.TypedState`; `TyOrder`, `Rows` and `Reader` declared and empty). `#auto_census` runs
nowhere but its docstring; `#proof_wanted` and `#typed_state_obligations` only in their control;
`#frame_rules` once. The instruments exist and the loop does not pass through them. Every slice
from M1 on runs this loop, and its receipt reports the numbers.

1. **Measure before touching a proof.** `#auto_census <module> using aesop` on every module
   of the radius, in a scratch file importing the built tree. The report says which theorems
   search already closes and at what line cost; those are rewritten to the searched proof,
   the rest are the real work. The numbers go in the receipt.
2. **Statements first, into the ledger.** Every theorem whose statement changes gets an
   `Obligation` declaration and `#proof_wanted` before any proof is attempted, so
   `#typed_state_obligations <namespace> ceiling N using aesop` shows the open set; the
   ceiling falls to 0 by the last commit of the slice and is the slice's gate.
3. **Delete first.** A slice that removes a predicate removes its lemmas before restating
   anything; a smaller graph is attacked, not the old one plus the new.
4. **One bank per proof graph, grown as the slice goes.** Declare the bank in
   `Laws/Auto/RuleSets.lean` if it does not exist (for the store steps: `Effect4.Stores`).
   Register every reusable closing step there as the slice finds it: unconditional equations
   as `norm simp`, inversions as `safe destruct`, conditional round trips as `safe forward`,
   with one red control per bank (a theorem that closes only with it, as `AtomRules.lean`
   has). Re-run `#auto_census` with the bank at the end; the count that closes must have
   risen, and that number is in the receipt.
5. **The proof loop is statement, `aesop`, residual goals, register, again.** Read the residual
   goals aesop prints; each names a missing fact. Prove it as a small lemma by `cases` and
   `simp`, register it, retry. If a statement resists after two rounds, restate it (a smaller
   lemma or a missing hypothesis), never pile tactics. No `first`, `simp_all` or `try` by hand;
   catch-all arms take one tactic or one rule, never a constructor list.
6. **Frames are generated.** A structure-valued invariant restated over new field types gets
   its frame lemmas from `#frame_rules`, not by hand.
7. **Skeletons are filled, not drafted.** Where a slice's predicate family is generated
   (`#typed_state`), the work is the clauses the generator leaves open, in the order the
   ledger lists them; the skeleton is never edited around.
8. **Narrow builds, small commits.** One module per build, its own diagnostics read; a green
   module is committed by path at once; no confirmation builds.

The receipt of a slice therefore carries four numbers beside the commit hash: theorems closed
by search before and after, rules added to the bank with its red control, the ledger ceiling's
trajectory to 0, and lines deleted.

## 7. Open for the owner

- **Row 84**: the connector obligation for an embedded straight attempt (outer continuation and
  stores, entry/exit work, reserved budget, isolation) under which `straight_sufficient`'s bound
  is inherited. I will author its specification next, as a design note; it is the substance of
  the transaction profile and needs no M1–M3 result.
- **Row 85**: `Arena` as the first refinement consumer. The interface text in §5.3 is the
  proposal; the ruling is yours. It can be authored beside row 84.
- **Row 80**: replay vs retained suspension. Not needed for a first straight profile under
  row 84; the brief's "adopt replay" is a recommendation, not a ruling.
- **Rows 81, 82, 83**: unchanged; none blocks M1–M3.
- **The placement moves' slot**: between M1 and M2, as one commit, as proposed in §6.

## 8. Receipts

Read at `f9d3112b`: `docs/core/{machine-state,decisions,lcnf-route}.md`, `docs/STATE.md`, the
plan (§3–§5, §14), the M1 specification, the deep-dive review (§0, §3, §9–§11), the follow-up,
the landed-architecture review (§2, §3), the stores map (§2, §4–§7), the typed-state plan (§2–§4)
and composed graph (§3–§5, §9), the reference-invariant caveats (§2.2, §2.4), the STM scout
(§2.6, §3, §5), the catalogue (§3, §5), the critique response (§5, §6), the papers review
(§1.3, A3), the Hazel notes (§4, §5), the core-math note (§7, §8), the LCNF reification note
(§2.4–§2.6, §4(ii), after-the-push, references); in foldlab: `CONTEXT-MAP.md`, `entity-store/
STORE-MODEL.md` §3–§4, `library/machine/MACHINE-ALGEBRA.md` §4–§5, `library/cas/EFFECTS-BACKEND.md`
R1–R3, `docs/research/{language-verification-ecosystems, effect-modeling-wasm-interoperability-
optimization-frontier, effect-runtime-ground-truth-extraction-scope}.md` (the sections cited),
`formal/effect-core-v1` (scaffold only).

Verified by command: the `Stores.lean` line numbers; `completionPrim` at `:1813`; `poll`'s
type; `DeferredOk`/`StoresOk` at `Hooks.lean:33-41`; `Stores.le`/`WF`/`MemoValid`; `Obs`;
`World` at `Handles.lean:812`; `Completion`, `Owed`, `WakeList`; `RefKernel`; `HeapNat`;
`progress`; `Protocol.lean` in full; `Sources.lean` rows 58–62; `Expect`'s constructors and
their uses; `FiberOp` = 40 constructors; `heapNotMonotone`'s statement; the aesop banks; `make
-n gen-lcnf` and `gen-cas`; `generate.py --only`'s arity; `E4_table`'s `Map.Make(Int)`;
`Externs.lean`'s row kinds; `Profile`; the line counts of the lowering estate; `Test/Machine/
Runtime/StoresLawsContract.lean:80-84`. Not built, not proved, not regenerated.
