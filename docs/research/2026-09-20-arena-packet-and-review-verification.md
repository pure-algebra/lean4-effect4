# Packet 2: the review verified, M1's connector corrected, and the `Arena` interface (row 85)

Written 2026-09-20 at `58d56109` with Codex's M1 in flight (`97e75781` committed, 38 files
modified and 4 new in the working tree; none touched here; nothing built). Three parts: the
owner's rulings review checked against the tree (§0), the course correction the owner asked
for on M1's representation connector (§1), and the `Arena` packet the review directs next (§2).

## 0. The review, verified

| the review says | checked | disposition |
| --- | --- | --- |
| `ObservationTx.bornAsChild`: two runs with equal `Obs`, different supervision | `docs/research/2026-09-19-critique/ObservationTx.lean:43-47`: `#guard obs initial = obs bornAsChild`; `fiberStatuses bornAsChild = [(root, .daemon)]` | **Right.** |
| `Run.observe { m with trace := t } = Run.observe m` is `rfl` after R3 | every `trace` read on the holder path is `statusOf` through `forkedIds` (`Api/Supervision.lean:166-181`, `:238-247`); `Run.lean`, `Api/Inspection.lean`, `HostSession.lean` read none | **Right**, once `statusOf` reads `origin`. |
| `Profile` lives in `Effect4.Core` | no module or namespace `Effect4.Core` exists (`src/Effect4/`: Api, Arch, Codegen, Data, Ingest, Laws, Machine, Program, Schema, Store) | **Amended.** A profile is a proof-side object; row 59's rule puts it under Laws: `Laws/Machine/Profile.lean`. |
| the holder view factors through `RunMachine` state and `HostSession.ledger` | the session record has no `ledger` field; the ledger is `active`, `pending`, `consumed`, `retired` on `Session` (`HostSession.lean:84-93`) | naming only; the mandate stands. |
| row 20: `site : List Nat` on `Origin.forked`, closing `supervision_static` through state | `spawn`'s callers carry no path: `WithFiberAction.fork program options` (`Fibers.lean:1196`), `forkIn`, `forkScoped`, the race entrants (`:941`, `:952`); `supervision_static` matches a site to a fork **by flag only** ("nothing about the run enters", `Laws/Api/Supervision.lean:285-300`) | **Accepted with its cost named.** The site must be threaded from the compiler (`Point.path` at the fork node) into the fork primitive: `Prim.fork`/`WithFiberAction.fork` gain `site`, an alphabet change with LCNF regeneration. Not one line; still the R3 slice. |
| `Arena` instantiates the **relation** form | a lawful arena has a total `toList`; the projection form follows from the laws (§2.4). The relation form is for containers that quotient order or duplicates: the keyed tables (scopes, memo maps), later | **Amended.** |
| Codex can consume the projection form at once: `alpha : StoresOld → StoresNew`, total on `StoresOk` | both types must exist in one tree for the statement. Codex's working set resolves this with `Laws/Machine/LegacyStores.lean` (334 lines copied from `6dcfe79a`) and a `projectCompletion` totalized by an `invalidCompletionFallback` (`Refinement.lean:17-27`) | **My §3 invited it, and it is the wrong shape.** The correction is §1. |
| rows 48, 51, 52 ratified as M3 content | as recorded in `decisions.md:95-99` | **Right.** |
| M1 is unblocked | M1 was already in flight: `97e75781` "store deferred completions as data", receipt `docs/research/2026-09-20-m1-receipt.md` | **Right.** |

I agree with the rulings as rulings. Two of the review's restatements would have sent the
work the wrong way (the connector's shape, Arena's form), and one under-prices row 20. Those
are corrected above, and the rulings stand with the corrections.

## 1. The course correction: M1's connector without a legacy copy or a fallback

**What is in the working tree.** `LegacyStores.lean` copies the old `MemoEntry`, `DeferredCell`,
`DeferredStore` and their operations verbatim (with fragment digests), `Refinement.lean` defines
`readCompletion : Program → Option Completion`, totalizes it with
`invalidCompletionFallback := .ofExit (.success unit)`, and states `syncOpStep_alpha` and
`obs_alpha` as obligations over an `OldObs`. It is faithful to my §3 and it is the expensive
reading of it: 334 lines of historical code kept alive in the proof graph, a fallback value that
the invariant then has to exclude, and a second observation type.

**The cleaner approach.** The deferred store's operations never inspect what a cell holds:
`make`, `cellAt`, `setCell`, `isDone`, `poll`, `register`, `cancel`, `complete`, `drainDue`,
`wakeBatch` (`Stores.lean:1097-1161` at `97e75781`) treat the completion as opaque, before and
after M1. So the store **is a functor in its payload**, and the old representation is the same
store at a different payload. The tree already has the idiom: `RunMachine`, `RunFiber` and
`Owed κ` take their code type as a defaulted parameter.

1. Make the payload a defaulted parameter, so no call site changes:
   ```
   structure DeferredCell  (κ : Type := Completion Val Err Defect FiberId Ann) where
     completion : Option κ
     wake : WakeList Unit
   structure DeferredStore (κ : Type := Completion Val Err Defect FiberId Ann) where
     cells : List (DeferredCell κ)
     due : List (Owed κ)
   ```
   `DeferredStore` written alone is the machine's store; `DeferredStore Program` is the old one.
   The ten operations are stated once with `{κ}`; the `Stores` rows that construct a completion
   (`deferredInterruptWith`, `memoComplete`) do so at the default.
2. The map and its naturality, generic in `f`, one lemma per operation, each closed by
   unfolding because no operation reads `κ`:
   ```
   def DeferredCell.map  (f : κ → κ') (c : DeferredCell κ)  : DeferredCell κ'  := ⟨c.completion.map f, c.wake⟩
   def DeferredStore.map (f : κ → κ') (d : DeferredStore κ) : DeferredStore κ' := ⟨d.cells.map (.map f), d.due.map (Owed.mapCode f)⟩
   theorem map_make     : (d.map f).make = ((d.make).1, (d.make).2.map f)
   theorem map_cellAt   : (d.map f).cellAt c = (d.cellAt c).map (.map f)
   theorem map_poll     : (d.map f).poll c = (d.poll c).map (Option.map f)
   theorem map_register : (d.map f).register c w t = ((d.register c w t).1.map f, (d.register c w t).2.map f)
   theorem map_complete : (d.map f).complete c (f e) = ((d.complete c e).1.map f, (d.complete c e).2)
   theorem map_drainDue : (d.map f).drainDue = ((d.drainDue).1.map (Owed.mapCode f), (d.drainDue).2.map f)
   … and cancel, setCell, isDone, wakeBatch
   ```
   Registered in `Effect4.Stores` as `norm simp`. `map_id` and `map_comp` close the functor.
3. The old invariant is the image of the embedding. `completionPrim` is injective (its two arms
   land on different `Prim` heads, `Stores.lean:1813`), so with `DeferredOk` restated in Laws on
   `DeferredStore Program` (three lines; it is deleted from the machine):
   ```
   theorem deferredOk_iff_image (d : DeferredStore Program) :
       DeferredOk d ↔ ∃ d' : DeferredStore, d = d'.map completionPrim
   ```
   Then every old operation on a shaped store is the embedding of the new operation, by the
   naturality lemmas at `f := completionPrim`. No inverse, no fallback, no copy: the old
   operations are the generic ones at `κ := Program`.
4. The observation-level statement is `Factors` through the projection `Stores.deferreds`
   (`Factors.trans`, `2026-09-19-critique/Contracts.lean:44`); there is no `OldObs`.
5. The memo field is a deletion, not a representation change: nothing read `MemoEntry.effect`
   but the key set (`Handles.lean:747`) and the two `StoresLaws` writers. Its connector is the
   restated `layer.memo-build-once` witnesses on the cell (already in Codex's receipt) plus one
   fact on the new type: the entry's keys still name `entry.deferred`, which is the only handle
   the deleted await program named. No legacy `MemoEntry`.
6. Delete `LegacyStores.lean`; from `Refinement.lean` delete `readCompletion`,
   `invalidCompletionFallback`, `projectCompletion`, the `alpha*` family, `OldObs`, `obsOld`,
   `projectObs`, and the two obligations over them. `Refinement.lean` keeps R79.4's two shapes
   (`Projects`, `Refines`) with the deferred functor as the first instance and `Arena` (§2) as
   the second. `CompletionData.lean` (the bank and the store obligations) stays.

**Brief for Codex** (relayed by the owner; I edit none of the in-flight files):

```
Course correction on the M1 connector (packet 2 §1). Replace the legacy-copy connector with the
functor form:
- DeferredCell and DeferredStore take a defaulted payload parameter (the RunMachine idiom);
  no call site changes. The old store is DeferredStore Program.
- DeferredCell.map / DeferredStore.map and one naturality lemma per operation, generic in f,
  registered in Effect4.Stores; map_id, map_comp.
- completionPrim_injective; DeferredOk restated in Laws on DeferredStore Program;
  deferredOk_iff_image. The connector is naturality at f := completionPrim.
- Memo: the restated witnesses plus memoEntry_keys on the new type. No legacy MemoEntry.
- Delete LegacyStores.lean and the alpha/OldObs/fallback half of Refinement.lean; keep the two
  shapes and CompletionData.lean.
- Receipt per §6a: auto_census before/after, rules added, ceiling to 0, lines deleted (the 334
  should appear there).
```

## 2. The `Arena` packet (row 85, slice P2)

### 2.1 What it is, and what it is not

The kernel already decouples the heap rows from the heap's representation: `refStepOf cell k
heap` reads one cell, runs the kernel, writes back (`Laws/Machine/RefKernel.lean:30-52`), and
`refStep_eq_refStepOf` proves the machine's `refStep` is that table. Row 85 makes the
representation a parameter of the *laws*, not of the machine: the interface, its laws, the
generic kernel with its three theorems, the list instance, and the theorem that any lawful
instance projects onto the list. The machine keeps `RefHeap := List Val` and `refStep`, because
no function value or class dictionary may enter the runtime closure (`RefKernel.lean` header;
row 76). Nothing under `src/Effect4/Machine` changes, nothing is regenerated, and the 110 sites
that read `s.refs` as a list are untouched.

The OCaml instance is the trusted carrier already in place (`E4_store` over `E4_table`, reached
through `field Effect4.Machine.Stores.refs M.t`, `externs.txt:55`) and its evidence is
`prop_store.ml`, tier *tested*. No cost claim is made (the follow-up's rejection stands:
`E4_table` is `Map.Make(Int)`, logarithmic, the list linear; neither is an array). No Lean
`Array` instance while the translator lowers `Array` to a list (F10).

### 2.2 The interface

Lean core's idiom: operations in a class, laws in a `Prop` class over it (`BEq`/`LawfulBEq`).

```
class Arena (σ : Type) (α : outParam Type) where
  empty : σ
  size  : σ → Nat
  peek  : σ → Nat → Option α
  poke  : σ → Nat → α → σ
  alloc : σ → α → Nat × σ
```

`peek`, `poke`, `alloc` are exactly `E4_store.peek`, `poke`, `grow` and Lean's `refPeek`,
`refPoke`, `refMake` (`e4_store.mli` header; `Stores.lean:845-879`). `size` is `cardinal`.

### 2.3 The laws, each with the countermodel it excludes

Row 85's text names five laws. Five are four short of what the projection and the kernel
theorems need. Ten, with `size_empty` trivial:

| law | statement | excludes |
| --- | --- | --- |
| `size_empty` | `size empty = 0` | — |
| `dense` | `(peek s i).isSome ↔ i < size s` | a sparse table: the scope store, whose keys are supply-drawn (ST6b), is **not** an arena and must not pass |
| `alloc_fresh` | `(alloc s v).1 = size s` | a fresh key that is not the extent (a free-list reuse) |
| `size_alloc` | `size (alloc s v).2 = size s + 1` | allocation that does not grow |
| `peek_alloc_new` | `peek (alloc s v).2 (size s) = some v` | the allocated value not stored |
| `peek_alloc_old` | `i < size s → peek (alloc s v).2 i = peek s i` | allocation disturbing an existing cell |
| `size_poke` | `size (poke s i v) = size s` | a write that allocates |
| `peek_poke_same` | `i < size s → peek (poke s i v) i = some v` | a write that misses |
| `peek_poke_other` | `j ≠ i → peek (poke s i v) j = peek s j` | a write that aliases another cell |
| `poke_absent` | `size s ≤ i → poke s i v = s` | **a write out of range that inserts** (ST2's point: `List.set` is a no-op there and the carrier must not insert, or density breaks) |

Old snapshots are unchanged by construction in Lean (values are immutable); for the OCaml
carrier that is the persistence of `Map.Make`, a property the tests state (critique §6: a shared
mutable payload would still break it; the payload here is an immutable `Val` image).

### 2.4 The generic kernel, the list instance, the projection

```
def writeBackA [Arena σ α] (s : σ) (cell : RefKey) : Option α → σ
  | some next => poke s cell.index next | none => s
def refStepOfA [Arena σ Val] (cell : RefKey) (k : RefKernel) (s : σ) : Option (Val × σ) :=
  (peek s cell.index).bind fun a => (k a).map fun r => (r.1, writeBackA s cell r.2)

instance : Arena (List Val) Val := ⟨[], List.length, (·[·]?), List.set, fun xs v => (xs.length, xs ++ [v])⟩
instance : LawfulArena (List Val) Val   -- core lemmas: getElem?_set_self, getElem?_set_ne, length_set, getElem?_append, …
theorem refStepOfA_list : refStepOfA cell k (xs : List Val) = refStepOf cell k xs := rfl
```

so `refStep_eq_refStepOf` and every existing kernel theorem are unchanged in statement. Then, for
every lawful arena:

```
def toList [Arena σ α] [LawfulArena σ α] (s : σ) : List α := (List.range (size s)).filterMap (peek s)
theorem toList_length : (toList s).length = size s                       -- dense
theorem peek_toList   : peek s i = (toList s)[i]?                         -- dense
theorem toList_poke   : toList (poke s i v) = (toList s).set i v          -- size_poke, peek_poke_same/other, poke_absent
theorem toList_alloc  : toList (alloc s v).2 = toList s ++ [v]            -- size_alloc, alloc_fresh, peek_alloc_new/old
theorem toList_refStepOf : (refStepOfA cell k s).map (Prod.map id toList) = refStepOf cell k (toList s)
```

The last line is R79.4's **projection form** for the heap, proved once from the laws: any lawful
arena's kernel step is the list's kernel step through `toList`. `refStepOfA_size` and
`refStepOfA_keeps` are its corollaries through `refStepOf_length` and `refStepOf_keeps`, so the
"one proof for every kernel row" is one proof for every kernel row *at every carrier*.

### 2.5 The second family

The deferred cells are the same arena at another payload: `DeferredStore.make`, `cellAt`,
`setCell` are `alloc`, `peek`, `poke` on `List DeferredCell` (ST4 says so on the OCaml side;
in Lean it is `rfl` at the list instance). Stated as three `rfl` lemmas, so one interface
serves the two dense families exactly as `E4_store` serves them in OCaml, and after §1 it does so
at any payload.

### 2.6 The instances and their evidence tiers

| instance | carrier | evidence | tier |
| --- | --- | --- | --- |
| `List Val`, `List (DeferredCell κ)` | the machine's | `LawfulArena` from core list lemmas | proved |
| `E4_store` over `E4_table` (`Map.Make(Int)`) | OCaml, `field … refs M.t`, `field … DeferredStore.cells M.t` | `prop_store.ml`: ST1 `peek` = `heap[k]?` (`dense`, `peek_*` on dense heaps), ST2 `poke` no-op out of range (`poke_absent`, `size_poke`), ST3 `grow` = fresh key `heap.length` and `to_list = heap ++ [v]` (`alloc_fresh`, `size_alloc`, `peek_alloc_new`, `peek_alloc_old`), ST4 the deferred cells, ST7 random-op agreement with the list | tested |
| `api_engine_ref.ml` list twins | OCaml reference engine | reproduce the Lean operations one for one; `test_diff.ml` | tested |
| Lean `Array Val` | — | refused while `Array` lowers to a list | — |

Three laws have no dedicated OCaml line: `dense` (implied by ST1 on dense heaps only),
`peek_alloc_old` (implied by ST3's `to_list` equality), `peek_poke_other` (implied by ST7's
random agreement). The packet adds one property line each, so the OCaml tier is law-by-law
complete and a future carrier swap is checked against the same ten names.

### 2.7 Files, order, receipt

- `src/Effect4/Laws/Machine/Arena.lean` (new, ~150 lines): §2.2–§2.4, the two list instances,
  `toList` and its five theorems. Laws in the `Effect4.Stores` bank as `norm simp` (the equations)
  and `safe forward` (`dense`).
- `src/Effect4/Laws/Machine/RefKernel.lean`: `refStepOfA` beside `refStepOf`, `refStepOfA_list`,
  the two corollaries; existing theorems unchanged.
- `src/Effect4/Laws/Machine/Refinement.lean`: the `Projects` instance for the heap through
  `toList` (its second instance after §1's functor).
- `Test/Machine/Runtime/ArenaContract.lean` (red control): a carrier whose `poke` inserts out of
  range fails `poke_absent`; the scope store fails `dense`; the list passes all ten by `decide`
  on small heaps.
- `ocaml/engine/test/prop_store.ml`: ST9 `dense`, ST10 `peek_alloc_old`, ST11 `peek_poke_other`.
- `docs/core/decisions.md` row 85 status; `docs/core/machine-state.md` §4 row.
- Order: after M1 lands; independent of M2/M3; a half-day Laws slice; I take it unless the owner
  seats it. Receipt per the kickoff note §6a: `#auto_census` on `RefKernel` before and after,
  rules added to `Effect4.Stores` with the red control, the ledger ceiling to 0, no runtime diff
  (`make check-gen` shows no generated change).

### 2.8 The ruling asked (row 85)

Adopt `Arena` as §2.2 with the **ten** laws of §2.3, in the class-plus-lawful-class form,
Laws-only (no runtime change, no regeneration), with the two list instances proved, the OCaml
carrier as the trusted instance at tier *tested* with the three added property lines, the
deferred cells as the second family, and no Lean `Array` instance. R79.4's instances are then:
first the deferred functor (§1), second the heap projection (§2.4).

## 3. Receipts

Read at `58d56109`: `Laws/Machine/RefKernel.lean` in full; `Stores.lean` at `97e75781`
(`DeferredCell`, `DeferredStore`, the ten operations, `RefHeap`, `refPeek/refPoke/refStep`);
`ocaml/engine/e4_store.mli` (the ST list), `e4_table.mli` (the signature), `prop_store.ml` (ST1–ST8
as named lines), `externs.txt:55-56`; the working-tree `Refinement.lean:1-64`, `LegacyStores.lean:1-25`,
`CompletionData.lean` (read only); `docs/research/2026-09-20-m1-receipt.md`; the deep-dive review
F10; `Api/Supervision.lean` and `Laws/Api/Supervision.lean:285-300` for row 20; `2026-09-19-critique/
ObservationTx.lean:11-54`. Counted: 110 `.refs` sites under `src` and `Test` (24 in `StoresLaws.lean`;
the `Store/*` hits are the CAS node's `refs`, not the heap). Nothing built.
