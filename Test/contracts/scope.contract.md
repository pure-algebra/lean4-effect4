# Scope runtime first-order state machine contract

Status: FROZEN / RED, breaker-authored 2026-09-01

Implementation fence:
`Effect4/Runtime/Scope.lean`

Lean battery:
`Effect4Test/Runtime/ScopeContract.lean`

Axiom report:
`Effect4Test/Runtime/ScopeAxiomReport.lean`

Counterexamples: `E4-RUN-CE-001` through `E4-RUN-CE-009` in
`test/counterexamples/REGISTER.md`; witnesses in
`Effect4Test/Counterexamples/Runtime/Scope.lean`; attack shapes in
`test/counterexamples/runtime/ATTACKS.md`

Proof graph: `SCOPE-PG-STATE` in `docs/SCOPE-DAG.md`

Pinned source: `effect@4.0.0-rc.112` under `vendor/effect-4.0.0-rc.112/src/`.
Reading: `docs/effect-rc112-fiber-runtime.html` section 6.

## Claim boundary

This packet freezes one bounded model: Effect v4's `Scope` as a first-order
state machine over two externally admitted alphabets — the finalizer key `κ`
and the finalizer name `φ` — together with an externally supplied finalizer
interpretation `run : φ -> Exit β ε δ ι α -> Exit Unit ε δ ι α`, and the
already-canonical `Effect4.Exit` and `Effect4.Cause` carriers, which it reuses
unchanged.

It does not implement the model. It does not model effect syntax, primitives,
continuation frames, the run loop, fibers, the fiber context, interruption
masks, the scheduler, JavaScript `Map` objects, or object identity. It makes no
Effect TypeScript compatibility claim and no code-generation claim.

It does **not** claim that `Effect4.Scope` is equivalent to rc.112's `Scope`.
It claims that each named clause of each named census row in the per-row table
of `docs/SCOPE-DAG.md` has an exact theorem over the Effect4 model, and it
names, in four `SCOPE-FB-*` rows of that document, exactly what was dropped:
host key freshness, host state-object identity, the meaning of a finalizer
name, and the whole fiber machine. Six of the fifteen assigned census rows are
declared **partial**; see the per-row table.

## CATEGORIES

- `inductive-data` — strategies, states, and scopes are first-order data
  parameterized by externally owned alphabets;
- `total-functions` — every operation is a total, kernel-reducible function of
  its arguments and of one supplied total `run`; there is no relation, no fuel,
  and therefore no determinism theorem to state;
- `protocol-state` — registration order, the `Open` shape, key duplicate
  freedom, close idempotence, and close order are protocol invariants, which is
  why the assurance route is a graph and not a leaf;
- `algebraic-laws` — insertion order, `Map.set`/`Map.delete`, the three close
  result arms, the LIFO order, the fork linkage, and the two brackets;
- `counterexamples` — nine finite proved witnesses force the representation;
- `claim-scope` — the pinned host boundary is named, not silently modelled, and
  six rows are declared partial rather than green.

## REQUIRES

1. Lean core and Std at the repository's pinned toolchain. No Mathlib.
2. `Effect4/Runtime/Scope.lean` imports `Effect4.Semantics.Exit` and nothing
   else from Effect4. It must not import `Effect4/Concurrency/`,
   `Effect4/Layer/`, `Effect4/Channel/`, `Effect4/Context/`, or any other area
   beside or above Runtime in `docs/ARCHITECTURE.md` "Dependency direction".
3. `κ`, `φ`, and the four cause alphabets `ε`, `δ`, `ι`, `α`, plus the exit
   value `β`, are opaque parameters. No constructor, decidable equality, order,
   or default value of any of them is assumed beyond the instance binders
   written in the frozen signatures. Only `κ` carries `[DecidableEq κ]`, and
   only on the operations that compare keys.
4. `Effect4.Exit`, `Effect4.Cause`, `Effect4.Reason`, and
   `Effect4.ReasonAnnotations` are consumed exactly as
   `test/contracts/cause-exit.contract.md` froze them. This packet declares no
   new exit or cause carrier, adds no arm to either, and claims no conversion,
   view, or adapter.
5. `DecidableEq` is derived, never classical. `Classical.choice`,
   `native_decide`, `sorry`, `admit`, `partial`, `unsafe`, and new axioms are
   not allowed in the packet or the implementation. The axiom ceiling for every
   public theorem is `propext` and `Quot.sound`.
6. Universe policy: `κ`, `φ`, `ε`, `δ`, `ι`, `α` live in one explicit
   `Type u`; the exit value `β` lives in `Type v`. This is exactly the shape
   `Effect4/Semantics/Exit.lean` already uses for `Exit (β : Type v)
   (ε δ ι α : Type u)`, and the two universes are inherited from it rather than
   chosen here.
7. Auxiliary lemmas beyond the list below are permitted but must be `private`,
   so the generated declaration snapshot has no unannotated public export.

## Public declarations

Binder names may differ. Public names, constructor order and fields, argument
roles, result types, and theorem propositions are frozen by the Lean battery's
`#check (@name : proposition)` ascriptions. **The battery is the authority**;
the Lean shown here is a reading aid. Every theorem's binders are, in order,
the type parameters actually mentioned, taken from `{κ φ : Type u}`,
`{β : Type v}`, `{ε δ ι α : Type u}`, then `[DecidableEq κ]` where the
operation compares keys, then the explicit arguments.

### Existing-type and duplicate-prevention rows

The five rows — three native, two reuse — with their owners, relationships,
pins, and assurance routes are in `docs/SCOPE-DAG.md` "Existing-type rows",
together with the per-declaration records for every definition. They are not
restated here.

### D0 — the finalizer strategy

```lean
inductive FinalizerStrategy
  | sequential
  | parallel
deriving DecidableEq, Repr

FinalizerStrategy.all : List FinalizerStrategy
```

rc.112's `"sequential" | "parallel"` union. It is a label with no scheduler
payload; `docs/SCOPE-DAG.md` separation 7 records why.

### D1 — the scope state machine

```lean
inductive ScopeState (κ φ : Type u) (β : Type v) (ε δ ι α : Type u)
  | empty
  | openEmpty
  | openInline (key : κ) (finalizer : φ)
  | openMap (entries : List (κ × φ))
  | closed (exit : Exit β ε δ ι α)
deriving DecidableEq

ScopeState.entries      : ScopeState … -> List (κ × φ)
ScopeState.isOpen       : ScopeState … -> Bool
ScopeState.isClosed     : ScopeState … -> Bool
ScopeState.closingExit? : ScopeState … -> Option (Exit β ε δ ι α)
```

rc.112's `Scope.State` is `Empty | Open | Closed`, where `Open` is one record
with three fields under an XOR invariant:

```ts
type Open = {
  readonly _tag: "Open"
  finalizerKey: {} | undefined
  finalizer: ((exit: Exit<any, any>) => Effect<void>) | undefined
  finalizers: Map<{}, (exit: Exit<any, any>) => Effect<void>> | undefined
}
```

Exactly three shapes of that record are reachable, and the three `open*`
constructors are those three shapes:

| rc.112 `Open` shape | Reached by | Effect4 constructor |
| --- | --- | --- |
| all three fields `undefined` | `scopeRemoveFinalizerUnsafe` clearing the inline slot | `openEmpty` |
| `finalizerKey`/`finalizer` set, `finalizers` `undefined` | the first add, or an add after the inline slot was cleared | `openInline` |
| `finalizers` set (possibly empty), inline fields `undefined` | the second add, or `Map.delete` emptying the map | `openMap` |

Making them three constructors rather than one record with two `Option` fields
makes the XOR invariant unconstructible-otherwise instead of checked, which is
the same choice `Effect4.ReasonAnnotations` makes for its unique-key invariant
in the other direction. `openEmpty` and `openMap []` are **not** identified:
the next add lands inline in the first case and in the map in the second.
`ScopeState.openEmpty_ne_openMap_nil` freezes that, and `E4-RUN-CE-005` is the
attack it rejects. `Empty` is a third zero-finalizer state, distinct from both
because it is the only pre-`Open` one.

`Repr` is deliberately **not** derived: the `closed` arm carries an `Exit`,
whose `Cause` reasons carry `ReasonAnnotations`, which has no `Repr`.

### D2 — the scope

```lean
structure Scope (κ φ : Type u) (β : Type v) (ε δ ι α : Type u) where
  strategy : FinalizerStrategy
  state : ScopeState κ φ β ε δ ι α
deriving DecidableEq

Scope.make           : FinalizerStrategy -> Scope …
Scope.makeDefault    : Scope …
Scope.finalizers     : Scope … -> List (κ × φ)
Scope.finalizerKeys  : Scope … -> List κ
Scope.finalizerCount : Scope … -> Nat
Scope.isOpen         : Scope … -> Bool
Scope.isClosed       : Scope … -> Bool
Scope.closingExit?   : Scope … -> Option (Exit β ε δ ι α)
```

rc.112's `Scope.Closeable` also carries two type-id brands and, for a
`Closeable`, a close method; those are host tagging and are not modelled.
`Scope.finalizerCount` is `scopeFinalizerCountUnsafe`, which answers zero for
every non-`Open` scope.

`β` is a real parameter, not an artefact: rc.112 finalizers receive
`Exit<any, any>` and a `Closed` state stores that exit, so the closing exit's
value type has to be fixed somewhere. Fixing it at the scope is the cheapest
faithful choice; erasing it to `Exit Unit` would have needed a `Exit.asVoid`
that `Effect4/Semantics/Exit.lean` does not declare and this packet must not
add.

### D3 — the keyed insertion-ordered finalizer table

```lean
Scope.tableInsert : [DecidableEq κ] -> List (κ × φ) -> κ -> φ -> List (κ × φ)
Scope.tableRemove : [DecidableEq κ] -> List (κ × φ) -> κ -> List (κ × φ)
```

`tableInsert` is `Map.prototype.set` and `tableRemove` is
`Map.prototype.delete`:

```lean
Scope.tableInsert table key finalizer =
  if table.any (fun entry => decide (entry.fst = key)) then
    table.map (fun entry => if entry.fst = key then (key, finalizer) else entry)
  else
    table ++ [(key, finalizer)]

Scope.tableRemove table key =
  table.filter (fun entry => decide (entry.fst ≠ key))
```

An existing key keeps its slot and only its value changes; a new key is
appended. `tableRemove` agrees with `Map.delete` because the table's keys stay
duplicate-free, which the `Nodup`-preservation receipts establish rather than
assume. `Effect4.Data.Row` is not reused (it is the canonical finite *set*:
order-erasing, duplicate-erasing, value-less) and neither is
`Effect4.ReasonAnnotations` (a `String`-keyed annotation map with a different
owner, key domain, and merge). See `docs/SCOPE-DAG.md` separation 4.

### D4 — registration, removal, close, fork, brackets

```lean
Scope.addUnsafe      : [DecidableEq κ] -> Scope … -> κ -> φ -> Scope …
Scope.addExit        : [DecidableEq κ] ->
  (φ -> Exit β ε δ ι α -> Exit Unit ε δ ι α) -> Scope … -> κ -> φ ->
    Scope … × Exit Unit ε δ ι α
Scope.removeUnsafe   : [DecidableEq κ] -> Scope … -> κ -> Scope …

Scope.closeState     : Scope … -> Exit β ε δ ι α -> Scope …
Scope.closeOrder     : Scope … -> List φ
Scope.closeExits     :
  (φ -> Exit β ε δ ι α -> Exit Unit ε δ ι α) -> Scope … -> Exit β ε δ ι α ->
    List (Exit Unit ε δ ι α)
Scope.closeResult    :
  (φ -> Exit β ε δ ι α -> Exit Unit ε δ ι α) -> Scope … -> Exit β ε δ ι α ->
    Exit Unit ε δ ι α
Scope.close          :
  (φ -> Exit β ε δ ι α -> Exit Unit ε δ ι α) -> Scope … -> Exit β ε δ ι α ->
    Scope … × Exit Unit ε δ ι α

Scope.fork           : [DecidableEq κ] ->
  Scope … -> FinalizerStrategy -> κ -> φ -> φ -> Scope … × Scope …

Scope.addAll         : [DecidableEq κ] -> Scope … -> List (κ × φ) -> Scope …
Scope.runScoped      : [DecidableEq κ] ->
  (φ -> Exit β ε δ ι α -> Exit Unit ε δ ι α) -> List (κ × φ) ->
    Exit β ε δ ι α -> Scope … × Exit Unit ε δ ι α
Scope.acquireRelease : [DecidableEq κ] ->
  (φ -> Exit β ε δ ι α -> Exit Unit ε δ ι α) -> Scope … -> κ -> φ ->
    Exit β ε δ ι α -> Scope … × Exit Unit ε δ ι α
```

`close` is split into four named phases on purpose. "State before finalizers"
is otherwise a comment about an implementation; here `closeState` takes no
`run` at all, so `close_state_independent_of_run` is a theorem and not a
promise, and `close_reentrant_add` says what a finalizer observes.

`Scope.runScoped` carries rc.112's `scoped` name. `scoped` is a Lean keyword,
so `Effect4.Scope.scoped` would need `«scoped»` at roughly ten ascription
sites; the rename is recorded in `docs/SCOPE-DAG.md`'s declaration table.
`runScoped` takes the body's registration trace as first-order data rather than
a computation, which is the same defunctionalization DB-05 requires of every
scoped operation.

`Scope.acquireRelease` registers only after a successful acquire, because
rc.112 uses `tap`, which does not run its second argument on failure.

The four phase definitions, as frozen:

```lean
Scope.closeState self exit =
  if self.isClosed then self else { self with state := .closed exit }

Scope.closeOrder self = (self.finalizers.map Prod.snd).reverse

Scope.closeExits run self exit =
  self.closeOrder.map (fun finalizer => run finalizer exit)

Scope.closeResult run self exit =
  if self.isClosed then Exit.void
  else match Scope.closeExits run self exit with
    | [] => Exit.void
    | [only] => only
    | first :: second :: rest => Exit.asVoidAll (first :: second :: rest)

Scope.close run self exit = (Scope.closeState self exit, Scope.closeResult run self exit)
```

The three `closeResult` arms are `scopeCloseUnsafe`'s own three arms, in its
own order: `finalizers === undefined || finalizers.size === 0` returns nothing;
`finalizers.size === 1` returns `finalizers.values().next().value!(exit_)` — the
single finalizer's own effect, **not** wrapped in `exitAsVoidAll`; and only the
many case reaches `scopeCloseFinalizers` and its
`return yield* exitAsVoidAll(exits)`. The distinction is observable in exactly
one place: a single finalizer that fails with an empty cause fails the close,
where `Exit.asVoidAll [Exit.failure Cause.empty]` succeeds — the
already-proved `Exit.asVoidAll_empty_cause`. `E4-RUN-CE-009` is the attack, and
`closeResult_single` is the frozen law. A builder who merges the one-finalizer
case into the general merge fails that ascription.

## ENSURES — public theorem spine

Every proposition below is frozen in the Lean battery by exact ascription. A
weaker statement does not satisfy this contract. Ninety-eight theorems, in
battery order.

### S0 — the strategy alphabet (census: scope.make, scope.close-parallel)

```lean
FinalizerStrategy.all_nodup     : FinalizerStrategy.all.Nodup
FinalizerStrategy.mem_all       : forall strategy, strategy ∈ FinalizerStrategy.all
FinalizerStrategy.cases_receipt : forall strategy, strategy = .sequential \/ strategy = .parallel
```

### S1 — the state machine (census: scope.states)

```lean
ScopeState.cases_receipt :
  state = .empty \/ state = .openEmpty \/
    (exists key finalizer, state = .openInline key finalizer) \/
    (exists table, state = .openMap table) \/
    (exists exit, state = .closed exit)

ScopeState.entries_empty / entries_openEmpty / entries_openInline
  / entries_openMap / entries_closed
ScopeState.isOpen_empty / isOpen_openEmpty / isOpen_openInline
  / isOpen_openMap / isOpen_closed

ScopeState.isClosed_eq : state.isClosed = true <-> exists exit, state = .closed exit
ScopeState.closingExit_closed : (ScopeState.closed exit).closingExit? = some exit
ScopeState.closingExit_of_not_closed : state.isClosed = false -> state.closingExit? = none
ScopeState.openEmpty_ne_openMap_nil : ScopeState.openEmpty ≠ ScopeState.openMap []
```

`entries_openInline = [(key, finalizer)]` and `entries_openMap = table` are the
"one inline finalizer or a keyed insertion-ordered map" clause;
`entries_empty`, `entries_openEmpty` and `entries_closed` are all `[]`, which is
what makes `scopeFinalizerCountUnsafe` answer zero off `Open`.

### S2 — the scope and its observations (census: scope.states, scope.make)

```lean
Scope.make_strategy      : (Scope.make strategy).strategy = strategy
Scope.make_state         : (Scope.make strategy).state = ScopeState.empty
Scope.make_finalizers    : (Scope.make strategy).finalizers = []
Scope.makeDefault_eq     : Scope.makeDefault = Scope.make .sequential
Scope.makeDefault_strategy : Scope.makeDefault.strategy = .sequential

Scope.finalizers_eq      : self.finalizers = self.state.entries
Scope.finalizerKeys_eq   : self.finalizerKeys = self.finalizers.map Prod.fst
Scope.finalizerCount_eq  : self.finalizerCount = self.finalizers.length
Scope.finalizerCount_not_open : self.isOpen = false -> self.finalizerCount = 0

Scope.key_freshness_refused :
  forall (mint : γ -> κ) (left right : γ), left = right -> mint left = mint right
```

`key_freshness_refused` is the theorem-shaped refusal of
`SCOPE-FB-KEY-IDENTITY`, the sibling of `Reason.host_memory_refused` in the
Cause packet: rc.112 mints a key as a fresh `{}` and two evaluations of that
expression are distinct objects, whereas any Effect4 minting function is a
function of its argument. Key distinctness is therefore the caller's
obligation, and every law that needs it carries an explicit
`key ∉ self.finalizerKeys` hypothesis.

### S3 — the finalizer table (census: scope.add-finalizer, scope.remove-finalizer)

```lean
Scope.tableInsert_new :
  key ∉ table.map Prod.fst -> Scope.tableInsert table key finalizer = table ++ [(key, finalizer)]
Scope.tableInsert_existing :
  key ∈ table.map Prod.fst ->
    Scope.tableInsert table key finalizer =
      table.map (fun entry => if entry.fst = key then (key, finalizer) else entry)
Scope.tableInsert_keys_of_mem :
  key ∈ table.map Prod.fst ->
    (Scope.tableInsert table key finalizer).map Prod.fst = table.map Prod.fst
Scope.tableInsert_nodup :
  (table.map Prod.fst).Nodup -> ((Scope.tableInsert table key finalizer).map Prod.fst).Nodup

Scope.tableRemove_eq :
  Scope.tableRemove table key = table.filter (fun entry => decide (entry.fst ≠ key))
Scope.tableRemove_keys  : key ∉ (Scope.tableRemove table key).map Prod.fst
Scope.tableRemove_nodup :
  (table.map Prod.fst).Nodup -> ((Scope.tableRemove table key).map Prod.fst).Nodup
```

`tableInsert_keys_of_mem` is the in-place half of `Map.set`: re-setting an
existing key does not move it to the end. Without it a builder could
"reasonably" delete-then-append and still satisfy `tableInsert_new`.

### S4 — registration (census: scope.add-finalizer, scope.add-after-closed)

```lean
Scope.addUnsafe_strategy   : (self.addUnsafe key finalizer).strategy = self.strategy
Scope.addUnsafe_empty      :
  self.state = .empty -> (self.addUnsafe key finalizer).state = .openInline key finalizer
Scope.addUnsafe_openEmpty  :
  self.state = .openEmpty -> (self.addUnsafe key finalizer).state = .openInline key finalizer
Scope.addUnsafe_openInline :
  self.state = .openInline existingKey existing ->
    (self.addUnsafe key finalizer).state =
      .openMap (Scope.tableInsert [(existingKey, existing)] key finalizer)
Scope.addUnsafe_openMap    :
  self.state = .openMap table ->
    (self.addUnsafe key finalizer).state = .openMap (Scope.tableInsert table key finalizer)
Scope.addUnsafe_closed     : self.isClosed = true -> self.addUnsafe key finalizer = self
Scope.addUnsafe_promotes   :
  self.state = .openInline existingKey existing -> existingKey ≠ key ->
    (self.addUnsafe key finalizer).finalizers = [(existingKey, existing), (key, finalizer)]
Scope.addUnsafe_finalizers :
  self.isClosed = false -> key ∉ self.finalizerKeys ->
    (self.addUnsafe key finalizer).finalizers = self.finalizers ++ [(key, finalizer)]
Scope.addUnsafe_keys_nodup :
  self.finalizerKeys.Nodup -> (self.addUnsafe key finalizer).finalizerKeys.Nodup

Scope.addExit_open :
  self.isClosed = false ->
    Scope.addExit run self key finalizer = (self.addUnsafe key finalizer, Exit.void)
Scope.addExit_closed :
  self.state = .closed exit ->
    Scope.addExit run self key finalizer = (self, run finalizer exit)
Scope.addExit_closed_registers_nothing :
  self.state = .closed exit -> (Scope.addExit run self key finalizer).fst.finalizers = []
```

`addUnsafe_openEmpty` is the arm a builder is most likely to get wrong: after
`scopeRemoveFinalizerUnsafe` clears the inline slot, `finalizers` is still
`undefined`, so the *next* add takes the inline branch again rather than
allocating a map. `addUnsafe_closed` is rc.112's absent `Closed` arm — the
function simply falls through — and `addExit_closed` is the census clause
"runs it immediately with the stored closing Exit instead of registering it".

### S5 — removal (census: scope.remove-finalizer)

```lean
Scope.removeUnsafe_strategy    : (self.removeUnsafe key).strategy = self.strategy
Scope.removeUnsafe_inline_hit  :
  self.state = .openInline key finalizer -> (self.removeUnsafe key).state = .openEmpty
Scope.removeUnsafe_inline_miss :
  self.state = .openInline existingKey finalizer -> existingKey ≠ key ->
    self.removeUnsafe key = self
Scope.removeUnsafe_openMap     :
  self.state = .openMap table ->
    (self.removeUnsafe key).state = .openMap (Scope.tableRemove table key)
Scope.removeUnsafe_not_open    : self.isOpen = false -> self.removeUnsafe key = self
Scope.removeUnsafe_keys        : key ∉ (self.removeUnsafe key).finalizerKeys
Scope.removeUnsafe_keys_nodup  :
  self.finalizerKeys.Nodup -> (self.removeUnsafe key).finalizerKeys.Nodup
```

`removeUnsafe_inline_miss` is the `else if (state.finalizers !== undefined)`
guard: in the inline shape there is no map, so a key that does not match the
inline key removes nothing. `removeUnsafe_not_open` is the census clause
"leaving a non-Open scope untouched", and it is the only thing that stops a
removal from resurrecting an `Empty` or `Closed` scope as an `Open` one
(`E4-RUN-CE-005`).

### S6 — closing (census: scope.close-state-first, scope.close-lifo,
scope.close-sequential, scope.close-parallel, scope.close-merge,
rule.scope-close-lifo-state-first)

```lean
Scope.close_eq :
  Scope.close run self exit = (Scope.closeState self exit, Scope.closeResult run self exit)
Scope.close_state_independent_of_run :
  (Scope.close leftRun self exit).fst = (Scope.close rightRun self exit).fst

Scope.closeState_state      : self.isClosed = false -> (Scope.closeState self exit).state = .closed exit
Scope.closeState_strategy   : (Scope.closeState self exit).strategy = self.strategy
Scope.closeState_finalizers : (Scope.closeState self exit).finalizers = []
Scope.closeState_isClosed   : (Scope.closeState self exit).isClosed = true
Scope.closeState_idempotent : self.isClosed = true -> Scope.closeState self exit = self
Scope.close_closingExit     :
  self.isClosed = false -> (Scope.closeState self exit).closingExit? = some exit

Scope.close_idempotent : self.isClosed = true -> Scope.close run self exit = (self, Exit.void)
Scope.close_twice :
  Scope.close run (Scope.close run self first).fst second =
    ((Scope.close run self first).fst, Exit.void)
Scope.close_reentrant_add :
  self.isClosed = false ->
    Scope.addExit run (Scope.closeState self exit) key finalizer =
      (Scope.closeState self exit, run finalizer exit)

Scope.closeOrder_eq         : self.closeOrder = (self.finalizers.map Prod.snd).reverse
Scope.closeOrder_last_first :
  self.finalizers = table ++ [(key, finalizer)] ->
    self.closeOrder = finalizer :: (table.map Prod.snd).reverse
Scope.closeExits_eq      :
  Scope.closeExits run self exit = self.closeOrder.map (fun finalizer => run finalizer exit)
Scope.closeExits_reverse :
  Scope.closeExits run self exit = self.finalizers.reverse.map (fun entry => run entry.snd exit)
Scope.closeExits_length  :
  (Scope.closeExits run self exit).length = self.finalizers.length

Scope.closeResult_nil    : self.finalizers = [] -> Scope.closeResult run self exit = Exit.void
Scope.closeResult_single :
  self.isClosed = false -> self.finalizers = [(key, finalizer)] ->
    Scope.closeResult run self exit = run finalizer exit
Scope.closeResult_many   :
  self.isClosed = false -> Scope.closeExits run self exit = first :: second :: rest ->
    Scope.closeResult run self exit = Exit.asVoidAll (first :: second :: rest)
Scope.closeResult_reasons :
  self.isClosed = false ->
    (Scope.closeResult run self exit).causeReasons =
      (Scope.closeExits run self exit).flatMap Exit.causeReasons
Scope.closeResult_closed : self.isClosed = true -> Scope.closeResult run self exit = Exit.void

Scope.close_strategy_irrelevant :
  (Scope.close run { strategy := .parallel, state := state } exit).snd =
    (Scope.close run { strategy := .sequential, state := state } exit).snd
```

**State first.** `closeState` does not take `run`, so
`close_state_independent_of_run` holds by construction rather than by
inspection: no finalizer result can reach the state the close writes.
`closeState_finalizers` empties the registration list, so an implementation
that flipped the state and *then* read its own finalizers would run none, which
is why `closeExits` is stated over the pre-close scope. `close_reentrant_add`
is the sharp observational form: a finalizer that registers another finalizer
while the scope closes sees a `Closed` scope, and its registration therefore
runs immediately with the closing exit. It ties `scope.close-state-first` to
`scope.add-after-closed` rather than restating either.

**LIFO.** `closeOrder_eq` is the definition, `closeExits_reverse` is the
`Array.from(finalizers.values())` loop run backwards, and
`closeOrder_last_first` is the census clause in its sharpest form: whatever was
registered last is the head of the close order.

**Capture, not throw.** `closeExits` is a total `map`, so
`closeExits_length` says every registered finalizer contributes an exit — no
early exit on failure. `closeResult_reasons` says every one of those failures
reaches the closing cause. Together they are the modelled half of
`scope.close-sequential`; the temporal "awaited" half is not modelled and the
row stays `partial`.

**The merge.** `closeResult_many` is `exitAsVoidAll` verbatim.
`closeResult_reasons` holds unconditionally for a non-closed scope, including
the nil and single arms, because `[].flatMap = []` and
`[only].flatMap causeReasons = only.causeReasons`. The single arm is therefore
observable only through the exit itself, not through its reasons — which is
exactly the empty-cause case that `E4-RUN-CE-009` attacks.

**The strategy.** `close_strategy_irrelevant` is deliberately a statement about
this model's *silence*, not about rc.112: the label selects nothing here, so
two census rows stay `partial`. It is frozen rather than left implicit so that
a later fiber packet must consciously supersede it, and so that no reader
mistakes strategy-carrying signatures for strategy-dependent behaviour.

### S7 — fork linkage (census: scope.fork-linkage)

```lean
Scope.fork_closed_parent :
  parent.state = .closed exit ->
    Scope.fork parent strategy key closeChild detachFromParent =
      (parent, { strategy := strategy, state := .closed exit })
Scope.fork_closed_parent_child_exit :
  parent.state = .closed exit ->
    (Scope.fork parent strategy key closeChild detachFromParent).snd.closingExit? = some exit
Scope.fork_open_parent :
  parent.isClosed = false ->
    Scope.fork parent strategy key closeChild detachFromParent =
      (parent.addUnsafe key closeChild, (Scope.make strategy).addUnsafe key detachFromParent)
Scope.fork_child_finalizers :
  parent.isClosed = false ->
    (Scope.fork parent strategy key closeChild detachFromParent).snd.finalizers =
      [(key, detachFromParent)]
Scope.fork_parent_finalizers :
  parent.isClosed = false -> key ∉ parent.finalizerKeys ->
    (Scope.fork parent strategy key closeChild detachFromParent).fst.finalizers =
      parent.finalizers ++ [(key, closeChild)]
Scope.fork_child_strategy :
  (Scope.fork parent strategy key closeChild detachFromParent).snd.strategy = strategy
Scope.fork_shared_key :
  parent.isClosed = false ->
    key ∈ (Scope.fork …).fst.finalizerKeys /\ key ∈ (Scope.fork …).snd.finalizerKeys
Scope.fork_detach :
  parent.isClosed = false -> key ∉ parent.finalizerKeys ->
    ((Scope.fork parent strategy key closeChild detachFromParent).fst.removeUnsafe key).finalizers =
      parent.finalizers
```

`fork` takes the two linked finalizer names as arguments because they are
closures in rc.112 — `(exit) => scopeClose(newScope, exit)` and
`(_) => scopeRemoveFinalizerUnsafe(scope, key)` — and DB-02 forbids storing
those. What this packet freezes is the linkage *shape*: one key, registered on
both sides, such that removing it restores the parent exactly.
`fork_shared_key` and `fork_detach` are the two halves; with two distinct keys
the second fails, which is `E4-RUN-CE-007`. Tying the names to their operations
needs a scope store and belongs to the fork/supervision packet, so
`scope.fork-linkage` stays `partial`.

`fork_closed_parent` returns the parent untouched. A child of a `Closed` parent
gets the parent's exit and no finalizer, so anything later registered on it runs
immediately (`E4-RUN-CE-006`).

### S8 — the two brackets (census: scope.scoped, scope.acquire-release)

```lean
Scope.addAll_nil  : self.addAll [] = self
Scope.addAll_cons : self.addAll (entry :: rest) = (self.addUnsafe entry.fst entry.snd).addAll rest
Scope.addAll_finalizers :
  self.isClosed = false -> (self.finalizerKeys ++ registrations.map Prod.fst).Nodup ->
    (self.addAll registrations).finalizers = self.finalizers ++ registrations
Scope.make_addAll_finalizers :
  (registrations.map Prod.fst).Nodup ->
    ((Scope.make strategy).addAll registrations).finalizers = registrations

Scope.runScoped_eq :
  Scope.runScoped run registrations bodyExit =
    Scope.close run ((Scope.make .sequential).addAll registrations) bodyExit
Scope.runScoped_fresh_scope :
  (Scope.make .sequential) = { strategy := .sequential, state := ScopeState.empty }
Scope.runScoped_state    : (Scope.runScoped run registrations bodyExit).fst.state = .closed bodyExit
Scope.runScoped_strategy : (Scope.runScoped run registrations bodyExit).fst.strategy = .sequential
Scope.runScoped_empty :
  Scope.runScoped run [] bodyExit =
    ({ strategy := .sequential, state := .closed bodyExit }, Exit.void)
Scope.runScoped_lifo :
  (registrations.map Prod.fst).Nodup ->
    Scope.closeExits run ((Scope.make .sequential).addAll registrations) bodyExit =
      registrations.reverse.map (fun entry => run entry.snd bodyExit)

Scope.acquireRelease_failure :
  Scope.acquireRelease run ambient key release (Exit.failure cause) = (ambient, Exit.void)
Scope.acquireRelease_success :
  Scope.acquireRelease run ambient key release (Exit.success value) =
    Scope.addExit run ambient key release
Scope.acquireRelease_registers :
  ambient.isClosed = false -> key ∉ ambient.finalizerKeys ->
    (Scope.acquireRelease run ambient key release (Exit.success value)).fst.finalizers =
      ambient.finalizers ++ [(key, release)]
Scope.acquireRelease_closed_ambient :
  ambient.state = .closed exit ->
    Scope.acquireRelease run ambient key release (Exit.success value) = (ambient, run release exit)
```

`runScoped_fresh_scope` is the "installs a fresh scope" clause, and it is
stated over `Scope.make .sequential` rather than over `runScoped` because
rc.112's `scoped` calls `scopeMakeUnsafe()` with no argument: the default is
the observation. `runScoped_lifo` is the delimited body's registration trace
closed in reverse; it needs `Nodup` keys because two registrations under one
key are one `Map` entry, not two.

`acquireRelease_failure` is `tap`: a failed acquire registers nothing, so a
resource that was never acquired is never released.
`acquireRelease_closed_ambient` follows from `addExit_closed` and is stated
separately because it is the practically important case — acquiring against a
scope that has already closed must run the release now, not leak it.

## Census row to obligation map

The clause-by-clause table, including which clauses are left to the
fork/supervision and continuation-machine packets and the expected coverage
state of each of the fifteen rows after the join, is in `docs/SCOPE-DAG.md`
"Census rows this packet targets". It is not duplicated here, because two
copies of a clause map is exactly the ownership error `AGENTS.md` forbids.

Summary: eight rows are green-able (`scope.states`, `scope.make`,
`scope.add-finalizer`, `scope.add-after-closed`, `scope.remove-finalizer`,
`scope.close-state-first`, `scope.close-lifo`,
`rule.scope-close-lifo-state-first`); six stay `partial`
(`scope.close-sequential`, `scope.close-parallel`, `scope.close-merge`,
`scope.fork-linkage`, `scope.scoped`, `scope.acquire-release`); and
`scope.exit-as-void-all` is already green from the Cause/Exit packet and must
not be re-witnessed.

## Counterexample obligations

| ID | Frozen attack | Forced repair |
| --- | --- | --- |
| `E4-RUN-CE-001` | close may run its finalizers and then write the `Closed` state | write the state first; `closeState` takes no `run`, and a finalizer that re-enters the scope sees `Closed` and runs immediately |
| `E4-RUN-CE-002` | finalizers run in registration order | reverse the materialised list; the last registered runs first, and the order is visible in the merged cause |
| `E4-RUN-CE-003` | a second close re-runs finalizers, or overwrites the stored exit | guard on `Closed` first; the second close returns the scope untouched with `Exit.void` |
| `E4-RUN-CE-004` | adding to a `Closed` scope registers the finalizer, or silently drops it | run it now with the stored exit and register nothing |
| `E4-RUN-CE-005` | removal may normalise every scope into a map, and a cleared inline slot is just the empty map | leave a non-`Open` scope untouched; keep `openEmpty`, `empty`, and `openMap []` three distinct states |
| `E4-RUN-CE-006` | a child forked from a `Closed` parent is a fresh `Empty` scope | born `Closed` with the parent's exit, so nothing can be registered on it that never runs |
| `E4-RUN-CE-007` | the parent-side and child-side finalizers may use two fresh keys | one shared key, so the child's own finalizer detaches the parent's entry exactly |
| `E4-RUN-CE-008` | a failing finalizer aborts the sequential close | capture each exit through `exit()` and keep going; the length law and the flat reason law |
| `E4-RUN-CE-009` | close always merges through `exitAsVoidAll` | keep the three arms: nothing, the single finalizer's own exit, and the merge. A single finalizer failing with an empty cause fails the close |

The nine witnesses are finite self-contained breaker models in
`Effect4Test/Counterexamples/Runtime/Scope.lean`. They prove the attacks, not
the production laws, and they remain executable after the repair lands.

## Trust and acceptance

The checker is Lean's kernel at the pinned toolchain. `decide` is allowed for
finite propositions. `native_decide`, `sorry`, `admit`, `Classical.choice`, and
new axioms are not allowed in the packet or the implementation.

Known axiom traps for this packet, recorded in `COORDINATION.md` "Operational
facts worth not rediscovering":

- `simp` on a positive disequality over an opaque `DecidableEq` alphabet can
  pull `Classical.choice`; prefer `decide` or an explicit `if_neg`.
- `decreasing_by` pulls `Quot.sound`. Every definition frozen here is
  structurally recursive or a plain `map`/`filter`/`foldl`; none needs a
  termination argument.
- Build `Decidable` instances with `inferInstanceAs` over the spelled-out
  proposition so the ground `decide` receipts in the battery still reduce in
  the kernel.

The breaker phase is accepted when

```sh
lake build Effect4Test.Counterexamples.Runtime.Scope
```

exits zero, while

```sh
lake env lean -DmaxErrors=10000 Effect4Test/Runtime/ScopeContract.lean
lake env lean -DmaxErrors=10000 Effect4Test/Runtime/ScopeAxiomReport.lean
```

both exit nonzero with *only* unknown-identifier and unknown-constant
diagnostics for the fenced `Effect4.Scope*`, `Effect4.ScopeState*`, and
`Effect4.FinalizerStrategy*` names. A parse error, an import error, or a
failure in the battery's own helper code is not a clean red result. Both red
modules are declared in `test/fixtures/trust-gate/known-red.txt`, which is
self-checking in both directions: they must be removed the moment they go
green.

The builder phase requires all three files plus the complete project test suite
to exit zero, with `#print axioms` receipts inside `propext`/`Quot.sound` for
every one of the ninety-eight public theorems. It does not authorize any
coverage-number change: the runtime-coverage join in
`Effect4Test/Audit/RuntimeCoverage.lean` is a separate packet with a separate
claim, as recorded in `docs/SCOPE-DAG.md`.

## Open questions

**One `run`, or one per operation.** `addExit`, `close*`, `runScoped`, and
`acquireRelease` each take the same `run` argument. A later packet that models
a scope *store* will want one interpretation shared across a whole scope tree,
at which point `run` becomes an environment rather than an argument. That is an
additive change: every theorem above is universally quantified over `run`, so
instantiating it from an environment satisfies each one unchanged.

**Whether `closeExits` should be public.** It exists so `closeResult_many` and
`closeResult_reasons` can be stated without repeating the reverse-map, and so
`runScoped_lifo` has something to be about. It could be `private` with those
three laws restated over `closeOrder`. Recommendation: keep it public — the
list of finalizer exits is the observation that `scope.close-merge` is about,
and hiding it would make the merge law harder to read, not smaller.

**The five-constructor state versus a record with two options.** A record
`Open (inline : Option (κ × φ)) (table : Option (List (κ × φ)))` would be closer
to the rc.112 field list, at the cost of an admissibility side condition
excluding `some`/`some`. Recommendation: keep five constructors. The XOR
invariant then has no unconstructible witness to rule out, `DecidableEq` and
the ground `decide` receipts stay cheap, and `ScopeState.cases_receipt` reads as
the state diagram it is.
