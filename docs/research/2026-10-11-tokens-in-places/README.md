# Scouting: tokens in places (2026-10-11)

The owner, 2026-10-11: keep scouting, reading the literature and modelling, forward-looking and
exploratory. This note reads the open planned goals as a class, matches them to the literature, and
proposes the next shared structure.

**First, what to know.** Six open application goals have one shape: writes to a store cell, by
identity, are bounded by events minted on the trace. One ledger proves the shape: tokens held in
places never exceed tokens minted. Its places are code and data. The code weight is the generated
native fold that Codex landed today (`Machine/Fold.lean`, `PrimWeights`). Native code names a
written cell by its concrete key (`StoreExecution.compile_modify`). So the writer census that these
goals lack is a leaf weight of that fold, not a new analysis.

## 1. The open goals, by kind

| Goal | Shape | Kind |
| --- | --- | --- |
| `Atomic.Cleanup.log_debits` | `cleaned.count i ≤ trace.countP (startedAt (requestPath i))` | data count ≤ minted |
| `QueueWorkers.logs_history` | `(log m).count (.nat i) ≤ trace.countP (releaseAt (acquirePath i))` | data count ≤ minted |
| `Workers.logs_step` | preserves `LogDebits`, the same shape | data count ≤ minted |
| `Timeout.cleanup_keeps` | each ended attempt stands once in the cleanup log, with its own count | data count ≤ minted, with the written value |
| `Atomic.Store.shop_stages` | the shop's stages fit, "one check per write site" | a write-site census |
| `FinalizerRun.once_placed_pushes_once` | `trace.countP (registeredAt q) ≤ 1` | minted ≤ a static potential of 1 |
| `QueueWorkers.jobs_step`, `rest_step` | the model relations survive a command | simulation |
| `Routing.request_leads` | a live request leads to a call position | simulation |

The first six are safety properties of one kind. The last three are simulations, and this note
does not treat them. None of the fourteen application goals is a liveness property.

## 2. The model

### 2.1 Places, tokens, mints

A machine holds tokens in places. A place is any location that holds code or data:

- **code places:** each fiber's current code and saved stack, each race's unlaunched programs,
  each scope entry's finalizer, each pending command's program;
- **data places:** a store cell, whose token count is an observation of its content (the number
  of entries `i` in a log).

A trace event can mint tokens. The invariant is:

`tokens(m) ≤ minted(m.trace) + cap`

The per-step obligation is the balance: a step moves tokens between places, and adds no more than
the events it emits mint. This is a place invariant of a Petri net, read on the machine. The
existing `Ledger.Funded` is the special case whose only places are the fibers' saved stacks, and
whose consumption is counted on the trace.

The six goals instantiate it:

- the code weight of a fiber counts the write sites `refModify qlog t env` whose term appends
  `i`; a finalizer's weight is minted when it starts;
- the data weight of the log is `count i`;
- a write moves one token from code to data: the site leaves the current code, and the log gains
  one entry.

`once_placed_pushes_once` is the same law read backwards. The once-placed source holds one token in
the root program, and each registration spends one.

### 2.2 The three ingredients, and where each stands

1. **Code weight as a fold.** Landed. `PrimWeights.Model` has a leaf weight for the sync thunk,
   and a sync thunk carries `op (refModify q term env)` with a concrete key `q`. The write-site
   weight is one `Model` instance:
   `thunk (.op (.refModify q t env)) := if q = qlog ∧ appends t env i then 1 else 0`.
2. **The store's frame rule per key.** A store operation on key `q'` leaves the content at every
   other key unchanged. This is the frame rule of separation logic on the store, and it replaces
   each scenario's "writer census" premise. The tree has laws per operation
   (`StoresLaws.syncOpStep_*`, `NativeReferences.*_refs`) and no frame rule per key of the
   reference heap.
3. **Code that is compiled later.** A continuation's source is compiled when it runs, against the
   environment of that moment. Its write sites are known only through the value bound to the
   cell's variable. The source-opportunity budget already counts source sites per path. Its leaf
   extends to write sites, with one points-to fact: a variable bound by the allocation at a site
   holds that site's key. That is allocation-site abstraction, standard in points-to analysis.

### 2.3 What the literature says

| Source | What it gives us |
| --- | --- |
| Tarjan, "Amortized computational complexity", 1985 | the potential method: a potential that pays for each step is a bound. `Funded` is its physicist's form. |
| Hofmann and Jost, "Static prediction of heap space usage for first-order functional programs", POPL 2003 | potential attached to program syntax by type: the weight of a constructor. The generated native fold is this attachment. |
| Atkey, "Amortised resource analysis with separation logic", ESOP 2010 | potential as a separation-logic resource, so the frame rule splits it. `FiberSum.split` is this rule on the fiber table. |
| Carbonneaux, Hoffmann and Shao, "Compositional certified resource bounds", PLDI 2015 | the weights are found by a linear program over per-construct constraints, and the proof assistant checks the solution. |
| Hoffmann, Marmar and Shao, "Quantitative reasoning for proving lock-freedom", LICS 2013 | tokens prove a liveness property: each retry is paid by another thread's progress. This is the route to progress claims later. |
| Murata, "Petri nets: properties, analysis and applications", Proc. IEEE 1989 | place invariants (P-semiflows): a weighted token sum that no transition increases. |
| Talpin and Jouvelot, "The type and effect discipline", 1992; Tofte and Talpin, "Region-based memory management", 1997 | effects as sets of writes to abstract locations; the census as a typing. |
| Miller, *Robust composition*, PhD thesis, 2006 | object capabilities: only connectivity begets connectivity. A key in code is a capability, and the census is its confinement. |

The texts are not yet vendored. A packet should hold them before a proof cites a section.

## 3. Proposals

**P1. One place ledger.** It generalizes `StackLedger`:

- places: the fibers through `FiberSum`, the scope entries, the races' unlaunched programs, the
  pending commands, and named data places read from the store;
- mints: a weight per trace event;
- the balance per step, and `funded_reachable` from it, stated once.

`StackLedger` becomes the instance with no data place. The source-opportunity budget and release
custody, which each build their places by hand today, become instances too. This was the
"frame-weight ledger" of the machine-models note. The six goals add its data places.

**P2. The store frame rule, once.** `Stores.frame : q' ≠ q → (op q s).refs[q'] = s.refs[q']`, over
the key-indexed store. The per-family `*_refs` theorems become its instances.

**P3. The write census as a leaf weight.** A `PrimWeights.Model` per (cell, value). No new
traversal. The source side extends the source-opportunity leaf with the allocation-site fact.

**P4. Weights found, then checked.** Each instance today picks its weight table by hand. The
balance per evaluator arm is a linear inequality in the table's coefficients. A tool can generate
the inequalities and solve them, as Carbonneaux, Hoffmann and Shao do, and Lean checks the
solution arm by arm. An infeasible system is evidence too: no linear potential bounds that
resource. This is a later step, after P1 has two more instances.

**P5. The horizon: progress.** Every open goal is safety. "Exactly once" claims and request
progress will need liveness under fair scheduling. The token route of Hoffmann, Marmar and Shao is
the one that reuses P1: a potential that falls on every fair round bounds the rounds. With the
rule that fuel exhaustion is a live frontier, a bound reads as "no frontier within budget B".

## 4. Two smaller findings

**F1. The context region should be an instance of the region bracket.** Codex's typed context
(`0dcebf98c` on `codex/symbolic-native-fold`) adds `provideContext` as program syntax. The machine
already proves a region bracket for masks (`MaskBracket.compiled_region_bracket`, and
`StackRegionRun.compiled_region_bracket_of_prefix`). In the literature, masking, context
provision, scopes and finalizers are all scoped operations. The sources are Wu, Schrijvers and
Hinze, "Effect handlers in scope", 2014, and Lindley et al., "Scoped effects as parameterized
algebraic theories", ESOP 2024. So compile `provideContext` to a frame that restores the context
on every exit. Prove its bracket as an instance of the existing one, not as a new region law.

**F2. Edit messages form a trace monoid.** R2's `applyFiberEdits` folds an ordered edit list
over the machine, so the list monoid acts on it, with the emitted commands appended. Two edits
commute when they are independent:

- `observe` and `interrupt` at distinct targets;
- `dropToken k` and an `observe` whose observer does not carry token `k`.

So the order that matters is a Mazurkiewicz trace, not a list. The R2 laws then need one
commutation lemma per independent pair, and an edit of another fiber keeps the owner by
`FiberSum.outside_update`. This also connects R2 to schedule independence (DET-1 to DET-5):
independent edits are one more independence relation.

## 5. What this note does not establish

- No theorem. It reads statements and code, and it proposes structure.
- The six goals also need three things the ledger does not give:
  - each value's identity at the acquisition;
  - the single placement of each source;
  - the history that `Run.HistoryOf` admits. Those premises
  stay where the goals state them.
- The allocation-site fact of 2.2(3) is a claim about the compiler, to be proved; it is not read
  off a theorem here.
- Section 2.3 cites from knowledge of the literature. The texts are not on disk.

## 6. Next

1. Land P1 and P2 in `Laws/Machine`, beside `Ledger` and `FiberSum`, with `StackLedger` as the
   first instance (Claude, proof infrastructure).
2. Hand P3 and the six instances to Codex, as item 3's second half.
3. Codex's prompt gets F1 now, under item 7.
