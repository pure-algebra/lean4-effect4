# Scalar and storage critique audit

The coordinator should know first: **accept the need for explicit scalar and container
contracts, but reject saturation as a general repair and reject the diagram's interfaces
as complete signatures.** Executed counterexamples expose intermediate overflow, varying
cached-view functions, impure callbacks, and shared mutable payloads. These are precise
premises to put into the existing abstraction laws, not reasons for another gate framework.

Audited base/head: `6d2385cdb9d18f3513d51e92f24835feed394c88` in
`/Users/pooks/Dev/lean4-effect4`. No repository edits, Lake runs, commits, or sweeps. Main
still has only the owner's modified `README.md`. Read `AGENTS.md` and
`ocaml/STANDARDS.md`. Scope is scalar lowering and the six proposed container law families.

## 1. What the critique gets right and what needs correction

The current translator maps `Nat`, `Int`, and every `UInt*`/`USize` to OCaml `int`
(`src/OCaml5/Lcnf/Types.lean:49-52`). This is a target profile with restrictions, not a
general implementation of those Lean types. The current `Translate.builtin?` has:

- `Nat.add` and `Nat.succ`: raw `+` (`Translate.lean:160,173`).
- `Nat.mul`, `Nat.pow`, `Nat.shiftLeft`: saturation at `max_int`
  (`Translate.lean:161-167,176-188`).
- `Nat.div`/`Nat.mod`: explicitly guarded zero divisors (`Translate.lean:168-169`).
- Large `Nat` literals: clamped to `max_int` starting at `2^62`
  (`Translate.lean:663-667`). The cutoff and shift-right cutoff are hard-coded to this
  native-width profile, not parameterized by every future host's width.
- `UInt64` and `USize` literals: emitted as an OCaml integer literal without the `Nat`
  clamp (`Translate.lean:672-673`); wide-value representability is a separate obligation.

`E4_nat.add`/`succ` saturate (`ocaml/engine/e4_nat.ml:35-37,51`), so the helper library and
generated arithmetic disagree at the boundary. `e4_nat.mli` also has stale claims that
division is unguarded and multiplication/shift-left raw in the generator. Do not use those
comments as current semantic evidence.

The critique's `forall reachable s, val(s) < 2^62-1` is only sufficient if `val` includes
**every intermediate evaluation operand/result**, not only stored states or public outputs.
The exact representable natural range on this tested OCaml profile is inclusive
`0 <= n <= 2^62-1`; a strict bound can be chosen conservatively but is not the hardware
definition. Fresh counters need headroom for the particular operation: `scopeFork` reserves
two names (`Stores.lean:1990-1991`), while many others increment by one. Logical clocks add
arbitrary admitted durations (`Timer.lean:61,94`). No single start-state bound proves these
operations remain representable forever.

The critique's alternative “checked saturating/widening arithmetic with refusal” conflates
three different behaviors. Widening to exact naturals can preserve the source operation;
checked refusal can preserve a prefix under an explicitly partial/resource-limited target
profile; saturation computes a different numeric value. None is silently interchangeable.

The JS probe below demonstrates Number's boundary behavior, **not** that every existing TS
emission path uses Number for every natural. `Codegen/PrintLeaf.lean:158` emits a natural
literal as the target integer expression; JSON data numbers separately use their explicit
`Float64` model (`Codegen/Target.lean:122-130`). Keep semantic numeric roles distinct.

## 2. Executed finite probes

Files:

- `/private/tmp/effect4-critique-scalars.ml`
- `/private/tmp/effect4-critique-scalars.output.jsonl`
- `/private/tmp/effect4-critique-scalars.js`
- `/private/tmp/effect4-critique-scalars.js.output.jsonl`

Commands, both exit 0:

```sh
opam exec --switch=effect4 -- ocaml /private/tmp/effect4-critique-scalars.ml
bun /private/tmp/effect4-critique-scalars.js
```

OCaml 5.1.1, `Sys.int_size = 63`; Bun 1.4.2. The OCaml script `#mod_use`s actual carrier
modules from the checkout. The two arithmetic expressions labeled Translate transcribe the
translator's current source; this is not a newly generated compiler artifact. All assertions
in the probe pass.

| Probe | Observed result | Consequence |
| --- | --- | --- |
| `x = max_int - 1; (x * 2) / 2` | Exact integer result `4611686018427387902`; current clamped translation `2305843009213693951` | Inputs and final result fit; intermediate closure is required |
| Successor at `max_int` | Translate raw addition `-4611686018427387904`; `E4_nat.succ` `4611686018427387903` | Wrapping leaves Nat image; saturation repeats a fresh-counter value |
| `max_int < 2^64` after literal clamp | Target `false`, mathematical comparison `true` | Clamp is not a general arithmetic relation; a specialized length-bound rewrite needs its own premise |
| Duplicate memo insertion | Raw list values `[10,20,99]`; map values `[20,10]`; first lookup returns `10` in both | Lookup quotient agrees; raw length/order do not |
| Delete duplicated memo key | Lookup becomes absent in both | Deletion must remove all matching list entries, not reveal the next duplicate |
| Pure memo update | First-binding projections agree | The quotient is closed under pure value transformations |
| Effectful memo update callback | List calls callback twice, map once | Callback purity is a real premise, not implicit in the OCaml function type |
| Table update and log chunk transition | Old table unchanged; log versions stay length 255, 256, 257 | These actual implementations maintain the tested snapshots |
| Mutable value inserted in a persistent table | Old snapshot reads `2` after external mutation of its shared `ref` payload | Persistent container spine alone does not freeze arbitrary payloads |
| Cached path made with resolver A, read with B | Cached node `1`; recomputation with B `101` | Path law must fix its resolver/code object |
| Derived view writes using different projections | Cache `[7,-9]`; recomputation with later projection `[-7,-9]` | View law must fix one projection across all writes |
| JS Number repeated successors | `9007199254740991 + 1 = 9007199254740992`; next successor stays equal | Number cannot mint an unbounded sequence of distinct handles |

The literal-clamp example does **not** alone refute the existing `Val.wf` optimization:
`Store/Val.lean:352-366` compares encoded **byte lengths** against `2^64`. That specialized
comparison can remain true on all physically representable byte sequences if a strict
length bound is proved. Its argument does not license general `Nat` saturation elsewhere.

The changing-resolver/projection and mutable-payload probes deliberately violate premises
the generated callers appear intended to satisfy. They identify missing general interface
contracts; they are not evidence that normal generated calls currently change those functions
or mutate generated immutable `Val` fields.

SHA-256:

```text
593d0d6404394397bc7a1a5d2992c6d9c09c921f2bf8ac752d79673a461fc9e6  effect4-critique-scalars.ml
7f7f65ab0380ee472ad9b2c947550ed8c3839e81856f65dc4dea772a1b7c0858  effect4-critique-scalars.output.jsonl
ac7b04c5344e8322913d67ec1bbc6c478f101870231d82c0c1c5d404472a7cf5  effect4-critique-scalars.js
9b0528c717d797003eddd3dcfa8ade8b7baa3a5ac4142867c262794d9f506b5c  effect4-critique-scalars.js.output.jsonl
```

## 3. Proposed scalar relation, rather than a global clamp

Keep source mathematics in Lean. For each target scalar profile define:

```text
RepNatP : Nat -> TargetScalar -> Prop
AdmittedOpP : Op -> List Nat -> Prop
```

For the bounded exact profile, `RepNatP n z` means `0 <= z`, `toNat z = n`, and `n <= M`.
For a big-natural profile, it is exact decoding without a fixed bound. A source `Float64`,
signed `Int`, wrapping `UInt64`, timer duration, or abstract identity requires its own
appropriate relation; a target language's use of one physical integer carrier does not
merge their logical semantics.

One operation law is:

```text
RepInputs ns zs -> AdmittedOpP op ns ->
  evalTargetP op zs = returned z -> RepNatP (evalSource op ns) z
```

Also require **existence** of that returned result under admission and sufficient target
resources. Merely proving the implication on successful outputs can be vacuous if the
target refuses everything. A checked bounded operation must characterize refusal separately:
which bound/resource failed, the retained state, and the preserved prefix. An overflow
refusal is not fabricated into a source typed error or a successful saturated value.

Lift these laws through the admitted evaluator/LCNF fragment by induction over evaluation.
Its invariant covers all intermediate values, lengths, counters, comparisons and inputs.
For fresh allocation, add injectivity and domain extension:

```text
RelHandle h k -> k notin targetLiveDomain ->
  allocTarget value c = (k,c') /\ RelState source' c'
```

The concrete freshness condition is derived from the abstract operation and state relation,
not assumed merely because the handle is wrapped in a newtype. If the counter increases by
`delta`, require `counter + delta <= M`, or perform an exact widening; saturation is never
an allocator implementation. Reuse/reclamation is possible only with a generation/renaming
relation that also covers every outstanding reference, queued wake and retained snapshot.

A specialized rewrite such as a large length bound may use a weaker relation **at that
expression only** when the enclosing observation is proved unchanged. It is not a second
semantics for all Nat operations. This keeps existing useful optimizations while giving
their licence an exact statement.

## 4. Corrected container contracts

The six rows in the synthesis are useful families of laws. Do not freeze them as six
universal modules. The current OCaml functor already has seven distinct parameters:
TABLE, TRACE, LAYERS, DISPATCHER, PPATH, PENV, FIBERS (`api_engine.ml`, instantiated in
`api_engine_inst.ml:39`). Bring semantic contracts upstream and reuse these implementations.

### Dense arena

Model: `List V`; indices are natural positions, optionally wrapped in a sort-specific key.
Expose `empty`, `extent`, `get`, `replaceExisting`, `allocate`. Keep replacement total with
the reference machine's no-op-on-missing behavior. `get k` is present iff `k < extent`;
replacement preserves extent and every other index; allocate returns old extent and extends
the model by `[v]`. Well-formedness is preserved by **every** operation, not just allocation.
No deletion or reuse is implied.

The critique's arbitrary `DenseArena<K,V>` leaves the correspondence between `K` and the
extent unspecified. Supply an explicit index/key relation. Sparse scope identities are
drawn from `Stores.nextName`, not table cardinality (`Stores.lean:1960,1990`;
`e4_store.ml:29-33`). Do not merge sparse keyed insertion with dense allocation.

### Keyed tables and the memo quotient

Give replacement, insertion, duplicate policy, deletion and enumeration separate laws. For
memo, define `first xs k` and `alpha xs = first-binding finite map`. For pure `f`:

```text
first (xs ++ [(k,v)]) q = if first xs q is some w then some w
                         else if q = k then some v else none
first (updateAll k f xs) q = if q = k then (first xs q).map f else first xs q
first (deleteAll k xs) q = if q = k then none else first xs q
```

These determine the map implementation, and are enough for pure lookup-only consumers.
`alpha` can be a function even though it quotients the list; there is no necessity to insist
that quotients can only be expressed as binary relations. A relation remains useful when
values or identities themselves use a representation relation.

Enumeration is an independent interface feature. Sorting/deduping is legitimate only if the
consumer requests that normalized view or proves it irrelevant. The frozen `Obs` sees raw
stores, so its raw list equality cannot be obtained from these lookup laws. Code comments
claiming memo insert changes “nothing any observation can see” (`e4_memo.ml:25-27`) must be
read as restricted to the admitted lookup/update/delete interface. First-binding loss is
observable if deletion removes only the first occurrence, callbacks are effectful, raw
length/order is observed, or hidden values carry resource obligations.

### Ordered work sequences

The model must name ordering (FIFO within priority, stable timer order, etc.), registration
identity, and cancellation scope. `drainSnapshot : Q -> List T` in the critique omits the
new state and cannot express transfer of ownership. The actual dispatcher uses
`drain : Q -> List T * Q` (`e4_buckets.ml:27,84-90`). Snapshot draining and live traversal
are different operations with different laws, not one interchangeable method. If issued
work remains cancellable, its ownership/liveness must remain in a separate explicit
protocol state or capability after removal from the queue. A plain pending queue cannot
prove cancellation of a captured batch.

### Append sequences

Use one exact sequence model with empty, append-batch, length, index and projection laws.
`model (append xs c) = model c ++ xs`; every preexisting index is unchanged. Persistence
holds for all retained versions. Existing `E4_log.Vec` freezes arrays after construction
(`e4_log.ml:39-50`); the finite 255/256/257 probe exercises that boundary. A ring that drops
entries needs a different diagnostic observation, not a relaxed authoritative-journal law.

### Paths and environments

Share a lawful persistent sequence implementation if useful; preserve **two sorts and
additional contracts**. An environment is `List Val` with positional lookup/prefix laws.
A path is `List Nat` rooted in a code object, with
`cachedNode = resolve fixedResolver codeRoot path`. The critique's merged `PathEnv` storing
Vals cannot express this. Cache coherence fixes the resolver and root across every
operation, as the actual `E4_ppath` counterexample demonstrates. A module parameter or an
indexed law bundle can fix them once; do not burden every caller with re-proving identity.

### Derived views

Fix a projection `project : BaseModel -> ViewModel` once, then require
`decodeView c = project (decodeBase c)` after initialization and every exposed mutation.
Expose operations through the base's owner; no unrelated setter for the cached view.
Physical sharing is an optimization, not a proof premise. Existing FIBERS carries the exit
view and updates it (`e4_fibers_view.ml:22,77-112`); changing `exit_of` across operations
invalidates the law despite all functions being pure. Fix that projection at the semantic
module level.

## 5. Persistence and ownership

For immutable representations, retained values provide the old model. For an owned mutable
representation, the theorem ranges over heap, roots and ownership, not just an OCaml record:
every retained root still denotes its previous model after an allowed update, or the consumed
root is explicitly no longer retained. Copy-on-write, frozen chunks and a unique mutable
owner are alternative implementations of that contract. A single scheduler thread proves
none of them by itself.

Even a persistent container can share a mutable payload. Either the admitted value
representation is immutable (as intended for first-order program/Val data), or the state
relation accounts for those payload locations and allowed mutations. This requirement is
reused for every container rather than repeated as bespoke checks.

## 6. Minimal integration proposal

1. Amend the synthesis with these exact scalar premises and the fixed-resolver/projection
   contracts; do not add another runtime or new data representation.
2. Formalize one operation/law bundle over an existing model and one existing implementation
   connector. Dense allocation and first-binding memo are the smallest useful instances.
3. Keep the one generic lifting theorem parametric in those law bundles. Composition then
   instantiates it; the module's concurrency behavior remains a separate protocol law.
4. Record unimplemented target operations/contracts as existing wanted declarations or
   explicit law parameters. Passing a signature or finite test is not a proof of the law.
5. Repair stale OCaml arithmetic comments and unify the selected arithmetic profile only in
   its owned implementation slice. These findings do not authorize silently changing the
   Lean Nat semantics or frozen observations now.

No new generic tooling, gate, container framework or full build is needed for this design
correction. No Lean theorem is claimed by this report; no axiom output was produced because
the parent reserved the Lean slot and this subtask changed no Lean source.
