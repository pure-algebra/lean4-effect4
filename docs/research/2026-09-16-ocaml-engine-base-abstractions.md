# The OCaml engine as the long-term platform for Eff: base abstractions

2026-09-16. Written against `f9595bbe` (select and the two-field loop landed in the engine;
51 programs, 408 tapes, 0 divergences). It answers a pasted proposal and replaces its list
with one checked against the tree.

## 1. What the pasted proposal got wrong about the present state

Most of its sections 2 and 3 describe things the engine already has.

| proposed | already in the tree |
| --- | --- |
| a typed carrier signature and a functor | `api_engine.ml:125`: `Make (M : TABLE) (T : TRACE) (L : LAYERS) (D : DISPATCHER) (P : PPATH) (E : PENV) (F : FIBERS)`. `externs.txt` is checked by the functor body compiling with no instance; a missing row is a generator refusal or a type error, never a silent guess |
| fast persistent carriers beside list carriers, with a differential | `Fast` and `Ref` in `e4_engine.mli`, each carrier with its `_list` twin (`e4_table_list.ml`, `e4_trace_list.ml`, ...), `test_diff` over three engines, `prop_*` per carrier, `bench_carriers` |
| a write-ahead log and crash recovery | `cas/e4_wal`, `cas/e4_checkpoint` (chunked, shared by digest), `cas/e4_pack`, `cas/e4_index`, `test_crash` |
| a multi-domain scheduler | `e4_sched` with mailbox, inbox, trigger, admission, quiescence, abandon |
| a manifest instead of pinned counts | `eff_manifest.txt` and `Eff_types.ctor_names_*` exist; the tests just do not use them yet |

One proposal contradicts a standing rule. "Work-stealing fibers across domains" breaks W1 and
the memory rule of `e4_sched.mli` (one machine, one owner domain) and S1 (placement is
unobservable). Fibers of one machine share one store value, so a single fiber is not a unit
that can move. The unit of parallelism is the machine; the unit of migration is the machine
value as bytes (item C below).

The `blockEnv` failure was the generator refusing loudly, which is the design working. What
is improvable is that the `carg` rows are a hand-stated analysis result (item E).

## 2. The base abstractions, in the order I would land them

### D. One generated structure table (before `iterate`)

`cas/e4_subterm.ml` carries the children table by hand, and a second hand `Tree.child`, and
says so in its own header: amendment M18 already ruled that the table is `TreeSig`-driven and
that the emitter is owed. `tools/Effect4Gen` already produces `Node.binders` and the node
lenses. Emit one row per constructor: family, ordinal, and for each child the pair
(program child index, value argument index). The second number is the M5 divergence
(`branch`: 0,1 to 1,2; `whileLoop`: 0 to 3; now `select`: 0,1 to 2,3), which is exactly the
part a person gets wrong.

With it, also emit one minimal inhabitant per constructor (`Eff_witness.all`). Then the tests
quantify over `Eff_types.ctor_names_*` and the witness list, and the four pinned counts go.

Deletes: the hand table, the hand `Tree.child`, the S5 witness list in `test_cache.ml`, the
pinned integers. Golden G9 becomes a by-product.

### E. Infer the environment-carrier parameters (before `iterate`)

A parameter carries `E.t` exactly when some call site hands it a value whose type came from a
`field` row. That is a fixpoint over the call graph of the closure, and `LcnfGen` holds both
the closure and the field rows. Compute it; keep `carg` only as an override; print the
inferred rows in the generated header so a reviewer still sees them.

Same family of fragility: two `fn` rows name compiler specialisations
(`spawn._at_...spec_19`). Those names move whenever anything upstream changes. Match a row
against the base name and every `_at_` specialisation of it.

`iterate` will add helpers that take the environment (the result term is evaluated in the
loop's false branch). With E they need no table edit.

### A. One program type, not two

There are two OCaml type families for the one Lean inductive: `Eff_types.*` (EffGen's names,
outside the functor) and the functor's own copy (LcnfGen's names, inside `Make`). Between
them sit `e4_program.ml` (about 300 lines of constructor-for-constructor translation, by
hand), `e4_program_layout.ml` (a Python-generated signature transcription), the ordinal pin
ledger, and a manifest parser that exists to check the two agree.

The program alphabet mentions no carrier. So the generator can declare it once: either a
`type` extern family that points the LCNF names at `Eff_types`, or the carrier-free type
group emitted once outside the functor by the same environment walk EffGen uses. Needs one
naming function shared by both generators (today `Cause_term_fail` and `CauseTerm_fail`).

Deletes: the translation, the layout script, the pin, the manifest check. This is deeper than
generating the translation: the translation stops existing. The chip filed on 2026-09-16
(generate the hand mirrors) should be re-aimed at this.

To check first: that the mono-phase type of `NativeEff` is structurally the source inductive
(no erased field, no specialised argument). The existing `PROGRAM_TYPES` signature already
type-checks against every instance, which is good evidence.

### B. Hoist every carrier-free type out of the functor

Same move, wider: events, exits, causes, values, decisions. Today each functor application
makes its own `event` type, so `e4_engine.mli` says the differential "must compare
RENDERINGS, not values", and `INSTANCE` carries a hand transcription of the machine alphabet
with line citations into a generated file. Once hoisted, `Fast.event = Ref.event`, the
differential is `=`, and the hand renderers become one generated printer or go.

### C. The machine value as canonical content (the large one)

`e4_checkpoint.mli` is explicit: the image is a rendering of the engine's free rows, marked
pending until the Lean shapes exist, and `machine_of_image` gives back a summary, not a
machine that can be stepped. So today recovery is replay from the load, and a checkpoint
bounds verification but not recovery time.

Generate the codec for `RunMachine` from the Lean structure (the `deriving Canonical` step of
the one-generator plan), written over the carrier signatures (`to_list`/`of_list`). Every
frame and continuation is already first-order data (names, points, environments), so nothing
in the value resists encoding. That one codec gives:

- restore without replay (checkpoint plus WAL tail);
- a byte-level differential: one sha256 of the machine per tape position, compared across
  Lean, `gen/`, `Fast`, `Ref`. Stronger than renderings and no renderer to maintain;
- migration of a machine between domains, processes and hosts as bytes, which is the sound
  form of the proposal's "fiber stealing";
- typed decisions on the scheduler boundary in place of strings (same codec family);
- CAS commit 7 discharged, `image_version` leaves 0.

### F. The prelude's hand bodies as a carrier vocabulary with laws

`api_engine_prelude.ml` has 34 hand `sh_*` bodies; the README already owes their retirement.
Each is a list operation restated on a carrier. `src/OCaml5/Lib/*` already has Lean carriers
with laws. Make the row a triple: the Lean operation, the carrier operation, and the Lean
law `toList (C.op x) = op (toList x)`. Then generate the property test from the law, in place
of the hand `prop_*` files. An extern row is then justified by a theorem and tested against
that theorem's statement.

### G. One host signature

The reactor idea is right if placed behind one rule: every host answer is a decision row in
the WAL before it is applied. A reactor (Eio or Picos; both have Lean models in
`OCaml5/Lib`) is then an answerer of parks and nothing else, and replay never touches it.
State it as one `HOST` signature: answer external rows, timers, clock. The scheduler's
`engine` record stays free of Lean and generated names, as now.

### H. The engine as the third column of the truth harness

Owed in the README. Cheap after C (compare bytes) or even before it (compare exits). This is
what makes the engine a product face and not a mirror.

## 3. Order

D and E first: they are small, and `iterate` trips on exactly the two things that broke
tonight (a new constructor, new helpers taking the environment). Then A, then B. C is the
platform item and wants its own packet. F rides with any prelude change. G and H follow the
host-rows work.
