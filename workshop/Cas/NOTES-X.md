# Lane X notes — the Char room

Running notes of lane X (`workshop/Cas/LANDING.md`, "X — the Char room"). One dated entry per
module: what is retyped, what is deleted, what is generated, what is open. Times are the
machine clock (`Get-Date`).

## 2026-09-05 10:57 — start; state of the machine, and the plan the reading forced

Read in the given order: `LANDING.md` (the X section, "The one lake, by lock" with its
`LEAN_NUM_THREADS` paragraph, "Layout after the landing"), `BRIEF.md`, the facts note §5
(Q1–Q8, Q3 and Q4 closely) and §6a, the plan §3 (the kind table) and §5 (the lane rows),
`NOTES-L1.md` (all five entries and the "Open" list), `REPORT-S1.md`, `REPORT-S2.md`; then
`src/Effect4/Store/{Canonical,Digest,Node,Kind,Genesis}.lean`, `Store/PinDerived.lean` (the
generated model, with its `--kind` line at 168), `scripts/generate-derived.ps1` (the manifest
and the invocation), and the whole Char room.

Machine: no `lean.exe`/`lake.exe`, no `LAKE.lock`; `LAKE.log` shows lane U released at
10:56:52 with exit 0, so this lane runs alone. `git status` shows U's seven `Surface/*.lean`
files and nothing of mine.

Facts checked before writing a line:

- Nothing outside the room consumes it: the only importers of `Effect4.Evidence.Char.*` are
  `src/Effect4.lean:166-169` (four import lines, unchanged by this lane) and the room's own
  modules. There is no `Test/Evidence/Char/` directory, so plan §5's "the batteries re-pinned"
  (lane Y's row) is empty at the landing.
- The Queue room names no address: a grep for `digestOf|addr|address|Canonical|Store.|json|hex|
  Digest` over `Evidence/Char/Queue/**` and over `Core.lean` matches only two prose lines in
  `Core.lean` (30, 397). So the Queue changes not at all, as the landing expects.
- `digestOf` no longer exists (L1's `Store/Digest.lean` is the spike's); `Canonical.digest` is
  the payload digest and `address` the node address. `address` is declared under `variable
  [Content Document]` (`Store/Node.lean:330,363`), so every module that calls it must have
  `Effect4.Store.Genesis` in its import closure (`instContentDocument`, `Genesis.lean:36`).
- `Ref α` is a plain structure over `Digest` (`Store/Node.lean:53`) and needs **no** instance to
  be named in a field type; only `instCanonicalRef` (line 102) needs `[Content α]`. That is what
  makes the retypings possible before `Char/Derived.lean` exists.

### The four ordering facts that shaped the layout

1. A generated `Canonical T` for a carrier with a `Ref β` field needs `Content β` **first**, and
   `--kind` emits `Content` right after that type's `Canonical` (the PinDerived model). So one
   generated file can carry the whole room if its type list is in dependency order.
2. `Evidence.fixture (… ) (receipt : Ref Receipt)` names `Receipt`, which `Conformance/
   Consume.lean` declares. To keep the field **typed** (the landing's wording; `AnyRef` is the
   escape only "where a `Ref` needs a type parameter the room cannot name"), `Evidence.lean`
   now imports `Conformance/Consume.lean`. No cycle: `Consume.lean` never mentions `Evidence`
   (its `asFixtureEvidence` answers refs, not an `Evidence`).
3. The generic hand instances must exist **before** `Consume.lean` (`receiptOf` addresses a
   `Fact`) and before `Surface.lean` (`Characterized.ofParts` addresses a `VectorSet` and a
   `Receipts`). So `src/Effect4/Evidence/Char/Canonical.lean` sits between `Conformance/
   Vector.lean` and `Conformance/VectorSet.lean`, and `Derived.lean` reaches it transitively —
   the landing's "imported by Derived" holds.
4. `Cell.lean` is the room's worked instance: it builds a `Target` and calls
   `Characterized.ofParts`, so it needs `Content Target` and `Content Implementation`, which are
   generated. So `Cell.lean` imports `Char/Derived.lean` and is the one module of the room below
   it. Its own alphabet `Label` therefore cannot be generated (the generated file would have to
   import `Cell.lean` to see it, and `Cell.lean` imports the generated file); its instance is
   hand, written in the generator's shape. Recorded as a departure.

### The import order after this lane

`Core → Conformance/{GSet, Vector} → Char/Canonical → Conformance/{VectorSet, Generators,
Compose, Consume} → Evidence → Manifest → Conformance/Surface → Char/Derived →
Conformance/Cell → Conformance` (the doc root). `Queue/*` hangs off `Core` and is untouched.

(That order was revised twice during the day, once by a cycle the typings force and once by a
generator gap; the entries below record both, and the order as landed is in the closing
report.)

## 2026-09-05 11:05 — `Conformance/{GSet, Vector}` and the new `Char/Canonical.lean`

`GSet.lean`: `import Effect4.Store.Store` → `Effect4.Store.Canonical` (the old import was for
the tuple instance and the Trie's `Path`, both gone); the one-line `Canonical (GSet α)` deleted;
the algebra table and the header say where the instance is now; a receipts section (42 lines)
added — the module had none.

`Vector.lean`: the same import change; the four tuple instances (`Provenance`, `ClientReading C`,
`Fact L C`, `Vector L C`) and `Vector.addr` deleted; header and table rewritten for `address`;
receipts (7).

`Char/Canonical.lean` (new, 430 lines): the hand instances, each with `shapeDoc`, `toVal`,
`ofVal`, `ofVal_toVal`, `ofVal_exact`, `fits` and the instance, on `Store/PinDerived.lean`'s
emitted templates — `GSet α`, `ClientReading C`, `Provenance`, `Fact L C`, `Vector L C` — plus
`Content (GSet α)`, `Content (Fact L C)`, `Content (Vector L C)` at kind `vector`, and `anyRef`
(the untyped form of `address`: `⟨Content.kind α, (address a).digest⟩`). Fifteen `#guard`s at
`L = C = Nat` run the three laws, the two refusals and the three kinds. 37 receipts, none above
the ceiling.

Three things the first draft got wrong, each measured, each worth writing down:

1. **A generic `shapeDoc` is stuck.** `def shapeDoc : ShapeDoc` under `variable {α} [Canonical α]`
   has `α` in no part of its *type*, so every use site (`shapeDoc.defs`, `shapeDoc.accepts`, the
   instance) leaves `α` a metavariable and Lean reports "typeclass instance problem is stuck:
   `Canonical ?m`". Every use has to name it: `(shapeDoc (α := α)).defs`. The generated files
   never hit this because every carrier they emit is monomorphic. **This is the first thing the
   generator will need when it takes a bare parameter.**
2. **The exported field names shadow.** `Store/Canonical.lean:45` exports `shape`, `toVal`,
   `ofVal`, `ofVal_toVal`, `ofVal_exact`, `fits` into `Effect4.Store`. A per-carrier namespace
   *inside* `Effect4.Store` shadows them (that is why `Store/PinDerived.lean` reads as it does);
   a namespace under `Effect4.Char` with `open Effect4.Store` does not — the instance's `fits`
   field then resolves to the class projection and fails with an application type mismatch. So
   the hand instances live in `namespace Effect4.Store`, with carrier names written from the
   root, exactly as the generated files do.
3. `Provenance` is hand rather than generated: `Vector L C` and `VectorSet L C` carry it, both
   are hand, and both are needed before `Derived.lean` exists.

## 2026-09-05 11:10 — `Conformance/VectorSet.lean`

Imports `Char/Canonical.lean` (so everything above it in the conformance chain has the generic
instances); `VectorSet.address` deleted in favour of the store's `address` at kind `vector`;
header and table rewritten; receipts (17). Nothing else moved: `Sound`, `kills`, `facts` and
their eight theorems are untouched.

## 2026-09-05 11:20 — the cycle the typings force, and `Conformance/Receipt.lean`

The landing asks for `Evidence.fixture (…) (receipt : Ref Receipt)` **and** for
`Target.model : Ref Manifest`. Naming a type in a field needs that type's module imported, so
the two together order the modules

    Implementation ≺ Receipt ≺ Evidence ≺ Claim ≺ Manifest ≺ Target ≺ Characterized

and today's `Conformance/Consume.lean` held `Implementation`, `Receipt` **and** `Target` in one
file, which cannot sit both below `Char/Evidence.lean` and above `Char/Manifest.lean`. The data
has no cycle (nothing points back at `Target`); only the file did. So `Implementation`,
`Receipt`, `Receipts`, `Receipts.verdict`, `Receipts.failures` and `Receipt.asFixtureEvidence`
moved to a new `src/Effect4/Evidence/Char/Conformance/Receipt.lean`, and `Consume.lean` kept
`Target`, `Target.pin`, `receiptOf`, `consume`, `replayAgainst` and the seven consume theorems.
Both headers carry the argument. **This is the one structural departure of the lane**; the
alternative was to leave `Evidence.fixture`'s receipt an `AnyRef`, which the landing's wording
refuses where a type can be named.

Retypings in the new module: `Receipt.vector : AnyRef` (kind `vector`; `Receipt` is monomorphic
and cannot name `Fact L C` — the landing's stated exception), `Receipt.pin : Ref Implementation`,
`Implementation.pins : List Digest` **kept** (a span digest is a foreign hash under Q4, checked
by recomputation, never resolved), `asFixtureEvidence : Option (AnyRef × Ref Receipt)` (it
"answers refs" as plan §5 asks) with two small theorems. `Implementation.addr`, `Target.addr`
and `Receipt.addr` are gone.

`Consume.lean`: `Target.model : Ref Manifest`, `Target.implementation : Ref Implementation`,
`Target.pin t = t.implementation` (a projection now, not a digest recomputation, with
`Target.pin_eq`); `receiptOf` keys the vector by `anyRef f`; the two hand instances the module
declared for types it does not own (`Canonical Digest`, `Canonical (Failure String)`) deleted —
the first is the store's (`Store/Canonical.lean:435`), the second is generated. 14 receipts.

## 2026-09-05 11:35 — `Char/Evidence.lean` and `Char/Manifest.lean`

`Evidence.lean`: imports `Conformance/Receipt.lean` and `Store/PinDerived.lean` (for
`Content Pin`), no longer `Store/Digest.lean` or the deleted `Store/JsonCanonical.lean`;
`set_option autoImplicit false` added (the file had none). The five constructors are retyped as
the landing states: `pin (span : Ref Pin) (guard : String)`,
`fixture (vector : AnyRef) (receipt : Ref Receipt)`, `thm (name axioms : String) (statement :
Digest)`, `decided (name domain : String) (statement : Digest)`, `assumed (premise : String)`.
`Claim.evidence : List (Ref Evidence)`, and `supported`/`coherent`/`not_outranks`/
`evidence_le_supported` take `Ref Evidence → Option Evidence`. `Evidence.json`,
`Evidence.address`, `Claim.json`, `Claim.address` and the two `Canonical … := ⟨fun x => encode
x.json⟩` instances deleted. `supported_not_by_count`'s witness now carries `zeroDigest`
(cheapest closed `Digest`; `rung` never looks at it, so the `decide` is unchanged in cost).

`Claim.path` and `Manifest.path` answered `Path`, which **no longer exists**: it was the trie's
name type and left with `Store/Trie.lean` in L1. Both now answer `List String`, with a sentence
saying a name space is a `tree` node (Q3). Retyping rather than deleting, because the census
lane builds its tree from exactly these lists.

`Manifest.lean`: `Verb.pins : List (Ref Pin)` — the field's own doc said "addresses of
`Effect4.Store.Pin` entities", which is a pointer at a node, so Q4 makes it a reference; this is
the one retyping the landing does not spell and the ruling does. `strings`, `Entry.json`,
`Grade.json`, `Verb.json`, `GradeRow.json`, `Manifest.json`, `Manifest.address`,
`Manifest.address_congr` (the store proves `address_congr` once, generically) and the
`Canonical Manifest` instance deleted; `set_option autoImplicit false` added. What is left is
the carrier, `GradeRow.ofGraded`, `declared` and `path`: 3 receipts.

**No consumer reads the deleted JSON.** Checked by grep over the whole tree: `Manifest.json`,
`Evidence.json` and `Claim.json` were read only by each other and by `Manifest.address`; nothing
under `Test/`, `harness/`, `ocaml/` or `src/` outside the room mentions them, and the room's
only importer is `src/Effect4.lean:166-169`. The printer that replaces them is
`Canonical.print`, read off the same shape as the spec, and it emits the same key order and the
same lowercase hex.

## 2026-09-05 11:45 — `Conformance/Surface.lean`

`ClaimRung` keeps its two fields and loses its instance (generated); its rung now encodes as the
`Option Rung` it is rather than as its spelling, so the row and the registry agree without a
string in the middle. `Characterized` is retyped `target : Ref Target`, `vectors : AnyRef` (kind
`vector` — the set's `L` and `C` are unnameable here), `receipts : Ref Receipts`, and its
instance is generated at kind `annotation`. `Characterized.ofParts` takes `[Content Target]` and
`[Canonical Receipt]` as **section variables**, the device of `Store/Node.lean:330`, because
both instances are derived below this module; it now computes `address T`, `anyRef vs` and
`address rs`. One theorem added, `ofParts_vectors_kind`, so the `vector` kind of that pointer is
a fact and not a comment. `VectorSet.toFixture` reads `T.model.digest.hex` and `T.pin.digest.hex`
(the driver's JSON is unchanged: the same two lowercase hex strings). 14 receipts.

## 2026-09-05 11:55 — the generator, and the gap it has

First run (all fifteen carriers, `--kind` for seven of them) emitted 1,069 lines and **failed to
elaborate**. The cause, reproduced and minimised: for a **non-recursive sum**, `Effect4Gen` emits
a one-argument reader per case whatever the case's arity —

    | .ctor 3 [v0] => (Canonical.ofVal (α := _root_.String) v0).map .decided

for `decided (name domain : String) (statement : Digest)`. Every non-recursive sum the spike
exercised (`ExportKind`, `PinRole`, `Lit`, `FnName`, `FinalizerStrategy`, `MaskMode`,
`ObserverMode`) has at most one argument per case, so the gap had never been reached. The
generator's **recursive** path is right (`src/Effect4/Program/Derived.lean:565`,
`| .ctor 2 [v0, v1] => match Canonical.ofVal … , rawTerms v1 with | some a0, some a1 => …`), so
the fix is to use that emitter's argument list in the non-recursive one. `Evidence` is the only
carrier in this room with a multi-argument case.

Second obstacle, found while working around the first: moving `Canonical Evidence` out of the
generated file needs `Content Receipt` above `Char/Evidence.lean`, and `Content Receipt` needs
`Canonical Implementation` above it. So three instances are hand and the rest generated:

- `Implementation` and `Receipt` in `Conformance/Receipt.lean` — **the generator's own output
  for those two structures, pasted unedited** from the first run (structures are emitted
  correctly), so they return to the generated file unchanged the day it can be emitted above
  `Char/Evidence.lean`;
- `Evidence` in `Char/Evidence.lean` — `shapeDoc`, `toVal`, the five `lift_*` and `fits` pasted
  from the same run; only `ofVal` is written by hand, as `guarded toVal raw`
  (`Store/Canonical.lean:250`), so `ofVal_exact` is `guarded_exact` and the only proof owed is
  `raw (toVal a) = some a` by `cases a <;> simp`. `toVal` and `shape` are the generator's, so
  **the bytes and the spec are what a fixed generator will emit and no address moves**;
- `Label` in `Conformance/Cell.lean`, for the ordering reason below, in the generator's shape.

Third run, twelve carriers, four `--kind`s: 830 lines, green, 64 receipts. The exact command is
in the file's own header and in the report below. Regenerating a fourth time reproduced the file
byte for byte (`Get-FileHash` equal), so the group is idempotent the way the other four are.

## 2026-09-05 12:05 — `Conformance/Cell.lean`

Cell is the room's worked instance and it addresses its own target, so it needs `Content Target`
and `Content Implementation`: it therefore imports `Char/Derived.lean` and is the one module
below it. That makes its alphabet `Label` ungeneratable (the generated file would have to import
Cell to see it), so `Label`'s instance is hand, in the generator's shape for a sum with one
argument per case.

`target` is retyped: `model := ⟨Canonical.digest "cell-model"⟩` — a stand-in reference, which is
exactly what the old `digestOf "cell-model"` was, now typed as what it points at — and
`implementation := address impl`, a **real** node address, since `impl` is a value this module
holds (it was inline in the old `Target`). `Implementation.pins` keeps its stand-in payload
digest. Everything else — the machine, the two mutants, the five `by decide` theorems, the
twenty-odd `#guard`s over the sixty-fact characterization — is unchanged and still passes; four
guards were added for the kinds as landed and one for `characterized.vectors.kind`.

**The cost of addressing, measured.** Every `receiptOf` now computes a node address, which
evaluates `specFor`, which evaluates the genesis (a SHA-256 over 92,462 bytes,
`docs/research/2026-09-04-cas-trait-facts.md` §6a). The worry was that Cell's sixty facts times
three sets would make the module unbuildable. Measured: `Effect4.Evidence.Char.Conformance.Cell`
builds in **8.8 s** (it was a `#guard`-heavy module before), peak `lean.exe` 549 MB. `#guard`
evaluates in the interpreter, where a 92 KB hash is cheap; the landing's kernel-cost warning is
about `by decide`, and this room has none over an address.

## 2026-09-05 12:15 — the gate

`lake build Effect4.Evidence.Char.Conformance Effect4.Evidence.Char.Queue.Mutants
Effect4.Evidence.Char.Queue.Grade Effect4.Evidence.Char.Derived` under the lock
(`LAKE.log` 11:23:52 → 11:24:14, lane X): **57 jobs, "Build completed successfully", exit 0 in
22 s**, no error and no warning. Peak `lean.exe` 505 MB; nothing killed in any run of the lane;
`LAKE.lock` released after every build (ten acquire/release pairs at 11:02–11:24, one of which
waited 30 s behind lane C; lane U had finished at 10:56). Generator runs and probes were
`lake env lean -M 3072`, one at a time, taking no lock; peak `lean.exe` in a generator run
1,572 MB, well under the 3 GB watchdog.

Receipts in the gate's log: **811 `#print axioms` lines — 150 with no axioms, 214 `[propext]`,
447 `[propext, Quot.sound]`** (four of them wrapped over two lines by long names; each
continuation checked to read ` Quot.sound]`), none other. No `sorryAx`, no `Classical.choice`,
no `sorry`, `partial`, `unsafe`, `native_decide`, `axiom`, `extern` or `implemented_by` anywhere
in the room. 297 of the receipts are the Char room's:

| module | receipts |
| --- | --- |
| `Canonical.lean` | 37 |
| `Derived.lean` | 64 |
| `Evidence.lean` | 49 |
| `Manifest.lean` | 3 |
| `Conformance/GSet.lean` | 42 |
| `Conformance/Vector.lean` | 7 |
| `Conformance/VectorSet.lean` | 17 |
| `Conformance/Receipt.lean` | 19 |
| `Conformance/Consume.lean` | 14 |
| `Conformance/Surface.lean` | 14 |
| `Conformance/Cell.lean` | 31 |

Every `#guard` in the room passes, so as executable facts: the three class laws hold on one
value of each generic carrier and on `Evidence`, `Implementation`, `Receipt` and `Label`; a byte
appended or dropped is refused on each; a `Ref Pin` refuses the `annotation` kind byte; the kind
table below is what the environment says; the cell's sixty vectors still kill both mutants, the
self-replay still verdicts `true` with sixty receipts, the mutant replay still fails with
exactly ten findings, and the fixture still projects sixty rows.

## 2026-09-05 12:20 — close

State at close: no `lean.exe`/`lake.exe` running, `LAKE.lock` absent, `git status` shows exactly
the twelve files of the report below (plus lane U's and lane C's, untouched by me). No `git add`,
`commit`, `stash` or `checkout` was run; nothing outside `src/Effect4/Evidence/Char/**` and this
notes file was written.

## Report

### Files, one line each

| file | what |
| --- | --- |
| `src/Effect4/Evidence/Char/Canonical.lean` | **new**: hand `Canonical`/`Content` for `GSet α`, `ClientReading C`, `Provenance`, `Fact L C`, `Vector L C`, plus `anyRef` |
| `src/Effect4/Evidence/Char/Derived.lean` | **new, generated**: `Canonical` for twelve monomorphic carriers, `Content` for four of them |
| `src/Effect4/Evidence/Char/Conformance/Receipt.lean` | **new**: `Implementation`, `Receipt`, `Receipts`, `asFixtureEvidence`, and the two pasted generated instances |
| `src/Effect4/Evidence/Char/Evidence.lean` | the five constructors and `Claim.evidence` retyped; the JSON route deleted; the hand `Canonical Evidence` |
| `src/Effect4/Evidence/Char/Manifest.lean` | `Verb.pins : List (Ref Pin)`; five `json` functions, `address` and `address_congr` deleted |
| `src/Effect4/Evidence/Char/Conformance/Consume.lean` | `Target` retyped to two references; `Receipt` and `Implementation` moved out; three `addr` helpers and two foreign instances deleted |
| `src/Effect4/Evidence/Char/Conformance/Surface.lean` | `Characterized`'s three fields typed; `ofParts` addresses through the store under two section variables |
| `src/Effect4/Evidence/Char/Conformance/Cell.lean` | imports `Derived`; hand `Canonical Label`; `target` retyped; the kind guards |
| `src/Effect4/Evidence/Char/Conformance/GSet.lean` | tuple instance out, import narrowed, receipts in |
| `src/Effect4/Evidence/Char/Conformance/Vector.lean` | four tuple instances and `Vector.addr` out, receipts in |
| `src/Effect4/Evidence/Char/Conformance/VectorSet.lean` | `VectorSet.address` out, `Char/Canonical` imported, receipts in |
| `src/Effect4/Evidence/Char/Conformance.lean` | the root's imports and its module table follow the new order |

`src/Effect4/Evidence/Char/Core.lean` and every `Queue/*.lean` are **untouched**: a grep for
`digestOf|addr|address|Canonical|Store\.|json|hex|Digest` over them matches two prose lines in
`Core.lean` and nothing in the Queue, so the Queue room names no address, as the landing expects.

### The kind table, as landed

| carrier | kind | where the instance is |
| --- | --- | --- |
| `Manifest` | `component` | generated |
| `Implementation` | `source` | hand (generator output, pasted) |
| `Receipt` | `annotation` | hand (generator output, pasted) |
| `Evidence` | `annotation` | hand (`ofVal` by the `guarded` recipe) |
| `Claim`, `Target`, `Characterized` | `annotation` | generated |
| `Fact L C`, `Vector L C` | `vector` | hand (generic) |
| `GSet α`, so `VectorSet L C` and `Receipts` | `vector` | hand (generic) |

No `Content` instance is claimed for `Rung`, `ClaimKind`, `Entry`, `Grade`, `Verb`, `GradeRow`,
`Failure String`, `ClaimRung`, `ClientReading C`, `Provenance` or `Label`: they are fields of
other carriers and nothing references them as nodes (plan §3's rule, "a kind enters only with a
consumer that references it").

### The one kind decision beyond the table

`Content (GSet α) := ⟨.vector⟩` is **generic**, so `Receipts := GSet Receipt` files under
`vector` beside `VectorSet L C`. The table's row 14 names "VectorSet, Vector, Fact"; a receipt
set is not one of those. The alternative, `Content Receipts := ⟨.annotation⟩`, cannot be written
anywhere this room can put it: it needs `Canonical Receipt`, which is above `Char/Evidence.lean`
by the ordering above and would have to be a second hand module *below* `Derived.lean`, with
`Characterized.ofParts` carrying a third section variable. Q3 says the kind byte is not
injective on types, and `Ref Receipts` and `Ref (VectorSet L C)` stay different Lean types over
the one byte, so nothing is lost but the reading of the row. **Cheap to overrule**: one line in
`Char/Canonical.lean` becomes two specific instances plus one hand module, and the only address
that moves is a receipt set's.

### Open, for the coordinator

1. **The generator's non-recursive sum reader** (the fix that would delete three hand blocks):
   in `tools/Effect4Gen/Main.lean`, the non-recursive sum's `ofVal` emitter writes
   `| .ctor i [v0] => (Canonical.ofVal (α := T0) v0).map .case` for every case; it should write,
   for a case of arity n ≥ 2, the form its own recursive emitter already writes —
   `| .ctor i [v0, …, v(n-1)] => match Canonical.ofVal (α := T0) v0, … with | some a0, …, some
   a(n-1) => some (.case a0 … a(n-1)) | _, …, _ => none` — and `ofVal_exact`'s template then
   needs the struct emitter's nested `split at h` / `next b… h…` script rather than the
   `Option.map` one. With that, `Effect4.Char.Evidence` goes back into the group and
   `Char/Evidence.lean` loses its `namespace Effect4.Store` block.
2. **Bare parameters** (lane G's open item): when the generator takes one, note (1) of the 11:05
   entry — a generic `shapeDoc : ShapeDoc` must be applied explicitly at every use site, or every
   use is a stuck instance problem.
3. **The group is not in `scripts/generate-derived.ps1`** (not this lane's file). Its row, ready
   to paste after the `Pin` row, is

   ```powershell
   [pscustomobject]@{
     Name    = 'Char'
     Imports = 'Effect4.Evidence.Char.Conformance.Surface'
     Out     = 'src\Effect4\Evidence\Char\Derived.lean'
     Guards  = ''
     Kinds   = @('Effect4.Char.Claim=annotation', 'Effect4.Char.Manifest=component',
                 'Effect4.Char.Target=annotation', 'Effect4.Char.Characterized=annotation')
     Types   = @(
       'Effect4.Char.Rung', 'Effect4.Char.ClaimKind', 'Effect4.Char.Claim', 'Effect4.Char.Entry',
       'Effect4.Char.Grade', 'Effect4.Char.Verb', 'Effect4.Char.GradeRow',
       'Effect4.Char.Manifest', 'Effect4.Char.Failure@String', 'Effect4.Char.Target',
       'Effect4.Char.ClaimRung', 'Effect4.Char.Characterized')
   },
   ```

   with `Guards` empty because a `--append` fragment would live under `tools/Effect4Gen/guards/`,
   which this lane may not write. The acceptance guards it would have carried are in the room
   instead: the kinds and the round trips are `#guard`ed in `Conformance/Cell.lean` (the kind
   table), `Conformance/Receipt.lean`, `Char/Evidence.lean` and `Char/Canonical.lean`.
4. **`Effect4Gen` emits into `namespace Effect4.Store`** whatever the group, so
   `Evidence/Char/Derived.lean`'s declarations are `Effect4.Store.CharGen.*` over
   `Effect4.Char.*` carriers. Harmless (instances are namespace-blind) but worth a `--namespace`
   option when someone is in the tool.
5. **`Conformance/Receipt.lean` is a new module** the landing did not plan, and
   `Char/Canonical.lean` is the one it did. Both are named in `Conformance.lean`'s table.
6. `GradeRow.evidence` stays an `Evidence` **by value**, as its own doc says; it is the one place
   the room stores evidence rather than referencing it, and the landing does not ask otherwise.
7. `Cell.lean`'s `target.model` is a stand-in reference (the cell has no manifest node), exactly
   as it was a stand-in digest before.
