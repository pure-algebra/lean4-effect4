# Lane B notes — the batteries, the register, the docs

Running notes of lane B (`workshop/Cas/LANDING.md`, "B — batteries, register, docs"). One dated
entry per milestone: what changed, what it cost, what is open. Times are the machine clock
(`Get-Date`).

## 2026-09-05 11:30 — start; the census before the first edit

Read in the given order: `LANDING.md` ("The one lake, by lock" with the `LEAN_NUM_THREADS`
paragraph, "Layout after the landing", the B section), `BRIEF.md`, the facts note §5/§6/§6a, the
plan §7, then `NOTES-L1.md`, `NOTES-U.md`, `NOTES-C.md`, `REPORT-S1.md`, `REPORT-S2.md`; then the
spike's `Cas/{Templates,Probe,Genesis}.lean`, the tree's `Test/Store/StoreContract.lean`,
`Test/Evidence/ArchContract.lean`, `Test/All.lean`, `Test/Counterexamples/REGISTER.md`,
`docs/ARCHITECTURE.md:19,48`, `Test/Audit/AxiomGate.lean` and `lakefile.toml`; and the landed
substrate `src/Effect4/Store/{Val,Digest,Kind,Canonical,Node,Store,Word,Traits,Genesis}.lean`,
`src/Effect4/Program/Wire.lean`, `src/Effect4/Evidence/StdLib/{Rc112,Links}.lean`,
`src/Effect4/Evidence/{Views,SurfaceViews}.lean`, `tools/Effect4Gen/Check.lean`.

Machine at start: no `lean.exe`/`lake.exe`; no `LAKE.lock`; `LAKE.log` ends with lane X's
release at 11:24:14 (exit 0), so every earlier lane is off the lock. `git status` shows lanes
U's, X's and C's files and the untracked `.coordination-append.md`; none of this lane's.

What the census found, beyond the landing's list:

- **Half of the spike's `Probe.lean` already landed inside `src/`.** Lane L1 copied the spike's
  modules verbatim, and the spike put its store, word and trait guards in the modules
  themselves: `Store/Store.lean:558-634` (`probeSchema`, `probeEntry`, `outcomeIs`,
  `refusedWith`, `afterPut`, `probeStore`, the admission and root guards),
  `Store/Word.lean:879-952` (`probeWord`, `replayed`, `probeLocal`, `verified`, the closure,
  layered, outbox and verify guards) and `Store/Traits.lean:258-351` (`entryRef`, the four
  traits, `traitStore`, the resolution and supersession guards). `WordContract` and
  `TraitContract` therefore restate the brief's list against those fixtures rather than
  re-inventing them, and add what the library does not guard: the layered read in both
  directions, a `wf` word applied twice through `Word.apply`, and the one-byte flip.
- **The module-closure half of the axiom gate is a hard constraint on this lane.**
  `Test/Audit/AxiomGate.lean:520-532,547-552` walks every `.lean` under `Test/` (outside
  `Test/fixtures/`) and fails the build if a file is not reachable from `Test.All`. Every new
  battery file must therefore be imported by `Test/All.lean` in the same change, and a battery
  that is left half-written is not merely untested — it is red.
- **`Effect4Gen` is outside the audited tree.** `belongsToAuditedTree`
  (`Test/Audit/AxiomGate.lean:369-371`) admits `Effect4`, `Test` and `Fixtures` only, and
  `auditedSources` walks `src/Effect4`, `Test` and `Fixtures` only, so importing
  `Effect4Gen.Check` into a battery subjects none of *its* declarations to the ceiling. What it
  does do is put `import Lean` in the closure — which `Test.Audit.AxiomGate` already has — and
  make `Effect4Gen.Check` a build dependency of `TestStore`.
- **`Effect4Gen.Check.main` cannot be the battery's entry point.** It calls `initSearchPath`
  and `importModules` (`tools/Effect4Gen/Check.lean:238-239`) and ends in `IO.Process.exit`
  (`:249`). Run from inside an elaborator that is already holding the whole `Effect4`
  environment, that builds a *second* environment in the same process — the shape that crashed
  this machine twice — and then kills the compiler. The per-file entry point `checkFile`
  (`:184`) is a `MetaM` action over the ambient environment and is the one that can run in a
  battery; the measurement below decides whether it is affordable.
- **`Effect4.Arch.jsonBytes` is gone with `Store/JsonCanonical.lean`**, so
  `ArchContract`'s first receipt has no referent; `Effect4.Arch.acceptsShape`
  (`src/Effect4/Schema/Accepts.lean:65`) and `Effect4.Arch.serviceJson` are unchanged.
  `Effect4.StdLib.rc112` is gone too; the store is `Effect4.StdLib.store`.

## 2026-09-05 11:36 — the measurement the landing asked for: the kernel cost is not a kernel cost

The landing and the plan both assume that stating the §6a addresses is expensive — `Store/
Genesis.lean:24-26` says "a kernel `decide` over a SHA-256 of ninety-two kilobytes is not a
receipt worth its cost", and the B section says to `#eval` them if a `#guard` does not decide in
about a minute. Measured, the assumption is false at this toolchain: **`#guard` does not reduce
in the kernel**. It elaborates `decide p` and evaluates it with the compiled evaluator, so a
SHA-256 over 92 KB is a fraction of a second.

```
lake env lean -M 3072 <scratch>\probe-genesis.lean
  #guard genesisAddress.hex = "2794d94c…2926"        2 s wall, 73 MB peak, exit 0
  the same guard with one hex digit changed          exit 1, "did not evaluate to `true`"
```

The negative control is the important half: the guard has teeth, it is not passing vacuously.
With that settled, `#eval` was not needed anywhere; a second probe printed the whole §6a table
in 4 s and every number agrees with the facts note to the byte:

| what | value | agrees with |
| --- | --- | --- |
| `Val.encode (toVal metaSchema)` | 92,462 bytes | §6a |
| `genesisAddress` = `specOf Document` | `2794d94c…020c2926` | §6a, `NOTES-C.md` 11:19 |
| `(shape Templates.Entry).document` payload | 1,270 bytes | §6a |
| `specOf Templates.Entry` | `268ee118…0dc8aa7c` | §6a |
| `(nodeOf Templates.entry).encode` | 108 bytes | §6, §6a |
| `address Templates.entry` | `1c3c9497…067272eb` | §6a |
| `specFor metaSchema = zeroDigest` | `true` | §6a |

So `NodeContract` **guards** the genesis and the §6a addresses rather than printing them, as
the B section's first branch allows. Its module build is 7.5 s in all, most of it those hashes.

## 2026-09-05 11:38 — the seven battery files

One line each, in the order they depend on each other.

- `Test/Store/Templates.lean` (new, 390 lines) — the spike's `Cas/Templates.lean` with the
  module renames, keeping `ExportKind` (all-nullary sum), `Entry` (structure, the facts note's
  §6 payload) and `Tree`/`Forest` (mutual pair) with their five items each and the tactic
  scripts in the section prose; the hand `Canonical Float64` and `Canonical Json` **dropped**
  (they are `Store/Derived/Json.lean`'s now and a second instance would be ambiguous), their
  nested-recursion receipts kept over the derived instance as `templateJson`. Namespace
  `Effect4.Store.Templates`, as in the spike, so `NodeContract` addresses `Templates.entry`
  under the name the facts note uses.
- `Test/Store/StoreContract.lean` (rewritten, 206 lines) — the tag byte of all eleven `Val`
  constructors and the head byte of each one's frame; the primitive bytes of the previous
  revision's lines 39–47 restated through the class, plus the four primitives the landing added
  (`Bytes`, `UInt8`/`UInt64`, `Int`, `Digest`); the `option`-renders-one-way block; the eleven
  `Val.decode` refusals; the §6 numbers — 74 bytes and `8fab16…61fa` for the entry, 66 bytes and
  `fa5f40…62a3` for `p42` through `Effect4.Program.Wire`; nineteen receipts.
- `Test/Store/NodeContract.lean` (new, 212 lines) — the kind table and its two round trips;
  `Content Templates.Entry := ⟨.«export»⟩`; the entry node under the stand-in spec `6a1c…cac8`
  (108 bytes, `1437a1…705b`) and the kind-6 twin `ca0785…0990`; the typed `Ref` frame and its
  two refusals; the §6a block above; the lattice stated.
- `Test/Store/WordContract.lean` (new, 230 lines) — the three outcomes and the five refusals on
  real addresses; the word, its reverse refused, `apply` run twice; the closure of a root; the
  layered read in both directions and `preload`; the outbox synced twice; `verify` green, then
  refusing the one-byte flip and the missing spec; the root plane with the stale-version
  refusal.
- `Test/Store/TraitContract.lean` (new, 126 lines) — a trait as content and its reference
  refusals; admission of a trait node; the subject's bytes and address unchanged through nine
  nodes and again after the superseding trait; `effective` at node, spec and registry, and with
  no registry; supersession through `prev`.
- `Test/Store/ProbeContract.lean` (new, 119 lines) — what the spike's `Cas/Probe.lean` guarded
  that the three above do not: the hand-seeded store in which the stand-in spec resolves
  (`fresh`, `duplicate`, the twin, `dangling`, `wrongKind`, and `verify` refusing the seed as
  `digestMismatch`), and `p42` as a `program` node at `8032…c13a` with the zero spec that every
  store refuses.
- `Test/Store/DerivedCheck.lean` (new, 68 lines) — the projection guard, in the build. See the
  next entry.

## 2026-09-05 11:40 — `DerivedCheck`: workable, with one substitution

The B section asks for `#eval` of "`Effect4Gen.Check`'s entry point". The tool's `main`
(`tools/Effect4Gen/Check.lean:225-251`) cannot be it: it calls `initSearchPath` and
`importModules` to build an environment of its own, inside a compiler that is already holding
this one — the shape that crashed this machine twice — and it ends in `IO.Process.exit`. Its
per-file entry point `checkFile` (`:184`) is a `MetaM` action over the ambient environment and
is what the battery runs, once per file, after importing exactly the modules the generated
files elaborate in. Nothing else changed.

Measured (`lake env lean -M 3072`, then the module's own build): **five files, forty-one
shapes, 10–12 s, 878 MB peak**, "ok" on every shape. Negative control: a copy of
`PinDerived.lean` with `("spanDigest"` renamed to `("spanDigestX"` is refused —

```
REFUSED …\PinDerived.lean: shape "Pin" projects no carrier in the environment
        generated: struct Pin [·(…, spanDigestX, text)]
      Effect4.Store.Pin: struct Pin [mk(…, spanDigest, text)]
```

— so the guard is real. Five files, not four: lane C's `Evidence/StdLib/Derived.lean` exists
and is checked here even though `scripts/generate-derived.ps1` still owes it a manifest row
(`NOTES-C.md`, open item 2). `Evidence/Char/Derived.lean` is deliberately **not** named: the
brief says not to, it landed while this lane was writing, and it owes the same manifest row.

Two facts that make importing a tool library into a battery safe, both checked rather than
assumed: `Test/Audit/AxiomGate.lean:369-371` audits modules under `Effect4`, `Test` and
`Fixtures` only, and `auditedSources` (`:520-532`) walks those three trees only, so nothing
under `tools/` enters either pass; and `#eval` leaves no declaration behind, so the `MetaM`
action contributes nothing to the ceiling. The second was measured, not read off the source —
see the next entry.

## 2026-09-05 11:42 — `Test/Evidence/ArchContract.lean`, and what it cost

Lane C's mapping (`NOTES-C.md`, open item 3) applied in full: `digestOf` → `Canonical.digest`
for a payload and `address` for a node; `rc112.resolve p` → `entryAt p` (no index, so no
`·.2`); `rc112.find (digestOf e)` → `store.find (address e).digest`; `rc112.size` →
`store.nodes.length` = 1,861; `rc112.under ["Fiber"]` → a filter over `names`; `Rc112.files` →
`Rc112.sources` with `(·.sha256.hex)`; `storeJson` taking the store alone; `viewStore.size` →
`Arch.viewStore.nodes.length` = 7 and `Surface.viewStore.nodes.length` = 5; the id guard
(`(viewStore.resolve ["arch","service"]).map (·.1) = some 0`) dropped, since ids retired, and
replaced by the tree's binding names and the root's kind. The `Effect4.Arch.jsonBytes` receipt
is replaced by `storeJson`, `viewStore`, `StdLib.store`, `entryAt` and `nameTree`.

Two things the old file could not say, added because the new API makes them cheap: every
entry's `source` is `address` of its own module's pinned `Source` (no address literal anywhere
in the census), and the tree's `treeResolve` agrees with the census list's `resolve`.

The entry-schema refusal moved as lane C said it would. `Entry` carries `source : Ref Source`
now, so the negative guard cannot be a hand-written object; `entryJsonWith` takes the census's
own printing of `Effect.gen` and replaces the `kind` field, and the same document accepts
`const` and `namespace_` and refuses `enum` and `namespace` — the last one is the interesting
half, because the shape reads **constructor** names, so the census TSV's spelling is not the
app face's (`NOTES-C.md`, 11:12).

Cost, and what was done about it. The first green build was **67 s**. A timing probe over the
same imports:

| block | ms |
| --- | --- |
| `accepts` on the four view documents | 30 |
| six `Codegen.Schema.generate?` | 72 |
| `Rc112.entries` forced | 2,222 |
| `names` (the 1,649-binding tree) | 1,893 |
| both `viewStore`s | 3,742 |
| `storeSources` (25 nodes) | 1,366 |
| **`StdLib.store` (1,861 nodes)** | **5,669** |
| `links` | 116 |

So the whole-store guard the landing worried about is 5.7 s, not the cost; the cost was
forcing `Rc112.entries`, `names`, `viewStore` and `store` once per `#guard`. Consolidating the
census, name-space, view and store blocks into one guard each — same claims, one forcing apiece
— took the module to **25 s**, and the whole-store guard stays, well inside the B section's
minute. It is guarded rather than stated because "1,861 = 4 + 21 + 1,835 + 1, every put
admitted and no two rows colliding" is the census's whole claim.

## 2026-09-05 11:52 — the gate

Under the lock (`LAKE.log`, nine `B` acquire/release pairs; every wait 0 s, two exit 1 while the
files were being written and the rest exit 0):

```
LEAN_NUM_THREADS=3  lake build TestStore Test.Evidence.ArchContract
11:52:46 → 11:52:48  exit 0   "Build completed successfully (94 jobs)"
```

Module times from the runs that built them: `Templates` 1.5 s, `StoreContract` 1.2 s,
`NodeContract` 7.5 s, `WordContract` 1.2 s, `TraitContract` 1.2 s, `ProbeContract` 1.0 s,
`DerivedCheck` 10 s, `ArchContract` 25 s — 49 s of lane B module time in all. The one warning
in every log is pre-existing and not this lane's: `src/Effect4/Machine/Frames.lean:1893:40`, the
unreferenced `hstack` both `NOTES-L1.md` and `NOTES-C.md` record.

**Receipts.** The gate log replays every module's receipts: **787 `#print axioms` lines — 139
with no axioms, 199 `[propext]`, 445 `[propext, Quot.sound]`, none other** (four of the 445 are
wrapped over two lines by their long generated names, the same four L1 counted). No `sorryAx`
and no `Classical.choice` anywhere in the log. Of those, this lane's eight modules contribute
the sections listed above.

**The gate's own passes, run over lane B's modules.** `lake build Test` is the coordinator's,
so the two passes of `#effect4_axiom_gate` were reproduced in a probe over exactly the eight
modules this lane owns — `info.isUnsafe`, `info.isPartial` and `collectAxioms` against
`[propext, Quot.sound]`, with the gate's own `isGeneratedSafeRecursor` exemption
(`Test/Audit/AxiomGate.lean:381-388`) applied:

```
lane B declarations: 330; outside the ceiling: 0
```

Without that exemption the eight `_unsafe_rec` companions Lean mints for the mutual
`Tree`/`Forest` block and their `DecidableEq` instances show up; the gate skips exactly those,
and there is nothing else. `#eval` in `DerivedCheck` leaves no declaration at all, which is the
half that had to be measured rather than assumed.

Every hand-written line in the eight files is at or under 100 columns. No `sorry`, `partial`,
`unsafe`, `axiom`, `native_decide`, `extern` or `implemented_by` token outside the `/-! ## Axiom
receipts -/` headings, which Lean's tokenizer consumes as module documentation and the source
trust gate therefore never sees as tokens.

## 2026-09-05 11:52 — the register and the docs

`Test/Counterexamples/REGISTER.md`: eight rows appended in the file's five-column voice,
`E4-CAS-CE-001` … `008`, all SEEDED, each naming the guard that witnesses it — one payload at
two kinds is two addresses (`NodeContract`, `entryNode`/`entryTwin`); a wrong-kind or short
`Ref` refuses at decode with no store in hand (`NodeContract`, `TraitContract`); a trait leaves
every address unchanged (`TraitContract`, and `nodeBytes_trait_free`); a duplicate put leaves
the store unchanged and the third outcome is exhibited (`WordContract`); `apply` and `sync` are
idempotent (`WordContract`); a degenerate store exhibits `conflict` and `verify` catches the
flipped byte, so reflection is never unconditional (`WordContract`); a schema node whose spec is
not the meta-schema refuses, the genesis excepted (`NodeContract`, `WordContract`); `option`
renders one way everywhere (`StoreContract`, the block added for this row).

`docs/ARCHITECTURE.md`: row 19 (the layer sketch) now reads "Store (Val, one byte codec,
Canonical, Kind, Ref, node, store, word, traits)" instead of "(canonical bytes, digest, trie)";
row 48 is rewritten for the trait — the value tree and its codec, the class and what derives
from it, kinds and typed references, the node layout with the meta-schema as the zero-spec
genesis, admission and roots, words and the layered read and `verify`, traits as annotation
nodes outside identity, the generated instances and where they live, and the census's 1,861
nodes under `stdlib/rc112`.

`Test/All.lean`: six import lines added beside `Test.Store.StoreContract` — `Templates`,
`NodeContract`, `WordContract`, `TraitContract`, `ProbeContract`, `DerivedCheck`. This is not
decoration: `Test/Audit/AxiomGate.lean:520-552` fails the build for any file under `Test/` that
the audit root does not reach, so a battery that is not imported is red, not merely unchecked.

### Open, for the coordinator

1. **`Evidence/Char/Derived.lean` is not in `DerivedCheck`**, on the brief's instruction. Lane X
   landed it after this lane started. Adding it is one line in `derivedFiles` plus the
   `import Effect4.Evidence.Char.Derived`, once `scripts/generate-derived.ps1` has its manifest
   row (`NOTES-C.md` open item 2 owes the same row for `StdLib`). Until then `-Verify` covers
   three of the five files this battery covers, and neither covers Char.
2. **`TestStore` now depends on `Effect4Gen`.** `Test/Store/DerivedCheck.lean` imports
   `Effect4Gen.Check`, so `lake build Test` builds the tool library too. That is a feature —
   the tools are type-checked by the default build now — but the coordinator should know the
   edge exists before removing the `Cas` hunk from the lakefile.
3. **`#guard` is not a kernel reduction at this pin.** Two module headers in `src/` say or imply
   that it is (`Store/Genesis.lean:24-26`, and the landing's B section). The measurement above
   is the correction; the headers are the store owner's files, not this lane's, so they are
   unchanged. Anyone deciding what a battery can afford should read this entry, not those.
4. **`ArchContract` is the slow module of `Test/Store` and `Test/Evidence`** at 25 s, all of it
   reducing the census. If that ever needs to come down, the lever is `Store.putNode`'s linear
   `find` per put (`NOTES-C.md` open item 4), not the battery.
5. **`Effect4.Store.Templates.*` and `Effect4.Store.templateJson` are declared from a battery
   into the library's namespace**, as the spike did. Nothing in `src/` carries those names and
   nothing collides today; if the generator ever grows a bare-parameter rule and the templates
   retire, they go with it.

## 2026-09-05 11:53 — close

State at close: the five modified and six new files listed above and nothing else of this
lane's; `LAKE.lock` absent; `LAKE.log` carrying nine `B` acquire/release pairs; no
`lean.exe`/`lake.exe` running; nothing killed, and no run near the watchdog (peak 898 MB against
a 3 GB cap, longest single run 68 s against a 900 s cap). `git` was never invoked beyond
`status`. `git status` also shows lanes U's, X's and C's files and the untracked
`.coordination-append.md`; none are this lane's.
