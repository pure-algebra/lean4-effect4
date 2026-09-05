# The landing — the CAS trait into `src/`, one commit

Written 2026-09-05 ~01:05 by the coordinator. Step 2 of `docs/research/2026-09-04-cas-trait-plan.md`
§8. The spike (`workshop/Cas/`, frozen, snapshot branch `spike/cas-trait`) is the source of
every module below; nothing is redesigned here. `BRIEF.md`'s rules hold for every lane (PowerShell
only; no `git`; never edit `lakefile.toml`, `Test/Audit/AxiomGate.lean`, `COORDINATION.md`; the
axiom ceiling; `set_option autoImplicit false`; house-voice doc comments; dated notes).

## The one lake, by lock

Several lanes run at once and each needs targeted builds, so the one-lake rule is enforced by a
lock file, `workshop/Cas/LAKE.lock`:

```powershell
# acquire (retry every 30 s, give up after 30 min and write it in your notes)
New-Item -ItemType File -Path workshop\Cas\LAKE.lock -ErrorAction Stop | Out-Null   # fails if held
try   { $env:LEAN_NUM_THREADS = '3'; lake build <exactly your own modules> 2>&1 | Tee-Object -FilePath <your log> }
finally { Remove-Item workshop\Cas\LAKE.lock -Force }
```

**Why `LEAN_NUM_THREADS` (added 2026-09-05 10:55, after the second memory crash).** This lake
has no `-j` flag; it schedules its build jobs on the Lean runtime's thread pool, whose size is
the machine's 16 logical cores unless `LEAN_NUM_THREADS` says otherwise. Measured on four leaf
modules: unset → 3 `lean.exe` at once; `=1` → 1. The variable is inherited by every child
compiler too, so `3` is the balance on this 15.6 GB machine with ~8 GB free at idle: at most
three compilers, each under the lakefile's `-M6144`. Probes are `lake env lean -M 3072`, one at
a time per lane. Never run any other `lake` (in this or another repository) while a lane
builds; the crash at 10:25 was a sibling repository's uncapped, unthrottled build beside the
editor's servers and two lanes' probes, not a locked build.

Build **only your own modules** (`lake build Effect4.Surface.Entity …`); their imports are built
on the way. Never `lake build Effect4` or `Test` — those are the coordinator's gate. `lake env
lean -M 4096 <file>` needs no lock (it writes nothing) but only sees oleans somebody built.
Kill any `lean.exe` past ten minutes or 5 GB and say so in your notes. Write the lock's holder
and time in `workshop/Cas/LAKE.log` on acquire and release, one line each.

## Layout after the landing

| from (spike) | to (tree) | module |
| --- | --- | --- |
| `Cas/Digits.lean` | `src/Effect4/Store/Digits.lean` | `Effect4.Store.Digits` |
| `Cas/Utf8.lean` | `src/Effect4/Store/Utf8.lean` | `Effect4.Store.Utf8` |
| `Cas/Val.lean` | `src/Effect4/Store/Val.lean` | `Effect4.Store.Val` |
| `Cas/Digest.lean` | `src/Effect4/Store/Digest.lean` (replaces) | `Effect4.Store.Digest` |
| `Cas/Kind.lean` | `src/Effect4/Store/Kind.lean` | `Effect4.Store.Kind` |
| `Cas/Shape.lean` | `src/Effect4/Store/Shape.lean` | `Effect4.Store.Shape` (its `highestBit`/`binary64OfNat`/`Json.ofNat` copies deleted in favour of `Effect4.Data.JsonNumber`) |
| `Cas/Canonical.lean` | `src/Effect4/Store/Canonical.lean` (replaces) | `Effect4.Store.Canonical` |
| `Cas/Node.lean`, `Store.lean`, `Word.lean`, `Traits.lean` | `src/Effect4/Store/{Node,Store,Word,Traits}.lean` (`Store.lean` replaces) | `Effect4.Store.{Node,Store,Word,Traits}` |
| `Cas/Genesis.lean` | `src/Effect4/Store/Genesis.lean` | `Effect4.Store.Genesis` (`Content Document`; the `Templates.Entry` instance and its `#eval`s go to the battery) |
| `Gen-out/Json.lean` (regenerated) | `src/Effect4/Store/Derived/Json.lean` | `Effect4.Store.Derived.Json` |
| `Gen-out/Schema.lean` (regenerated) | `src/Effect4/Store/Derived/Schema.lean` | `Effect4.Store.Derived.Schema` |
| `Gen-out/Program.lean` (regenerated) | `src/Effect4/Program/Derived.lean` | `Effect4.Program.Derived` (it imports `Program.Native`, so it lives with the program, not under the store) |
| `gen/Main.lean`, `gen/Check.lean` | `tools/Effect4Gen/{Main,Check}.lean` | `Effect4Gen.{Main,Check}` (lake library `Effect4Gen`, declared by the coordinator) |
| `tools/generate-derived.ps1` | `scripts/generate-derived.ps1` | paths and imports moved; `-Verify` = `git diff --exit-code` on the derived files |
| `Cas/Templates.lean`, `Cas/Probe.lean`, `Cas/Program.lean` | `Test/Store/Templates.lean`, `Test/Store/ProbeContract.lean`; `Program.lean` retired (the derived module is the instance; its oracle role ends) | batteries |
| new | `src/Effect4/Data/JsonNumber.lean` | `Effect4.Data.JsonNumber`: `highestBit`, `binary64OfNat`, `Json.ofNat` moved verbatim from `Store/JsonCanonical.lean:61-81`, **namespace `Effect4.Arch` kept** (Codegen/JsonSchema, Ingest/JsonSchema, Surface/{Entity,Api,Deploy}, Views, Entry, Char address them as `Arch.…`) |
| deleted | `src/Effect4/Store/JsonCanonical.lean`, `src/Effect4/Store/Trie.lean` | — |
| per area | `src/Effect4/Evidence/StdLib/Derived.lean`, `src/Effect4/Evidence/Char/Derived.lean`, `src/Effect4/Store/PinDerived.lean` | derived instances live beside their carriers, so the store never imports an area above it |

Generated files are regenerated at their landing paths with landing imports by
`Effect4Gen.Main`; the oracle guards (which called the hand `Cas.Program`) are replaced by the
golden and reader guards only (the corpus hex under `ocaml/goldens/eff/*.hex`; a byte appended
or dropped refused; a leading-zero index refused).

`Effect4Gen.Main` gains one option in lane L1: `--kind <Type>=<kind>` emits `instance : Content
<Type> := ⟨.<kind>⟩` right after that type's `Canonical` instance, because a typed reference
field (`source : Ref Source`) needs the target's `Content` before the referring type's instance
can be derived. Types are emitted in the order given, so a group lists its targets first.

## Lanes, in order

### L1 — the substrate into `src/` (Fable; alone; first)

Owns: everything in the layout table except the three per-area derived files and the
batteries; plus `src/Effect4/Program/Wire.lean`, `src/Effect4.lean`'s import block for the
store, `src/OCaml5/Eff/Goldens.lean` if its `import Effect4.Store.Canonical` needs a name.

1. Copy (never move; the spike stays frozen) the modules to their paths; rename every `import
   Cas.X` to the new module names; delete the two modules; write `Data/JsonNumber.lean`;
   in `Store/Shape.lean` import it and drop the three copies.
2. `Store/Pin.lean`: keep the carrier and the two pin theorems; delete `Pin.json`, `Pin.address`,
   `Pin.contentPath`, `address_congr` and the `open Effect4.Arch`; `spanDigest : Digest` stands.
   `Store/PinDerived.lean`: the generated `Canonical Pin` with `--kind Pin=source`.
3. `Program/Wire.lean`: keep the header prose (rewritten for the new layer), `Corpus`, and the
   guards; `encodeProgram := Canonical.encode`, `decodeProgram := Canonical.decode`, the two
   laws as theorems from the class (`decode_encode` under `(toVal p).WF`, `decode_exact`), the
   byte codec gone (it is `Store/Val.lean`). `Api.bytesOf`/`ofBytes` keep their text.
4. Regenerate `Derived/Json`, `Derived/Schema`, `Program/Derived` at their paths with landing
   imports and golden-only guards; `Store/Genesis.lean` without the template entry.
5. `src/Effect4.lean`: the store import block becomes the new modules in dependency order
   (`Digits, Utf8, Val, Digest, Kind, Shape, Canonical, Node, Store, Word, Traits, Derived.Json,
   Derived.Schema, Genesis, Pin, PinDerived`); `Program.Derived` before `Program.Wire`; the
   `JsonCanonical` and `Trie` lines gone; the header comments rewritten for what is there.
6. Gate (under the lock): `lake build Effect4.Store.Genesis Effect4.Store.PinDerived
   Effect4.Program.Wire Effect4Gen` green at the ceiling; receipts sections present; the corpus
   guards pass. Report in `workshop/Cas/NOTES-L1.md`, final `REPORT-L1.md` (if the harness
   refuses the file, put it in the closing message).

From here until lane B finishes, `lake build Effect4` is red by design; the coordinator's
snapshot branch is the safety net.

### U — the Surface library (Opus; after L1; with X)

Owns `src/Effect4/Surface/{Annotate,Entity,Api,Agent,Deploy,Site,Observability}.lean`.
Delete the six hand `Canonical` instances (nothing consumes them; the census of 2026-09-04
found no `digestOf` on a Surface carrier outside their own modules). `import
Effect4.Store.JsonCanonical` → `Effect4.Data.JsonNumber` where the file uses `Arch.Json.ofNat`;
`Annotate.lean`: `some ⟨digestBytes⟩` becomes `Digest.ofBytes? digestBytes` (the length is a
field now), `import Effect4.Store.Digest` stands; `Observability.lean`: its `hexOfBytes`/
`bytesOfHex` replaced by the store's (`Effect4.Store.hexOfBytes : Bytes → List Char`,
`bytesOfHex : List Char → Option Bytes`), guards kept. Gate: `lake build Effect4.Surface.Site
Effect4.Surface.Observability Effect4.Surface.Deploy Effect4.Surface.Api Effect4.Surface.Agent`
plus `Effect4.Codegen.JsonSchema Effect4.Ingest.JsonSchema Effect4.Codegen.App` (they reach the
helpers through you). Notes `NOTES-U.md`.

### X — the Char room (Opus; after L1; with U)

Owns `src/Effect4/Evidence/Char/**` and `src/Effect4/Evidence/Char/Derived.lean`. Order inside
the room: `Evidence` → `Manifest` → `Conformance/{GSet,Vector,VectorSet,Consume,Surface,Cell}`
→ `Derived` → the rest. Retypings (facts note §5 Q4, plan §5): `Evidence.pin (span : Ref Pin)
(guard : String)`; `Evidence.fixture (vector : Ref Vector…) (receipt : Ref Receipt)` — where a
`Ref` needs a type parameter the room cannot name at that point, use `AnyRef` with the kind and
say so; `Evidence.thm … (statement : Digest)`, `Evidence.decided … (statement : Digest)`;
`Claim.evidence : List (Ref Evidence)`; `Target.model : Ref Manifest`, `Target.implementation :
Ref Implementation`; `Receipt.vector : Ref …`, `Receipt.pin : Ref Implementation`;
`Characterized.{target, vectors, receipts}` typed. Kinds: `Manifest` → `component`;
`Implementation` → `source`; `Receipt`, `Claim`, `Evidence`, `Target`, `Characterized` →
`annotation`; `VectorSet`, `Vector`, `Fact` → `vector`. Delete the fourteen tuple instances,
the `json`-as-identity functions (`Manifest.json`, `Evidence.json`, `Claim.json` stay only if a
consumer reads that exact JSON — say which), `Implementation.addr`/`Target.addr`/`Receipt.addr`/
`Vector.addr`/`Manifest.address`/`Evidence.address`/`Claim.address`/`VectorSet.address` in favour
of `address`; `Canonical Digest` and `Canonical (Failure String)` leave `Consume.lean` (`Digest`
is the store's; `Failure` is generated). Generic carriers (`GSet α`, `ClientReading C`, `Fact L
C`, `Vector L C`, `VectorSet L C`, `Provenance`'s companions) get **hand** instances on S1's
`Prod`/`List` templates (`Test/Store/Templates.lean` after L1; `workshop/Cas/Cas/Canonical.lean:
445-560` now) with the three laws, because `Effect4Gen` does not yet take a bare parameter;
everything monomorphic is generated into `Derived.lean` with `--kind`. The Queue room
(`Queue/*.lean`) changes only where it names an address. Gate: `lake build
Effect4.Evidence.Char.Conformance Effect4.Evidence.Char.Queue.Mutants
Effect4.Evidence.Char.Queue.Grade Effect4.Evidence.Char.Derived`. Notes `NOTES-X.md`.

### C — the census and the views (Opus; after U)

Owns `src/Effect4/Evidence/StdLib/{Entry,Rc112,Links,Derived}.lean`,
`scripts/generate-stdlib-census.ps1`, `src/Effect4/Evidence/Views.lean`,
`src/Effect4/Evidence/SurfaceViews.lean`. `FilePin` → `Source {module, file, sha256 : Digest}`
with `--kind Source=source`; `Entry` gains `source : Ref Source`, and the census file keeps
names only: `Rc112.lean` lists `sources : List Source` (thirty-ish, each digest a `Digest.ofHex?`
literal with its `by decide` proof, or a `Digest.ofHexLit` helper you add to `Store/Digest.lean`
— say which) and `rawEntries : List (String × String × ExportKind × Nat)`; `entries` is the
map that fills `source := address (the module's source)`, computed at elaboration through a
thirty-row table so no address literal is ever written. Regenerate the file with the script.
`StdLib.store : Store` = the genesis, the entry document as a schema node, the sources, the
entries, one `tree` node of `module/name → Ref Entry`, the root `stdlib/rc112` (root kind
`stdlib`), built by `putNode` in that order; state it, do not `#guard` it (lane B measures the
kernel cost of the 1,835 hashes plus the 92 KB genesis before deciding what the battery
reduces). `Views.storeJson`/`storeDoc`: nodes by hex address, kind and spec, roots by name; ids
gone. Both `viewStore`s: documents as schema nodes under the genesis, a `tree` per family, a
root each. Gate: `lake build Effect4.Evidence.StdLib.Links Effect4.Evidence.SurfaceViews
Effect4.Evidence.StdLib.Derived`. Notes `NOTES-C.md`.

### B — batteries, register, docs (Opus; last)

Owns `Test/Store/{StoreContract,NodeContract,WordContract,TraitContract,Templates,ProbeContract,
DerivedCheck}.lean`, `Test/Evidence/ArchContract.lean`, `Test/All.lean` (the new imports),
`Test/Counterexamples/REGISTER.md` (rows `E4-CAS-CE-001..008`, plan §7), `docs/ARCHITECTURE.md`
(rows 19 and 48 rewritten for the new store). `StoreContract` restates the tag bytes and the
refusals; `NodeContract` the §6a numbers (`2794d9…2926`, `268ee1…aa7c`, `1c3c94…72eb`) as
guards **if** the kernel hashes the 92 KB genesis in under a minute (measure with one `#guard`
first; else `#eval` them and guard the small nodes); `WordContract`, `TraitContract` from
`Cas/Probe.lean`; `DerivedCheck` runs `Effect4Gen.Check` over the four derived files and
refuses a difference. `ArchContract`: `digestOf` → `Canonical.digest`, `rc112.find (digestOf …)`
→ the new store's `find (address …)`. Gate: `lake build Test` (under the lock; the
coordinator's `lake build Effect4 Test` follows). Notes `NOTES-B.md`.

### The coordinator

Before L1: the `Effect4Gen` library in the lakefile. After B: `lake build Effect4 Test` with
nothing else running and the Lean language server closed; the receipts read; the `Cas` hunk
removed; `COORDINATION.md` updated; one commit by pathspec of every file the lanes list in
their reports; the snapshot branch deleted; the Mac told.
