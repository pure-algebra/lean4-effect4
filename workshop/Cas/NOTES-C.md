# Lane C notes — the census and the views

Running notes of lane C (`workshop/Cas/LANDING.md`, "C — the census and the views"). One dated
entry per milestone: what changed, what it cost, what is open. Times are the machine clock
(`Get-Date`).

## 2026-09-05 11:05 — start; the census before the first edit

Read in the given order: `LANDING.md` ("The one lake, by lock" with the `LEAN_NUM_THREADS`
paragraph, "Layout after the landing", the C section), `BRIEF.md`, the facts note §5 (Q3, Q4,
Q7) and §6a, `NOTES-L1.md`, `NOTES-U.md`, `REPORT-S2.md`; then
`src/Effect4/Store/{Canonical,Digest,Node,Store,Kind,Genesis}.lean`,
`src/Effect4/Store/PinDerived.lean` (the `--kind` model), `scripts/generate-derived.ps1`,
`tools/Effect4Gen/Main.lean:940-1030` (the emitted file's frame), and the four files this lane
owns plus `Test/Evidence/ArchContract.lean` (lane B's, read to know what it asks of this API).

Machine at start: no `lean.exe`/`lake.exe`; no `LAKE.lock`; `LAKE.log` ends with lane X's
release at 11:02:54. `git status` shows lane U's seven Surface files and lane X's Char files;
none of this lane's.

What the census found, beyond the landing's list:

- **There is no tree carrier.** `Store/Kind.lean:45` reserves the byte (`tree` = 11, "a name
  space: name → reference pairs") and `Store/Store.lean:608-613` guards nodes at that kind by
  hand, but no Lean type carries the payload, and `putNode`'s typed face (`Store.put`) needs a
  `Content` instance. Lane C owns no file under `src/Effect4/Store/`, so the carrier is declared
  in `src/Effect4/Evidence/StdLib/Entry.lean` **under the store's own namespace**
  (`Effect4.Store.Tree`) and generated in this lane's derived file. Naming it in the store's
  namespace is deliberate: when the store's owner moves the four lines to `Store/Node.lean`
  beside `AnyRef`, no consumer changes — only the generator manifest row moves.
- **Admission wants three schema nodes, not one.** The landing lists "the entry document as a
  schema node"; `Store.putNode` resolves edge 0 (the spec) for every non-genesis node
  (`Store/Node.lean:296-306`, `Store/Store.lean:199-201`), so a `Source` node needs
  `specOf Source` resident and a `Tree` node needs `specOf Tree`. The store therefore puts the
  documents of `Source`, `Entry` and `Tree` under the genesis before any content of those kinds.
- **`Store.Path` is gone with the trie.** `Link.path`, `Entry.path`, `rc112.resolve/under/size`
  and `SurfaceViews`' `Store.Path` all named it. Names live in the tree now, so a census path
  `[module, name]` is spelled `module/name` in the tree and `pathName` is the one joiner.
- **`Arch.Document.toJson?` is this lane's to re-home**, as `NOTES-U.md` item 1 says; it lands
  in `Evidence/Views.lean` over `Codegen.Schema.documentExpr`, with `import
  Effect4.Codegen.Schema` (no cycle: `Codegen/Schema.lean` imports only `Schema.Authoring` and
  `TypeScript`).
- **The import direction between `Views.lean` and `StdLib/Entry.lean` inverts.** Today
  `Entry.lean` imports `Views.lean` for `Schema.Authoring` and `Arch.Json.ofNat`; with the trait
  the entry's document is `Canonical.document Entry` and needs neither, while `Views.lean` needs
  the tree carrier and its instance. So `Entry.lean` imports `Effect4.Store.Genesis` and
  `Views.lean` imports `Effect4.Evidence.StdLib.Derived`. Nothing outside this lane imports
  `StdLib.Entry` or `Views` except `src/Effect4.lean:90-92` and `Test/Evidence/ArchContract.lean`
  (lane B's), so the inversion is invisible to them.

## 2026-09-05 11:12 — the carriers and the generated instances

`src/Effect4/Evidence/StdLib/Entry.lean`, rewritten. `ExportKind` unchanged (six nullary cases).
`FilePin` → `Source {module, file, sha256 : Digest}`; `Entry` gains `source : Ref Source` and
loses nothing. Both drop `deriving Inhabited` (there is no `Inhabited Digest`, and none is
wanted: a default address is a lie). Gone with the trie: `Entry.path : Path`, the hand
`Canonical Entry` over the tuple `(module, name, kind.spelling, line)`, the hand-authored
`entryDoc`, `Entry.json`, `FilePin.json`, `store (entries : List Entry)`. Added: `pathName`
(the one `[module, name] ↦ "module/name"` joiner), `Entry.pathName`, `digestOfHex`, and — under
`namespace Effect4.Store`, for the reasons in the 11:05 entry — `Tree`, `putOr` and
`putRootOr`.

The digest literals: **the total helper, not `by decide`**. `digestOfHex hex :=
(Digest.ofHex? hex).getD zeroDigest` in `Effect4.StdLib`, and the generated census carries
`#guard rawSources.all fun row => (Digest.ofHex? row.2.2).isSome` plus `#guard sources.all fun
source => source.sha256 ≠ zeroDigest`, so a mistyped literal refuses the module. The landing's
other offer — a `Digest.ofHex?` literal with a `by decide` beside each of the twenty-one rows —
was refused because `Store/Digest.lean` is not this lane's file (`Digest.ofHexLit` cannot be
added there) and because twenty-one kernel evaluations of the hex reader buy nothing the guard
does not already refuse.

`src/Effect4/Evidence/StdLib/Derived.lean` (new, generated, 315 lines), by

```
lake env lean -M 3072 --run tools\Effect4Gen\Main.lean --group StdLib
  --imports Effect4.Evidence.StdLib.Entry --out src\Effect4\Evidence\StdLib\Derived.lean
  --kind Effect4.StdLib.Source=source --kind Effect4.StdLib.Entry=export
  --kind Effect4.Store.Tree=tree
  Effect4.StdLib.ExportKind Effect4.StdLib.Source Effect4.StdLib.Entry Effect4.Store.Tree
```

34 s, peak `lean.exe` 992 MB, 23 receipts, no repair by hand. The generator took `Ref Source`
and `List (String × AnyRef)` as field types through their own instances, exactly as it took
`Digest` in the Pin group; `--kind` emitted the three `Content` instances. Re-running it after
the doc-comment edits reproduced the file byte for byte (6 s).

One consequence to record: the document a shape renders reads the **constructor** names off the
inductive, so `ExportKind` crosses the app face as `class_` and `namespace_`, not as `class` and
`namespace`. `ExportKind.spelling` stays the census TSV's column and says so in its doc comment.
The printer follows the same table, so `accepts entryDoc (Entry.json e)` is still the honest
receipt — the alphabet on both sides moved together.

## 2026-09-05 11:14 — the census script and `Rc112.lean`

`scripts/generate-stdlib-census.ps1`: the TSV half is untouched (same 21 modules, same
1,835 rows, same file). The Lean half now emits `import Effect4.Evidence.StdLib.Derived`,
`set_option autoImplicit false`, `open Effect4.Store`, and:

- `rawSources : List (String × String × String)` — module, path, hex — and
  `sources : List Source := rawSources.map fun row => ⟨row.1, row.2.1, digestOfHex row.2.2⟩`;
- `sourceAddresses : List (String × Ref Source) := sources.map fun s => (s.module, address s)`,
  the twenty-one-row table;
- `rawChunk0 … rawChunk9 : List (String × String × ExportKind × Nat)` (two hundred rows each)
  and `rawEntries` their concatenation;
- `entries : List Entry`, which reads the table **once** (`let table := sourceAddresses` above
  the `map`, so the twenty-one hashes are twenty-one, not one per row) and fills
  `source := address (the module's source)`. No address literal is written anywhere;
- `count`, five `#guard`s (row counts, every hex literal readable, every module of a row having
  a pinned file, no source digest zero) and five receipts.

Regenerated: `pwsh -File scripts\generate-stdlib-census.ps1` — 21 modules, 1,835 rows, the TSV
unchanged, `Rc112.lean` 1,958 lines. `lake env lean -M 3072` on it: 6 s, 563 MB, five receipts
(`rawSources` none, `sources` `[propext]`, the other three `[propext, Quot.sound]`), every
`#guard` passing. A second run reproduced both files byte for byte.

## 2026-09-05 11:17 — `Links.lean`: the store, the name space, the links

`src/Effect4/Evidence/StdLib/Links.lean`. New above the links: `sourceDoc`, `entryDoc`,
`treeDoc` (each `Canonical.document _`) and `Source.json`, `Entry.json` (each
`Canonical.print`) — they live here, not beside the carriers, because their instances are in
the generated module between the two. Then `bind`/`bindings`/`nameTree`, the store, and the
readers.

`StdLib.store : Store`, children-first, each step `putOr`:

| # | what | nodes after |
| --- | --- | --- |
| 1 | `metaSchema` — the genesis, kind `schema`, zero spec | 1 |
| 2 | `sourceDoc` as a schema node under the genesis | 2 |
| 3 | `entryDoc` | 3 |
| 4 | `treeDoc` | 4 (`storeSchemas`) |
| 5 | the twenty-one `Source`s, spec `specOf Source` | 25 (`storeSources`) |
| 6 | the 1,835 `Entry`s, spec `specOf Entry`, each with a `ref` edge at kind `source` | 1,860 |
| 7 | `nameTree`, spec `specOf Tree`, 1,649 `ref` edges at kind `export` | 1,861 |
| 8 | `putRootOr` the root `stdlib/rc112`, plane `stdlib`, kind `tree`, version 1 | — |

**Departure from the landing's list, and why.** The landing names "the entry document as a
schema node"; three documents go in, not one. `Store.putNode` resolves edge 0 — the spec — for
every node that is not the genesis (`Store/Node.lean:296-306`, `Store/Store.lean:199-201`), so a
`Source` node is `dangling (specOf Source)` unless `sourceDoc`'s node is already resident, and
the same for the tree. Steps 2 and 4 are that requirement, not a widening of the store.

The name space: `bindings` folds `bind` over the census, keeping one binding per distinct
`module/name` at the position of its first row and the address of its last. That is what the
retired trie's repeated `putAt` left under a path, and it is why `Effect.gen` — a `const` at
line 1947 and a `declare namespace` later — binds to the namespace. 1,649 bindings for 1,835
rows.

Readers: `entryAt : List String → Option Entry` (the last row with that path, off the census
list — cheap, it hashes only the twenty-one file addresses), `resolve := (entryAt ·).map
address`, `treeResolve` (the same question asked of the tree node's bindings, which is what a
reader holding only the store would do), `names`. `Link` keeps `path : List String` — now the
census spelling, no longer a store path — so `Link.checked` and `semanticsOf` keep their
signatures and their thirty-six rows verbatim; only `rc112.resolve` became `entryAt`.
`rc112 : Store Entry` is gone; the store is `StdLib.store`.

Fifteen `#guard`s, all on the reading side. `store` is stated and not guarded, as the landing
asks; `storeSchemas` and `storeSources` are exported so lane B can measure prefixes instead of
the whole thing.

## 2026-09-05 11:19 — `Views.lean` and `SurfaceViews.lean`

`src/Effect4/Evidence/Views.lean`. Imports: `Store.JsonCanonical` and `Store.Store` out,
`Effect4.Evidence.StdLib.Derived` and `Effect4.Codegen.Schema` in; `set_option autoImplicit
false` added (the file had none). `Arch.Document.toJson?` re-homed here as the one line
`Codegen.Schema.reifyJson? (Codegen.Schema.documentExpr document)`, per `NOTES-U.md` item 1.
`serviceDoc`/`layerDoc`/`requirementDoc` and their projections are untouched.

`storeDoc`/`storeJson` rewritten for the heterogeneous store: `nodes` as `{address, kind,
spec}` — hex, kind name, hex — and `roots` as `{name, plane, kind, address, version}`; ids
gone, and so is the `value : α → Json` projection the old view took, because a payload is only
readable through the spec its node cites and that is the reader's business, not the view's.

Both `viewStore`s follow the census's shape: the genesis, `Canonical.document Tree`, each view
as a schema node under the genesis, one `tree` node per family, one root — `arch/views` and
`surface/views`, both at root kind `schema`, kind `tree`, version 1. The two `putAt` folds are
gone. `views` is now `List (String × Document)` with names `arch/service`, `arch/layers`,
`arch/requirement`, `arch/store` and `surface/entity`, `surface/domain`; `viewPaths` became
`viewNames`, and `views_nodup_paths`/`views_paths` became `views_nodup_names`/`views_names`
(both still `by decide`/`rfl`, no axioms).

## 2026-09-05 11:19 — the gate, and the numbers for lane B

Under the lock (`LAKE.log`, five acquire/release pairs for this lane, all `waited 0 s`;
lane X waited 30 s once behind the last one):

```
LEAN_NUM_THREADS=3  lake build Effect4.Evidence.StdLib.Links Effect4.Evidence.StdLib.Derived
  Effect4.Evidence.SurfaceViews Effect4.Evidence.Views
11:19:14 → 11:19:29  exit 0 (16 s)   "Build completed successfully (76 jobs)"
```

Built in the run: `StdLib.Entry` 1.0 s, `StdLib.Derived` 1.1 s, `SurfaceViews` 4.6 s, `Views`
4.6 s, `StdLib.Rc112` 4.7 s, `StdLib.Links` 8.5 s. No errors. The one warning in the log is
pre-existing and not this lane's: `src/Effect4/Machine/Frames.lean:1893:40`, an unreferenced
`hstack`, replayed from that module's cached build — the same line `NOTES-L1.md` records.

Receipts, 77 over the six modules — `Derived` 23, `Links` 18, `Views` 18, `Entry` 7,
`SurfaceViews` 6, `Rc112` 5 — of which 26 have no axioms, 11 are `[propext]` and 40 are
`[propext, Quot.sound]`. Nothing else: no `sorryAx`, no `Classical.choice` anywhere in the gate
log, and no `sorry`, `partial`, `unsafe`, `native_decide`, `axiom`, `extern` or
`implemented_by` token in any of the six files. Every hand-written line is at or under 100
columns; the sixteen over it are in the two generated files (`Derived` 7 — lane G's known
emitted-width item — and `Rc112` 8 long data rows, as before this landing).

**The measurements lane B asked for** (`lake env lean -M 3072` on a scratch probe, one run,
peak 471 MB / 458 MB, no watchdog trip):

| what | interpreter |
| --- | --- |
| `storeSchemas.nodes.length` = 4, all kind `schema` | with the rest of the cheap probe, 22 s total |
| `storeSources.nodes.length` = 25 | " |
| `Arch.viewStore` 7 nodes, root `arch/views` | " |
| `Surface.viewStore` 5 nodes, root `surface/views` (`tree`, plane `schema`) | " |
| `nameTree.bindings.length` = 1,649 | " |
| **`store.nodes.length` = 1,861**, one root `("stdlib/rc112", "stdlib", "tree", 1)`, the tree node found at its address with 1,649 references | **38 s** |

1,861 = 4 + 21 + 1,835 + 1: every put was admitted and no two entries collided, so the census
store holds one node per row exactly as the retired `rc112.size = Rc112.count` said.

The addresses this landing fixes under version byte 0:

| what | address |
| --- | --- |
| `genesisAddress` | `2794d94c40e85c5643ebc081a54eed287da0e746537f4f8ecfd4efc3020c2926` |
| `specOf Source` | `56304bf5f5d5b7e92d4acc34bd16f1c1be65ecd81194c2fb0375988734fb5ee2` |
| `specOf Entry` | `36d78745f1e4811bd22920cfc437fe0c99f533e8bef354b369ce7a3610a6e9c3` |
| `specOf Tree` | `0ad654f49550e0145c2b012c132fde2b038f0aa0d6aa27b574f3b55bc80f1bd7` |
| `address` of the `Ref` module's `Source` | `aa0c01ba07128294cc81cc61862111adde3f197b5dcc55ecb5ace0628d66e610` |
| `address (entryAt ["Ref","get"])` | `25f5e70291825552e994015a829b65f4d3c6534e882ee4f2496461c03d37ab04` |
| `store.root? "stdlib/rc112"` = `address nameTree` | `57abb48e3c64737a2c1a482473a6f0ae5de294061add474b9a440186a076a5b8` |

The genesis address agrees with the facts note §6a to the byte, which is the cross-check that
this lane changed nothing below it.

### Open, for the coordinator and the later lanes

1. **`Store.Tree`, `Store.putOr` and `Store.putRootOr` are squatting.** They are declared in
   `src/Effect4/Evidence/StdLib/Entry.lean` under `namespace Effect4.Store` because lane C owns
   no file under `src/Effect4/Store/`. `Tree` belongs beside `AnyRef` in `Store/Node.lean`; the
   two combinators belong at the foot of `Store/Store.lean`. Moving all three changes no
   consumer — only the generator group that emits `Canonical Tree` moves out of the StdLib row.
2. **`scripts/generate-derived.ps1` owes a manifest row**, which this lane may not add. The row,
   after the `Pin` one and in dependency order (it reads `Effect4.Store.Genesis` through
   `StdLib.Entry`):

   ```powershell
   [pscustomobject]@{
     Name    = 'StdLib'
     Imports = 'Effect4.Evidence.StdLib.Entry'
     Out     = 'src\Effect4\Evidence\StdLib\Derived.lean'
     Guards  = ''
     Kinds   = @('Effect4.StdLib.Source=source', 'Effect4.StdLib.Entry=export',
                 'Effect4.Store.Tree=tree')
     Types   = @('Effect4.StdLib.ExportKind', 'Effect4.StdLib.Source', 'Effect4.StdLib.Entry',
                 'Effect4.Store.Tree')
   }
   ```

   Until it is there, `-Verify` does not see this file and `Test/Store/DerivedCheck.lean` (lane
   B) will run the projection guard over four files, not five. No acceptance guards are appended
   (`Guards = ''`): the laws are exercised by `Links.lean`'s and `Rc112.lean`'s `#guard`s over
   the real census, which is a stronger battery than a sample would be. Lane X's
   `Evidence/Char/Derived.lean` wants a row of the same shape.
3. **`Test/Evidence/ArchContract.lean` (lane B) needs more than the landing's two lines.** The
   old-store API it reads is gone. The mapping, one line each:
   `digestOf x` → `Canonical.digest x` (payload) or `address x` (node);
   `rc112.resolve p` → `entryAt p` (`Option Entry`, no index — drop the `·.2`);
   `rc112.find (digestOf e)` → `store.find (address e).digest`, or `store.get (address e)` for
   the typed read;
   `rc112.size` → `store.nodes.length`, which is 1,861 (4 schema nodes + 21 sources + 1,835
   entries + 1 tree), not 1,835 — the schema nodes and the tree are nodes too;
   `rc112.under ["Fiber"]` → `names.filter fun n => n.startsWith "Fiber/"` (1,649 names in all);
   `viewStore.size` → `Arch.viewStore.nodes.length` = 7, `Surface.viewStore.nodes.length` = 5;
   `(viewStore.resolve ["arch","service"]).map (·.1)` → `Arch.viewTree.bindings.head?` or
   `treeResolve`-style lookup by the name `"arch/service"` — ids are gone, so nothing answers
   `some 0` any more;
   `Rc112.files` → `Rc112.sources`, and `(·.sha256)` is a `Digest`, so the vendored-pin guards
   read `.map (·.sha256.hex)`;
   `storeJson (fun s => .str s) ((Store.empty : Store String).putAt …)` → `storeJson` takes the
   store alone now, and `Views.lean` already guards it on the empty store and on a one-root
   store;
   `accepts entryDoc (Entry.json e)` still stands, with `entryDoc = Canonical.document Entry`
   and `Entry.json = Canonical.print` — but the kind literal in the negative guard moves from
   `"enum"` to any string outside `{const, function, class_, interface, type, namespace_}`.
4. **Kernel cost, the question the landing left to lane B.** In the interpreter the whole census
   store is 38 s and 458 MB; `storeSchemas` (four nodes, one of them the ninety-two-kilobyte
   meta-schema) is a small fraction of a 22 s probe that also built `nameTree`. Nothing in
   `src/` reduces any of it — no `#guard` in this lane's six files touches `store`,
   `storeSchemas`, `storeSources` or either `viewStore`. If the battery wants a receipt, the
   cheap end is `storeSchemas.nodes.length = 4` and `Arch.viewStore.nodes.length = 7`; the
   expensive end is the 1,861-node fold, whose `putNode` does a linear `find` per put and is
   therefore quadratic in the census.
5. **`Effect4.Evidence.StdLib.Derived` is not named in `src/Effect4.lean`.** It is reached
   transitively (`:91-92` import `StdLib.Entry` and `StdLib.Rc112`, and `Rc112` imports it), so
   nothing is red; the coordinator may want the line anyway, beside the other derived modules.
   `src/Effect4.lean` is not this lane's file.
6. **The `Views.lean` ↔ `StdLib/Entry.lean` import direction inverted** (11:05 entry). Any lane
   that adds `import Effect4.Evidence.Views` to something below `StdLib/Entry.lean` will make a
   cycle; the base of this family is now `StdLib/Entry.lean` over `Store.Genesis`.
7. **§6a is untouched by this lane.** `StdLib.Entry` has five fields now and is *not* the entry
   of the facts note's illustrations; that one is `Store/Val.lean`'s `sampleEntry`, which lane
   B's `NodeContract` reads and which still gives `8fab16…61fa` (`Store/Digest.lean:315`) and
   the §6a node numbers.

## 2026-09-05 11:22 — close

State at close: the six files above modified or added and nothing else of this lane's;
`LAKE.lock` absent; `LAKE.log` carrying five `C` acquire/release pairs, all exit 0; no
`lean.exe`/`lake.exe` running; nothing killed and no run near the watchdog (peak 1,623 MB, on
the generator's second run). `git` was never invoked beyond `status`. `git status` also shows
lanes U's and X's files and the untracked `.coordination-append.md`; none are this lane's.
