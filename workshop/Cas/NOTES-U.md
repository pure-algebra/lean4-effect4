# Lane U notes — the Surface library

Running notes of lane U (`workshop/Cas/LANDING.md`, "U — the Surface library"). One dated entry
per milestone: what changed, what it cost, what is open. Times are the machine clock
(`Get-Date`).

## 2026-09-05 10:52 — start; the census before the first edit

Read in the given order: `LANDING.md` ("The one lake, by lock" with the `LEAN_NUM_THREADS`
paragraph, "Layout after the landing", the U section), `BRIEF.md`, `NOTES-L1.md`; then
`src/Effect4/Store/{Digest,Canonical,Node}.lean` (`Digest.lean` whole, the other two's headers
and the declarations this lane names) and `src/Effect4/Data/JsonNumber.lean`.

Machine at start: no `lean.exe`/`lake.exe`; no `LAKE.lock`; `LAKE.log` ends with L1's three
release lines (01:18:53). `git status` shows one modified file, `src/Effect4/Surface/Entity.lean`
— the edit the restarted first launch of this lane left behind (the `JsonCanonical` import
replaced by `Data.JsonNumber`, plus an added `import Effect4.Codegen.Schema`). Both halves of
that edit are **kept**: the second is not decoration, it is required (see below).

What the census found, beyond the landing's list:

- **`Effect4.Arch.Representation.toJson?` has no home any more.** It was declared in the
  deleted `Store/JsonCanonical.lean:84-85` (`git show a47c268~1:src/Effect4/Store/JsonCanonical.lean`)
  and only `highestBit`, `binary64OfNat` and `Json.ofNat` moved to `Data/JsonNumber.lean`. Three
  files in this lane read it: `Surface/Entity.lean:536`, `Surface/Api.lean:1823`,
  `Surface/Agent.lean:590`. Its sibling `Document.toJson?` has one reader,
  `Test/Evidence/ArchContract.lean:78`, which reaches it through `Evidence/Views.lean` and not
  through any Surface module — so it is lane C's to re-home, not this lane's.
- **`import Effect4.Codegen.Schema` in `Entity.lean` is load-bearing.** `Entity.lean:588-615`
  calls `Codegen.Schema.module?`, `generationReady`, `rawDocumentDecl`, `documentDecl`, and the
  only path that reached that module was `Store.JsonCanonical` (`JsonCanonical.lean:2`):
  `Codegen/Spell.lean` imports `Surface.Annotate`, `Schema.Dimension` and `TypeScript`, none of
  which reach `Codegen.Schema`. Removing the import would make the file red.
- **`Digest.ofBytes?` lives in `Store/Node.lean:82`, not in `Store/Digest.lean`.** Importing
  `Store.Node` into `Surface/Annotate.lean` would put `Store.{Kind,Shape,Canonical,Node}` into
  the closure of every Surface module, and with `open Effect4.Store` still on five of them that
  is a live ambiguity for `Kind` (`Surface/Kind.lean`'s, which `Api.lean:1826` uses as an
  implicit binder type) and `Shape`. The landing says `import Effect4.Store.Digest` stands, so
  `Annotate.lean` spells the same checked constructor inline
  (`if h : digestBytes.length = 32 then some ⟨digestBytes, h⟩ else none`) and cites
  `Store/Node.lean:82`. Open item for the store's owner: move `Digest.ofBytes?` next to
  `Digest.ofHex?` in `Store/Digest.lean` and this becomes the call.
- **`open Effect4.Store` is dead in five files** once the six hand instances go: `git grep` for
  `Bytes`, `sha256`, `framed`, `be64`, `natBytes`, `Val`, `Tag.`, `Digest` over
  `Surface/{Entity,Api,Agent,Site,Deploy}.lean` returns nothing. The opens are dropped with the
  instances they were there for; `Annotate.lean` keeps its narrow `open Effect4.Store (Digest)`.
- **Nothing outside `Observability.lean` reads its hex helpers.** `hexLower`, `hexUpper`,
  `hexDigit`, `hexIndex`, `hexValue`, `hexOfByte` have no reader in `src/`, `Test/`, `harness/`
  or `ocaml/`; `Test/Audit/AxiomGate.lean:184` names only `parseHexId`, which keeps its name and
  its `String.toList`.

## 2026-09-05 11:00 — the seven files, changed and green

One line each, in the order the landing lists them.

- `Surface/Annotate.lean` — `parse?`'s `source` branch builds the `Digest` through the checked
  constructor: `bytesOf?` then `if h : digestBytes.length = 32 then some ⟨digestBytes, h⟩ else
  none`, so a `source` array of any other length refuses the whole mark instead of silently
  becoming `none`; `parse?_encode`'s `cases digest` becomes `cases digest with | mk digestBytes
  hlen` and the length hypothesis joins the `simp` set, which discharges the new `dite`; the
  doc comment says why the check is spelled here and cites `Store/Node.lean:82`. `import
  Effect4.Store.Digest` stands, as the landing said.
- `Surface/Entity.lean` — `import Effect4.Store.JsonCanonical` → `Effect4.Data.JsonNumber`,
  `import Effect4.Codegen.Schema` added (the path `JsonCanonical` used to supply for
  `Codegen.Schema.module?` and its three neighbours at the foot of the file); a short
  `namespace Effect4.Arch` block above `namespace Effect4.Surface` carrying
  `Representation.toJson?` verbatim from the retired module, with a section note saying where it
  came from, who reads it and where its sibling is owed; the two hand instances (`Canonical
  Entity`, `Canonical Domain`) and their `## Content` heading deleted; `Effect4.Store` dropped
  from the `open` line; the header's `Canonical` sentence and the `Entity.json` citation
  rewritten.
- `Surface/Api.lean` — the hand `Canonical (Api refs)` deleted; `Effect4.Store` dropped from
  the `open` line. `Arch.Json.ofNat` (`:1855`) and `Arch.Representation.toJson?` (`:1823`) reach
  their definitions through `import Effect4.Surface.Entity`; no other edit.
- `Surface/Agent.lean` — the hand `Canonical (McpServer refs)` and its `## Content` heading
  deleted; `Effect4.Store` dropped from the `open` line; the header's `Canonical` sentence
  rewritten. `Arch.Representation.toJson?` (`:590`) reaches Entity the same way.
- `Surface/Deploy.lean` — `import Effect4.Store.JsonCanonical` → `Effect4.Data.JsonNumber`; the
  hand `Canonical Deployment` deleted; `Effect4.Store` dropped from the `open` line; the four
  prose citations of `Store/JsonCanonical.lean:{61-81,73,73-81,81}` retargeted at
  `Data/JsonNumber.lean:{27-46,38,38-46,46}` (`highestBit` 27, `binary64OfNat` 38, `Json.ofNat`
  46); the header's `Canonical` clause rewritten.
- `Surface/Site.lean` — the hand `Canonical Site` deleted; `Effect4.Store` dropped from the
  `open` line; the header's citation for the over-the-bytes route retargeted from
  `Store/Canonical.lean` at `Store/Utf8.lean`, which is where that route now lives.
- `Surface/Observability.lean` — `import Effect4.Store.Digest` added; `hexLower`, `hexUpper`,
  `hexDigit`, `hexIndex`, `hexValue`, `hexOfByte` and the recursive `bytesOfHex` deleted;
  `hexOfBytes` is `String.ofList (Effect4.Store.hexOfBytes bs)` and `bytesOfHex` is
  `Effect4.Store.bytesOfHex` — the same types, the same spellings, so `toHeaders`, `w3c`,
  `parseHexId` and all thirteen `#guard`s below are untouched and pass; the section note now
  cites the store's codec and its two proofs. Nothing else in the estate read the deleted names.

That is six hand instances deleted (`Site`, `Entity`, `Domain`, `Api`, `McpServer`,
`Deployment`), the two `JsonCanonical` imports repointed, one checked `Digest`, one hex codec.

### The gate

Under the lock (`LAKE.log`, two acquire/release pairs, both `waited 0 s`; the second run is the
first plus two doc-comment rewraps):

```
LEAN_NUM_THREADS=3  lake build Effect4.Surface.Site Effect4.Surface.Observability
  Effect4.Surface.Deploy Effect4.Surface.Api Effect4.Surface.Agent
  Effect4.Codegen.JsonSchema Effect4.Ingest.JsonSchema Effect4.Codegen.App
10:56:32 → 10:56:52  exit 0 (20 s)   |   10:58:36 → 10:58:56  exit 0 (20 s)
```

"Build completed successfully (62 jobs)", no errors and no warnings in either log.
`Effect4.Codegen.App` is **in** the gate and green: its closure is `Codegen.Rule`
(`Rule.lean:2-5` imports the four Surface modules) plus `Codegen.*` and `Ingest.*`, and reaches
no `Evidence/Views.lean` or `SurfaceViews.lean`, so lane C's red files never enter it. Built in
the run: `Surface.Annotate` 1.7 s, `Surface.Observability` 2.6 s, `Codegen.Spell` 1.4 s,
`Surface.Entity` 1.6 s, `Surface.Deploy` 2.3 s, `Surface.Site` 1.5 s, `Surface.Agent` 2.9 s,
`Surface.Api` 2.0 s, then the twelve `Codegen`/`Ingest` modules at 0.9–2.6 s each. Peak
`lean.exe` working set never tripped the watchdog (3 GB / 600 s); nothing was killed; no
`lean.exe`/`lake.exe` left afterwards; the lock is released.

Receipts: no Surface module has ever carried a `#print axioms` section (checked: `git grep`
finds none under `src/Effect4/Surface/`), so the axiom evidence is a probe instead, `lake env
lean -M 3072` over a scratch file importing `Surface.{Site,Api,Agent,Observability}`:

```
Effect4.Arch.Representation.toJson?              [propext, Quot.sound]
Effect4.Surface.SurfaceMark.parse?               [propext]
Effect4.Surface.SurfaceMark.parse?_encode        [propext]
Effect4.Surface.markKey                          [propext]
Effect4.Surface.markKey_lawful                   [propext]
Effect4.Surface.Observability.hexOfBytes         (no axioms)
Effect4.Surface.Observability.bytesOfHex         [propext]
Effect4.Surface.Observability.toHeaders          [propext]
Effect4.Surface.Observability.encodeW3c          (no axioms)
Effect4.Surface.Observability.decodeW3c          [propext]
Effect4.Surface.Observability.decodeW3c_encodeW3c [propext]
Effect4.Surface.Entity.json / repJson / persistedJson   [propext, Quot.sound]
```

and the gate's pinned choice list is still exactly its five, unchanged by this lane:
`parseHexId`, `w3c`, `b3`, `xb3`, `fromHeaders`, each `[propext, Classical.choice, Quot.sound]`
through `String.toList`/`String.splitOn`, as `Test/Audit/AxiomGate.lean:184` and the module
header say. Nothing this lane wrote reaches `Classical.choice`; no `sorry`, `partial`, `unsafe`,
`native_decide`, `axiom`, `extern`, `implemented_by` anywhere in the seven files. Every added
line is at or under 100 columns.

### Open, for the coordinator and the later lanes

1. **`Arch.Document.toJson?` is owed by lane C.** It died with `Store/JsonCanonical.lean:88-89`
   and its one reader is `Test/Evidence/ArchContract.lean:78`, which reaches `Effect4.Arch`
   through `Effect4/Evidence/Views.lean` (itself `namespace Effect4.Arch`, and itself still
   importing the deleted module). Putting it in this library would not help that reader —
   nothing under `Evidence/` imports `Surface/` — so it belongs in `Views.lean`, one line:
   `def Document.toJson? (document : Document) : Option Json := Codegen.Schema.reifyJson?
   (Codegen.Schema.documentExpr document)`. `Views.lean` will need `import Effect4.Codegen.Schema`
   for it, exactly as `Entity.lean` now does.
2. **`Arch.Representation.toJson?` is parked in `Surface/Entity.lean`, not homed.** It is a
   Surface-only reader set today, so the placement is honest; but if the coordinator would
   rather have one home for both halves of the retired module, the natural one is
   `Effect4/Codegen/Schema.lean` (it owns `representation`, `documentExpr` and `reifyJson?`),
   and then `Entity.lean` loses its `namespace Effect4.Arch` block and lane C loses item 1.
   That file is nobody's in this landing, which is why this lane did not touch it.
3. **`Digest.ofBytes?` is in the wrong module.** `Store/Node.lean:82` declares it while
   `Store/Digest.lean` declares `Digest.ofHex?`; `Annotate.lean` therefore spells the
   length check rather than calling it, because importing `Store.Node` here would push
   `Store.{Kind,Shape,Canonical,Node}` into every Surface module's closure and make `Kind` and
   `Shape` ambiguous under the `open Effect4.Store` the five view modules used to carry.
   Moving the three declarations (`ofBytes?`, `ofBytes?_bytes`, `ofBytes?_exact`) down into
   `Store/Digest.lean` costs nothing and turns three lines of `Annotate.lean` into one call.
4. **`open Effect4.Store` is gone from `Surface/{Entity,Api,Agent,Site,Deploy}.lean`** — it was
   there only for the deleted instances' `Canonical`/`encode`, and no other Store name occurs in
   those files. Lane X and lane C should know that Surface no longer opens the store namespace,
   so nothing there will collide when `Store.Kind` reaches a wider closure.
5. Deleted with no replacement, deliberately: `Observability.{hexDigit, hexValue, hexOfByte}`
   were public names with no reader anywhere in the tree. If a later module wants a nibble
   printer it is `Effect4.Store.hexDigit` (`Nat → Nat`, code points) now.

## 2026-09-05 11:00 — close

State at close: the seven files above modified and nothing else of mine; `LAKE.lock` absent,
`LAKE.log` carrying this lane's two acquire/release pairs; no `lean.exe`/`lake.exe` running.
`git status` also shows `src/Effect4/Evidence/Char/Conformance/GSet.lean` (lane X, running
beside this one) and the untracked `.coordination-append.md`; neither is this lane's.
No file was killed, no run hit the watchdog, and `git` was never invoked beyond `status`,
`diff`, `grep` and one `show` of the retired `JsonCanonical.lean`.
