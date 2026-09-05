# Lane L1 notes — the substrate into `src/`

Running notes of lane L1 (`workshop/Cas/LANDING.md`, "L1 — the substrate into `src/`"). One
dated entry per step: what moved, what changed, what is proved, what is open. Times are the
machine clock (`Get-Date`), which agrees with the spike's file times.

## 2026-09-05 01:00 — start; state of the machine and the tree

Read in the given order: `LANDING.md`, `BRIEF.md`, `REPORT-S1.md`, `REPORT-S2.md`,
`REPORT-G.md`, `NOTES.md`, `NOTES-S2.md`, `NOTES-G.md`; the facts note §5–§6a and the plan;
then the spike's `Cas/{Canonical,Shape,Node,Genesis,Digest,Val,Digits}.lean` (headers or whole),
`gen/{Main,Check}.lean`, `gen/guards-*.lean`, `tools/generate-derived.ps1`; the tree's
`Store/{Pin,JsonCanonical,Digest}.lean`, `Program/Wire.lean`, `src/Effect4.lean`,
`OCaml5/Eff/Goldens.lean`, `OCaml5/Bridge.lean:1-60`, `Test/Store/StoreContract.lean:1-70`,
`lakefile.toml`, the eight goldens under `ocaml/goldens/eff/`.

Machine: no `lean.exe`/`lake.exe` running; no `LAKE.lock`; `git status` shows only the
coordinator's `lakefile.toml` hunk (the `Effect4Gen` library at `tools/`, `lakefile.toml:42-50`).
Oleans present from the 2026-09-04 gates for `Effect4.Program.{Eff,Typing,Native}`,
`Effect4.Schema.{Document,Authoring}`, `Effect4.Data.Json`, `Effect4.Machine.Supervision`
(the carriers the generator reads); the OCaml5 tree has 58 oleans but not `OCaml5.Eff.{World,
Emit,Goldens}` — `World` imports only `Lean` and `Effect4.Program.Native`, so building
`OCaml5.Eff.Goldens` costs three small modules and joins the gate.

Every `lake` invocation runs through `scratchpad\run-lean.ps1` (polls every 2 s; kills a
`lean.exe` past 600 s or 5 GB and the run past 45 min; logs the output) and every build through
`scratchpad\locked-build.ps1` (the lock protocol of `LANDING.md`: `New-Item -ErrorAction Stop`
on `workshop\Cas\LAKE.lock`, retry every 30 s up to 30 min, `LAKE.log` lines on acquire and
release, release in `finally`). Probes and generator runs (`lake env lean -M 4096 …`) take no
lock.

Facts checked before writing:

- `OCaml5/Eff/Goldens.lean` reads `Effect4.Store.{Bytes, framed, natBytes, Tag.*}` — all
  present in the new `Canonical` closure (`Digits.lean`, `Val.lean`) under the same names, so
  the file needs no edit; `OCaml5/Bridge.lean` opens `Effect4 Effect4.Api Effect4.Machine
  Effect4.Program`, never `Effect4.Store`, so its own `hexOfBytes`/`bytesOfHex` stay
  unambiguous beside the store's; it and `Tools/EffWire.lean` use only `Wire.encodeProgram`,
  `Wire.decodeProgram` and `Wire.Corpus.all`, which the rewritten Wire keeps.
- `Effect4.Json.ofNat` does not exist (`Data/Json.lean` declares `Float64 {bits}`, `Json`,
  and no `ofNat`), so `Json.ofNat` under `open Effect4.Arch` resolves uniquely to
  `Effect4.Arch.Json.ofNat`; six modules address the helpers as `Arch.…`
  (`Surface/{Entity:532,Api:1855,Deploy:520}`, `Codegen/JsonSchema:428-601`,
  `Ingest/JsonSchema:280`), which is why the namespace is kept.
- Nothing in `src/` or `Test/` consumes `Pin.json`, `Pin.address`, `Pin.contentPath`,
  `Pin.address_congr` or `PinRole.spelling` outside `Store/Pin.lean` itself
  (`Evidence/Char/Manifest.lean:27,52` mention `Pin.address` in prose only — lane X's file).
- The spike modules mention `Cas` only in import lines, `# Cas.X` titles and prose citations
  (`Cas.Kind`, `Cas/Node.lean`, …); `renderCases` is the one other `Cas` substring and is not
  touched by a rename of `Cas.`/`Cas/`.

## 2026-09-05 01:07 — steps 1 and 2 (the modules): copied, edited, built green

What moved (copies, the spike untouched): `Cas/{Digits,Utf8,Val,Digest,Kind,Shape,Canonical,
Node,Store,Word,Traits,Genesis}.lean` → `src/Effect4/Store/<same>.lean`, with `import Cas.X` →
`import Effect4.Store.X`, `# Cas.X` → `# Store.X`, and the prose citations `` `Cas.X` ``/`` `Cas/X.lean` ``
→ `` `Store.X` ``/`` `Store/X.lean` `` (a case-sensitive pass over `Cas.`/`Cas/` only; nothing else in
the files changed). `Digest.lean`, `Canonical.lean` and `Store.lean` replace the old modules of
the same name. Deleted: `src/Effect4/Store/JsonCanonical.lean`, `src/Effect4/Store/Trie.lean`.

What changed by hand:

- `src/Effect4/Data/JsonNumber.lean` (new): `highestBit`, `binary64OfNat`, `Json.ofNat` moved
  verbatim from `JsonCanonical.lean:61-81`, namespace `Effect4.Arch` kept (the six `Arch.…`
  consumers listed above), `set_option autoImplicit false`, four `#guard`s on the bit patterns
  (`0`, `1`, `1947 = 0x409E6C0000000000`, the first truncation at `2^53 + 1`), receipts.
- `Store/Shape.lean`: imports `Effect4.Data.JsonNumber`, `open Effect4.Arch (Json.ofNat)`, the
  three copies and their receipts deleted, the header sentence rewritten.
- `Store/Canonical.lean`: the one guard that spelled `Json.ofNat` now spells `Arch.Json.ofNat`
  (line 671); nothing else.
- `Store/Pin.lean`: the carrier (`PinRole`, `Pin`), `spanBytes`, `lineCount`, `isWellFormed`,
  `WellFormed`, `spanDigest_eq_of_wellFormed`, `holds_or_collision`, `holds_of_injective` kept;
  `Pin.json`, `Pin.address`, `Pin.contentPath`, `address_congr`, the `open Effect4.Arch` and the
  `JsonCanonical` import deleted; `set_option autoImplicit false` and a receipts section added
  (the old file had neither); the header rewritten for the derived instance. `PinRole.spelling`
  is kept: the landing list does not name it and it costs nothing (no consumer either way).
- `Store/Genesis.lean`: `instContentTemplatesEntry` and the eight `#eval`s dropped (they go
  to the battery with the templates); `kind_document` joins the receipts; the header
  rewritten and the §6a numbers cited as the battery's to state.

Build 1 under the lock (`LAKE.log` 01:06:21 → 01:06:56, 34 s, waited 0 s): `lake build
Effect4.Store.Traits Effect4.Store.Pin Effect4.Data.JsonNumber` — 32 jobs, "Build completed
successfully", no warnings. Receipts in the log: 402 `#print axioms` lines — 89 with no
axioms, 115 `[propext]`, 198 `[propext, Quot.sound]`, none other; no `sorryAx`, no
`Classical.choice`. Slowest module `Data.JsonNumber` at 22 s (the `2^53` guards run in the
interpreter; the module is otherwise three definitions), `Kind` and `Digits` 12 s each (first
compile of the closure), everything else 0.6–3 s. Peak `lean.exe` working set under 1 GB.

Open after the step: `Genesis` is not yet built (it imports `Derived.Schema`, step 4);
`PinDerived` does not exist yet (step 2's second half, generated in step 4).

## 2026-09-05 01:15 — step 4 (the generator and the four groups), with step 2's `PinDerived`

The tool: `workshop/Cas/gen/Main.lean` → `tools/Effect4Gen/Main.lean` (module
`Effect4Gen.Main`), `gen/Check.lean` → `tools/Effect4Gen/Check.lean` (`Effect4Gen.Check`), the
guards fragments → `tools/Effect4Gen/guards/{json,schema,program,pin}.lean` (not modules of any
library: the `Effect4Gen` globs name only `Main` and `Check`), `tools/generate-derived.ps1` →
`scripts/generate-derived.ps1`. Changes to the tool beyond the paths:

- `--kind <Type>=<kind>` (any number, `@` for a space in the type): after the emitted
  `instance instCanonical…` of that type, `/-- Every node carrying a `T` files under kind
  `k`. -/ instance instContent… : Content (T) := ⟨.k⟩`, plus its receipt line; a `--kind`
  naming a type the group does not emit is an error. The kind is a `Kind` constructor name
  and is not checked by the tool (the emitted file's elaboration checks it).
- `main` imports exactly the `--imports` modules (the spike's `main` imported `Cas.Templates`,
  `Cas.Program`, `Effect4.Schema.Document` by name), so the environment the tool reads is the
  environment the emitted file elaborates in; `--imports` and at least one type are required;
  `--kind`/unknown options are diagnosed instead of being read as type names.
- The header: `GENERATED by tools/Effect4Gen/Main.lean`, the regenerating command with the
  real `--out`, `--append` and `--kind` arguments (the spike hard-coded `Gen-out\<G>.lean`),
  a pointer at `scripts\generate-derived.ps1 -Verify`; the module doc mentions the `Content`
  line.
- `Check.lean` imports the union of the `import` lines of the files it is given (the spike
  imported the three fixed modules), so it checks each generated file against the environment
  that file elaborates in.
- Toolchain hygiene: `String.trimRight`, `String.trim`, `String.mk` are deprecated on v4.33.1
  (`String → String.Slice` now); replaced by `trimAsciiEnd.copy`, `trimAscii.copy`,
  `String.ofList`, so `lake build Effect4Gen` is warning-free. A parser slip of mine (the last
  positional argument read as a flag) cost one failed run and is fixed.
- `scripts/generate-derived.ps1`: repo root `$PSScriptRoot\..`; manifest at the landing paths
  with an `Out` and a `Kinds` column; `-Verify` keeps the hash comparison and adds
  `git diff --exit-code --quiet -- <derived files>`; `-Check` unchanged in kind (type-check,
  receipt scan for `sorryAx`/`Classical.choice`, the projection guard).

The manifest, in the order the groups depend on each other:

| group | imports | out | kinds | carriers |
| --- | --- | --- | --- | --- |
| Json | `Effect4.Store.Canonical` | `src/Effect4/Store/Derived/Json.lean` | — | `Float64`, `Json` |
| Schema | `Effect4.Store.Derived.Json` | `src/Effect4/Store/Derived/Schema.lean` | — | the thirteen of the spike |
| Program | `Effect4.Program.Native,Effect4.Store.Canonical` | `src/Effect4/Program/Derived.lean` | — | the ten of the spike |
| Pin | `Effect4.Store.Pin,Effect4.Store.Node` | `src/Effect4/Store/PinDerived.lean` | `Effect4.Store.Pin=source` | `PinRole`, `Pin` |

The Schema group's import is `Derived.Json`, not `Canonical`: the Schema carriers hold `Json`
and `Float64` fields, whose instances the spike took from `Cas.Templates` and the landing
takes from the generated Json group (the first run with `Canonical` alone failed with
`failed to synthesize Canonical Json`, 69 receipts reaching `sorryAx` — the tool's fallback
`first | … | exact nomatch h` swallowing the failures, as S1's hazard list warns). So the
order is: generate Json → build `Effect4.Store.Derived.Json` (build 2 under the lock,
`LAKE.log` 01:12, 28 jobs, 1.6 s for the module) → generate Schema.

Guards, golden-only (the hand oracles `Cas.Templates`/`Cas.Program` are not in `src`):

- `json.lean`: the reader round trips (through `guarded toValJson rawJson` and through the
  class), refusals of a byte appended/dropped, shape acceptance, the primitive frames of
  `StoreContract.lean:39-47` on the image (`.str "A"`, `.null`, and `Float64 ⟨3⟩` as a
  `ctor 0` around a `nat`). Dropped: every comparison with `JsonCanonical.toVal`.
- `schema.lean`: the spike's, verbatim (it never had an oracle); `Cas/Shape.lean` cited as
  `Store/Shape.lean`.
- `program.lean`: `p42` and `pCatch` restated by hand and held to their goldens (the hex from
  `ocaml/goldens/eff/{p42,pCatch}.hex`), `p42` at 66 bytes and digest `fa5f40…62a3`, the
  reader's round trip and refusals (appended, dropped, a leading-zero constructor index) spelled
  without the class, shape acceptance, and the alphabets' `ofVal_toVal` run. The other six
  goldens are guarded in `Program/Wire.lean` over `Canonical.encode`: the corpus lives there
  and the Wire imports this module, so the derived module cannot name `Wire.Corpus`; a second
  copy of the eight programs here would be the duplication the landing removes elsewhere.
- `pin.lean` (new): a well-formed sample pin (its digest recomputed from its lines), the laws
  run, refusals, `Content.kind Pin = .source`, the spec root a struct, the printer's object
  (keys in declaration order, `role` as its constructor name, `spanDigest` as lowercase hex),
  and a `Ref Pin` frame — 42 bytes, `0b … 21 01 …` — round-tripping and refused at kind byte 2
  and at 31 bytes.

Results (`gen2.log`, `gen3.log`, every run `lake env lean -M 4096`, ten-minute cap, none
near it; slowest the Schema check at ~14 s): Json green, 9 receipts; Program green, 67;
Pin green, 11 (PinRole 5, Pin 5, `instContent` 1); Schema green, 84; the projection guard
agrees on 37 shapes (the spike's 35 plus `PinRole` and `Pin`). Line counts: Json 353,
Schema 1869, Program 1694, PinDerived 243. The receipt census of the four files is read off
the gate log below.

## 2026-09-05 01:16 — step 3 (`Program/Wire.lean`) and step 5 (`src/Effect4.lean`)

`Program/Wire.lean` (rewritten, 23.9 KB → ~13 KB): imports `Effect4.Program.Derived`;
`encodeProgram p := Canonical.encode p`, `decodeProgram b := Canonical.decode b`;
`decode_encode (p) (h : (Canonical.toVal p).WF)`, `decode_exact : decodeProgram b = some p →
b = encodeProgram p ∧ (Canonical.toVal p).WF`, `encode_injective` — all three one-liners from
`Canonical`'s theorems; `hexOf p := hexString (encodeProgram p)`; the `Corpus` namespace
verbatim (`forkOptions`, the eight programs, `all`); the guards: `typeOf nativeSignature` on
the corpus, round trip, appended/dropped refused, the leading-zero index refused (now spelled
with `Canonical.encode (Term.lit .unit)`), **the eight goldens byte for byte** (the hex
literals copied from `ocaml/goldens/eff/*.hex`), `p42` at 66 bytes with digest `fa5f40…62a3`;
receipts for the six declarations; `set_option autoImplicit false` (the old file had none).
Gone: `ctor`, the seventeen `enc*` encoders, the byte-level readers (`natOfDigits`,
`readFrame`, `done`, `readNat`, `readBool`, `contBits`, `utf8Chars`, `readString`,
`readCtor`), the twenty `dec*` decoders and `decEnum`, the old `instance Canonical (Eff
NativeOp) := ⟨encodeProgram⟩`. `Api.bytesOf`/`ofBytes` (`Api.lean:74,78`) still read
`Wire.encodeProgram`/`Wire.decodeProgram` with the same types; `OCaml5/Bridge.lean:104,115`
and `OCaml5/Tools/EffWire.lean:50-57` likewise (`Corpus.all`, `encodeProgram`) — none edited.

`src/Effect4.lean`: `import Effect4.Data.JsonNumber` after `Data.Json`; the store block is
the sixteen modules in the landing's order with a rewritten comment; the `JsonCanonical` line
and the `Trie` line are gone and the middle-tier comment no longer claims a JSON canonical
form; `import Effect4.Program.Derived` precedes `import Effect4.Program.Wire` with a
rewritten comment. The root itself is red by design until lane B (Surface, Evidence, Char and
Codegen still import the retired modules); not built here.

## 2026-09-05 01:19 — step 6, the gate: green at the ceiling

`LAKE.log` 01:18:28 → 01:18:53 (25 s, waited 0 s): `lake build Effect4.Store.Genesis
Effect4.Store.PinDerived Effect4.Program.Wire Effect4Gen OCaml5.Eff.Goldens` — 61 jobs,
"Build completed successfully". Built in this run: `Effect4Gen.Check` (4.5 s), `Effect4Gen.Main`
(4.6 s, no deprecation warnings), `Effect4.Program.Derived` (17 s), `OCaml5.Eff.World` (17 s),
`Effect4.Program.Wire` (1.1 s), `Effect4.Store.Derived.Schema` (19 s), `Effect4.Store.PinDerived`
(19 s), `OCaml5.Eff.Emit` (2.9 s), `Effect4.Store.Genesis` (0.9 s), `OCaml5.Eff.Goldens`
(2.1 s, unedited: `Bytes`, `framed`, `natBytes`, `Tag.*` resolve in the new closure). The one
warning in the log is pre-existing and not mine: `src/Effect4/Machine/Frames.lean:1893:40`,
an unreferenced `hstack`, replayed from that module's cached build.

Receipt census over the three builds' logs (the gate log replays every module's receipts):
587 `#print axioms` lines — 95 with no axioms, 155 `[propext]`, 337 `[propext, Quot.sound]`
(four of them wrapped over two lines by their long names; checked), none other. No `sorryAx`,
no `Classical.choice`. By module: the store chain, `Pin` and `JsonNumber` 402 (build 1);
`Derived.Json` 9; `Derived.Schema` 84; `Program.Derived` 67; `PinDerived` 11; `Genesis` 8;
`Wire` 6 (`encodeProgram`, `decodeProgram`, `decode_encode`, `decode_exact`,
`encode_injective`, `hexOf`, all `[propext, Quot.sound]`). Every `#guard` passed, so: the
eight corpus programs are byte-identical to `ocaml/goldens/eff/*.hex` through
`Canonical.encode` (`Wire.lean`) and two of them again through the generated `toValEff`
(`Program/Derived.lean`); `p42` is 66 bytes with payload digest `fa5f40…62a3`; the primitive
bytes of `Test/Store/StoreContract.lean:39-47` hold on `Val` and on the trait
(`Val.lean`, `Canonical.lean`); the refusals hold (appended, dropped, leading-zero digit and
index, non-shortest UTF-8, wrong tag, three-frame pair, wrong-kind and short `Ref`).

Idempotency: `pwsh -File scripts\generate-derived.ps1 -Verify` after the gate — `same` for all
four groups, `git diff --exit-code` clean, exit 0 (19 s). Long lines above 100 columns in the
emitted files: Json 1, Schema 71, Program 10, Pin 6 (one of each is the header's regenerating
command); lane G's open item, unchanged in kind.

Machine: nothing killed in any run; peak `lean.exe` working set well under 1 GB in every
monitored run; no `lean.exe`/`lake.exe` left; `LAKE.lock` released after each build (three
acquire/release pairs in `LAKE.log`, no waiting).

### Open, for the coordinator and the later lanes

- `lake build Effect4` and `Test` are red by design until lanes U, X, C, B: `Evidence/Views.lean`,
  `Evidence/SurfaceViews.lean`, `Char/Conformance/{Vector,GSet}.lean` import the old
  `Effect4.Store.Store` API; `Surface/{Entity,Deploy}.lean`, `Evidence/Char/Evidence.lean`,
  `Evidence/Views.lean` import the deleted `Effect4.Store.JsonCanonical`; `Surface/Annotate.lean`
  builds a `Digest` from bare bytes (now `Digest.ofBytes?`); `Test/Store/StoreContract.lean`
  imports the deleted `Trie` and `LawfulCanonical`.
- The goldens split: all eight in `Program/Wire.lean` (the corpus's home), `p42`/`pCatch` in
  `Program/Derived.lean`'s guards; if the coordinator wants all eight below the Wire, the
  corpus has to move into the derived module's guards (and `Wire.Corpus`, which
  `OCaml5/Tools/EffWire.lean` reads, would re-export it).
- `PinRole.spelling` kept without a consumer; `Effect4Gen.{Main,Check}` carry no receipts
  section (tools over `Lean.Meta`, outside the audited libraries, as `REPORT-G.md` and the
  lakefile comment say; they use `partial def` where the spike did).
- `Effect4Gen` still refuses a bare parameterised type (G's open item); the emitted line width.
- The §6a numbers (`2794d9…2926`, `268ee1…aa7c`, `1c3c94…72eb`) are the battery's to state
  (lane B, `NodeContract`), per the landing's note on the kernel cost; nothing prints them now
  that `Genesis` has no `#eval`.
- `OCaml5/Bridge.lean` keeps its own `hexOfBytes`/`bytesOfHex` copy (plan §6 retires it; not an
  L1 file; it is not ambiguous, since the module never opens `Effect4.Store`).
- Timing oddity, harmless: `Kind` and `Digits` took 12 s and `JsonNumber` 22 s in build 1
  while `Val` (38 KB of proofs) took 1 s — the first jobs of a cold `lake` on this machine;
  the gate's `Program.Derived`/`Derived.Schema`/`PinDerived` at 17–19 s match the spike's.

## 2026-09-05 01:21 — close

The tool harness refused to write `workshop/Cas/REPORT-L1.md` (as it refused S1's, S2's and
G's report files); the report — files created, changed and deleted with one line each, the gate
summary, the receipts census, departures and open items — is delivered as this lane's closing
message to the coordinator. Its content is the five entries above. State at close: no
`lean.exe`/`lake.exe` running, `LAKE.lock` absent, `git status` shows exactly the files listed
in the 01:07 and 01:15–01:16 entries plus the coordinator's `lakefile.toml` hunk.
