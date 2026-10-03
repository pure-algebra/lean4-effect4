# Generated code in this tree: one map, one rule, one command, one gate (2026-09-08)

Status: the developed plan, replacing `2026-09-08-one-generator-plan.md` (kept for the record).
Tree at `7f8a9fc`. Written from five read-only scout notes against the tree, each with its
own `file:line` evidence: `2026-09-08-one-generator-scout-s1.md` (the three reflections and
the closure), `-s2.md` (bytes, ordinals, goldens, the ledger), `-s3.md` (the LCNF route,
externs, carriers, staleness), `-s4.md` (consumers, gates, sequencing, the value tables),
`-s5.md` (prior art in Lean and compilers, the easier path). Every number below sits behind a
command quoted in one of those notes; a number without one is a target and is labelled.

The owner's instruction, verbatim: *"the problem to me was too many generated moving pieces..
im hoping we can learn something from the compiler/lean world to just help us be better
organized here so i dont get confused about what the hell we're generating and for what"*, and
*"if there's an easier solution we should take it"*, and *"ignore the mac PC split that should
be removed"*. This plan takes all three literally.

## 0. The verdict in ten lines

1. The old plan diagnosed "four reflections" and prescribed a merge. There are three
   reflections, not four (TsGen already reads EffGen's world block, `tools/Tools/TsGen.lean:6-7`),
   and the count is not the disease.
2. The disease, measured: fourteen producers, about 325 tracked generated files, about 40,000
   committed generated lines, **one** drift gate in the sweep (`ts-eff`), **zero** generated files
   that record what they were cut from, and seven of the eight Lean generators with no bash
   entry point at all (S4 §2.1, S5 F12 to F16).
3. The consequence is already in the tree: both generated OCaml engines lack the timer store,
   the `advance` decision and the whole wake protocol. They were cut from a tree at or before
   `57dbb8c` and committed ten hours after the timer landed at `e2285a9`. Nothing could say so
   (S3 §2.5). Separately, `ocaml/engine` does not compile at `7f8a9fc` and the sweep's OCaml gate
   has been red and undeclared since `30d60bb` (S2 §2.8).
4. The old plan's "one representation rule" is three rules wearing one name. The wire framing
   is fixed by Lean and pinned by goldens; the in-memory type per target is free exactly where
   that target has no byte writer; naming is a third table. Its §7 sentence about `ServiceName`
   would break the wire if a printer believed it (S2 §2.10, S1 §2.2).
5. Its step 2 ("functions over shared types") is impossible as written: OCaml has no
   higher-kinded type variables, eight of the hundred generated type declarations mention a
   carrier, and the only shape that compiles kills the oracle arm of the differential (S3 §2.4).
6. Its `world.ledger` text file contradicts CAS amendment M17, which makes the ledger a stored
   node of kind `table` (S4 Q2). Its "carriers as attributes" is blocked by Lean itself: an
   attribute can only be attached in the declaring module (S5 F7).
7. The compiler world's answer to the owner's question is one rule: **every generated file
   has exactly one producer command, exactly one gate, and a header naming both plus what it
   was cut from.** The tree already implements that rule correctly on one route
   (`scripts/generate-ts-eff.sh` plus `scripts/check-ts-eff.sh`, keyed on Lake traces). The
   work is to copy it, not invent it (S5 F14, S3 §2.7).
8. The Lean world's answer is derivation at the declaration. A `deriving Canonical` handler can
   replace the four generated Lean modules (4,592 lines) and their whole tool chain, theorems
   included; the generic universe design is the wrong trade here; the prerequisite is a policy
   decision about `import Lean` in the audited library (S5 §2.6, S1 §5.2).
9. So: **Phase 0** (one lane, this week): the map, the stamps, one `generate.sh`, one
   `check-generated.sh` in the sweep, the engine build repaired, the PowerShell deleted.
   **Phase 1** (the engine lane, after ingest commit 5): regenerate the engines against the
   current machine with a gate that can tell. **Phase 2** (owner decision): `deriving Canonical`.
   **Phase 3** (with the CAS lane's X2 and commit 7): the cross-language description as a
   `#guard`-pinned Lean value and the ledger as M17's table node. No type split. No PC.
10. Phase 0 alone answers the owner's complaint. Everything after it deletes pieces rather than
    reorganising them, and each phase is independently useful.

## 1. The problem, measured

### 1.1 What is generated today

Fourteen producers, ten families, about 325 tracked files (S4 §2.1, `git grep -l GENERATED`
plus the family inventory). The routes that matter:

| route | producer | committed output | lines | gate in the sweep | stamp |
| --- | --- | --- | --- | --- | --- |
| Effect4Gen | `tools/Effect4Gen/Main.lean` via `Driver.lean` or `scripts/generate-derived.ps1`, from `tools/Effect4Gen/manifest.json` | `src/Effect4/Program/Derived.lean`, `src/Effect4/Store/Derived/{Schema,Json}.lean`, `src/Effect4/Store/PinDerived.lean` | 4,592 | none for drift (shape only, inside `lake build Test`: `Test/Store/DerivedCheck.lean:46-59`) | none |
| EffGen | `src/OCaml5/Tools/EffGen.lean` over `src/OCaml5/Eff/World.lean` + `Emit.lean` | `ocaml/eff/eff_{types,wire,json,native}.ml`, `eff_manifest.txt`, `ocaml/eff/goldens/*` (121 files) | 2,212 + goldens | none for drift (`dune test eff` tests the committed bytes against themselves) | none |
| EffWire, CasGoldens | `src/OCaml5/Tools/EffWire.lean`, `CasGoldens.lean` | `ocaml/goldens/eff/*` (9), `ocaml/engine/cas/goldens/*` (119) | bytes | `dune test eff` for the first; **nothing** for the second (`check-ocaml.sh:52` runs `eff gen`, never `engine`) | none |
| LcnfGen | `src/OCaml5/Tools/LcnfGen.lean` over `src/OCaml5/Lcnf/*` | `ocaml/gen/{api_gen,fibers_gen,machine_gen}.ml`, `ocaml/engine/api_engine.ml` (with `externs.txt`, `api_engine_prelude.ml`) | 31,435 | `dune test gen` tests the file, not correspondence; `ocaml/engine/tools/gen-check.sh` is outside the sweep and hardcodes `REPO=/mnt/c/Users/kokok/…` (`:27`) | none |
| TsGen | `scripts/generate-ts-eff.sh` over `tools/Tools/TsGen.lean` | `ts/eff/{eff,json,profile,taxonomy,forms,wire}.gen.ts` | 1,179 | **`scripts/check-ts-eff.sh`**, byte for byte, stamped on the Lake trace of the generator (`:47-53`) | partial (`profile.gen.ts:8-9`, self-referential) |
| Describe, RenderDeep | `src/OCaml5/Tools/{Describe,RenderDeep}.lean` | `src/OCaml5/Avatar/Derived/*.lean` (563), the generated blocks inside `ocaml/avatar/deep_*.ml` | 563 + blocks | none; `render-deep.sh` diffs, nothing runs it | none |
| the daemon's dune rules | `ocaml/server/dune:13-80` | `e4d_{masks_data,families_data,armmap,pins}.ml` | build artifacts | `daemon-protocol`, `armmap-citations` | dune's |

Two things the table says that no document in the tree says today. First, exactly one
Lean-derived artifact has a byte-for-byte drift gate. Second, the daemon route already does
what compilers do: its four generated modules are dune `(rule)` outputs that are never
committed (S4 §2.1, fifth bullet). The tree contains the right pattern twice and does not
apply it elsewhere.

### 1.2 The staleness, with the archaeology

`grep -c timer ocaml/gen/api_gen.ml` = 0; `grep -c advance` = 0; the same for
`ocaml/engine/api_engine.ml`, and `grep -c wake` = 0 there too. Lean has `timers : TimerStore`
(`src/Effect4/Machine/Stores.lean:2032`), `RunDecision.advance` (`Fibers.lean:457`) and imports
`Machine.Wake` (`Fibers.lean:4`).

`git log -S` puts `timers`, `advance` and `Timer.lean` in one commit, `e2285a9`, at 06:09 on
2026-09-08; `Wake` entered at `5347294` (03:05). Both generated files were committed at 16:09
the same day (`4cdf19b`, `30d60bb`), from a tree at or before `57dbb8c`; `4cdf19b`'s own message
says `api_gen.ml` came from `7d53312`. No header records any of this (S3 §2.5).

Why nothing caught it: the 148,612-comparison differential compares three engines that are all
LCNF output from the same stale tree, so a field Lean grew is absent on every side; its
hand-written tape alphabet `E4_diff.decision` has seven arms to `RunDecision`'s eight, so no
generated tape can even reach `advance`; `dune test gen` runs two programs against constants a
human typed (S3 §2.5). These are true statements about the seam and the carriers. They were
never statements about correspondence with Lean, and the old plan (§7, "the acceptance test of
every regeneration") mistakes them for one.

### 1.3 The engine does not build

In an isolated copy, `dune build engine` exits 1 with four warning-8 errors: `e4_program.ml:353-375`
(`of_native_op`, `sleep`/`clockNow` unmatched), `:377-403` (`of_eff`, the three join
constructors unmatched), `corpora.ml:985-1002` and `:1055-1070` (the same three). `eff` and
`gen` build clean. Because `30d60bb` added `engine` to `ocaml/dune`, the sweep row
`ocaml|dune-tests` (`dune build && dune test eff gen`) is red on `main` and is not declared in
`Test/fixtures/trust-gate/known-red.txt` (S2 §2.8). The next seat to run `sweep.sh --ocaml`
will stop on it; the ingest packet's commit 3 requires that sweep green.

Two further facts about the engine's alphabet. Its `eff` has the join's three constructors
(`Eff_provideLayer` appears in `api_engine.ml`), so `of_eff`'s missing arms are mappings. Its
`native_op` predates the timer, so `sleep` and `clockNow` have no engine counterpart and the
converter must refuse them. And `E4_program.pin`'s prefix law (the wire's constructor names must
be a prefix of the engine's, `e4_program.ml:199-221`) now fails on `native_op` in the other
direction, so even a compiled engine refuses every load until it is regenerated. The repair in
Phase 0 is therefore a compile repair that makes the sweep honest; the engine becomes usable
again in Phase 1.

### 1.4 Nine framings, seventeen ordinal tables

The wire's framing is one line of Lean (`src/Effect4/Store/Val.lean:52-53`, tags at `:57-73`,
`Val.encode` at `:147-160`). It is implemented nine times across Lean, OCaml and TypeScript,
and the constructor ordinals are copied seventeen times, six by hand (S2 §2.2, §2.4). One hand
copy is already wrong in three ways (`ocaml/eff/README.md:100-125`), one hand list inside a Lean
tool restates what the environment already knows (`src/OCaml5/Tools/EffWire.lean:30-49`), the
engine's manifest parser skips every structure row so field order is pinned by nothing
(`e4_program.ml:266-276`), and `e4_be.ml` is an untested hand copy of `eff_frame.ml` on the
CAS's critical path (S2 §2.2 row F).

## 2. What we take from Lean and from compilers

Four disciplines exist for generated code. Each fits one tier of this tree and none fits all
of it (S5 §2.4).

| discipline | where it comes from | what it means here | fits |
| --- | --- | --- | --- |
| **derive at the declaration, no file** | Lean's `deriving` (`registerDerivingHandler`, `Lean/Elab/Deriving/Basic.lean:276-292`; proof-producing handlers exist, `DecEq.lean:47-52`); OCaml's `ppx_deriving` | instances produced by `lake build` where the type is named; nothing committed, nothing to regenerate | the Lean-to-Lean route (Effect4Gen) |
| **committed, stamped, checked** | `go generate` plus `git diff --exit-code`; Lean's own `stage0` with one update procedure and one refusing check (from memory, S5 F9) | the file carries the command and the revision it was cut from; one gate regenerates into a temp dir and refuses a byte difference | every cross-language projection: OCaml types and codecs, TypeScript schemas and codecs, the goldens |
| **build artifact, never committed** | dune `(rule (targets …))`, Lake facets | the build system reproduces it from declared inputs | already used by `ocaml/server/dune`; usable for any OCaml-only output whose producer is cheap |
| **one description, many bindings** | protobuf, Cap'n Proto, ASN.1: one schema, field numbers appended never reused, conformance goldens | here the description is a Lean value (the tree's idiom is `#guard`, 2,074 uses under `src/`), never a text file with its own parser; the printers are ordinary Lean functions over it | the OCaml and TypeScript type projections, once they share one world value |

And one rule that all four share, which becomes this tree's rule (S5 §4.2):

> Every generated file has exactly one producer command, exactly one gate, and a header that
> names both plus what it was cut from. If a file cannot name a single producer, it is not one
> artifact and is split. If it cannot name a gate, it is not committed.

Two things the Lean world rules out (S5 F7, F31; S3 §2.6). An attribute can only be attached in
the module that declares the constant (`Lean/Attributes.lean:209,285`), so a `@[carrier …]`
row on `RunMachine.fibers` would have to be written inside `src/Effect4/Machine/Fibers.lean`,
and `src/Effect4` imports `Lean` in zero modules today. The workable form of "the table lives
beside the declarations" is a Lean data module with a compile-time check that every name in it
resolves in the environment. And `lakefile.toml` supports only `lean_lib`, `lean_exe`,
`input_file` and `input_dir` (`Lake/Load/Toml.lean:430-437`); traced custom targets need a
`lakefile.lean`. There is no `[[lean_exe]]` in this tree; `lean_run` over built oleans is what
every generator uses, and a bash dispatcher over it is the one command.

## 3. Three tables, not one "representation"

The old plan's §1 and §7 conflate three things. Write them apart, because every printer is
read against them (S2 §4.1, S1 §4.1).

**Table W, the wire.** Fixed by Lean, pinned by goldens, identical on every target. A frame is
`tag :: be64 length ++ payload` (`Val.lean:52-53`); twelve tags (`:57-73`); a constructor is
`ctor` with its 0-based declaration index (`:157`); a structure is `ctor 0` with its fields in
declaration order (`Program/Derived.lean:795-796`, `ts/eff/wire.gen.ts:262-264`, pinned by
`ocaml/eff/goldens/pProvide.bin` bytes 132..160 and by the 400-program `.eff` corpus
differential in `scripts/check-ts-eff-corpus.sh`); builtins as `Store/Canonical.lean:288-616`
says; kind bytes and the version byte as `Store/Kind.lean:60-75` and `Store/Node.lean:170-171`
say. A structure and a one-constructor inductive frame identically; shape is a spec and
printing decision the bytes cannot see.

**Table R, the in-memory representation.** Declared per target; may differ; never observable
on the wire. `ServiceName` is the structure in Lean, a record `{ service_name_value : int }` in
`ocaml/eff`, a `Schema.Struct` in TypeScript, and the alias `service_name = int` in
`ocaml/gen/api_gen.ml:706`, which is one of eleven aliases the compiler's trivial-structure
verdict produces there (`api_gen.ml:698-707`). All four are correct, because `api_gen.ml` has
no byte writer. The rule, in one sentence: *a target's representation is free exactly where it
has no writer of its own; a target that writes bytes writes Table W's bytes whatever its
representation is.* The old plan's §7 ("EffGen's structure-as-record for `ServiceName` is the
bug") has it backwards, and a printer that believed it would emit `nat 4` where every host
writes `ctor 0 [nat 4]`.

**Table N, naming.** One function per target, collisions resolved once and recorded.
`src/OCaml5/Lcnf/Naming.lean:85-100` already does this for the LCNF route
(`Effect4.Api.Outcome` keeps `outcome`, `Effect4.Machine.Outcome` becomes
`effect4_machine_outcome`, decided before anything is rendered). The world merge of Phase 3
makes two more collisions fire (`Store.Node` against `Program.Node`, `Effect4.Row` against
`Program.Row`) and the losers become ledger rows forever (S1 §2.3).

Where the compiler's verdict does belong: the LCNF route's *own* in-memory types, so that the
generated functions and the generated types agree by construction. That is Table R for one
target. It is not the wire and it is not the world.

## 4. The map and the rule (Phase 0's deliverable)

Owner amendment, 2026-09-08: stamps for raw data, the two manifests and vendored
inputs may live in adjacent `.cut-from` files. Generated source retains in-file
comment stamps. The shared Lean stamp function writes both; the map records the
association, and the gate checks metadata as well as the artifact's complete bytes.
No existing data decoder, golden, fixed data-row count or allowlist changes to pass.
This resolves the format conflict recorded in the Phase 0 delivery receipt.

Owner amendment, 2026-09-08: the dispatch freezes all four avatar blocks,
`ocaml/avatar/deep_{stores,layer,context,forkflow}.ml`, outside Phase 0 stamping. They remain explicitly
unstamped, owned by avatar retirement, with the stale/missing producer evidence
retained. This is a named scope exception; it does not label either output current.
The owner also deferred `generated/schema-structural-assurance.tsv` after its
manual producer refused the old frozen fingerprint for Schema/Document.lean.
Its report, frozen fingerprint and existing manual gate remain unchanged.
All other stamping and generation checks remain mandatory.

`docs/GENERATED.md`, tracked under `docs/` beside `ARCHITECTURE.md`, with a row in
`AGENTS.md`'s authority map. One row per generated artifact: *file, tier, producer command,
inputs, consumers, gate, stamped, committed*. Three tiers, named in the row:

- **build artifact**: produced by a dune `(rule)` or a Lake facet, never committed
  (`ocaml/server/dune` is the model);
- **committed projection**: committed, stamped, gated byte for byte;
- **vendored input**: copied from elsewhere with provenance recorded
  (`ocaml/server/generated/archived-from.tsv` is the model).

The rule beside the table: an artifact with no row may not be committed; a row whose gate is
`none` carries an owner and a date. The full seed table is S4 §2.1; after Phase 0 it reads as
S5 §4.3.

**The stamp.** One line in every generated header, in that file's comment syntax, written by
the generator, computed in Lean so every target's stamp comes from one implementation:

```
cut-from: rev=<git describe --always --dirty> toolchain=<lean version> inputs=<sha256>
```

where `inputs` is a digest over the sorted Lake traces of the generator's import closure (the
same objects `check-ts-eff.sh:47-53` already keys on), so it changes when and only when the
Lean sources the generator reads change. `rev` is informational and never compared. Phase 3
adds `world=<digest>` restricted to the families the file covers, so a machine change does not
invalidate `ocaml/eff`.

**Two checks, kept separate** (S2 §4.4): *stale*, recompute `inputs` and compare with the
stamp, in under a second, no regeneration; *drift*, regenerate into a temp dir and `cmp`. The
stale check runs first in the sweep because it is the cheap one and it is the one that would
have caught the timer.

## 5. The phases

### Phase 0: legible and honest (one lane, one checkout, this week)

Changes no generated byte except header lines. Every step has its acceptance command.

| # | step | acceptance |
| --- | --- | --- |
| 0.1 | **Repair `ocaml/engine`'s build.** `e4_program.ml`: three `of_eff` arms mapping `provideLayer`/`service`/`provideService` to the engine's constructors; two `of_native_op` arms refusing `sleep`/`clockNow` with `Ordinal_mismatch` and the words "engine cut before the timer rows"; `corpora.ml`: the three walker arms. Record in `docs/GENERATED.md` that `E4_program.pin` refuses every load until Phase 1. | `cd ocaml && dune build && dune test eff gen` exit 0; `bash scripts/check-ocaml.sh dune-tests` PASS |
| 0.2 | **`docs/GENERATED.md`** from S4 §2.1, plus the `AGENTS.md` row. | `bash scripts/check-source-citations.sh` (every path in the table exists) |
| 0.3 | **Retire the machine split.** Delete `scripts/generate-derived.ps1` (`tools/Effect4Gen/Driver.lean` already does everything it does except the timeout, `Driver.lean:45-50`). Fix `ocaml/engine/tools/gen-check.sh:27` to a computed `repo_root`. Fix the `Regenerate:` header `harness/truth/run-truth.ts` writes (it names the deleted `.ps1`). Fix the four mentions in `Test/Store/DerivedCheck.lean:12,31,45,59`. Delete the PowerShell and WSL commands from `ocaml/gen/NOTES.md`. | `bash ocaml/engine/tools/gen-check.sh` prints its PASS on this machine; `git grep -n 'generate-derived.ps1'` returns nothing |
| 0.4 | **The stamp** in every generator: `Effect4Gen/Main.lean`, `EffGen.lean`, `EffWire.lean`, `CasGoldens.lean`, `LcnfGen.lean` (`:117-119`), `TsGen.lean`, `Describe.lean`. Headers on the two headerless outputs (`ocaml/eff/eff_manifest.txt`, `ocaml/goldens/eff/manifest.txt`). | every file under the map carries a `cut-from:` line; `scripts/check-generated.sh --stale` PASS |
| 0.5 | **`scripts/generate.sh`**, bash, dependency-ordered, `--only <family>`, `timeout 600` per Lean invocation, the lane lock held for the whole run, delegating to `Driver.lean`, `EffGen`, `EffWire`, `CasGoldens`, `generate-ts-eff.sh`, and behind `--only lcnf` the two LCNF commands verbatim from the file headers (draft in S4 §2.6). | `bash scripts/generate.sh && git diff --exit-code` (after 0.4 has landed the headers) |
| 0.6 | **`scripts/check-generated.sh`**, the shape of `check-ts-eff.sh`: key = the script, `generate.sh`, `lean-toolchain`, `lakefile.toml`, `manifest.json`, the Lake traces of `Effect4`, `OCaml5`, `Tools`, `Effect4Gen`, and every tracked generated file; on a miss regenerate the 24 cheap files (Effect4Gen's four, EffGen's five, EffWire's nine, TsGen's six) into a temp dir and `cmp`; for the LCNF route and the 119 CAS goldens compare the stamp's `inputs` digest instead of regenerating. New sweep rows `hermetic\|generated-stale` (first, cheapest) and `hermetic\|generated` (after `ts-eff`). Delete `eff_manifest.txt`'s hand twin `EffWire.lean:30-49` (read the environment the tool already has open) and `ocaml/eff/README.md:100-125` (point at the manifest). Close the `ops` staleness hole at `LcnfGen.lean:178-188`. | `bash scripts/sweep.sh --hermetic` green; a second run reports `hit` on both new rows; `EFFECT4_FORCE=1 bash scripts/check-generated.sh` green. **Expected on the first run: the LCNF route is red on `inputs`.** That is the gate working; it is declared in `known-red.txt` under `# gate: generated-stale` with the reason "engines cut before `e2285a9`; cleared by Phase 1", and the declaration is removed by Phase 1's commit. |
| 0.7 | Add `dune test engine` to `check-ocaml.sh:52` as its own row `ocaml\|engine-tests`, declared red with the same reason until Phase 1 (its 29 test binaries, including every CAS golden comparison, run by nothing today). | `bash scripts/sweep.sh --ocaml` reports the row as declared |

What Phase 0 deliberately does not do: touch `tools/Tools/TsGen.lean` or any `ts/eff/*.gen.ts`
beyond the header line (the ingest packet's commits 3 to 5 read them and pin stamps in
`profile.gen.ts`, `taxonomy.gen.ts`, `forms.gen.ts`; the header line is added to TsGen in the
same commit as its check so the `ts-eff` gate stays green); touch any generator's logic; add a
`[[lean_exe]]`.

### Phase 1: the engines regenerated, with a gate that can tell (the engine lane, after ingest commit 5)

| # | step | acceptance |
| --- | --- | --- |
| 1.1 | Regenerate `ocaml/gen/api_gen.ml` and `ocaml/engine/api_engine.ml` from the current tree with `scripts/generate.sh --only lcnf`, as their own commit. The diff lands the timer store, `advance` and the wake protocol; `externs.txt` gains whatever carrier rows `TimerStore` needs; `E4_diff.decision` gains `Advance` so tapes can reach it. Remove the `known-red` declarations of 0.6 and 0.7. | `scripts/check-generated.sh` green with no declaration; `cd ocaml && dune build && dune test eff gen engine` green; `gen-check.sh` C3b (the functor body type-checks alone) green |
| 1.2 | The differential as the acceptance test **of the carrier and extern change**, stated in those words: 547 programs, 3,376 tapes, 148,612 comparisons at `30d60bb`, re-measured. It is not an acceptance test of correspondence with Lean; `check-generated.sh` is. | the receipt quotes both numbers and both sentences |
| 1.3 | **Carriers as Lean data** (the old plan's step 4, which is cheap and right): the 27 data rows of `externs.txt` (`type`, `field`, `elem`, `ops`, `carg`) move to `src/OCaml5/Lcnf/Carriers.lean` as Lean values with a compile-time check that every name resolves and every `field` row names a real field; the 31 `fn`/`fn?` rows stay text because they name OCaml bodies. The emitted OCaml is byte-identical, which the gate of 0.6 proves. | `scripts/check-generated.sh` green before and after; `externs.txt` has 31 rows |
| 1.4 | Delete `ocaml/engine/e4_be.ml` in favour of `Eff_frame` (its two extra functions move there) so the CAS lane writes bytes through the tested kernel (S2 §4.6). | `dune test engine` green |

**Amendment (2026-09-08, from the carrier-vocabulary scouting,
`2026-09-08-carrier-vocabulary-plan.md` §5).** Step 1.1's regeneration cannot splice the
current prelude as it is: `sh_stores_empty` builds a five-field `Stores` where Lean has six,
and the deferred bodies predate `DeferredCell.wake`. Step 1.1 therefore includes the smallest
hand repair of those bodies and the refresh of the 29 stale Lean citations in
`api_engine_prelude.ml` (C1 §2.3, N7), as part of its own diff. **Step 1.3 moves behind the
carrier-vocabulary plan and is folded into that plan's step 4**, so the extern table is
migrated once, after the prelude is gone; its acceptance line above ("`externs.txt` has 31
rows") is withdrawn. The corpus widening to the timer rows (`sleep`, `clockNow`, which
`corpora.ml:752-814` never draws) is the engine lane's, in step 1.2, so the differential's zero
divergences cover the machinery 1.1 adds.

Two rules from S3 §4 carried into `docs/GENERATED.md`: `ocaml/gen/api_gen.ml` is not deleted
while `api_engine_prelude.ml` has a body in it, because Gen-versus-Ref is the only check on
the 31 extern rows and the 33 hand bodies; and "delete one engine" and "the Lean side abstracts
the carriers" are the same change (900 mention sites, 570 inside `Effect4.Laws`), a wave in its
own right, not a clause in this plan.

### Phase 2: derive the Lean side at the declaration (two lanes, on the owner's decision)

The single largest deletion available: `src/Effect4/Program/Derived.lean` (2,065),
`src/Effect4/Store/Derived/Schema.lean` (1,869), `Store/Derived/Json.lean` (353),
`Store/PinDerived.lean` (305), `tools/Effect4Gen/manifest.json`, `Driver.lean`, `Check.lean`,
`Test/Store/DerivedCheck.lean`, and Phase 0's `derived` half of the gate: about 5,100 lines and
eight tool files (S5 §4.1 B, S4 §4.3).

What replaces them: a `deriving Canonical` handler (and `deriving Content` for the kind rows)
under `src/Effect4/Store/Deriving/`, registered with `registerDerivingHandler`, reusing
`Lean.Elab.Deriving.Util`'s `mkContext`/`mkHeader`/`mkInstanceCmds` for the mutual blocks
(`Util.lean:103-122,147-189`), which is what `Effect4Gen/Main.lean:207-293` reimplements by hand.
The four modules keep their positions in the import graph and shrink to
`deriving instance Canonical for …` lines (Lean's `deriving instance` command exists for
exactly this, `Basic.lean:356-381`), so nothing new enters the `Program` layer's imports. The
acceptance guards (`tools/Effect4Gen/guards/*.lean`) move to `Test/` modules, where they belong.
A trace class prints the derived text on demand
(`set_option trace.Effect4.Deriving.canonical true`), as `Repr.lean:135` does. The axiom
receipts are asked for by name in `Test/Store/`; `Test/Audit/AxiomGate.lean` already audits
`Effect4.*` wholesale, which is stronger than the per-file counting `Driver.lean:243-260` does.

Two design rulings from the scouts (S5 §2.7, S1 §5.2). Do **not** build a generic universe
(codecs and laws once over a description type, one isomorphism per family): the tree's
acceptance evidence is kernel-reduced hex (`tools/Effect4Gen/guards/program.lean:35-43`) and a
universe interpreter puts every golden byte through deep reduction, which is where this estate
has already been bitten. Do build **more combinators of the `guarded` kind**
(`Store/Canonical.lean:261-281`): a `fits` proved once over a described shape deletes the
`lift_*`, `mem_*` and `acceptsFields_cons` scaffolding that is the bulk of the 223 generated
theorems, leaving `toVal`, `ofVal` and one left inverse per type as the irreducible content.
Core's precedent is against proof-producing handlers on mutual and nested inductives
(`LawfulBEq.lean:21-24` refuses both); this handler would do what core declines to, and the
current generated file is the reference it is checked against, family by family.

Prerequisite, the owner's call: `deriving` puts `import Lean` into the audited `Effect4`
closure for the first time (`grep -rln '^import Lean' src/Effect4` is empty). Either the
handler joins the audit ceiling, or the ceiling grows a documented exemption for
elaboration-time code. Until that is decided, Phase 0's gate keeps the generated files honest
and nothing is lost by waiting.

Acceptance: `lake build Effect4` is the gate (a constructor added, reordered or renamed either
derives a different instance and the goldens refuse, or fails to derive); the eight hex goldens
of `Program/Wire.lean:127-147` unchanged; `scripts/check-generated.sh` loses four files.

### Phase 3: one description, as Lean data (with the CAS lane's X2 and commit 7)

The old plan's good idea, in the form the tree already half has. `OCaml5.Eff.World.blocks`
(`World.lean:86-109`) is a hand list of 26 families in 20 groups that EffGen and TsGen both
read; `readBlocks` computes constructors and carriers off the environment (`:172`). Phase 3
makes the computed description a pinned Lean value and the OCaml and TypeScript printers
total functions over it.

| # | step | what it settles |
| --- | --- | --- |
| 3.1 | `Effect4.World` as data: families, constructors, fields, and **per field four verdicts** rather than one reader's opinion: `relevance` (content / erased-prop / erased-type), `framing` (framed / transparent), `carrier` per target, `grouping` (S1 §4.1). The `TypeRef` grammar fixed: `builtin` as an enumerated set with a per-target table, `var` by position, `family`, `carrier`, `arrow`, `erased Reason`; `Param` with universe, binder kind and default (S1 §4.2). Roots named as full Lean names; the frontier rule stated (content families versus parameter families such as `PrimInterp`, `RunInterp`, `Signature`, `Dispatcher`); the collisions decided once (S1 §4.3, §4.4). | the eleven grammar gaps; the ambiguous roots |
| 3.2 | The pin: a `#pin_world` command (or a `MetaM`-built definition plus `#guard`, the pattern of `Test/Store/DerivedCheck.lean:12-22` and `DecEq.mkEnumOfNat`) refuses when the reflected world differs from the committed value. The ledger is **not** a text file: it is this value, and its stored form is M17's node of kind `table` in the CAS (`2026-09-08-cas-amendments.md:30`), written by the CAS lane's own commit. | the M17 contradiction; `eff_manifest.txt` retires when `check_manifest` reads the value |
| 3.3 | The append-only check as a verdict table, run before any file is written (S2 §4.3): constructor or family appended, allowed; field appended, inserted, removed or reframed, refused; constructors or fields swapped, refused; a constructor removed, refused unless tombstoned (M12); a rename, refused without an explicit `was=` row; a kind byte reassigned, refused; `shape` changed, allowed with a warning and only if no framing changes. | what "append-only" means, precisely |
| 3.4 | `Lcnf/Types.lean` reads the same value for its family list and takes its Table R verdict (the compiler's alias) from the world's `framing` column instead of computing it; EffGen's `Emit.lean` and TsGen print from it. Three reflections become one, by making the others read the pinned value, not by deleting readers first. | the merge, safely, because Phase 0's gate says the bytes did not move |
| 3.5 | Machine state joins the roots only after two prerequisites: the `UInt8`/`Bytes` carrier rules for the OCaml-types and TypeScript routes that `Store.Val` needs and that do not exist (S1 D7), and Lean's `Kind` gaining the CAS's kinds 16 to 23 so one table serves both sides (M4 already moves the bound to 23). Then `Canonical` for `RunMachine`, `RunFiber`, `Stores`, `RunDecision`, `RunEvent` is the run-relative wire X2 and CAS commit 7 owe, and `e4_checkpoint.ml`'s pending image encoder is replaced by the printed instance, as its own header commits to (`e4_checkpoint.mli:24-31`). | the old plan's §5, in its right place and its right owner |

Acceptance for Phase 3 as a whole: every golden byte-identical (the 400-program `.eff`
differential, `dune test eff`, the eight hex pins); `scripts/check-generated.sh` green; the
`#pin_world` guard green; one reflection.

### Not in this plan, and why

- **The type split** (old step 2, "functions over shared types"). OCaml has no higher-kinded
  type variables; eight of the hundred generated type declarations mention a carrier; the only
  shape that compiles is a type functor plus a manifest `module type WORLD` signature (a second
  generated artifact of a hundred declarations), every consumer becomes a functor over it, and
  `Api_gen` and `Api_engine` become the same code over two carrier sets, which deletes the
  Gen-versus-Ref arm and with it the only check on the prelude's 33 hand bodies (S3 §2.4). It
  also deletes the property `gen-check.sh` C3b measures (S4 Q4). Dropped.
- **The Lean-side carrier abstraction** ("the architectural fix"). 900 mention sites, 570 of
  them proofs over `List` with standard-library `simp` lemmas that an abstract carrier does not
  have. A wave, scoped as one if ever wanted, and the same change as "one generated engine".
- **`externs.txt` as an attribute.** Blocked by `Attributes.lean:209,285` without editing the
  audited modules; the data-module form of 1.3 buys the same typo-safety.
- **`lake exe gen`.** No executable target exists; `lean_run` over built oleans is what every
  generator uses; a single process would save four environment imports on the Effect4Gen
  route, which Phase 2 deletes anyway. `scripts/generate.sh` is the one command.
- **A `world.ledger` text file.** A format, a parser, a writer and a gate for something the
  tree already pins with `#guard`, and a direct contradiction of M17.
- **Any step on the PC.** `tools/Effect4Gen/Driver.lean` is portable already; `gen-check.sh`'s
  hardcoded path is a three-line fix; `protectNTFS` does not occur in the tree. The `.exe`
  fallbacks in `check-ts-eff-corpus.sh` and `dune-test.sh` are host detection and stay.

## 6. Sequencing against what is in flight

- **The ingest packet** (commits 3 to 5 outstanding): reads `taxonomy.gen.ts`, `forms.gen.ts`,
  `wire.gen.ts`, and commit 3 adds `scripts/check-ingest.sh` to the sweep. Phase 0 touches
  TsGen only for the header line and does so in the same commit as the gate change; Phase 1
  starts after commit 5. Phase 0's step 0.1 must land **before** the packet's next sweep, or
  Codex stops on a red `dune-tests` that is not its own.
- **The CAS lane** (X2, commit 7): owns the `table` node and kinds 16 to 23. Phase 3 is written
  against it and waits for it.
- **The engine lanes**: own Phase 1. Their eleven notes remain the design of record for the
  engine; this plan adds the gate they were missing.
- **The avatar retirement**: rows F1 and F2 of the map hang off it, as do the daemon's
  `e4d_armmap.ml` and `e4d_pins.ml` (`ocaml/server/dune:61-79`) and two sweep rows declared red
  on its account. `docs/GENERATED.md` records those rows with the retirement as their owner;
  no gate is built for an artifact about to be deleted.
- **The two-roots split**: a generator library must not be reachable from `Effect4`
  (`Test/Store/DerivedCheck.lean:21-24` records the same rule). Phase 2 is the one place this
  is tested, and it is why Phase 2 is an owner decision.

## 7. Decisions for the owner

**Decided 2026-09-08, all nine as recommended** (the owner: "ok agreed on all"). In force:
Phase 0 starts today; `import Lean` may enter the audited closure under a written exemption
scoped to the four deriving modules and checked by the library-roots gate; derived proofs are
readable on demand through a trace option, not in the diff; the red OCaml gate is repaired,
not declared; kinds 16 to 23 enter Lean's `Kind` by the CAS lane before the ledger; a fixed
`.eff` oracle subset is committed; Phase 3 stamps are per file; renames are refused without a
`was=` row; `gen-check.sh` and the schema TypeScript gate join the sweep, the structural
assurance gate stays manual with an owner. The questions are kept below as the record of
what was asked.

1. **Phase 0 now?** It is one lane, changes no generated byte except headers, and unblocks the
   ingest packet's sweep. Recommended: yes, today.
2. **`import Lean` in the audited `Effect4` closure**, for Phase 2. The handler is elaboration
   code, not an axiom; the axiom gate would not see it; the library-roots gate would. Either
   admit it under a written exemption or keep the Lean side generated forever. Without a
   ruling, Phase 2 does not start.
3. **Readable derived proofs.** Phase 2 moves the proof text from the diff to a trace option.
   If a reviewer must read `cases a <;> simp […]` in a committed file, Phase 2 costs that.
4. **`dune-tests` red now.** Recommended: repair in 0.1 rather than declare, because the
   repair is five match arms and the declaration would hide the engine's whole test surface.
5. **Kinds 16 to 23 into Lean's `Kind`** before the ledger (Phase 3.5). M4 already moves the
   bound; the constructors are the CAS lane's to add.
6. **Commit a fixed `.eff` oracle subset** (the eight wire-corpus programs plus one per
   constructor of `Eff`, `ActionTerm`, `LayerTerm`, `NativeOp`) so the OCaml side gets the byte
   differential the TypeScript side has and `ServiceName`'s Lean framing is pinned against
   `eff_wire.ml` for the first time (S2 Q5). Cheap; recommended.
7. **Stamp granularity** for Phase 3: per-file `world` digests restricted to the families a
   file covers (recommended; costs a per-file family list) versus one global digest that makes
   every file stale on any world change.
8. **Renames.** Refuse without an explicit `was=` row (recommended), or allow freely since
   bytes carry no names.
9. **The three gates outside the sweep** (`check-schema-typescript-generation.sh`,
   `check-schema-structural-assurance.sh`, `gen-check.sh`): join it, or be recorded as manual
   with an owner in the map.

## 8. What the owner will be able to say afterwards

After Phase 0: "every generated file names its producer, its gate and what it was cut from;
one document lists them all; one command regenerates; one gate refuses a stale or drifted
file; the sweep is honest about the engine." After Phase 1: "the engines are the machine."
After Phase 2: "there is no generated Lean; the instances are derived where the types are
named." After Phase 3: "there is one description of our types, it is a Lean value, it is
pinned, and OCaml and TypeScript are printed from it."
