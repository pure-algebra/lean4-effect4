# S1, stable wire tags: ready packet

Date 2026-09-17. Plan section: `docs/research/2026-09-16-foundational-language-implementation-plan.md` §5, S1. Ruling: DI-79 (both alphabet series run under S1's stable tags).

## 0. The problem

A constructor's number in the canonical bytes was its declaration position. The Lean codec generator wrote the loop counter, the OCaml emitter wrote the list index, the TypeScript writer wrote the list index, and the golden bytes looked the position up in the environment. Four places computed the same number from the same order, so they agreed, and none of them could express a removal. When `Eff.choose` (23) was removed at `75d75fdb`, `provideLayer`, `service` and `provideService` moved down by one and `catchIf` landed on `provideService`'s old 26. Old bytes changed meaning without any check saying so. `make check-compat` has been failing since, first on that removal and then on a source form its layout scraper no longer found.

The `Eff` series retires four constructors and the `Ty` series adds two. Neither can run on positional tags.

## 1. The one assignment

`tools/Effect4Gen/wire-tags.json`, format `effect4-wire-tags-v1`. For each listed family: `active`, the tag of every declared constructor by short name, and `retired`, the tag every retired constructor held. Families are keyed by the inductive's name, also when the carrier is an applied type.

Rules, enforced by every reader:

- The active names of a listed family are exactly its declared constructors.
- Inside one family no tag and no name appears twice across active and retired.
- A retired name is not a declared constructor.
- A structure is never listed. It is constructor 0.
- A family that is not listed carries its declaration positions and has no retired tag.
- Every inductive family of the program world (`Tools.ProgramStructure.blocks`) must be listed. `OCaml5.Eff.World.readBlocks` refuses otherwise.

To add a constructor: the next tag above every active and retired tag of its family. To retire one: move its row from `active` to `retired`, tag unchanged. A tag is never given twice.

S1 lists the 21 inductive families of the program world at their current positions, so no byte moves. `choose` has no retired row, because 23 is `provideLayer`'s today; that history is an exemption in the compatibility policy (§4).

## 2. Declarations

`src/Effect4/Store/Shape.lean`:

```lean
| sum (name : String) (cases : List (String × Nat × List (String × Shape)))
def caseAt (tag : Nat) : List (String × Nat × List (String × Shape)) → Option (String × List (String × Shape))
def caseTags, def distinctNats
def Shape.wellTagged : Shape → Bool      -- mutual with wellTaggedFields, wellTaggedCases
def ShapeDoc.wellTagged (doc : ShapeDoc) : Bool
```

A case is name, tag, fields. `acceptsAt` and `printIn` find a case by `caseAt`, not by list position, so a value carrying a tag no case holds fits nothing and prints by structure. `render` (the spec document) never printed a number and is unchanged. `wellTagged` refuses a sum that gives one tag to two cases.

`src/Effect4/Store/Canonical.lean`: `acceptsAt_sum` and `accepts_sum` take `caseAt i cases = some (caseName, fields)`.

`tools/Tools/WireTags.lean` (new, `import Lean` only): `Assignment`, `parse`, `load`, `tagsOf`, `tagsIn`, `requireListed`, `requireKnown`. The one Lean loader.

`tools/Effect4Gen/Main.lean`: `CtorInfo.tag`; `buildItem` takes the assignment; `toVal`, `raw`/`ofVal`, the `fits` heads and the shape's cases write `c.tag`; each item ends with `#guard wellTaggedFields defs` or `#guard shapeDoc.wellTagged`. `tools/Effect4Gen/Check.lean`: `Case.tag`; the expected tag is the assignment's, the shape's stated tag and the `toVal` clause's number are both held to it. The driver is unchanged, so a new manifest group needs no code.

`src/OCaml5/Eff/World.lean`: `Ctor.tag`. `Emit.lean`: the encoder and decoder arms use `c.tag`; `Eff_types` gains `wire_tag_<t>` beside `ctor_index_<t>`, which stays the compiled position. `EffGen.lean`: the golden-byte lookup is by tag; `eff_layout.ml` gains `wire_tags`. `EffWire.lean`: writes `ocaml/goldens/eff/wire-tags.txt` from the derived shape documents, which is what the Lean codec does, not what the file says. `tools/Tools/TsGen.lean`: `w.ctor(tag, …)`, and `w.cons` takes the two tags of a cons list.

Kept apart on purpose: `tools/Conform/Source/Description.lean` (`Ctor.index := ci.cidx`), `scripts/lib/program_structure.py`, `ocaml/eff/eff_manifest.txt` and the engine's `ctor_index_*` keep reading the declaration, since the compiled layout follows it.

## 3. Controls

- `Shape.lean`: a sparse document (`a=0`, `b=2`, `c=5`): held tags accept, the hole and the dense position refuse at the root and nested, the printer names by tag, a repeated tag is invalid at the root, in a definition and under a list.
- `tools/Effect4Gen/guards/program.lean`, `WireTagAcceptance`: tags 29 and 255 of `Eff` refuse at the root and nested under `bind`, in the value tree, in the bytes and in the shape. A retirement adds its tag to `unheld`.
- `ocaml/eff/test/test_lean_wire.ml`, L1b: every line of `wire-tags.txt` equals `Eff_layout.wire_tags`, and no family repeats a tag.
- `scripts/test-program-structure.py`: a sparse tag in place of the declaration position is refused.
- `scripts/test-compatibility.py`: 17 tests (§4).

## 4. Compatibility

Snapshot format `effect4-compatibility-snapshot-v2` adds `tag` per constructor and `retired` per family. The retained `66ee4657-supplement-v1` stays in the first format, where a tag is the ordinal. `compare` works by tag and name:

- a retained constructor keeps name, tag and fields (`changed wire tag`, `changed payload or field shape`);
- a constructor leaves only by retirement at its own tag, named in `constructor_retirements` (`removed constructor`, `retired at tag …`, `undeclared retirement`);
- a new constructor is named in `constructor_additions` and takes a tag nobody held (`reused wire tag`);
- a retired row never drops, changes or comes back (`retired row dropped or changed`, `retired constructor declared again`);
- a new reached family and a new consumer selection are named (`family_additions`, `consumer_additions`); consumer selections compare as sets, since list order moves no byte;
- `historical_renumbering` names, for one family, exactly the removals, moves and reuses of a past event with its commit and reason; every row must match and an unmatched row fails;
- every permission must be used; an unknown field or a malformed row raises.

`retained_vectors` holds the `.hex` and `.bin` rows of `66ee4657/golden-digests.sha256` to their digests; `vector_removals` and `vector_migrations` name the exceptions, and a named vector that is present and unchanged is stale. The other rows of that listing are printed JSON and typing verdicts, not byte vectors.

The named policy is `Test/fixtures/baseline/66ee4657-supplement-v1.policy.json`: six additions (`catchIf`, `select`, `iterate`, `Ty.lit`, `Err.text`, `Defect.error`), one family (`Decision`), 21 consumer additions, the `choose` exemption, one removed vector (`pChoose.bin`) and three migrated (`pDiamond.bin`, `pMergeAll.bin`, `pProvide.bin`). No constructor's fields changed since the baseline.

The layout reader now finds the family selection in `tools/Tools/ProgramStructure.lean` and falls back to the old source forms for an old revision; a manifest group with its own `Tool` writes no codec and is not a consumer.

Promotion: `promote --work W --destination Test/fixtures/baseline/<name> --name <name>`. The name is eight revision digits and hyphenated words and begins with the revision's digits; the directory carries it; the origin is a full commit identity that still resolves to itself; a working-tree capture refuses; an existing directory and `66ee4657` refuse. The retained inventory's constructor names are required only of the original revision. Promotion stays a named owner act; nothing here promotes.

`make check-compat` runs the self-tests, captures the working tree, reflects (Lake, in a temporary checkout), compares under the policy with the vectors, and prints a summary.

The frozen README of `66ee4657-supplement-v1` still shows the old `constructor_appends` policy spelling. It is a retained fixture and is not edited; the policy file's own comment is the current reference.

## 5. Gates

`make gen-hermetic`, `make gen-lcnf`, `make check`, `make check-ocaml`, `make check-compat`. No file under `ocaml/goldens/eff/*.hex` or `ocaml/eff/goldens/` may change.

## Landed (2026-09-17)

As written above. Generated files that moved: the five codec modules (cases carry tags, one `wellTagged` guard per item, `WireTagAcceptance` appended to `Program/Derived.lean`), `ocaml/eff/eff_types.ml` (`wire_tag_*`), `eff_layout.ml` (`wire_tags`), `eff_wire.ml` (header text only), `ts/eff/wire.gen.ts` (`cons` takes its tags), and the new `ocaml/goldens/eff/wire-tags.txt`. No golden byte changed: the eight `.hex` and every `.bin` are identical, and the LCNF outputs are identical.

Gates: `make check` green (358 modules and 56381 declarations at `[propext, Quot.sound]`, the `Classical.choice` boundary 3 modules and 29 declarations; check-gen clean; conform cases and native pass; the reader matches 416 of 416 with 21 accepted and 7 refused without an oracle; 390 bun tests). `make check-ocaml` green (`test_eff` 451 checks, `test_lean_wire` 117 checks of which 43 are L1b, engine and gen-check pass). `make check-compat` green for the first time since `75d75fdb`: 33 named structural changes, 0 errors; 46 vectors unchanged, 4 named. `make check-tools`: its first step, `scripts/test-trust-gate.sh`, fails on `Test/fixtures/trust-gate/expr-equality.lean.txt` (a fixture of 2026-09-04 that passes a `String` where the pinned `typescript` package now wants a `TypeRef`); that is older than this slice and not touched by it. The lane's other six steps pass when run one by one.

Not verified: a real promotion (it needs a committed revision and is the owner's act); the refusals are self-tested, and the named-revision extraction was run to a snapshot without promoting. The host lanes other than `check-ocaml` were not run for this slice.

For the second lane (branch `player/bytes-boundary`): a family that is not listed keeps its positions; a new manifest group needs no driver change; families are keyed by the inductive's name, applied or not.
