# Seat S, type-language probe (2026-10-01): the Schema side per form, and the readable profile

Written incrementally by seat S in `/Users/pooks/Dev/lean4-effect4-probe-S`, branch `probe/S`,
base `bff50631`. Brief: `docs/research/2026-10-01-type-language-probe/brief-S.md`; rules:
`README.md` beside it. Status of each section is stated where it is written; the receipt at the
foot is complete at the commit that adds it.

## The one thing

**The Schema side of every form the data wave adds is done on a copy and measured, and W1 must
choose its exactness route before it starts.** The Schema pair's retraction
(`ofSchema (schema t) = t`) is proved at every form (records, optional keys, maps, tagged unions,
`nat`/`int`, and seat T's tuple, `app`, `null`, `undefined`, `number`, `bytes`), and the codec's
laws (`decode_of_encode`, `hasTy_decode`, `encode_injective`, `encode_sub` from P's `hasTy_sub`) at
every form it takes (records over row 165's named values, optional keys, maps, tuples, `int`); the
production-shaped patch is +764/−142 lines in three files. But exactness, row 128's ruled theorem
and W1's purpose, is proved here only **through a guard** (the reader re-encodes its answer and
compares modulo `N_J`/`N_S`: one extra encode per read); exactness of the plain readers **by
construction** is tested on the 23 inputs where the guard was compared (it never fires) and not
proved. W1 can aim for the second and land the first if it does not close (§7.1 item 3).

Then, in order of what they change:

1. **A defect in today's tree, for W1** (§4, §6.1 S-B): `Bridge.defectRep` names
   `effect/schema/Defect`, a declaration rc.112 never writes (its `Schema.Defect()` persists as
   `effect/schema/Json`), so Lean's `Exit`/`Cause` documents and rc.112's do not read each other
   (tested both ways). Two lines; nothing pins the id.
2. **Row 122's `codec_sub_adapt` is false at unions** (§1.2): where an earlier branch's adapter
   accepts a later branch's exact image, the adapter answers the earlier branch, as rc.112's
   default `anyOf` does (tested). Tagged unions with distinct tags meet the premise it needs.
3. **The canonical-branch check is still needed after row 165** (§1.2): named record values remove
   the record/record and record/`Result` overlaps, not `Result`/`Exit` or `Int`'s `ctor` image.
4. **The Lean readable profile is the printer; rc.112's `toCodeDocument` is only an oracle** (§4): the
   upstream route drops every `__proto__` field while tsgo accepts its types, and prints an `Exit`
   type tsgo rejects (TS2707); the Lean route is faithful on all 23 documents both emit, at half
   the size.
5. **Two number findings** (§6.1 S-A, §6.2 row 121): rc.112's own `Schema.Int` carries an
   `arbitrary` annotation the eight-key allowlist refuses (a ninth key proposed), and the codec's
   `nat` accepts 2^53, which the `isInt` check Lean writes refuses in rc.112 (the safe-integer
   bound proposed).
6. **Row 8's (C)** moves no committed artefact and makes the meta-schema module compile under tsgo
   7 (22 TS1117 to none), with a located refusal for a conflicting repeat (§5).

Merging `probe/S` adds only this folder (tested; receipt).

## 0. Base, tools, evidence words

- **Base.** `probe/S` at `bff50631`, `git status` clean at the start (tested). No tracked file is
  edited; everything this seat writes is under `docs/research/2026-10-01-type-language-probe/S/`.
- **Evidence words.** **proved**: a kernel theorem in a probe here, axioms printed at
  `[propext, Quot.sound]` or less. **tested**: a finite check run here (a `#guard`, a `bun` or
  `tsgo` run, a `git`/`grep` command), with its log. **reading**: read in code or notes, not run.
  **assumed**: not checked. Every Lean check is a finite probe; a model theorem is about the copy,
  not the tree.
- **Host tools** (tested, `S/host/logs/*.log` head each run with the versions): `bun 1.4.2`;
  `tsgo` 7.0.0-dev.20260629.1 at `/opt/homebrew/bin/tsgo` (the coordinator's rule of 2026-10-01:
  tsgo 7 is the one TypeScript compiler; nothing here ran TypeScript 5.9 or `tsc`); `node v22.23.2`.
  - `bun` runs the **vendored** rc.112 source: `S/host/tsconfig.json` maps `effect/*` to
    `vendor/effect-4.0.0-rc.112/src/*.ts`, and `import.meta.resolve("effect/Schema")` answers the
    worktree's vendored `Schema.ts` (tested, `S/host/smoke.ts`).
  - `tsgo` type-checks against the installed rc.112 declarations (`S/host/tsconfig.tsgo.json`,
    `S/host/node_modules` a symlink to the main checkout's `ts/eff/node_modules`, not committed):
    type-checking the vendored sources directly under the harness flags fails inside effect's own
    files (`noUncheckedIndexedAccess`; tested, first smoke run), so the declarations are used, as
    the schema harness does. The installed `effect/src` matches all 452 lines of
    `vendor/effect-4.0.0-rc.112/SHA256SUMS` (tested, `shasum -a 256 -c`), and so does the
    worktree's vendored copy.

## 2. Question 2: rc.112's own behaviour at the edges (tested)

**Status: done.** `S/host/q2-edges.ts` (86 checks, `bun run`, vendored rc.112): exit 0,
`logs/q2-edges.log`. Its red twin `q2-edges-red.ts` flips one expectation (E1b) and exits 1 with
exactly that check failing, `logs/q2-edges-red.log`. The first run (`q2-edges.run1-wrong-expectations.ts`,
kept as written, `logs/q2-edges.run1-wrong-expectations.log`, exit 1, 4 failures) caught four
wrong expectations of this seat's; each became a finding below (E4k, E7g, E9d, E10d). The
types half, `q2-types.ts` (`tsgo -p tsconfig.q2.json`): exit 0, 18 exact-type assertions and 8
rejecting `@ts-expect-error` controls; its red twin `q2-types-red.ts` (two false exact-type
claims) exits 1 with TS2344 at both, `logs/q2-types{,-red}.log`. Every persisted document the
checks read is printed as a `REPR` line in `logs/q2-edges.log`.

| Id | rc.112 at the pin (all **tested**) | What it means for the arms |
| --- | --- | --- |
| E1–E2 | `Struct({a,b})` accepts `{b, a}` and answers in declaration order; `Struct({b,a})` persists its properties in declaration order, so the two documents differ (`SchemaAST.struct` reads `Reflect.ownKeys`, `SchemaAST.ts:2520-2533`) | property order is content in rc.112's document: `N_S` must sort properties, and the readable emission writes the canonical order |
| E3 | default `onExcessProperty` strips an extra key; `"error"` refuses it; `"preserve"` keeps it; a missing key refuses | the Lean codec is the `"error"` mode (S-3 contract); the boundary adapter is the default mode |
| E4 | `optionalKey(A)`: `{}` accepted, `{a: undefined}` and `{a: null}` refused; persisted `isOptional: true` over `A`. `optional(A)`: `{a: undefined}` accepted and **kept as an own key**, `null` refused; persisted `isOptional: true` over `Union[A, Undefined]`. Under `toCodecJson`, `optional` **writes an explicit `undefined` as JSON `null` and reads `null` back as `undefined`**; `optionalKey` refuses `null`; an absent key stays absent in both (E4j–E4o, found by run 1). Types: `{ readonly a?: number }` against `{ readonly a?: number \| undefined }` | `optional` has a three-state slot (absent, `undefined`, value) and a JSON image (`null`) that `Ty` has no value for; the profile admits `optionalKey` and refuses `optional` by name |
| E5 | `mutableKey` persists `isMutable: true` and decodes like the plain field; `optionalKey(mutableKey(_))` and `mutableKey(optionalKey(_))` persist the same document; the type drops `readonly` | `Ty` records are readonly: `ofSchema` refuses `isMutable` by name; the readable emission preserves it as `Schema.mutableKey` |
| E6 | `Record(String, Number)` persists one index signature and no property; its output keeps the input's key order except that integer-like keys come first in ascending numeric order; JSON text with a repeated key decodes the last occurrence (at `JSON.parse`); `Record(Literals([a,b]), _)` persists two **required properties**, a struct, not a map; `Record(Number, _)` drops a non-numeric key, and keeps dropping it under `onExcessProperty: "error"` (the excess check runs only when the node has no index signature, `SchemaAST.ts:2261`) | a map is an index signature over `String`; a literal-keyed `Record` is a record; the strict codec's refusal of a repeated key is stricter than rc.112 on text |
| E7 | `Union([TaggedStruct A, TaggedStruct B])` selects by `_tag`; `TaggedStruct` persists `_tag` first, a `Literal`; `toTaggedUnion("_tag")` and `TaggedUnion({…})` persist the **same document** as the plain union and add guards; `toTaggedUnion` **throws on two members with one tag** while a plain `Union` of them is accepted (found by run 1); `anyOf` answers the first member that succeeds (stripping the other's keys), `oneOf` refuses a double success; `Schema.Union(a, b)` throws, the call shape is `Union([a, b])` | a tagged union needs no node of its own; distinct tags are a formation rule the target already enforces at `toTaggedUnion` |
| E8 | `Struct({["__proto__"]: N})` (computed) keeps the property and decodes an own `__proto__`; `Struct({"__proto__": N})` (quoted, the upstream `toCodeDocument` spelling) **has no property**, accepts `{}`, and tsgo still types it `{ readonly "__proto__": number }` (`q2-proto-quoted.ts`, exit 0); `Object.fromEntries` keeps the property but its `Type` loses the field list (`entries1: typeof ENTRIES.Type = {}` type-checks); an unquoted `a-b` is a `SyntaxError`; Unicode keys, `constructor`, `toString` and `""` are ordinary own properties (inherited members are not read: `Struct({constructor: Unknown})` refuses `{}` with "Missing key"); integer-like names lead in numeric order (`["9","10","b","01","a"]`), `"01"` is not integer-like | the readable emission spells `__proto__` computed, a non-identifier quoted, an identifier bare; never `Object.fromEntries` (types) and never a quoted `__proto__` (run time) |
| E9 | `Number.check(isInt(), isGreaterThanOrEqualTo(0))`, the chained spelling and `Schema.Natural` persist one document; `Number.check(isInt())` persists as `Schema.Int`; the persisted `isInt` filter carries `{expected, arbitrary}` and `isGreaterThanOrEqualTo(0)` `{expected}` (found by run 1); `isInt` is `Number.isSafeInteger` (`Schema.ts:8298-8316`): **2^53 refused**, 2^53 − 1 accepted; `Natural` **accepts −0** and keeps the sign; `Int` accepts −15, refuses 1.5, NaN, ±Infinity and `"42"`; plain `Number` admits NaN and 1.5 and `toCodecJson` writes NaN as `"NaN"` | the checks `Bridge.schema` writes are exactly `Schema.Int`/`Schema.Natural` modulo the filters' annotations; the Lean codec's `nat` domain and rc.112's checks disagree at both edges (Lean accepts 2^53, refuses −0: §1) |
| E10 | `Tuple([String])` persists one element and no rest, `Array(String)` no element and one rest; the tuple refuses `[]`; `Literals([a,b,c])` persists a flat three-member union; a nested `anyOf` union persists nested and accepts the same values as the flat one | a tuple is not an array; `ofSchema` must read an n-ary union (today it reads exactly two members) |

**Codex's four host probes, reproduced** (tested, copies under `S/host/codex/` with their SHA-256
equal to the originals, `logs/codex-copies.sha256`): `runtime.mjs` and `reuse.mjs` under `bun`
on the vendored source give byte-identical output to Codex's `runtime.log` and `reuse.log`
(`diff`, tested); `inference.ts` passes `tsgo` (exit 0) and `inference-red.ts` fails with the same
`TS2344` at `(6,44)` (exit 1). Codex ran these under TypeScript 5.9.2 and node; this rerun is
tsgo 7.0.0-dev.20260629.1 and bun 1.4.2 against the vendored source, with the same results.

## 3a. Revision 5 of the Schema scouting, reproduced once (tested)

**Status: done.** The amended brief (main `44a8551c`) makes revision 5 the input. Its files were
copied from `S-inputs/revision-5/` into `S/rev5/` (SHA-256 checked against its `inputs.json`;
`DefinitiveSchemaAudit.lean` rebuilt as `DefinitiveSchemaProbe.lean` + `ExtraSchemaChecks.txt`
exactly as its `verify-lean.py` does, `cmp` equal to the copied audit). This seat had written
nothing on the readable profile before the amendment; question 2's host work (§2) is independent
of the scouting and stands. **Revision-1 work repeated** before the amendment: Codex's four host
probes (`runtime.mjs`, `reuse.mjs`, `inference.ts`, `inference-red.ts`; §2's last paragraph),
reproduced under bun and tsgo 7. Kept: question 4 extends `reuse.mjs`, and the rerun is on the one
compiler.

| Run | Command | Result |
| --- | --- | --- |
| Lean, the readable fold and its audit | `probes/compile.sh rev5/DefinitiveSchemaAudit.lean rev5-schema` (`lake env lean -M6144 -DwarningAsError=true`, one thread) | exit 0, 6 s; the log body is byte-identical to revision 5's `schema.log` (`diff`, tested): 13 axiom lines, every one `[propext]` (`validateAnnotations`, `validateFilter`, `processProperties`, `toReadableSchema`, and the six reviewer equations `child_error_preserved`, `empty_children_normalized`, `nonempty_children_refused`, `duplicate_refused`, `semantic_object_annotation_refused`, `check_disabling_annotation_refused`), then the 19 `EXPR_` lines |
| Lean, the constructive key order | `probes/compile.sh rev5/ConstructiveProjectionProbe.lean rev5-projection` | exit 0; byte-identical to `projection.log`: `stringLt` and `insertSorted_mapPayload` no axioms; `typeCheck`, `eval`, `sortFields_mapPayload` `[propext]` |
| Lean, the whole-union image | `probes/compile.sh rev5/UnionImageProbe.lean rev5-union` | exit 0, no output (guards only), as revision 5 recorded |
| bun, the host harness | `cd rev5 && bun run runtime.mjs` (bun 1.4.2, **vendored** rc.112 through `tsconfig.json` paths; revision 5 ran node on the installed package) | exit 0; output byte-identical to revision 5's `runtime.log` (`diff`): the numeric controls, the nested, modifier, escape, tuple, array and union controls, and **144** annotation comparisons; the regenerated `generated.ts`, `expressions.json` and `duplicate-red.ts` are `cmp`-equal to revision 5's |
| tsgo, the type controls | `tsgo -p rev5/tsconfig.green.json` and `-p rev5/tsconfig.red.json` (tsgo 7.0.0-dev.20260629.1, `/opt/homebrew/bin/tsgo`) | green exit 0 (`inference.ts`: seven exact-type assertions and five rejecting controls on the generated module); red exit 1 with `TS1117` at `duplicate-red.ts(3,53)`. Revision 5 ran these on TypeScript 5.9.2 (`host-pins.json`); that run is history, this one is the evidence |

So the reviewed slice holds on this base under the one compiler: located refusals before
emission, the eight-key documentation allowlist (`identifier`, `title`, `description`,
`documentation`, `examples`, `default`, `message`, `expected`) erased under the observation
"structural type, acceptance and decoded value", behaviour-changing annotations (`parseOptions`,
any unknown key, `brands`) refused by name, the tuple/array distinction, the array call shape of
`Union`, `mutableKey` kept, duplicate fields refused before TS1117. What it does not do, and this
seat adds (§3): maps (`Record`), the computed `__proto__` spelling (revision 5 refuses
`__proto__`), identifier spelling for ordinary names, literal unions as `Schema.Literals`, and the
tie from each new `Ty` form's `schema` arm to its readable text.

## 1. Question 1: the K2 arms per form, on a copy (proved and tested)

**Status: done, with seat T's forms added** (the coordinator's message after T merged at main
`8036f0b4`). The copy is `S/probes/K2Copy.lean` (1,992 lines, `wc -l`): `PTy` is `Ty`'s twenty
constructors in order, then `record (fields : List (String × PTy))` (row 119's text, the same as
seat P's brief), `optKey (inner : PTy)` (stage 4's modifier, legal only as a record field's type,
so the record constructor's text stays row 119's: `(n, optKey τ)` is seat P's current
`(n, true, τ)`, `record (fields : List (String × Bool × Ty))` on `probe/P` (reading), and T §2.1's
"a field list that carries optionality" is either), `map (key value : PTy)` (row 125),
then seat T's §2.1 texts: `tuple (items : List PTy)`, `app (name : String) (args : List PTy)`,
`null`, `undefined`, `number`, `bytes`. Tagged unions are unions of records (stage 2). `int` is
inhabited by `Int`'s generated image (`Store/Domain/Canonical.lean:361-363`; stage 5). The value
encodings are assumed, seats P and R own them: **a record is `ctor 0 [list names, list slots]`,
both in canonical order** (probe R's row 165, recorded at main `e4481483` and ruled by the owner
at `2bf570ca`: the coordinator's message asked this seat to state the codec over it and to keep
row 119's positional `ctor 0 slots` only as a red control), an optional slot is `none`/`some v`, a
map is a list of `[key, value]` pairs ascending by key, a tuple is `Val.list` of its items (as `prod`), `bytes` the existing `Val.bytes`; `null`,
`undefined`, `number` and `app` have no value image here (owed, below).
`probes/compile.sh probes/K2Copy.lean k2copy` (`lake env lean -M6144 -DwarningAsError=true`, one
thread): exit 0, 6 s, `logs/k2copy.log`; 118 `#guard`s hold, 10 red controls fail as their
`#guard_msgs (error)` asserts (`grep -c` over the probe: 128 `#guard` lines, 10 under
`#guard_msgs (error)`); **all 43 theorems print `[propext, Quot.sound]`, `[propext]` or no
axioms** (the log's 43 lines). Runs 1–19 (`logs/k2copy.run*.log`) are the compile history:
parse errors (a docstring before `mutual`, `mut` is a keyword), unqualified names, a kernel
rejection of a defeq-only `exact` (repaired by reducing the match first), unused `simp`
arguments, the `do`-block bind that had to be unfolded before `firstRepeat` could be rewritten.

### 1.1 The per-form K2 table

Lines: the copy's per-form floor (`probes/count-arms.py`, `logs/count-arms.log`: the lines each
`-- [arm:…]` marker covers; definitions only, proofs not counted), then the measured patch
against the production file (§1.3).

| Form | `schema` arm | `ofSchema` admits (exact shape) | located refusals (path, reason) | codec layout | laws on the copy | lines (copy floor) |
| --- | --- | --- | --- | --- | --- | --- |
| record | `.objects none [] props []`, one property per field in the type's order (`Ty.schema` normalizes first, so canonical), `isOptional := false`, `isMutable := false`, no annotations, no checks | `.objects a [] ps []` with every name `.string`, no `isMutable`, documentation-only annotations on the node and each property; read in written order | a repeated name at `[n]` (`repeatedField`); `mutableKey` at `[n]`; a numeric key at `[]`; a symbol key at `[k]`; a non-documentation annotation at `[annotations]` or `[n, annotations]`; a property type's refusal under `[n, …]`; index signatures beside properties at `[indexSignatures]` | value `ctor 0 [list names, list slots]` (row 165). Encode: a JSON object whose keys are read from the value's name list (each checked against the type's), entries in canonical (UTF-8 byte) order, an absent optional key writing nothing; decode (`strict`): the exact field set in any order, refusing an unnamed key, a repeated key, a missing required key, and writing the canonical names with the slots, whatever the type's written order. Route A's adapter (`!strict`, row 122): the same fold with undeclared entries dropped | retraction `ofSchemaL_schema` **proved**; exactness modulo `N_S` **proved** for the guarded read, the unguarded read equal to it on 15 inputs (**tested**); `decode_of_encode`, `hasTy_decode`, `encode_injective` **proved**; `encode_sub` **proved** from `hasTy_sub` (seat P's law at records); `adapt_member` **proved**; probe R's paired control **tested** | 83 |
| optional key | inside a record: `isOptional := true` over the inner schema (rc.112 `Schema.optionalKey`) | `isOptional = true` reads as `optKey (read type)`; never read at the top; rc.112's `Schema.optional(A)` (`Union[A, Undefined]`, question 2 E4) reads as the three-state `optKey (union A undefined)` once the `undefined` leaf lands (without it: refused at `[n, types[1]]`) | as records | an absent key is a `none` slot, a present one `some v`; `null` refuses (rc.112's `optional` writes `null` for an explicit `undefined`, E4k): the `undefined` slot has no JSON image until its value image is ruled | as records (the field-mode half of the retraction's motive) | 22 |
| map (`string` keys) | `.objects none [] [] [⟨schema k, schema v⟩]` (rc.112 `Schema.Record(K, V)`) | exactly one index signature whose parameter is `.string a []` (documentation annotations only), no property | any other parameter (`Number`, `Symbol`, a checked string, a template literal, a union) at `[indexSignatures[0], parameter]` (row 125); a literal-keyed `Record` is a struct and reads as a **record** (E6g) | encode: an object keyed by the map's keys in the value's order (membership requires ascending); decode: refuses a repeated key (rc.112's text route keeps the last, E6c), sorts the pairs by key bytes | as records | 27 |
| tagged union | no new arm: a union of records with a `_tag` literal field; `union` stays binary, so a three-case union is written nested | an n-ary `anyOf` union of ≥ 2 members, read right-nested (today `ofSchema` reads exactly two: effect Red7, re-tested here); a nullary store sum reads as a literal union | `oneOf` at `[]`; one or zero members at `[]`; a member's refusal at `[types[i], …]` | the encoder takes the first branch whose membership holds; the decoder takes a later branch only when no earlier branch's membership holds of its value (**the canonical-branch check**, row 128) | as above; the nested writer and rc.112's flat `Literals`/`TaggedUnion` agree modulo `N_S`'s spine step (**tested**) | 10 (`n-ary-union`) + 4 (`canonical-branch`) |
| number / `int` | unchanged: `int` → `.number none [isInt]`, `nat` → `[isInt, isGreaterThanOrEqualTo 0]`; T's `number` leaf → `.number none []` | the **whole** check: the `isInt` filter with payload `null`, no `schemas`, not aborted, documentation annotations only (rc.112's own `Schema.Int` persists `expected` and `arbitrary`, E9d); `[isInt, ≥ +0]` reads `nat`; plain `Schema.Number` reads `number` (if row 121 rules binary64; refused by name until then) | `≥ 5` at `[checks[1]]` (today read as `nat`: red control on production); a filter group, an aborted filter, a `parseOptions` filter at `[checks[0]]`; the template parameter's declaration at `[]` (the `var` repair; today read as a handle: red control) | `int` (stage 5): exact signed integral binary64 (`intJson`, `int?`); **refuses −0, which rc.112's `isInt` accepts (E9g), and accepts 2^53, which rc.112's `isInt` refuses (E9e); production `decode .nat` accepts 2^53 today (tested on the production function)**. `number`: **owed**, obstacle: no binary64 `Val` frame (T's commit 3); its JSON writes non-finite values as `"NaN"`, `"Infinity"`, `"-Infinity"` (E9l) | as above (retraction at `number` **proved**) | 20 (`int`) + 15 (`whole-check`) + 3 (`number`) + 2 (`var`) |
| tuple (T) | `.arrays none [] (plain elements) []` (`Schema.Tuple([…])`); arity two is `prod` (T's normal form) | any arity's plain elements, documentation annotations only, no rest; two plain elements read `prod` | an optional element at `[elements[i]]` | an array of the items, exact arity; a list beside a tuple at a union is told apart by arity (tested both orders) | retraction **proved** (`readElems_schemaElems`; formation: arity ≠ 2) | 49 |
| nominal reference `app` (T) | `.declaration ⟨name, .null⟩ none (schema args) []`; `app t []` is `handle t` (T's normal form) | a declaration whose id is not reserved, with ≥ 1 type parameter, payload `null`; the reserved ids (`Option`, `Ref`, `Result`, `Fiber`, `Deferred`, `Cause`, `Exit`, `TypeParameter`, `Uint8Array`) read as their constructors | an argument's refusal at `[typeParameters[i], …]`; a reserved id at an arity it does not take at `[]` | **owed**: a declaration's codec is a host reviver; the codec refuses `app` by name (`isSupported`) | retraction **proved** (`readArgs_schemaList`; formation: args non-empty, name not reserved) | 19 + 8 (`declarations`) |
| `null`, `undefined` (T) | `.null none []`, `.undefined none []` | the nodes with documentation annotations only | — | **owed**, obstacle: the value images (P, with the optional-key policy): JSON `null` is already `unit`'s image (`Codec.lean:154`) and rc.112's `toCodecJson(optional)` writes an explicit `undefined` as `null` (E4k), so both leaves collide at `null` in a union | retraction **proved** | 4 + 3 |
| `bytes` (T) | `.declaration ⟨"effect/schema/Uint8Array", .null⟩ none [] []` (`Schema.ts:13605-13621`) | that declaration with no parameter (the name leaves `handle`, as `TypeParameter` does) | — | **owed**, obstacle: rc.112's JSON is a base64 string (`toCodecJson` → `Base64String`, `Schema.ts:13615-13619`) and the tree has no base64 codec (`git grep -il base64 -- src tools`: none) | retraction **proved**; membership is `Val.bytes` | 5 |

The writer-side normaliser is a fold: `N_S := cata_representation nsAlg` (`K2Copy.lean`, §6),
erasing every annotation bag and flattening an `anyOf` union's right spine; the JSON one is `NJ`
(§11), a stable key sort. **The level of the statement matters** (tested): the copy's `schema`
writes a record's fields in the type's own order and its reader keeps the written order (the
bridge level: `Bridge.schema`, `Bridge.ofSchema`, raw types, where today's `ofSchema_schema`
lives), so `N_S` needs no property sort and a permuted struct reads and writes back permuted.
The public writer `Ty.schema` normalizes first (`Bridge.lean:243-244`) and writes the canonical
order whatever the document's, while rc.112 persists declaration order (question 2 E1–E2): a
statement against it would need `N_Sp` (the copy's `nsAlg` with a stable, non-deduplicating
property sort; it identifies rc.112's `Struct({ b, a })` with the canonical writing, and the red
control `red_unsortedNS` records that `N_S` does not) **and** a reordering of union members,
which rc.112's ordered `anyOf` observes at overlapping members (E7). So the exactness theorem
belongs at the bridge level, as W1's draft states it ("beside `ofSchema_schema`"); the public
pair is exact on canonical types through `normalize`, which the vocabulary should say. Exactness is proved by the guard (probe C's route, the formal pass's
TY-09 route 1): `ofSchemaExact_exact`, `decodeExactP_exact`, with the retraction kept
(`ofSchemaExact_schema`, `decodeExactP_retract`). Exactness **by construction** (route 2: the
readers themselves answer only images) is **tested** on the 15 bridge inputs and 8 codec inputs
above (the guard never fires on them) and **not proved**: it is an induction over
`Representation` and over `PTy` with the nested lists, owed by the data wave's commit 1/5 (its
shape is §1.4's).

### 1.2 Row 128 at the new forms: do a record and a tagged union share an image?

**Under row 119's positional clause, yes; under row 165's named clause, no** (tested,
`K2Copy.lean` §13 (ii)–(v), §13b, §14). Positional values carry no names, so
`ctor 0 [str "A", nat 1]` is a member of the tagged case `record [(_tag, lit "A"), (x, nat)]` and
of the plain `record [(a, string), (b, nat)]` (`posRecordFits`, kept only for the red control
`red_sharedImage`), and a one-field record's `ctor 0 [v]` is also `Result`'s failure and `Exit`'s
success. With the names in the value (`ctor 0 [list names, list slots]`) the two record values
differ, a record never has `ctor 0`'s one-argument shape, and the tested unions of a tagged case
with a plain record, and of a one-field record with `Result` in both orders, decode **both**
images exactly (each its own branch; tested).

What remains is the check row 128 asks for, at the overlaps the named clause does not remove:

```lean
| .union a b, j =>
  match (conv strict a j).filter (fun v => Val.hasTy v a) with
  | some v => some v
  | none => (conv strict b j).filter (fun v => Val.hasTy v b && !Val.hasTy v a)
```

the encoder's own selection rule in the reader (a later branch answers only when no earlier
branch's membership holds of its value; at records the membership compares the name lists
first, so a record branch costs one list comparison). It excludes row 128's own witness at
`union (except nat nat) (exitOf nat nat)` (production decodes the `Success` image: red control
`red_productionExact`; the copy refuses it), and `union int (except nat nat)`, where a `Result`
failure is **outside the union's image** because `Int`'s generated image `ctor 0 [nat n]`
overlaps it (an argument for row 121's signed `Val` frame over the `ctor` image). The converse,
one JSON image with two values (`{"_tag":"Success","value":1}` for `exitOf nat nat`'s success and
for `record [(_tag, lit "Success"), (value, nat)]`), is the S-3 contract's existing clause: the
encoder refuses the second value (tested). With the check, every tested positive input decodes to
a value whose encoding is the input modulo `N_J`.

**Route A's row adapter, against probe R's** (row 122; R's `Boundary.adapt`, `Q4Boundary.lean`).
The copy's reader is one fold with R's one parameter (`convP strict`): `strict` is the codec,
`!strict` drops the entries the type does not name and still refuses a missing or duplicated
declared name. `adapt_memberP` (**proved**) is R's `adapt_member`; R's paired control holds
(**tested**: the adapter strips `role` from `{"id":2,"name":"bob","role":"member"}`, the codec
refuses it; a duplicated undeclared key is dropped by one and refused by the other; a wider object
nested inside a record is stripped and refused at depth; both refuse a missing and a duplicated
declared key), and R's `codec_sub_adapt` holds on every union-free positive input (**tested**).
**It does not hold at a union whose earlier branch names a subset of a later one's** (tested,
red control `red_codecSubAdaptUnion`): at `union (record [a]) (record [a, b])` the JSON
`{"a":1,"b":2}` is the later branch's exact image, so the codec answers `{a, b}`, while the
adapter strips `b` into the earlier branch and answers `{a}`, which is what rc.112's default
`anyOf` does (question 2 E7h). R's model has no union, so its theorem stands there; the
production statement needs a premise (no earlier branch's adapter accepts a later branch's exact
image; sufficient: tagged unions with distinct tags, whose tag literal refuses the other branch,
or record branches none of whose name sets is included in a later branch's) or an adapter that
tries the strict reading of every branch before projecting.
The owner's choice; this seat recommends the premise, stated as a formation check on a row's
answer type, because the second option makes the adapter disagree with rc.112's own decoder.

### 1.3 The patch text, measured (never applied)

`S/patches/{Bridge,Codec,LawsSchemaCodec}.lean.after` are the production files at `bff50631`
(blobs `07f08544`, `d29b1041`, `23bd52c0`) with the copy's arms written in production idiom
(`Ty`, `Val.hasTy`, `induction t with` through the generated eliminator); `*.diff` are
`diff -u` against the tree (tested; the counts are `diff | grep -c '^[<>]'`, `logs/patch-counts.log`):

| File | + | − | What |
| --- | ---: | ---: | --- |
| `src/Effect4/Schema/Bridge.lean` | 536 | 128 | `schema`'s nine arms (record, optional key, map, tuple, `app`, the four leaves) with `schemaProps`, `schemaElems`, `schemaList`; the declarations read through `reservedId` and `readReserved` (a reserved id reads as its constructor, any other id with parameters as `app`); the located reader `ofSchemaLocated` (with `readMembers`, `readProps`, the refusal carrier, the allowlist, the whole-check recognisers) replacing `ofSchema`, which stays as `(ofSchemaLocated r).toOption` so its 35 consumer lines do not move; `Ty.schemaWf`; the retraction rewritten for every form (premise `t.schemaWf = true` added, also on `ofSchema_schema_cty` and `CTy.ofSchema_schema`); `N_S` as a fold, `ofSchemaExact` and its two theorems; `import Effect4.Schema.Fold` |
| `src/Effect4/Schema/Codec.lean` | 188 | 14 | `layout`, `isSupported` arms (mutual helpers); `intJson`, `int?`; `encodeRaw`'s `int`, record, tuple and map arms with `fieldEncoders`, `encodeSlots`, `encodeItems`; the reader become `conv (strict : Bool)` (the 14 lines removed are its recursive calls, renamed) with `decodeRaw := conv true` and route A's `adaptRaw := conv false`, `adapt` beside `decode`; the canonical-branch check; `int`, record (the named value of row 165, `encodeNamed`), tuple and map arms with `fieldDecoders`, `lookupOnce`, `decodeSlots`, `decodeItems`; `N_J` (`normalizeJson`) |
| `src/Effect4/Laws/Schema/Codec.lean` | 40 | 0 | `adapt_member`; `decodeExact` and its three laws; `decode_of_encode`, `hasTy_decode`, `encode_injective`, `encode_sub` keep their text: they are generic in the arms |

What the patch takes from the other seats, by name: `Ty.record`/`optKey`/`map` and the
generated eliminator (P, Q; with P's optional flag in place of `optKey`, the `optKey` arms fold
into the record arm's flag branch, §7.2); `Ty.closedFields`, `Ty.firstRepeat`, `Ty.nameLt`,
`canonFields` (the canonical sort, P's `canon`); `Val.hasTy`'s `int`, record, optional and map arms and
`hasTy_sub` at them (P); `Store.IntCanonical.toVal` (exists). `Bridge.checkId` loses its only
caller and keeps a `fold_of` registration (`Laws/Program/Folds/Representation.lean:27`): delete
both, or keep both; the patch keeps them.

### 1.4 Production obligations the copy leaves (each named)

1. **Exactness by construction** (route 2), the stronger form row 128 asks for, at the bridge
   level: `ofSchemaLocated r = .ok t → normalizeSchema r = normalizeSchema (schema t)` and
   `decode t j = some v → ∃ j', encode t v = some j' ∧ normalizeJson j' = normalizeJson j`,
   each an induction (over `Representation` with its nested lists; over `Ty` with the record
   list and the canonical sort's permutation lemma for `N_J`). **Not proved here**; the guard
   gives both theorems now at one re-encoding per read, and the tests say the unguarded readers
   already meet them on the inputs above.
2. **`hasTy_sub` at the new forms** (seat P): `encode_sub`'s only premise beyond `layout`.
3. **The stored domain**: `Ty.schemaWf` must follow from formation (names distinct, optional
   keys only as fields, maps keyed by `string`, the handle name `effect/schema/TypeParameter`
   reserved) so that `CTy`'s retraction loses its extra premise.
4. **The DialectContract rows re-pin** (tested in the copy against the production
   `Store.render`): a store struct now reads as a record of `int` (the store's `nat` renders
   `isInt` alone: the existing "`nat` reads back as `int`" disagreement, now inside a record); a
   nullary sum reads as a literal union; a two-case sum as a union of tagged records; a one-case
   sum stays refused (a one-member union); `anyRef` refuses at `["address"]` (its pattern check).
5. **Seat T's forms whose codec is owed**, each with its obstacle: `null` and `undefined` (their
   value images; both would meet `unit` at JSON `null`, and rc.112 writes an explicit `undefined`
   as `null`); `number` (a binary64 `Val` frame, T's commit 3; non-finite values as strings);
   `bytes` (a base64 codec, none in the tree); `app` (a declaration's codec is a host reviver, or
   the located refusal it has here). Their Schema arms and retraction are done on the copy.

### 1.5 Static layout preparation, the Schema side, as the review bounds it (proved)

Revision 5's review (point 4) bounds this: the sort/map theorem is an ingredient, the evaluator
still sorts per value, and preparing a layout once needs its implementation and an
evaluator-agreement argument including evaluation and refusal order. What the copy adds is the
Schema side's half of that argument (`K2Copy.lean` §2 and §12, all in `logs/k2copy.log`):

- `canonF_of_sorted` (`[propext, Quot.sound]`): on a field list already in canonical order, the
  codec's deduplicating insertion sort is the identity.
- `canonF_map` (`[propext]`): the sort reads names only, so it commutes with any map of the
  payloads (revision 5's `sortFields_mapPayload`, for the deduplicating sort).
- `prepared_agrees` (`[propext, Quot.sound]`): for a record type whose fields are in canonical
  order, the encoder table, the decoder table (either mode, strict or adapter) and the membership
  table built from it are already canonical, so an arm that uses the type's own list (a layout
  prepared once at the type) is the same function as the arm that sorts per call.

The premise is met at every public entry: production's `encode` and `decode` normalize the type
first (`Codec.lean:230-240`), and a normal record's fields are in canonical order (seat P's
`Normal` law at records, **assumed** here). On the Schema side the agreement is an equality of
functions with `Option` results, so it carries no evaluation-order or refusal-order content: the
decoder walks the same list either way and has no located refusal to order. **Not done**: the
prepared evaluator itself (the copy's arms still call `canonF` per value), and the term-level
layout (record execution, read-back, the evaluator's refusal order), which is seat R's.

## 3. Question 3: the readable profile, per form (proved where marked, tested)

**Status: done.** `S/probes/ReadableProfile.lean` is revision 5's reviewed fold kept line for line
and extended per form: `diff rev5/DefinitiveSchemaProbe.lean probes/ReadableProfile.lean` is
+305/−16 lines (`logs/readable-vs-rev5.diff`), every change under a `[S]` marker.
`probes/compile.sh probes/ReadableProfile.lean readable`: exit 0, `logs/readable.log`; 37
`#guard`s hold (revision 5's 16, two of them updated where this seat changes the behaviour, and
21 new), and 6 red controls (the probe's §6b: a tuple printed as an array, the variadic `Union`
call shape, a dropped `mutableKey`, an unsupported node's annotation dropped and the node admitted,
a quoted `__proto__`, rc.112's own `Int` admitted by the eight keys) fail exactly as their
`#guard_msgs (error)` fixtures assert (added after the question's commit; the log's `EXPR_`/`REPR_`
lines, which the host harness reads, are byte-identical to the earlier run's: `diff`, tested); 8
axiom lines, every one `[propext]` (`validateAnnotations`, `validateFilter`,
`processProperties`, `structObject`, `keySpelling`, `toReadableSchema`, `admits`,
`admits_iff_explain`).

### 3.1 The admission predicate and the algebra

- **The algebra** is a second `RepresentationAlgebra` over the same generated
  `cata_representation`, beside the raw `printAlgebra` (`Codegen/Schema.lean:240`), which it does
  not touch: `moduleSyntax` and the persisted-document export stay as they are.
- **The predicate** is the emission's domain, with the located refusal as its explanation:
  `admits r := (toReadableSchema r is .ok)`, `explain r : Option SchemaRefusal`, and
  `admits_iff_explain` (**proved**). A declarative predicate proved equal to that domain is not
  built: the map arm's success depends on the parameter child being exactly `Schema.String`, which
  a Boolean fold of the children cannot see, so it needs a carrier richer than `Bool` (owed, small).
- **Admitted** (each arm; revision 5's plus this seat's): `Null`, `Undefined`, `Void`, `Never`,
  `Unknown`, `Any`, `String`, `Boolean`, `BigInt`, `Symbol`, `ObjectKeyword` with no check;
  `Number` with no check, `[isInt]` (`Schema.Int`) or `[isInt, isGreaterThanOrEqualTo 0]`
  (`Schema.Natural`), the checks `Bridge.schema` writes, compared whole (question 2 E9a–c: the
  names persist the same document as the checks by name); string, number and boolean literals;
  `Arrays` with one rest (`Schema.Array`) or plain elements and no rest (`Schema.Tuple([…])`);
  structs of string-named properties, no repeat, `Schema.optionalKey`/`Schema.mutableKey` kept;
  **[S] one index signature over a plain `Schema.String` and no property
  (`Schema.Record(Schema.String, V)`)**; `anyOf` unions (`Schema.Union([…])`, the array call
  shape), **[S] spliced along the right spine and printed `Schema.Literals([…])` when every member
  is a plain literal**.
- **Refused by name, located**: every declaration (so `option`, `except`, `exitOf`, `causeOf`,
  the handles, T's `app` and `bytes` have no readable text yet: owed, each a fixed spelling by
  id with its rc.112 reviver, e.g. `Schema.Option(A)`/`OptionReviver`), references, `Suspend`,
  `Enum`, `TemplateLiteral`, `UniqueSymbol`, bigint literals, numeric and symbol keys, `oneOf`,
  checks other than the two, filter groups, aborted filters, non-empty check schemas, index
  signatures other than the map's, and properties beside an index signature.
- **The annotation and modifier policy** (revision 5's, as the amendment adopts it): the eight
  documentation keys (`identifier`, `title`, `description`, `documentation`, `examples`,
  `default`, `message`, `expected`) are **erased under the observation** (structural `Type`,
  acceptance, decoded values; messages, identifiers, references and brands are outside it); every
  other key (`parseOptions`, `brands`, any unknown key) is **refused by name** at its path;
  `optionalKey` and `mutableKey` are **kept**. Reviewer equations at `[propext]`:
  `semantic_object_annotation_refused`, `check_disabling_annotation_refused` (revision 5's audit,
  reproduced in §3a). **One finding against the allowlist** (tested): rc.112's own persisted
  `Schema.Int` carries `arbitrary` on its `isInt` filter (question 2 E9d), so the profile refuses
  rc.112's own `Int` document at `["check[0]", "annotations"]` while rc.112 revives and decodes it
  (`host/q3-profile.ts`, the `RC_INT` lines). `arbitrary` is a fast-check generation hint read by
  no parser (`Schema.ts:8306-8310` writes it; the parser reads `parseOptions` only,
  `annotation-review.md`); **proposed: a ninth key**, as the K2 reader of §1 already takes it.
- **Exact property spelling** [S]: `__proto__` computed (`["__proto__"]`), an ASCII identifier
  that is not reserved bare, any other name quoted; a name needing an escape (`"`, `\`, newline,
  return, tab) makes the struct fall back to the renderer's all-quoted object, and beside
  `__proto__` it refuses by name (`["x\"y"]`). The target syntax has no per-key spelling: the
  probe passes the pre-rendered key text through `Expr.object` (which renders keys verbatim),
  built only where no escape is needed, because building a `String` from escaped bytes reaches
  `Classical.choice` (`String.fromUTF8?`, tested) while `"\"" ++ name ++ "\""` stays at
  `[propext]`. **Production needs the lean4-typescript bump** probe T and probe R name (N8:
  computed object keys; a per-key spelling owned by the package's renderer), not this workaround.

### 3.2 The emissions per form (tested, `#guard` on the rendered text)

| Form (`schema τ`'s node) | Readable text |
| --- | --- |
| record | `Schema.Struct({ a: Schema.Int, b: Schema.String })` |
| optional key | `Schema.Struct({ a: Schema.optionalKey(Schema.Int), b: Schema.String })` |
| rc.112 `optional` (with T's `undefined`) | `Schema.Struct({ a: Schema.optionalKey(Schema.Union([Schema.Int, Schema.Undefined])) })` |
| map | `Schema.Record(Schema.String, Schema.Int)` |
| tagged union, two cases | `Schema.Union([Schema.Struct({ _tag: Schema.Literal("A"), x: Schema.Int }), Schema.Struct({ _tag: Schema.Literal("B"), y: Schema.String })])` |
| tagged union, three cases (the writer nests them) | `Schema.Union([… A …, … B …, Schema.Struct({ _tag: Schema.Literal("C") })])`, flat |
| literal union (nested or flat) | `Schema.Literals(["a", "b", "c"])` |
| tuple (T) / list | `Schema.Tuple([Schema.Int, Schema.String, Schema.Boolean])` / `Schema.Array(Schema.String)` |
| `nat` / `int` | `Schema.Natural` / `Schema.Int` |
| special names | `Schema.Struct({ ["__proto__"]: Schema.Int, "a-b": Schema.String, "é": Schema.Boolean, constructor: Schema.String, "": Schema.Int, "10": Schema.Int, "9": Schema.Natural })` |
| a name needing escapes | `Schema.Struct({ "x\"y": Schema.String, "a": Schema.Int })` (all quoted) |
| mutable optional | `Schema.Struct({ "a-b": Schema.optionalKey(Schema.mutableKey(Schema.String)) })` |

Asserting controls kept from the brief's list: a tuple is not an array (`TUPLE3` against
`ARRAY`), a union keeps the array call shape, a mutable field keeps `mutableKey`, an annotation on
an unsupported node refuses (`Enum` with `parseOptions`: `["annotations"]`), and the refusals
are located: `["x\"y"]` (escape beside `__proto__`), `["indexSignatures[0]", "parameter"]` (a
`Number`-keyed map), `["indexSignatures"]` (struct with rest), `[]` (`oneOf`, a bigint literal),
`["check[0]", "annotations"]` (rc.112's `Int`).

### 3.3 The host evidence (tested)

- `host/q3-profile.ts` (bun 1.4.2, vendored rc.112; `logs/q3-profile.log`, exit 0): 31 examples
  (`logs/readable.log`'s `EXPR_`/`REPR_` lines: the per-form ones, seven adversarial names one at
  a time, and the four declarations `Bridge.schema` writes). For the 23 admitted ones, rc.112's
  persisted form of the evaluated readable text equals Lean's raw document **modulo `nS`**
  (annotations erased, the `anyOf` spine flattened, properties compared as a set because rc.112
  puts integer-like names first: question 2 E8p): 23 of 23; the evaluated text and rc.112's own
  revival of Lean's document (`fromRepresentation` with `isIntReviver`,
  `isGreaterThanOrEqualToReviver`) **accept and answer alike in 176 of 176 decode comparisons**,
  default and strict excess-property options; the 8 refused examples emit no code; rc.112 revives
  the `RC_INT` document the profile refuses. Red twin `q3-profile-red.ts` (TUPLE3 compared with an
  array's document): exit 1 at exactly that check.
- `host/q3-types.ts` (tsgo 7.0.0-dev.20260629.1, `/opt/homebrew/bin/tsgo -p tsconfig.q3.json`,
  `logs/q3-types.log`): exit 0; 16 exact-type assertions on the generated module (the intended
  types: readonly fields, `a?: number` against `a?: number | undefined`, the index signature, the
  discriminated unions, `readonly [number, string, boolean]`, the computed `__proto__` as a
  required own field) and 7 rejecting controls. Red twin `q3-types-red.ts`: exit 1, TS2344 ×2.

## 4. Question 4: the bounded upstream route, compared (tested)

**Status: done.** Route L is §3's readable profile. Route U is Codex's `reuse.mjs` extended: Lean's
persisted document → `SchemaRepresentation.fromJson` → `fromRepresentation` with a pinned reviver
list (`isIntReviver`, `isGreaterThanOrEqualToReviver`, `OptionReviver`, `ResultReviver`,
`ExitReviver`, `CauseReviver`, `Uint8ArrayReviver`, `JsonReviver`) → `toRepresentation` →
`toCodeDocument` (rc.112's public API, vendored source under bun). `reuse.mjs` itself reproduces
byte for byte (§2). `host/q4-routes.ts` (`logs/q4-routes.log`, exit 0; rerun byte-identical,
`logs/q4-routes.rerun.log`) runs both routes on the 32 documents of `logs/readable.log` (31, plus
Lean's `EXIT` with rc.112's defect id) and compares each with the **reference**, rc.112's own
revival of Lean's document: coverage, source size, the persisted form modulo `nS`, and decoder
agreement under the default and the strict options. Red twin `q4-routes-red.ts` exits 1 at its one
flipped check. Types: `q4-types.ts` (the intended types against route U's runtime, tsgo exit 0)
and `q4-types-auto.ts` (route U's own `Type` text against its runtime's inferred type, 31
assertions, tsgo exit 1 with exactly two errors, both upstream defects recorded below). Red twin
`q4-types-red.ts` (route U's tuple typed as an array; its `__proto__` loss visible in its type):
tsgo exit 1, TS2344 at both, `logs/q4-types-red.log`.

| Criterion | Route L: the Lean readable profile | Route U: revived document → `toCodeDocument` |
| --- | --- | --- |
| coverage, 21 ordinary documents | 13 emit; 8 refuse, each by name and path: the four declarations (`Option`, `Result`, `Exit`, `Uint8Array`), a `Number`-keyed `Record`, a struct with rest, rc.112's own `Int` (its `arbitrary` annotation), the Exit variant | 20 emit; Lean's `EXIT` refuses ("Missing reviver for effect/schema/Defect", below) |
| faithful on the ordinary ones (persisted form equal modulo `nS`, every decode equal to the reference) | 13 of 13 | 20 of 20 |
| 11 documents with adversarial names (`__proto__`, `a-b`, Unicode, `constructor`/`toString`/`default`/`class`, `""`, `"01"`/`"10"`/`"9"`/`"1e3"`, `x"y`, a newline), one at a time and mixed | 10 emit (a name needing escapes beside `__proto__` refuses), **10 of 10 faithful** | 11 emit, **8 of 11 faithful**: every `__proto__` document loses its field (`N_PROTO` 2 of 6 decodes agree, `SPECIAL` 0 of 4, `ESC_PROTO` persists without it), because `formatPropertyKey` quotes every key (`Formatter.ts:192-194`) and a quoted `__proto__` sets the prototype |
| source size, the 23 documents both emit | **1,606 bytes** | **3,523 bytes** of runtime text (every revived filter carries `.annotate({ "expected": … })`, every key is quoted) plus 1,223 bytes of `Type` text |
| exact types (tsgo 7) | 16 intended types hold (§3.3) | the 9 intended types checked hold, **including `N_PROTO` and `SPECIAL`, whose runtime has lost the field**: the type checker cannot see route U's loss; route U's own `Type` text matches its runtime in 29 of 31: not for the struct with rest (an intersection, not identical to `StructWithRest`'s type) and not for `Exit` (`Exit.Exit<number, string, Schema.Json>`: TS2707, `Exit` takes at most two arguments) |
| refusals | located (path and reason) before any text exists, in Lean at `[propext]` | a thrown `Error` at the host's run time, with a path (`Missing reviver for …`, `Missing toCode callback …`) |
| what it needs | nothing beyond the Lean fold | the host and rc.112's runtime, the reviver list pinned; imports `Option`, `Result`, `Exit` for declarations |

**One finding outside both routes** (tested, `host/q4-defect.ts`, `q4-defect-revive.ts`):
`Bridge.defectRep` (`Schema/Bridge.lean:34-35`) writes the defect slot of `Exit` and `Cause` as
`Declaration("effect/schema/Defect")`, an id rc.112 never writes: rc.112's `Schema.Defect()` is a
transformation over `Json` (`Schema.ts:10844-10853`) and persists as
`Declaration("effect/schema/Json")`. So rc.112 cannot revive Lean's `Exit`/`Cause` documents, and
`Bridge.ofSchema` refuses rc.112's own (its `isDefect` reads Lean's id; tested on the production
reader, `K2Copy.lean`'s `rcExitDoc` guards): the existing K2 pair at
`exitOf`/`causeOf` is not exact **against rc.112**, only against itself. With rc.112's id
(`EXIT_AS_RC`) and `JsonReviver`, route U revives and prints Lean's Exit (tested). **Proposed**: the
data wave's commit 1 changes `defectRep`/`isDefect` to `effect/schema/Json`. Nothing in the tree
pins the id (tested): `git grep -n 'effect/schema/Defect' -- . ':(exclude)docs/research'` answers
`Bridge.lean:35` and `:70` only, the writer and the reader; outside the bridge `Bridge.schema` has
one caller, its `fold_of` registration (`Laws/Program/Folds/Ty.lean:34`); the two round-trip
guards at `Test/Codegen/SchemaGenerationContract.lean:107-108` hold under either id because the
writer and the reader change together; the comment at `:117` names "the `Defect` declaration".

**Which route per form** (the recommendation):

- **Route L is the printer** for every form of the profile: records, optional keys (with
  `mutableKey`), string-keyed maps, tagged unions, literal unions, tuples, arrays, `nat`/`int`,
  and every field name, `__proto__` included. It is faithful on all of them, half the size, refuses
  with a path before emitting, and needs no host.
- **Route U is a test oracle**, not a printer: on the ordinary forms its decoders and persisted
  forms agree with the reference everywhere (20 of 20), so a conformance lane can run both and
  diff; on `__proto__` it is not even an oracle (wrong at run time, right in its types).
- **Declarations** (`Option`, `Result`, `Exit`, `Cause`, `Uint8Array`): route U covers them today
  with the pinned revivers; route L should take them **by id** (a closed list `Bridge.schema`
  writes, each a fixed spelling: `Schema.Option(A)`, `Schema.Result(A, E)`, `Schema.Exit(A, E,
  Schema.Json)`, `Schema.Cause(E, Schema.Json)`, `Schema.Uint8Array`), owed and small; route U
  cannot be the printer for `Exit` anyway (its `Type` text is invalid TypeScript).
- **Out of the profile, for both**: `Record(Number, _)` and struct-with-rest (no `Ty`); for them
  route U is a reference and nothing more.

## 5. Question 5: row 8's dedupe at the emitter, option (C), measured on a copy (proved and tested)

**Status: done.** `S/probes/RefDedupe.lean` (`probes/compile.sh probes/RefDedupe.lean refdedupe`:
exit 0, `logs/refdedupe.log`; 8 `#guard`s hold and 2 red controls fail as their `#guard_msgs (error)`
fixtures assert (a conflicting repeat deduplicated silently; the meta-schema's table without
repeats); 6 theorems and 2 definitions print `[propext, Quot.sound]`). Option (C) keeps `ShapeDoc.document`'s version-0 bytes and the store's addresses,
and deduplicates the references table where it is written as a JSON object:

- `dedupeRefs` keeps the first entry of each key, drops a later entry whose body is equal, and
  **refuses** a later entry whose body differs at `["references", key]` (tested on a conflicting
  table; seat G measured that no table in the tree has one: 0 of 19).
- **Proved:** `dedupeRefs_distinct` (on a table whose keys are distinct it is the identity, so (C)
  moves no byte of any document without repeats), `dedupeRefs_nodup` (what it answers has distinct
  keys), and `moduleSyntaxChecked_distinct` (the checked module equals today's `moduleSyntax` on such
  a document).
- **The checked emitter** wraps the production functions unchanged: `documentExprChecked`,
  `multiDocumentExprChecked`, `moduleSyntaxChecked : … → Except RefRefusal Module`.

**What changes under `harness/schema-generation/`** (the part receipt G left unmeasured):
**nothing** (tested, `host/q5-dedupe.sh`, `logs/q5-split.log`): the three fixtures re-emitted
through the checked emitter with their stamps are `cmp`-identical to the committed
`Person.generated.ts` (1,488 bytes, no references), `AllRepresentations.generated.ts` (4,964
bytes, 23 distinct keys) and `TwoRoots.generated.ts` (436 bytes, one key), as the identity law
says they must be.

**What (C) repairs** (tested): the defect a reader meets is TypeScript's, not rc.112's. The
meta-schema's table (`(shape Document).document`, 30 entries, 22 repeats) emitted as a module
today is 208,016 bytes and **tsgo refuses it with 22 TS1117** ("An object literal cannot have
multiple properties with the same name", `logs/q5-tsgo-raw.log`, exit 1); through (C) it is 92,683
bytes and tsgo accepts it (`logs/q5-tsgo-deduped.log`, exit 0). At run time rc.112 revives both to
equal documents (`q5/runtime.ts` under bun: the JavaScript object keeps one entry per key, and
every repeat's body is equal), so (C) changes no decoded behaviour. Its red twin `q5/runtime-red.ts`
(the claim that the raw object keeps one key per entry, 30) exits 1 with 8 keys,
`logs/q5-runtime-red.log`. No committed artefact emits a
shape document today; the six measured (`REPEATS` lines: `Document` and `MultiDocument` 22 repeats
each, `Representation`, `Check`, `ReferenceEntry` 7 each, `ShapeDoc` 1) would all deduplicate
without a refusal.

**What it touches** (reading): `Codegen/Schema.lean`'s `references` (its three lines, `:310-312`) and the three
entry points' signatures; the consumers that move to `Except`: the three `harness/schema-generation/
Emit*.lean` fixtures, `Test/Codegen/SchemaGenerationContract.lean`'s two guards on
`documentSource`/`moduleSyntax`, `Api.schemaDocument` (`Api.lean:572-573`), the axiom gate's
exact-name list (`AxiomGate.lean:164-167`, if the rendering entry points are renamed). A total
alternative (dedupe equal repeats, keep the signature, and leave a differing repeat unchecked) is
worse: it would print a module tsgo refuses without saying why.

## 6. Proposed decisions rows (the coordinator numbers and writes them; this seat edits no register)

### 6.1 New

**S-A. The readable Schema profile** (the Schema face's readable text; W5's item 2).
- *Proposal.* Beside the persisted `SchemaRepresentation` JSON (`moduleSyntax`, unchanged), the
  Schema face prints one readable rc.112 expression for every document the profile admits, and
  refuses every other document by name, with its path, before any text exists. The contract:
  1. **Algebra**: a second `RepresentationAlgebra` over the generated `cata_representation`, never
     a hand traversal, never replacing `printAlgebra`.
  2. **Predicate**: `admits r` is the emission's domain, `explain r` its located refusal,
     `admits_iff_explain` the agreement. Admitted: `Null`, `Undefined`, `Void`, `Never`, `Unknown`,
     `Any`, `String`, `Boolean`, `BigInt`, `Symbol`, `ObjectKeyword` with no check; `Number` with no
     check, `[isInt]` or `[isInt, isGreaterThanOrEqualTo 0]` compared whole; string, number and
     boolean literals; `Schema.Array`; `Schema.Tuple([…])`; structs of string-named properties
     with `optionalKey` and `mutableKey` kept; `Schema.Record(Schema.String, V)`; `anyOf` unions in
     the array call shape, spliced along the right spine, `Schema.Literals([…])` when every member
     is a plain literal.
  3. **Annotations**: revision 5's eight documentation keys erased under the observation; every
     other key refused by name at its path; nothing silently reinterpreted.
  4. **Observation**: the emitted schema's structural `Type` (tsgo 7 exact-type assertions), its
     acceptance and its decoded values under rc.112's default and `onExcessProperty: "error"`
     options, against rc.112's own revival of the persisted document; messages, identifiers,
     references and brands are outside it.
  5. **Spelling**: per key: `__proto__` computed, a bare-class name bare, any other quoted (row
     167's classes); production text waits for row 164's computed keys and a per-key spelling in
     the package's renderer.
  6. **Routes**: the Lean algebra (route L) is the printer; rc.112's `toCodeDocument` over the
     revived document (route U) is a conformance oracle, never a printer.
  7. **Owed**: declarations by id (`Schema.Option(A)`, `Schema.Result(A, E)`,
     `Schema.Exit(A, E, Schema.Json)`, `Schema.Cause(E, Schema.Json)`, `Schema.Uint8Array`, an
     `app` name table), each with its rc.112 reviver in the oracle.
- *Two choices inside it, for the owner.* (a) **`arbitrary` as a ninth documentation key**:
  rc.112's own `Schema.Int` persists it on its `isInt` filter (question 2 E9d), so without it the
  profile refuses rc.112's own `Int` document, which rc.112 revives and decodes (tested); rc.112's
  parser reads only `parseOptions` (`annotation-review.md`). Recommended: add it. (b) **The bare
  class**: the profile and the type printer use `targetIdentifier` (ASCII identifier, not one of the
  package's 46 reserved words, `Identifier.lean`: `default`, `class` print quoted), probe R's term printer uses
  `SourceBindings.identifierBytes` (keywords bare); both are faithful here (`N_RESERVED`, tested).
  Recommended: one class for every face, named in row 167; `targetIdentifier`, which two of the
  three printers already use.
- *Evidence.* S §3 (`ReadableProfile.lean`: 37 guards hold, 6 red controls; `admits_iff_explain`
  at `[propext]`; host: 23 of 23 persisted forms equal modulo `nS`, 176 of 176 decode comparisons,
  16 exact types and 7 rejecting controls under tsgo 7, red twins exit 1), §4 (the two routes),
  revision 5 (`S-inputs/revision-5/`, reproduced in §3a).
- *Owner*: owner. *Status*: open, recommended.

**S-B. A counterexample, not a decision: Lean's defect slot names a declaration rc.112 never
writes.** `Bridge.defectRep` writes `Declaration("effect/schema/Defect")` for the defect slot of
`exitOf` and `causeOf` (`Schema/Bridge.lean:35`, read back at `:70`); rc.112's `Schema.Defect()`
persists as `Declaration("effect/schema/Json")`. rc.112 cannot revive Lean's `Exit`/`Cause`
documents ("Missing reviver for effect/schema/Defect", `host/logs/q4-routes.log`'s `EXIT` row), and
production's `Bridge.ofSchema` refuses rc.112's own `Exit(Int, String, Defect())` while it reads the
same document with Lean's id (`K2Copy.lean`'s `rcExitDoc` guards on the production reader, the
shape from `host/logs/q4-defect.log`; tested); with rc.112's id and `JsonReviver`, Lean's `Exit`
revives in rc.112 (`host/q4-defect-revive.ts`, tested). Proposed for the
register under the next free `E4-SCHEMA-CE` id (seat G's is 060), witness `q4-defect.ts`, repair in
commit 1 (two lines; nothing pins the id, §4).

### 6.2 Amendments to existing rows

- **Row 8, option (C), measured** (S §5): at the emitter, (C) moves no committed artefact (the three
  `harness/schema-generation/` fixtures re-emitted `cmp`-identical; the identity law on tables
  without repeats proved), repairs the meta-schema module (22 TS1117 under tsgo 7 → none; 208,016 →
  92,683 bytes), changes no decoded value (bun), and refuses a conflicting repeat at
  `["references", key]` (none exists in the tree: seat G's census). Cost (reading): `references`
  (`Codegen/Schema.lean:310-312`) and the three entry points return `Except`; seven consumers move
  (the three `Emit*.lean`, two guards in `SchemaGenerationContract.lean`, `Api.schemaDocument`, the
  gate's exact names at `AxiomGate.lean:164-167` if renamed). The probe's text: `dedupeFrom` and
  `dedupeRefs` with the refusal carrier (`RefDedupe.lean:31-47`), the checked entry points
  (`:113-124`), the laws (`:49-110`, `:126-131`). Recommend ratifying (C) at the emitter.
- **Row 121** (with row 108): (i) **the JSON face's integer profile is the safe integers**: rc.112's
  `isInt` is `Number.isSafeInteger` (2^53 refused, 2^53 − 1 accepted, question 2 E9e), and the
  document Lean writes says `isInt`, but the codec's `decode .nat` accepts 2^53 today (tested on the
  production function, `K2Copy.lean:1749`; the copy's `int` too, red control `red_int2p53`), so a
  value Lean encodes can be refused by the TypeScript decoder of Lean's own document. Proposed:
  `nat` and `int` encode and decode only |n| ≤ 2^53 − 1 and refuse outside by name (row 108's
  "outside the profile the face refuses"); JSON `-0` stays refused (rc.112's `Natural` accepts it
  and keeps the sign, E9g). Inside the bound, `encode_sub` along `nat ⊑ int ⊑ number` holds with a
  binary64 `number` image. (ii) **For (a)**: `Int`'s generated `ctor 0 [nat n]` image overlaps
  `Result`'s failure at a union, so a `Result` failure is outside the image of
  `union int (except nat nat)` (tested, §1.2); the signed frame removes the overlap. (iii)
  `number`'s JSON: rc.112's `toCodecJson` writes NaN and the infinities as the strings `"NaN"`,
  `"Infinity"`, `"-Infinity"` (E9l): the binary64 codec follows that or refuses them by name.
- **Row 122**: probe R's `codec_sub_adapt` (the adapter agrees with the codec wherever the codec
  answers) is **false at a union whose earlier branch adapts a later branch's exact image**
  (tested: at `union (record [a]) (record [a, b])` the JSON `{"a":1,"b":2}` decodes to `{a, b}` and
  adapts to `{a}`, red control `red_codecSubAdaptUnion`); there the adapter does what rc.112's
  default `anyOf` does (E7). Proposed premise, as a formation check on a row's answer type: no
  earlier branch's adapter accepts a later branch's exact image; sufficient: tagged unions with
  distinct tags (the tag literal refuses the other branch), or record branches none of whose name
  sets is included in a later branch's. The alternative (an adapter that tries every branch strictly
  before projecting) disagrees with rc.112's own decoder, which route A's TypeScript side uses.
- **Row 123** (its input from the profile): the operation means the strict codec's fold, and rc.112's
  default decode strips excess keys (E3: route A's adapter, not the codec), so its TypeScript face is
  the profile's text decoded with `{ onExcessProperty: "error" }`; at a string-keyed map the option
  is moot (every key matches the index signature). A target outside the profile (the declarations,
  until their spellings land) has no readable face; its face there is the persisted document
  revived at run time with the pinned revivers (§4's reference), never route U's printed text.
- **Row 125**: the map's Schema face is `Record(String, V)` only; any other index-signature
  parameter refuses at `["indexSignatures[0]", "parameter"]`; a literal-keyed `Record` is a struct
  and reads as a record (E6g). Seat P's copy admits `nat` keys (`probe/P`, `P2Ty.lean:14`, reading):
  rc.112's `Record(Number, V)` drops a non-numeric key even under `onExcessProperty: "error"` (E6:
  the excess check skips nodes with index signatures), so a `nat`-keyed map needs DI-78's key
  contract before it gets a Schema face; refused by name until then.
- **Row 128**: the canonical-branch check as stated in §1.2 (still needed after row 165: at
  `Result`/`Exit` and at `Int`'s `ctor` image); exactness proved by the guard and tested, not
  proved, by construction (§1.4 item 1); the theorem stated at the bridge level, where `N_S` needs no
  property sort (§1.1); the vocabulary line: "`Ty.schema`/`ofSchema` (exact modulo `N_S` at the
  bridge: annotations erased, `anyOf` right spines flattened; the public writer normalizes first,
  so the public pair is exact on canonical types) and the JSON codec (exact modulo `N_J`, the
  object-key sort)".
- **Row 157**: `Schema.optional(A)` persists `isOptional` over `Union[A, Undefined]` (E4), seat P's
  reading `optionalKey(UndefinedOr(A))`; the strict codec refuses JSON `null` at an `optionalKey`
  slot (`red_optionalNull`); under `toCodecJson`, `optional` writes an explicit `undefined` as `null`
  and reads `null` back as `undefined` (E4k–E4o), so the three-state slot's JSON image is row 160's.
- **Row 158**: `app`'s Schema face is `Declaration(name, typeParameters := schema args)`; the
  reserved ids (`Option`, `Ref`, `Result`, `Fiber`, `Deferred`, `Cause`, `Exit`, `TypeParameter`,
  `Uint8Array` under `effect/schema/`) read as their constructors, never as `app`; rc.112 revives a
  declaration only through a reviver for its id ("Missing reviver for …", q4); the codec refuses
  `app` by name until a reviver per name exists.
- **Row 159**: a tuple's face is `Arrays` with plain elements and no rest (`Schema.Tuple([…])`);
  arity two reads `prod`; an optional element refuses at `["elements[i]"]`; a tuple and a list at one
  union are told apart by arity (tested both orders).
- **Row 160**: the faces `Null`/`Undefined` retract on the copy (proved); the codec waits for the
  value images. One constraint for whoever rules them: if commit 2 declares `undefined ⊑ unit`,
  `encode_sub` forces `undefined`'s JSON image to be `unit`'s (`null`, `Codec.lean:154`), which is
  what rc.112's `toCodecJson` writes for an explicit `undefined` (E4k); then `union null undefined`'s
  two values share `null`, the first branch wins at decode, and the encoder refuses the second
  (the S-3 clause): a nullable union holding `undefined` would not encode.
- **Row 161**: rc.112's `Uint8Array` JSON is a base64 string (`toCodecJson` → `Base64String`,
  `Schema.ts:13615-13619`) and the tree has no base64 codec (`git grep -il base64 -- src tools`:
  none): (a) costs a base64 encoder and decoder with their retraction and exactness (canonical
  padding); (b) leaves `Uint8Array` a declaration with a host reviver.
- **Rows 164 and 167**: the profile's per-key spelling needs computed keys and an object whose keys
  each carry their spelling (the package's renderer spells a whole object one way: `object` or
  `objectQuoted`); the probe's pre-rendered keys (§3.1) are a probe device, not production text.
  Row 167 should name its bare class (6.1 S-A choice (b)).

## 7. Brief text

### 7.1 For W1 (commit 1), the Schema half: lines to fill in

> S's note §1 is the reference on a copy (`S/probes/K2Copy.lean`; production idiom in
> `S/patches/*.after`). Take from it:
>
> 1. **The canonical-branch check** in `decodeRaw`'s union arm:
>    `match (decodeRaw a j).filter (fun v => Val.hasTy v a) with | some v => some v | none => (decodeRaw b j).filter (fun v => Val.hasTy v b && !Val.hasTy v a)`.
>    Red controls: row 128's witness (`red_productionExact`: production decodes the `Success` image
>    at `union (except nat nat) (exitOf nat nat)`). Keep as a recorded limitation (a guard, not a
>    control): at `union int (except nat nat)` a `Result` failure's JSON is outside the union's
>    image while `Int`'s image is `ctor 0 [nat n]`, until commit 3's signed frame.
> 2. **The normalisers as functions**: `N_J` a recursive stable object-key sort (`K2Copy.lean` §11);
>    `N_S := cata_representation nsAlg`, annotation bags erased and an `anyOf` right spine flattened
>    (`K2Copy.lean` §6). State exactness at the bridge (`Bridge.schema`, `Bridge.ofSchema`), beside
>    `ofSchema_schema`; there `N_S` sorts nothing (S §1.1; `red_unsortedNS` records what a
>    statement against the normalizing public writer would need).
> 3. **Choose the exactness route first.** (a) The guarded readers `ofSchemaExact`/`decodeExact`
>    (proved on the copy: `ofSchemaExact_exact` and `decodeExactP_exact`, about a dozen lines each;
>    one re-encode per read). (b) The plain readers by construction (tested on the 23 inputs where
>    S compared them with the guarded readers; not proved: an induction over `Representation` with
>    its nested lists, and over `Ty` with the canonical sort's permutation lemma for `N_J`). Aim for
>    (b); land (a) if (b) does not close, and record (b) as owed.
> 4. **Whole checks**: the `isInt` filter with payload `null`, no `schemas`, not aborted,
>    documentation annotations only; `[isInt, ≥ +0]` for `nat`; anything else refused at
>    `["checks[i]"]`. Red controls: `number ≥ 5` reads `nat` today (`red_ge5`); a filter group reads
>    `int` today (`groupedInt`).
> 5. **`TypeParameter`**: the handle named `effect/schema/TypeParameter` refused by name
>    (`red_typeParameter`).
> 6. **The defect id**: `defectRep` and `isDefect` name `effect/schema/Json` (S §4, §6.1 S-B);
>    `host/q4-defect.ts` becomes the green twin.
> 7. If row 121's safe-integer bound is ruled: `nat`/`int` refuse |n| > 2^53 − 1 at encode and
>    decode, with 2^53 and −2^53 as red controls (`K2Copy.lean:1749`, `red_int2p53`).

### 7.2 For W5 (commit 5): lines to fill in

> S's note §1.1 (the K2 table) and §1.3 (`S/patches/Bridge.lean.after`, `Codec.lean.after`,
> `LawsSchemaCodec.lean.after`: +764/−142 against `bff50631`, `diff | grep -c '^[<>]'`) are the arms
> in production idiom; §3 is the profile; §5 is row 8's (C).
>
> - **Translate two copy devices.** The copy's `optKey τ` field is seat P's flag
>   (`(n, optKey τ)` ↦ `(n, true, τ)`); its arms move into the record arm's flag branch. The copy
>   orders fields by UTF-8 bytes, P's current `fieldKey` is tag-first; the arms use only `canonF` and
>   its laws, so the order is the one P's commit 4 lands.
> - **Per form, arm, refusal and a red/green pair in `Test/Schema/`:** record (`objects`, string
>   names, refusals at `[n]`, `[]`, `[k]`, `["annotations"]`, `[n, "annotations"]`,
>   `["indexSignatures"]`; the codec over row 165's `ctor 0 [list names, list slots]`, strict:
>   unnamed, repeated and missing keys refused; route A's adapter as `conv false`); optional key
>   (`isOptional`; `optional(A)` once `undefined` lands; `red_optionalNull`); map
>   (`Record(String, V)` only; repeated key refused; keys ascending in the value); tagged unions (no
>   new arm; `ofSchema` reads n-ary `anyOf` right-nested, refuses `oneOf` and fewer than two
>   members; `red_flatWithoutNS`); `Number`/`Int` (the whole checks of commit 1; `number` reads
>   plain `Number`; its codec on commit 3's frame); `Null`/`Undefined` (faces and retraction;
>   codec when row 160 rules); tuples (`Arrays`, plain elements, no rest; arity two is `prod`);
>   `app` (a declaration with type parameters; reserved ids read as their constructors; codec
>   refused by name); `bytes` if row 161 (a) (`Declaration("effect/schema/Uint8Array")`; base64
>   codec owed).
> - **Laws.** `ofSchema_schema` with the premise `t.schemaWf = true` (also `ofSchema_schema_cty`,
>   `CTy.ofSchema_schema`) until formation gives it; `decode_of_encode`, `hasTy_decode`,
>   `encode_injective` keep their text; `encode_sub` from P's `hasTy_sub` at the new forms;
>   `adapt_member`; `codec_sub_adapt` under row 122's union premise (`red_codecSubAdaptUnion`);
>   commit 1's exactness extended. Keep the copy's red controls `red_sharedImage` (the positional
>   value clause) and `red_repeat` with the ones above.
> - **The readable profile** (if not split out, 7.3): `S/probes/ReadableProfile.lean` as a module
>   beside `Codegen/Schema.lean`, with its 37 guards and 6 red controls as a contract battery; the
>   pre-rendered key device replaced by the bumped package's per-key spelling.
> - **Row 8's (C)**: `dedupeRefs` and the checked entry points (`S/probes/RefDedupe.lean`), the
>   seven consumers moved to `Except`, the three laws; the three fixtures stay byte-identical.

### 7.3 A Schema-face slice (after W5, or W5's item 2 split out)

> **Seat SF: the Schema face's readable text.** Base: main after W5 and the bump (0a). Rules: the
> wave's (`README.md`, plan §4, `AGENTS.md`; tsgo 7 only).
>
> **The one thing.** One readable rc.112 expression per admitted document, from a fold beside the
> persisted export, refused by name otherwise; rc.112's own `toCodeDocument` runs beside it as the
> oracle, never as the printer (it drops `__proto__` fields while tsgo accepts its types: S §4).
>
> 1. The profile module and its export (`readableSource : Representation → Except SchemaRefusal String`
>    beside `moduleSyntax`; an `Api` entry beside `schemaDocument`), from S's `ReadableProfile.lean`.
> 2. Per-key spelling through the bumped package (computed keys), deleting the probe's pre-rendered
>    keys; the bare class as row 167 names it.
> 3. Declarations by id: `Schema.Option(A)`, `Schema.Result(A, E)`, `Schema.Exit(A, E, Schema.Json)`,
>    `Schema.Cause(E, Schema.Json)`, `Schema.Uint8Array`, and `app` through a registered
>    name-to-spelling table with a located refusal for an unregistered id; each with a red/green
>    pair and its reviver in the oracle.
> 4. The conformance lane: S's `host/q3-profile.ts`, `q3-types.ts` and `q4-routes.ts` as one host
>    check over a generated example list (bun on the vendored rc.112: acceptance and decoded values
>    under the default and strict options; tsgo 7: the exact types), with their red twins, read by
>    `make check-target`.
> 5. `arbitrary` as the ninth key if ruled (S-A (a)).
>
> Acceptance: every example of S §3.2 emits its text; every refusal keeps its path; the lane has
> no failure and its red twins exit 1. Receipt: the predicate and the admitted list, the lane's
> numbers, the rows touched (S-A, 164, 167).

## Receipt

**The one thing.** The Schema side of every form the data wave adds is done on a copy and measured
(retraction proved at every form; patch +764/−142 in three files), and W1 must choose its
exactness route first: exactness is proved here only through a guard, and by construction only
tested. Then: the defect id in `Bridge.defectRep` (W1, two lines); row 122's `codec_sub_adapt`
needs a premise at unions; the canonical-branch check stays after row 165; the Lean profile is the
printer and rc.112's `toCodeDocument` an oracle; `arbitrary` and the safe-integer bound; row 8's (C)
measured clean.

**Base and head.** Branch `probe/S` in `/Users/pooks/Dev/lean4-effect4-probe-S`, base `bff50631`;
head: the commit that adds this note, whose parent is `ebd61300`. The seat's commits, oldest first:
`562c4f77` (question 2), `12279e5f` (revision 5 reproduced), `68f5616b`, `a373f8b3`, `95ec0c9e`
(question 1; T's forms; row 165 and the adapter), `c7271d88` (question 3), `55c6a4df` (question 4),
`978b4cf9` (question 5), `baccf235` (red controls for questions 3–5), `186c772c` (question 1: the
level of the exactness statement), `ebd61300` (question 4: the defect slot on the production
reader), then this note. Nothing pushed; no `merge`, `checkout` or `reset` run.

**Changed paths.** Only `docs/research/2026-10-01-type-language-probe/S/`: `note.md`; `probes/`
(`K2Copy.lean`, `ReadableProfile.lean`, `RefDedupe.lean`, `compile.sh`, `count-arms.py`);
`patches/` (three `.lean.after`, three `.diff`); `logs/`; `host/` (the scripts, tsconfigs, `q5/`,
`codex/`, `logs/`); `rev5/`. Tested: `git diff --name-only bff50631..HEAD -- . ':(exclude)docs/research/2026-10-01-type-language-probe/S'`
is empty; before this note `git diff --name-only bff50631..HEAD | wc -l` is 141 (host 84, logs 31,
rev5 15, patches 6, probes 5); `git ls-files … | grep -c node_modules` is 0 (the two `node_modules`
links, `host/` and `rev5/`, are local and uncommitted). No tracked file outside the folder was
edited, and no generator ran.

**Commands and results: Lean** (`probes/compile.sh <file> <log>`, which runs
`LEAN_NUM_THREADS=1 lake env lean -M6144 -DwarningAsError=true <file>` in the worktree, toolchain
`leanprover/lean4:v4.33.1`, one process at a time; each log heads with the file's SHA-256).

| Probe | Log | Exit | Guards | Axiom lines (`#print axioms`) |
| --- | --- | --- | --- | --- |
| `probes/K2Copy.lean` | `logs/k2copy.log` | 0 | 118 hold; 10 red controls fail as asserted | 43 theorems: 31 `[propext, Quot.sound]`, 3 `[propext]`, 9 none |
| `probes/ReadableProfile.lean` | `logs/readable.log` | 0 | 37 hold; 6 red | 8, all `[propext]` |
| `probes/RefDedupe.lean` | `logs/refdedupe.log` | 0 | 8 hold; 2 red | 8 (6 theorems, 2 definitions), all `[propext, Quot.sound]` |
| `rev5/DefinitiveSchemaAudit.lean` | `logs/rev5-schema.log` | 0 | revision 5's | 13, all `[propext]`; body `diff`-equal to revision 5's `schema.log` |
| `rev5/ConstructiveProjectionProbe.lean` | `logs/rev5-projection.log` | 0 | revision 5's | 3 `[propext]`, 2 none; `diff`-equal to `projection.log` |
| `rev5/UnionImageProbe.lean` | `logs/rev5-union.log` | 0 | revision 5's | none printed |

Compile history: `logs/k2copy.run1…19.log`, `readable.run1.log`, `refdedupe.run{1,2}.log` (the
errors are listed in §1). The arm counts: `python3 probes/count-arms.py probes/K2Copy.lean`
(`logs/count-arms.log`, rerun at the head: unchanged).

**Commands and results: host** (from `S/host/` through `./run.sh <log> <command>`, which logs the
command, `bun 1.4.2`, `tsgo 7.0.0-dev.20260629.1` at `/opt/homebrew/bin/tsgo`, `node v22.23.2`, and
the exit; bun runs the vendored rc.112 source through `tsconfig.json` paths; tsgo checks against
the installed rc.112 declarations, whose sources match `vendor/effect-4.0.0-rc.112/SHA256SUMS`;
no TypeScript 5.9 and no `tsc` ran).

| Check | Command | Exit | Result |
| --- | --- | --- | --- |
| smoke | `bun run smoke.ts`; `tsgo -p tsconfig.tsgo.json` | 0; 0 | the vendored source resolves; the declarations check |
| question 2 | `bun run q2-edges.ts`; red twin; run 1 | 0; 1; 1 | 86 pass; 1 flipped expectation fails; 4 wrong expectations (history) |
| question 2 types | `tsgo -p tsconfig.q2.json`; `tsconfig.q2red.json`; `tsconfig.q2proto.json` | 0; 1; 0 | 18 exact types, 8 rejecting controls; TS2344 ×2; the quoted `__proto__` typed as a field |
| Codex's probes | `bun run codex/runtime.mjs`, `codex/reuse.mjs`, `codex/resolve-check.mjs`; `tsgo -p codex/tsconfig.green.json`, `red` | 0, 0, 0; 0, 1 | byte-identical to Codex's logs; TS2344 at `(6,44)` |
| revision 5 | `bun run runtime.mjs` (in `rev5/`); `tsgo -p ../rev5/tsconfig.green.json`, `red` | 0; 0, 1 | byte-identical to revision 5's `runtime.log`; TS1117 at `duplicate-red.ts(3,53)` |
| question 3 | `bun run q3-profile.ts`; red twin | 0; 1 | 31 examples, 176 decode comparisons, 0 failures; 1 |
| question 3 types | `tsgo -p tsconfig.q3.json`; `tsconfig.q3red.json` | 0; 1 | 16 exact types, 7 rejecting controls; TS2344 ×2 |
| question 4 | `bun run q4-routes.ts` (twice, byte-identical); red twin | 0; 1 | 33 checks, the summaries of §4; 1 |
| question 4 types | `tsgo -p tsconfig.q4.json`; `tsconfig.q4red.json`; `tsconfig.q4auto.json` | 0; 1; 1 | 9 intended types; TS2344 ×2; TS2344 (struct with rest) and TS2707 (`Exit`), the upstream defects |
| the defect slot | `bun run q4-defect.ts`; `bun run q4-defect-revive.ts` | 0; 0 | rc.112 persists the defect as `effect/schema/Json`; Lean's `Exit` revives with rc.112's id and `JsonReviver` |
| question 5 | `./q5-dedupe.sh`; `tsgo -p q5/tsconfig.raw.json`, `deduped`; `bun run runtime.ts`, red (in `q5/`) | 0; 1, 0; 0, 1 | the three fixtures `cmp`-identical; 22 TS1117, clean; equal revival, 8 keys |

**Bounded or host-only.** Every Lean result is about copies: theorems about `PTy`, the copied
arms and the probe's own definitions, plus finite `#guard`s, some on production functions (named
where used); nothing is a theorem about the tree. Every rc.112 behaviour is tested at the pin
(vendored rc.112 under bun 1.4.2; installed declarations under tsgo 7.0.0-dev.20260629.1), on the
inputs listed, and is host-only. Seat P's current copy (record fields with a `Bool` flag, a
tag-first field order, `nat` map keys) was read from `probe/P` with `git show` (reading, not
merged); the alignment statements in §7.2 and §6.2 depend on it.

**Owed** (each named where it arises): exactness by construction (§1.4 item 1); `hasTy_sub` at the
new forms (seat P); `Ty.schemaWf` from formation; the codecs of `null`, `undefined` (value images,
row 160), `number` (commit 3's frame), `bytes` (base64, row 161), `app` (host revivers); the
readable spellings of the declarations; per-key spelling through the bump (rows 164, 167); a
declarative admission predicate proved equal to the emission's domain (§3.1); the prepared
evaluator (§1.5).

**Proposed decisions rows and brief text.** §6 (new: S-A the readable profile, S-B the defect-id
counterexample; amendments to rows 8, 121, 122, 123, 125, 128, 157, 158, 159, 160, 161, 164, 167)
and §7 (W1's Schema half, W5, a Schema-face slice).

**Main moved during the seat** (the main checkout, branch `refactor/phase1-phase3`): seat T merged
(`8036f0b4`), probe R recorded (`e4481483`), row 165 ruled (`2bf570ca`), the data wave started
(`f8e2bb8b`) with briefs W1 and W5 drafted (`0f9f3a86`); §6 and §7 are written against those.
**Refused permissions**: none.
