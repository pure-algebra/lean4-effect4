# Seat R: the record terms, the faces, and the acceptance harness

Type-language probe, 2026-10-01. Worktree `/Users/pooks/Dev/lean4-effect4-probe-R`, branch
`probe/R`, base `bff50631`. Written incrementally; the receipt is at the foot.

## The one thing

**Row 119's positional value clause makes record projection type-directed, and only the checker
sees types: the evaluator, the authoring surface and both readers are type-blind, and the checker
produces no terms.** Proved on models: no atom and no untyped evaluator
can project a positional record soundly, with or without an index argument (the literal rule types
every number `nat`; `NativeAtom.eval` sees values only), so the stored term must carry a checked
position; the printed `t.name` drops that position, so no type-blind reader can invert the printer;
the authoring surface (`TermSrc`), the Lean reader and the TypeScript reader are all type-blind, and
the TypeScript reader has no checker at all; and one positional value fits two branches of a union
of records that rc.112 keeps apart, so stage 2's `_tag` select cannot be faithful. If a record value
carries its canonical names in the carrier's existing frames (`ctor 0 [list names, list values]`, no
new `Val` constructor), each of these goes away (proved: soundness with an untyped evaluator,
`read_print`/`read_exact` with an untyped reader, distinct values for the union's two objects).
**Recommendation:** amend row 119's value clause that way (row R-1) and add two `Term`
constructors (row R-2), `record (labels : List String) (args : Terms)` and
`field (target : Term) (name : String)`. If the owner keeps positional values, commit 6 must add a
resolution step (the Lean table reader threading the checker's environments, or an unresolved
projection resolved at admission) that the TypeScript reader cannot perform, and stage 2 needs a
discriminant-first field order.

## Evidence words

**Proved**: a kernel theorem run here, `#print axioms` at `[propext, Quot.sound]` or less.
**Tested**: a finite check run here (a `#guard`, a `#guard_msgs`, a `tsgo` or `node` run, a
count by command), with its red control. **Reading**: read in code or notes, not run.
**Assumed**: not checked. Every model theorem is about the model in its file, not about the tree.

## Q1. The term forms, both routes on a model

### The answer

**Route (b), dedicated `Term` constructors, spelled without nesting:**

```lean
| record (labels : List String) (args : Terms)   -- { l₁: t₁, …, lₙ: tₙ }, written order kept
| field  (target : Term) (name : String)         -- t.name; with the value clause of row R-1 (a)
| field  (target : Term) (index : Nat) (name : String)   -- instead, if positional values stay
```

Under row 119 as ruled (positional values) the atom route cannot be made sound for projection by
any evaluator (proved), and the brief's literal route (b), `field (t : Term) (name : String)`,
cannot either (proved): an untyped evaluator sees a positional value and a name, and the same
value and name need different answers at two record types. The stored projection must then carry
its checked position, and with it route (b) has progress and preservation over the whole term
language (proved). Q2 shows what the position costs on the faces: the printed `t.name` drops it,
so no type-blind reader can recover it (proved); that is the one thing of this note. With record
values that carry their names (row R-1 (a)), the name-only `field` is sound with an untyped
evaluator (proved), and so is the atom route; the recommendation stays constructors, because a
label is type-level data that prints as syntax (an atom's label is an argument: `recordGet(a0, a1)`
with `a1 : "b"` types, and leaves the printer no label to write as `a0.b`; tested, `Q1Named.lean`
§7) and the typing rule is then an arm of the `argTy` fold
rather than a custom scheme re-reading labels from `lit` argument types.

**The reason as a theorem shape.** What route (b) states and the atom route cannot (under
positional values; under R-1 (a) the field arm reads `lookupName n (canon fs) = some τ` and drops
the index):

```lean
-- the typing arm (a fold arm of argTy; a located refusal otherwise)
argTy sig Γ c (.field t i n) = some τ  ↔
  ∃ fs, argTy sig Γ false t = some (.record fs) ∧ (canon fs)[i]? = some (n, τ)
-- soundness: the tree's TermFits (Typed/Assembly.lean:837) with progress, from per-atom soundness
AtomsSound sig eval → EnvTyped Γ env → argTy sig Γ c t = some τ →
  ∃ v, evalTerm eval env t = some v ∧ hasTy τ v = true
```

The atom route's obligation is the tree's `NativeAtom.Sound` (`Laws/Program/Typed.lean:606`),
`typeOf tys = some τ → Fits vs tys → ∃ v, eval vs = some v ∧ hasTy v τ`, and for `recordGet` it is
false for every `eval`:

```lean
theorem recordGet_unsound   (ev : List Val → Option Val) : ¬ AtomSoundAt recordGetRule ev
theorem recordGetAt_unsound (ev : List Val → Option Val) : ¬ AtomSoundAt recordGetAtRule ev
theorem index_blind : argsTy sig Γ c [r, "n", k₁] = argsTy sig Γ c [r, "n", k₂]
```

The witness: `{a: nat, b: string}` and `{b: nat, c: string}` share the positional value
`ctor 0 [nat 1, str "x"]`; the argument list `[that value, "b"]` (or `[that value, "b", 1]`) fits
both argument-type lists, and soundness then demands one answer at `string` and at `nat`. The
typer cannot tell the index `1` from `0` because the literal rule types every number `nat`
(`Typing/Rules.lean:80`), and the evaluator cannot see the record type because `NativeAtom.eval`
takes `List Val` (`Machine/Term.lean:365`). This confirms Codex's `Projection.lean` (revision 2,
`projection_information_missing`) inside the checker's interface: a wrong-but-in-range index is
not refusable by an atom, and adding the index does not rescue it.

### Evidence (all **proved** in models unless marked; files under `R/probes/`)

| Claim | Theorem or check | File | Axioms |
| --- | --- | --- | --- |
| no evaluator makes `recordGet(r, "b")` sound (positional values) | `recordGet_unsound` | `Q1Positional.lean` | `[propext]` |
| nor `recordGet(r, "b", i)` | `recordGetAt_unsound` | same | `[propext]` |
| the literal rule erases the index | `index_blind` | same | `[propext]` |
| no untyped evaluator makes a name-only `field t name` sound (progress and preservation, as `NativeAtom.Sound` states it for atoms) | `NameOnly.unsound` | same | `[propext]` |
| route (b) with a checked position: progress and preservation | `sound`, `soundArgs` | same | `[propext, Quot.sound]` |
| the tree's `TermFits` shape (preservation only) | `termFits` | same | `[propext, Quot.sound]` |
| construction is sound: canonical permutation of values fits canonical fields | `align` (through `canon_map`, `mem_canon`) | same | `[propext, Quot.sound]` |
| projection at a checked position is sound | `field_sound` | same | `[propext]` |
| the evaluator is a fold of the generated shape | `evalTerm_fold` | same | `[propext, Quot.sound]` |
| a wrong-but-in-range index, an unknown name, a non-record target, a repeated label, a short label list: each refused; p2's `user.name` evaluates to `"bob"` | 11 `#guard`s, §10 | same | **tested** |
| the nested spelling `record (fields : List (String × Term))` does not derive `DecidableEq` (pinned); the recommended spelling does | `#guard_msgs`, 2 `#guard`s | `Q1NestedTermRed.lean` | **tested** |
| with names carried in the value: route (b) name-only projection has progress and preservation | `Named.sound`, `Named.termFits` | `Q1Named.lean` | `[propext, Quot.sound]` |
| with names carried: route (a) `recordGet` is sound | `Named.recordGet_sound` | same | `[propext]` |
| with names carried: an atom's label may be a variable of literal type, which types and has no member image | 4 `#guard`s, §7 | same | **tested** |

Commands: `bash R/run-lean.sh R/probes/<file>` (one thread, `-DwarningAsError=true`); logs
`Q1Positional.log` (exit 0, 1 s), `Q1Named.log` (exit 0, 2 s), `Q1NestedTermRed.log` (exit 0).
First runs: `Q1Positional` failed twice (an `if` rewrite `simp` read through `p.1 = q.1`, as the
data synthesis's model did; then `Decidable (… = some MTy.string)` with no equality on `MTy`,
replaced by `rfl`) and once at `Classical.choice` from `omega` in `zip3_proj`, replaced by
`Nat.succ_ne_zero`/`Nat.succ.inj`; `Q1Named` failed twice (a `match` on a hypothesis that did not
refine it, replaced by `cases`; a string disequality by `cases`, replaced by `injection` and
`decide`). Every final axiom line is in the logs.

### Per route: the rule, the equation, soundness, folds, wire, lines

| | Route (a): atoms `recordMake`, `recordGet` | Route (b): `Term.record`, `Term.field` |
| --- | --- | --- |
| typing | custom schemes over `List Ty`: `recordMake` reads labels from `lit` argument types (const-generic); `recordGet` reads `[record fs, lit n]` and answers `lookupName n (canon fs)`; an index argument types `nat` whatever its value | arms of the `argTy` fold (`Typing/Rules.lean:89-102`): `record ls ts` types `ts` at flag `false` (TypeScript widens literal field values), refuses `ls.length ≠ tys.length` and repeated labels, answers `record (ls.zip tys)`; `field t i n` answers the field type when `(canon fs)[i]? = some (n, τ)`, else a located refusal (`notARecord`, `unknownName n`, `wrongIndex n expected given`) |
| evaluation | `eval .recordMake [str n₁, v₁, …] = ctor 0 (values in canonical order)` is sound (labels are values); `eval .recordGet` has no sound definition on positional values | `evalTerm env (record ls ts) = ctor 0 ((canon (ls.zip vs)).map snd)`; `evalTerm env (field t i _) = (evalTerm env t).bind (· matches ctor 0 vs ↦ vs[i]?)` |
| soundness | `NativeAtom.Sound` false for `recordGet`, every evaluator | `sound`/`termFits` proved; the record and field arms are 25 lines of the 60-line mutual proof, on `align` and `field_sound` |
| generated folds | none: `Term` unchanged; the atom inventory (`Program/AtomInventory.lean`, generated from the enum) and the prelude (`harness/truth/prelude-atoms.gen.ts`) regenerate | `TermAlgebra` gains `term_record : List String → R .terms → R .term` and `term_field : R .term → Nat → String → R .term`; every position is `Pos.leaf` or `Pos.direct`, which the generator has (`tools/Effect4Gen/Fold.lean:44-62`), so `cata_term`, `foldM_term`, `foldMap_term`, `foldMapAt_term`, the `hom` connectors and `TermC.toValTerm` regenerate with no generator change (reading; the model's `evalTerm_fold` is the shape) |
| wire | none: atoms are named on the wire (`Machine/Term.lean:156`) | `Effect4.Program.Term` active `{var: 0, lit: 1, app: 2}` (`tools/Effect4Gen/wire-tags.json:41-43`): append `record: 3`, `field: 4` |
| compile-forced bill (`#exhaustive_gate` at `bff50631`, `Q1Bill.log`, **tested**) | `NativeAtom`: 3 (`eval`, `row`, `spec`); `CustomScheme`: 3 (`apply`, `declaredArity`, its `Repr`) | `Term`/`Terms`: 29 of 34 matches have no catch-all. Hand: `Term.scoped`, `Terms.scoped`, `Term.weaken`, `Terms.weaken`, `Terms.toList`, `Terms.names?`, `noRow`, `argTy`, `argsTy`, `evalTerm`, `evalTerms`, `printTerm`, `printTerms`; generated or `fold_of`-derived: `cata_term(s)`, `foldM_term(s)`, `foldMap_term(s)`, `foldMapAt_term(s)`, the `.hom`/`.alg` connectors, `TermC.toValTerm(s)`. Review (catch-all): `pairArgs?`, `readLiteral`, `tagTest?`, `tupleRequestReadable`, `TestClock.dilateAlgebra` |
| outside Lean (reading) | the prelude entries; the printer and reader special-case two atom names | `ts/eff/read.ts:647-668` (`readTerm`: object and member arms), the generated `eff.gen.ts`, `json.gen.ts`, `wire.gen.ts`, the OCaml `eff_*` group and the LCNF cut (`evalTerm` lowers) |
| model lines | `recordGetRule` 3, `AtomSoundAt` 3 | arms: `argTy` 8, `fieldTy` 6, `distinct` 3, `explainField` 7, `evalTerm` 10, `Term` 6; laws: 90 lines (`fitsL_*`, `zip3_proj`, `align`, `fieldTy_inv`, `field_sound`) on 70 lines of order lemmas shared with `Ty.normalize` (`ins_map`, `canon_map`, `mem_canon`) |

**Why the spelling `record (labels : List String) (args : Terms)`.** The tree keeps `Term`
un-nested on purpose (`Terms` is a hand list) and derives its equality and wire codec from the
declaration. `record (fields : List (String × Term))` nests `Term` under `List`/`Prod` inside the
mutual block, and Lean 4.33.1 refuses to derive its equality ("None of the deriving handlers for
class `DecidableEq` applied to `NTerm` and `NTerms`", pinned in `Q1NestedTermRed.lean`); the
labels-plus-`Terms` spelling derives (tested in the same file) and needs no generator work.

**Update, the tag select, optional fields, maps** (the other data-wave forms) are in Q3's forms
table; one finding belongs here. Positional values make a union of records ambiguous: two branches
can share a positional image (Codex's `{a: nat} | {b: nat}`, `#guard` in §9), and with a literal
`_tag` it happens as soon as a field name sorts before `_tag` in one branch, so that `_tag` sits at
different positions (UTF-8: `$`, digits and capitals sort before `_`):
`{_tag: "A", a: string} | {M: string, _tag: "D"}` admits the one value `ctor 0 [str "A", str "D"]`
in both branches (`union_value_ambiguous`, proved), and rc.112's two distinct objects
`{_tag:"A", a:"D"}` and `{M:"A", _tag:"D"}` lay out to that one value
(`positional_not_injective`, proved). A `_tag` select on positional values therefore cannot be
faithful to rc.112, and stage 2 needs either a discriminant-first order or a formation refusal of
overlapping branches. With names carried in the value the two objects stay two values, each a
member of its own branch only (`Named.union_values_distinct`, proved).

## Q2. Name preservation: printing, reading, special names

### The answer

Positional values carry no names, so a value prints and encodes only at its type: one value
prints as `{ body: "x" }` at `{body: string}` and as `{ name: "x" }` at `{name: string}`
(`printVal_needs_type`, proved; the record arm takes its keys from the type's canonical fields).
The term forms print as `{ l₁: t₁, … }` in written order and `t.name`, and **the printed
projection drops the stored position**: `field (var 0) 1 "b"` and `field (var 0) 0 "b"` both
print `a0.b`. Hence:

- **no reader that ignores types inverts the printer on well-typed terms** (`no_untyped_reader`,
  proved: the two terms above are well-typed at `{a: nat, b: string}` and `{b: nat, c: string}`);
- **a reader that resolves the position from the target's type does** (`read_print` on every
  well-typed term, `read_exact` on every accepted tree, proved), where resolving means typing the
  read target and taking the name's canonical position;
- **with names carried in the value, the untyped reader does** (`Named.read_print` on every
  scoped term, `Named.read_exact`, proved): `field t name` has nothing to resolve.

The tree's two readers are untyped: Lean's `readTerm (n : Nat) (x : Expr)`
(`Codegen/Read.lean:143-155`, depth only) and the TypeScript reader's `readTerm(n, x)`
(`ts/eff/read.ts:647-668`), which has no checker at all. Under row 119 as ruled, commit 6's
`read_print`/`read_exact` at `field` therefore needs one of: the Lean table reader threading the
checker's environment to every term leaf (the reader becomes the checker's traversal), or an
unresolved projection form that admission resolves (a second form of one construct in the stored
program, and a wire form the TypeScript reader emits that no evaluator can run). That is the one
thing of this note; the recommendation is the value-clause amendment (decisions row R-1 below).

### The printed image per name class, and what the reader accepts

| Name class | Construction | Projection | Vendored syntax | Evidence |
| --- | --- | --- | --- | --- |
| ASCII identifier, keywords allowed (`SourceBindings.identifierBytes`, `:46-49`), not `__proto__` | `{ b: "x", a: 1 }`, written order (`Expr.object`) | `a0.b` (`Expr.member`) | present | `#guard`s; tsgo green |
| any other name (`a-b`, `a"b`, `""`, `1`, Unicode such as `naïve`, `名前`) | every key quoted, `{ "a-b": 1, "default": true }` (`Expr.objectQuoted`); one non-identifier quotes all | `a0["a-b"]` | **bracket access missing**: one `Expr` constructor, one render arm, one `beq` arm, one `SourceBindings` arm (model `PExpr.index`) | `#guard`s; tsgo green; node |
| `__proto__` | every key computed, `{ ["__proto__"]: "x", ["a"]: 1 }` | `a0["__proto__"]` | **computed keys missing** (model `PExpr.objectComputed`) | node: own property; tsgo green |

The reader accepts exactly that image (tested, `Q2Faces.lean` §8): a quoted object whose keys are
all identifiers, a bare object with a non-identifier or `__proto__` key, a quoted object with a
`__proto__` key, and a bracket access at an identifier are each refused; `a0.b` reads as
`field (var 0) 1 "b"` under `[{a: nat, b: string}]` and as `field (var 0) 0 "b"` under
`[{b: nat, c: string}]`, and `a0.z` is refused.

**Host controls** (`R/host/names/`, all run on files in this folder):

- `node field-names.cjs` (node v22.23.2, exit 0, `field-names.log`, **tested**): a bare or quoted
  `__proto__` literal key creates no own property (Codex's control, both spellings); a computed
  key `{ ["__proto__"]: v }` and `Object.fromEntries` do; dot and bracket reads both find an own
  `__proto__`; `JSON.parse` creates an own `__proto__` and `JSON.stringify` writes it; spread copies
  it; composed and decomposed `é` are two keys; and JavaScript orders integer-like keys first
  (`{b, "10", "2", a}` iterates as `["2", "10", "b", "a"]`), so no face may read field positions off
  a JavaScript object's key order.
- `tsgo` (`/opt/homebrew/bin/tsgo`, 7.0.0-dev.20260629.1, `forms.log`, **tested**): the chosen
  images type-check (`forms-green.ts`, exit 0); `Object.fromEntries([["__proto__", "x"]])` does
  **not** type at `{ readonly __proto__: string }` (TS2741: `{ [k: string]: string }` lacks the
  property), so `Schema.dataObject`'s strategy (`Codegen/Schema.lean:32`) serves raw JSON data and
  maps, not typed records; and tsgo **accepts** the plain `{ __proto__: "x" }` at that type
  (`forms-trap.ts`, exit 0) although at run time it creates no own property, so a green tsgo check
  is not evidence for `__proto__`: the run-time control is node's. Red twins refused as expected
  (`forms-red.ts`, exit 1: TS2339 unknown name, TS2322 wrong field type, TS2741 missing field,
  TS2353 excess property in a literal, TS2741 for `fromEntries`).
- the exact strings `Q2Faces.lean` renders, at their types (`printed-forms.ts`): tsgo exit 0, and
  `node --experimental-strip-types` runs them (exit 0): the computed `__proto__` is an own
  property and every projection reads its field.

**Recommended name domain for stage 1.** Every string, with the three images above; or, if the
two missing `Expr` forms are not wanted in stage 1, refuse non-identifier names and `__proto__` at
record formation by name (B-accept) and lift the refusal when the forms land. p1–p5 use
identifier names only (reading of the five programs).

### The declared-type match and the parser arm

The Lean reader matches a service key's declared type by comparing `ofTy ty` with the parsed
`TypeRef` (`Codegen/Read.lean:356`); with `ofNormalized`'s record arm (Q3) the printer emits
`TypeRef.object`, so the round trip through the printer holds by the same equality. Source ingest
needs the parser arm `parseLegacy` lacks (`Codegen/Types.lean:18-21`): a copy of the parser with
an object arm (`Q3PrintedTypes.lean` §3, between `BEGIN`/`END` markers; 46 lines with comments,
`readFields` and `readFieldName`) reads back the eight printed forms tested (`readsBack`: plain,
quoted, Unicode and quote-bearing names, the empty record, an option of a record, a nested record,
a tagged union, a map of records), refuses five other spellings (no `readonly`, `,` separators, a
quoted identifier, `?`, a trailing `;`), and keeps the legacy sample of
`Test/Codegen/ExprContract.lean:81` (all **tested**). The TypeScript reader compares rendered
text (`readKey`, `ts/eff/read.ts:849-866`, through `typeName`, `:247-273`), which needs a
`TSTypeLiteral` arm producing the same text (reading).

### Evidence (files under `R/probes/` and `R/host/names/`)

| Claim | Theorem or check | Axioms or result |
| --- | --- | --- |
| a positional value prints only at its type | `Faces.printVal_needs_type` | `[propext]` |
| no type-blind reader inverts the printer on well-typed terms | `Faces.no_untyped_reader` | `[propext]` |
| the resolving reader: `read_print`, `read_exact` | `Faces.read_print`, `Faces.read_exact` | `[propext, Quot.sound]` |
| names in values: the untyped reader's `read_print`, `read_exact` | `Faces.Named.read_print`, `Faces.Named.read_exact` | `[propext, Quot.sound]` |
| the model renders as the vendored renderer on the shared fragment | 5 `#guard`s against `TypeScript.Render.expr` | tested |
| images per name class, and the reader's refusals | 16 `#guard`s, §8 | tested |

`Q2Faces.log`: exit 0. First run failed on `scoped` (a keyword) as a definition name, renamed.

## Q3. The printed types, the forms table, and row 68's record pairs

### The printed type forms

`ofNormalized` (`Codegen/Types.lean:268-313`) gains a record arm that prints `TypeRef.object` with
`readonly` fields in canonical order (model `ofTyM`, `Q3PrintedTypes.lean` §2; 3 lines plus a
7-line field helper; the canonical sort is taken after mapping, which `canon_map` makes equal to
mapping after sorting). The vendored renderer then spells every name outside `targetIdentifier`
quoted (`Render.lean:79-86`). Each spelling below was checked with tsgo against the type rc.112's
Schema gives the same data, by mutual assignability (B-print), in `R/host/types/printed-types.ts`
(green, exit 0) and its red twin (exit 1, four TS2345, one per refused spelling); compiler
`/opt/homebrew/bin/tsgo` 7.0.0-dev.20260629.1, effect 4.0.0-rc.112, log `printed-types.log`.

| Type (proposed `Ty`) | TypeScript spelling (printed) | tsgo, B-print | Reader arm |
| --- | --- | --- | --- |
| `record [(id, nat), (name, string), (role, "admin" \| "member")]` in any written order | `{ readonly id: number; readonly name: string; readonly role: "admin" \| "member" }` | mutual with `typeof Schema.Struct({…}).Type`, and with the permuted spelling: green | the object arm (`Q3PrintedTypes.lean` §3, 46 lines): reads back, tested; TypeScript reader: a `TSTypeLiteral` arm in `typeName` (reading) |
| a record with names outside the identifier profile | `{ readonly "content-type": string; readonly "default": boolean }` | mutual with the `Struct`: green | the object arm's quoted-name branch: tested |
| optional key, rc.112 `optionalKey` (stage 4; probe T's N1 brings it into the wave) | `{ readonly a?: number }` | mutual with `Struct({a: optionalKey(Number)})`: green | **none: `TypeRef.object` has no optional flag** (`TypeRef.lean:18`); the dependency bump (step 0) |
| optional, rc.112 `optional` | `{ readonly a?: number \| undefined }` | mutual with `Struct({a: optional(Number)})`: green; printing `a?: number` for it is **not** mutual: red | same |
| keyed map at string keys (row 125; probe T's `map (key value : Ty)`) | `Readonly<Record<string, number>>` (that is `{ readonly [x: string]: number }`) | mutual with `Schema.Record(String, Number)`: green; `ReadonlyMap<string, number>` is **not**: red | `TypeRef.name` with arguments: the legacy grammar reads it; round trip tested for a map of records |
| `ReadonlyMap` (rc.112 `Schema.ReadonlyMap`; a second map former only if a program needs `Map` values) | `ReadonlyMap<string, number>` | mutual with `Schema.ReadonlyMap(…)`: green | `TypeRef.name` |
| tagged union of records (stage 2) | `{ readonly _tag: "Deposit"; readonly amount: number } \| { readonly _tag: "Withdraw"; readonly amount: number }` | mutual with `Union([TaggedStruct…])`: green | union and object arms: tested |
| a record inside an existing former | `Option.Option<{ readonly body: string; readonly status: number }>` | green | tested |
| n-ary tuple (probe T's `tuple`) | `readonly [number, string, boolean]` | green; nested pairs are not a 3-tuple (TS2322): red (`forms-wave.ts`) | `TypeRef.tuple` exists; the legacy grammar reads tuples |
| nominal reference (probe T's `app`) | `Queue.Dequeue<{ readonly id: number; readonly payload: string }>` | green (`forms-wave.ts`) | `TypeRef.name` with arguments; a record argument needs the object arm (T's `HandleSpellings` guard 1 is today's refusal) |
| tagged error payload (row 120 as probe T amends it) | `export class NotFound extends Data.TaggedError("NotFound")<{ readonly id: number }> {}` | green; a structural record is not the class (TS2740): red | a class declaration read as its record type (probe T §4); `ClassDecl` exists in the vendored syntax, nothing emits it |

`#guard`s in `Q3PrintedTypes.lean` pin the rendered text of each Lean-side spelling (the record,
the quoted names, `__proto__` left bare in a type, the empty record `{}`, a record in an option,
the tagged union, the map); the parser arm reads back eight printed forms and refuses five other
spellings (Q2).

### The forms table: construction, projection, update, select, and what each prints as

All spellings tsgo-checked (`R/host/names/forms-*.ts`, `R/host/types/forms-wave.ts`, green exit 0,
red twins exit 1: nested pairs TS2322, index past the end TS2493 and TS2322, an unchecked map read
TS2322 under `noUncheckedIndexedAccess`, a record where the class is expected TS2740).

| Former | Construction | Projection | Update | Select | Term route | Vendored syntax |
| --- | --- | --- | --- | --- | --- | --- |
| record | `Term.record ls ts` → `{ a: x, b: y }` (written order; quoted or computed keys by name class) | `Term.field t (…) n` → `t.n` / `t["n"]` | not a stage-1 form; expressible as construction from projections; printed spread `{ ...t, b: y }` (tsgo green) needs a spread `Expr` | — | constructors (Q1) | object forms present; element access, computed keys, spread missing |
| optional field | omit the key; absent is the name missing from the value (names-in-value) or a slot marker (positional) | `t.a : τ \| undefined` lifted to `option τ` by the printer, `Option.fromUndefinedOr(t.a)` (reading; not tsgo-run) | as record | — | as record | the `?` flag missing |
| tagged union | a record with a literal `_tag` | after the select, record projection | as record | `Eff.select t (Decision.recordTag "A") hit miss` → `caseTagR(s, "A", hit, miss)`, a prelude helper narrowing by `Extract`/`Exclude` (tsgo green, `printed-types.ts`) | `Decision` gains a record arm (7 compile-forced matches, `Q1Bill.log`) | present |
| map (string keys) | atom over entries → `Object.fromEntries([["k", v]])` (types as the index signature; `__proto__` is an own property) | atom `mapGet(m, k)` → `Option`, reading own properties only (prelude, tsgo green) | atom `mapSet` (prelude, tsgo green) | — | **atoms**: the key is a run-time value, typed by a template over `map k v` | present |
| tuple | `[a, b, c]` (`Expr.arr`) | `t[2]` | rebuild | — | constructors, or atoms by arity | element access missing |
| nominal reference (`app`) | none (handles exist) | none | none | — | — | present (`TypeRef.name`) |
| tagged error payload | `new NotFound({ id: 2 })` | `e.id` after `catchTag("NotFound", …)` (tsgo green) | — | `Effect.catchTag` | payload carrier (row 120) | `new` missing; `ClassDecl` present, unused |

**Records against maps.** A record's labels are type-level (fixed by the type, known to the
checker, printed as syntax), so its forms are `Term` constructors; a map's keys are run-time
values, so its forms are atoms with template schemes, the DI-89 atom route doing what it is for.

### Row 68's record pairs (on a copy of the vectors, in this folder)

`Q3PrintedTypes.lean` §4 writes 19 pairs in `tools/Tools/TyVectors.lean`'s nine columns
(`R/host/assignability/record-vectors.tsv`): an exact `sub` (same canonical names, each field
below), and as the red control the same order with the record arm comparing written order. The
types are rendered in written order so that tsgo sees the permutations themselves.
`bun run.ts` (bun 1.4.2) asks `/opt/homebrew/bin/tsgo` 7.0.0-dev.20260629.1 both assignment
statements per pair and classifies as `tools/target/assignability.ts:68-85` does
(`record-assignability.tsv`, `run.log`, **tested**):

| Verdict | Pairs |
| --- | --- |
| agree (13) | permutation; nested permutation; tagged-union permutation; an option of permuted records; disjoint names; depth (`{a: "x"}` below `{a: string}`); the factor rule (`{a: nat \| string}` against `{a: nat} \| {a: string}`); record against tuple, `unknown`, `never`; three controls (`lit` below `string`, `nat`/`string`, a union above its member) |
| incomplete (6) | width and nested width (TypeScript's width rule); the literal-discriminant decomposition (`{a: "x" \| "y"}` is mutual with `{a: "x"} \| {a: "y"}` in TypeScript, TY-10's `record_sub_not_complete`); `{}` above `number` and above a record (TypeScript's `{}`); a record below a string map (an implicit index signature) |
| defect | none |

The red control is caught by four pairs (the three permutations and the option of permuted
records). Only the assignment-statement reading ran: the lane's driver takes its other reading,
the checker's `isTypeAssignableTo`, through tsgo's API from the repository's
`ts/eff/node_modules`, which this worktree does not have (bounded; `-` in the file). Pairs to add
to `TyVectors.lean` when `Ty.record` exists: these 19, generated from the real `Ty`.

## Q4. The boundary projection (row 122, route A)

### The answer

One fold reads a JSON value at a type and lays a record out in canonical order; its one parameter
is the policy at entries the type does not name (`Q4Boundary.lean`, `conv strict`):

- `conv true` is the **strict codec** (S-3, `Schema/Codec.lean:74-82`): it refuses extra,
  duplicate and missing keys;
- `conv false` is the **row adapter** of route A (`host-boundary.md` §7): it drops entries the
  type does not name, refuses a missing or duplicated declared name.

Proved on the model (`[propext, Quot.sound]` or less; `Q4Boundary.log`, exit 0, 1 s):

```lean
theorem codec_sub_adapt : decode t j = some v → adapt t j = some v      -- the codec's acceptances are the adapter's
theorem adapt_member    : adapt t j = some v → hasTy t v = true          -- what the session's reply check needs
theorem paired_control  : adapt userTy wider = some bob ∧ decode userTy wider = none
theorem adapter_not_exact : the canonical encoding of the adapted value has 3 keys, `wider` has 4
```

`adapt_member` is the membership half of host-boundary §4.5's receipt theorem at records: every
value the adapter hands the session is a member at the row's answer type, so the session's reply
check (`preflight` → `acceptReply`, `Api/HostSession.lean:162-174`) admits it. `adapter_not_exact`
is Codex's point (review §4) as a theorem: the adapter is a projection, the codec is the only one
of the two that can be an exact embedding (modulo `N_J`). The finite controls (tested): an exact
object in any key order is accepted by both with one value; a missing declared key and a duplicated
declared key are refused by both; a duplicated undeclared key is dropped by the adapter and refused
by the codec; a wider object nested inside a record is stripped at depth by the adapter and refused
at depth by the codec.

**The host control** (`R/host/boundary/rc112-excess.ts`, bun 1.4.2, effect 4.0.0-rc.112, exit 0,
`rc112-excess.log`, **tested**): rc.112's `Schema.decodeUnknownSync(User)` under its default parse
options strips the extra key exactly as `adapt` does (`{"id":2,"name":"bob","role":"member"}`), and
under `onExcessProperty: "error"` refuses it ("Expected no excess property") exactly as `decode`
does; both refuse a missing key. One difference, by design: a JSON text with a duplicated key
reaches rc.112 through `JSON.parse`, which keeps the last (`"id": 3`), while the Lean carrier keeps
both entries and both policies refuse (B-accept: refused by name, `duplicateKey`). A host object
cannot carry a duplicate, so route A's object path never meets the case.

### Where the adapter lives today, and the function it needs

Today there is no typed adapter (reading):

- the keyed session takes a `Val`: `Reply.completion : Answer` (`Api/HostSession.lean:48-54`),
  checked by `preflight`/`acceptReply` against the row (`:162-174`) through `externalValue` and
  `Val.hasTy` (`Program/Compile.lean:1371`);
- the truth harness's keyed driver turns host JSON into a `Val` with the untyped, shape-directed
  `decodeVal` (`harness/truth/session/Keyed.lean:84-107`: `{ctor, args}`, `{some}`, `{none}`,
  `{handle}`, arrays), which has no type to lay a record out by;
- on the TypeScript side the only row adapter is DB-15's error projection `toPair`
  (`harness/truth/prelude.ts:278-282`); no answer adapter projects objects.

The function the stage needs, beside the keyed session (a new `Api/Boundary.lean`, or in
`Api/HostSession.lean` before `submit`):

```lean
/-- Route A: host JSON at a row's answer type, extra keys dropped, laid out canonically. -/
def Boundary.adapt (row : Row) (j : Json) : Except AdaptRefusal Val      -- conv false row.answer.normalize
inductive AdaptRefusal | missingKey (at : Path) (name : String) | duplicateKey (at : Path) (name : String)
                       | notAnObject (at : Path) | leaf (at : Path)
theorem adapt_member : Boundary.adapt row j = .ok v → Fits w v row.answer   -- the receipt clause
theorem codec_sub_adapt : Schema.decode row.answer j = some v → Boundary.adapt row j = .ok v
```

On the TypeScript side the adapter is rc.112's own decode under default options followed by the
canonical layout, generated per row from the row's schema (`Row.document`), and the error side
stays `Effect.mapError(toPair)`. The stage's red controls keep the pair as a fixture: the adapter
strips `createdAt`, the codec refuses it (synthesis §7 item 4, the last control). Under the
names-in-value clause (Q1, row R-1) the adapter writes the names with the values and nothing else
changes.

## Q5. The acceptance harness

### The skeleton

`R/probes/P2RecordHarness.lean` (compiled with `-M6144`, exit 0, `P2RecordHarness.log`) is
`ProbeTodayP2.lean` re-spelled with records and written against an interface, `DataWave`, whose
parts are assembled from `parts : Parts`, each `none` today. The handler (§2), the scripted host
answering rc.112's objects as JSON (§3), the keyed session driver (§4, the programs seat's, unchanged),
the comparison with rc.112's answers modulo key order (§5, `N_J` as a function) and the report (§6)
are complete code today. `#guard_msgs` pins the six missing parts by name; `#guard acceptance == none`
and `#guard printedText == none` pin that nothing is checked yet. §7 runs the same handler and
driver today over a labelled pair stand-in for the interface (`pairsWave`, `pairHost`) and
reproduces rc.112's three answers, the checked type and the printed module's read-back (9
`#guard`s, tested), so the harness's machinery is known to work before the record parts arrive.

**Commit 8 is this diff:** fill the six fields of `parts` with the landed definitions; change
`#guard acceptance == none` to `#guard acceptance == some expected`; change
`#guard printedText == none` to the target module's text (below); the `#guard_msgs` becomes `[]`.
Nothing in §§2-6 changes unless the design does.

### What it needs from P, Q and S (the exact list)

| Part | Owner, data-wave commit | In the harness | State today |
| --- | --- | --- | --- |
| `Ty.record`, canonical order by name | P, 4 | `DataWave.recordTy` | missing |
| `Term.record`, `Term.field` and their authoring builders (`Program/Authoring.lean`, beside `app`) | R, 6 | `DataWave.record`, `DataWave.field` | missing |
| the codec's record arm, `Schema.encode`/`decode` at records (strict) | S, 5 | `DataWave.encode`, `DataWave.decode` | the codec exists, no record arm |
| the Schema arm, `Ty.schema` at records (S-1), for `Row.document` and the generated TypeScript adapter | S, 5 | not called by the run (the printer emits no schema, S-4) | missing |
| the row adapter at a record answer, Q4's `Boundary.adapt` | R or S, 8 (route A) | `DataWave.adapt` | missing |
| DB-15's error adapter for the tagged pairs | exists, host side (`harness/truth/prelude.ts:278-282`) | the row declarations of the `tsgo` check | present |
| the keyed session (`Api/HostSession.lean`) | exists | §4 | present |
| two host rows (`Row.host`) | exists | `getConfig`, `findById` | present |
| `Api.Author.build` admitting records (the generated groups regenerated, admission's record arm and inhabitance) | Q, 4 | `built?` | missing with `Ty.record` |
| the printer and reader arms (`printTerm`, `readTerm`, the object type arm) | R, 6 (and T's 8) | `Api.printModule`, `Api.readModule` | missing |
| the lean4-typescript bump (element access, computed keys if `__proto__` is admitted, the optional flag, `new`) | coordinator, step 0 | not needed by p2 (identifier names, no optional fields, no payload classes) | missing |

### The scripted host, the three answers, the printed module

The host answers rc.112's objects, each user row with one column the type does not name
(`createdAt`), so the adapter's stripping is exercised on every call; `UserRepo.findById` answers
rc.112's `toCodecJson` image of `Option` (`{"_tag":"Some","value":…}`, `Schema.ts:9720-9734`).
Expected answers (`hostruns.log`, bun 1.4.2, recorded by the model probe): `{"status":200,"body":"bob"}`,
`{"status":404,"body":"no user 9"}`, `{"status":401,"body":"bad token"}`, compared after `normJ`.

The printed module commit 8 must produce, checked with `/opt/homebrew/bin/tsgo` 7.0.0-dev.20260629.1
against p2's idiomatic object signatures with DB-15's error adapter on the rows
(`R/host/p2/printed-p2-records.ts`, log `typecheck.log`, **tested**):

```ts
export const handle: Effect.Effect<{ readonly body: string; readonly status: number }, readonly [string, string]> =
  Effect.catchIf(Effect.catchIf(Effect.flatMap(Effect.flatMap(AppConfig.get(), (a0) => Effect.suspend(() =>
  not(eq("secret", a0.adminToken)) ? Effect.fail(pair("Unauthorized", "bad token")) : … (a1) => Effect.suspend(() =>
  and(not(eq(a1.role, "admin")), not(eq(a1.id, 2))) ? … ), (a0) => Effect.succeed({ status: 200, body: a0.name })),
  … (a0) => Effect.succeed({ status: 401, body: snd(a0) }) … (a0) => Effect.succeed({ status: 404, body: concat("no user ", snd(a0)) }) …)
```

| Check | Result |
| --- | --- |
| the record module against idiomatic objects, rows through `toPair` | **exit 0** |
| the same module, rows without the error adapter (`SqlError` class) | exit 1, 2 errors (TS2375 ×2): the error channel only |
| today's positional module (the programs seat's red file, rerun here with tsgo 7) | exit 1, 12 errors (9 TS2345, 3 TS2375), as recorded at `2026-10-01-data-probe/programs/ts/typecheck.log` |

So records remove exactly the ten positional-projection errors, and DB-15's adapter the other two.

## Brief text for the data wave's commits 6, 7 and 8

Numbered as the synthesis's §7 series; probe T's draft series (its §2.4) numbers the same work 6
and 8 (terms and faces), 9 (vectors) and 10 (acceptance). Paste-ready.

**Step 0, required before commit 6 (coordinator).** Bump the lean4-typescript dependency
(`pure-algebra/lean4-typescript`, pinned at `6afc9b84` in `lake-manifest.json`) and pin it in
`lakefile.toml`, with: an optional flag on `TypeRef.object`'s fields (`readonly a?: T`); `Expr.new`
(payload classes, row 120); element access with an expression key, `target[key]` (record fields
outside the identifier profile, tuple projection at a literal index, map lookups at a run-time key);
and computed object keys, `{ [key]: value }`, if `__proto__` is admitted as a field name (the plain
and the quoted `__proto__` key create no own property, and `Object.fromEntries` does not type at a
record type: seat R's `host/names/forms-red.ts`, TS2741). Each is one `Syntax` constructor, one
`Render` arm, one `beq` arm, and one `SourceBindings` arm in this tree. Do not work around a missing
form by restricting the faces silently: a form the bump does not bring is refused by name at
formation (row R-3).

**Commit 6, the record term forms.** Rest on rows 119 (as amended by R-1) and R-2. First freeze
`Test/contracts/record-terms.contract.md` from seat R's draft
(`docs/research/2026-10-01-type-language-probe/R/contracts/record-terms.contract.md`) and write its
battery red (`Test/Program/RecordTermContract.lean`, `Test/Codegen/RecordFacesContract.lean`), with
falsifiers 001–012 as fixtures (the model theorems that refute the atom route and the positional
reader are kept as compiling theorems, not compile errors). Then, by explicit paths after narrow
builds:
1. `Machine/Term.lean`: append `record (labels : List String) (args : Terms)` and `field (target :
   Term) (name : String)` to the mutual block (the spelling that keeps `Term` un-nested and derives
   its equality), their `evalTerm` arms and `getField`; `tools/Effect4Gen/wire-tags.json`:
   `Effect4.Program.Term` gains `record: 3`, `field: 4`; regenerate the reached groups in the fixed
   order (derived, lcnf, eff, wire, cas, ts) and nothing else.
2. `Program/Typing/Rules.lean`: the two `argTy` arms (record fields typed at flag `false`), the
   located refusals `notARecord`, `unknownName`, `arity`, `repeated` in the checker; `Program/
   Authoring.lean`: the builders `record` and `field` beside `app`.
3. The hand traversals the append forces (`#exhaustive_gate`, 29 matches with no catch-all at
   `bff50631`): `Term.scoped`, `Terms.scoped`, `Term.weaken`, `Terms.weaken`, `Terms.toList`,
   `Terms.names?`, `noRow`, `argTy`, `argsTy`, `evalTerm`, `evalTerms`, `printTerm`, `printTerms`;
   review the five with a catch-all (`pairArgs?`, `readLiteral`, `tagTest?`, `tupleRequestReadable`,
   `TestClock.dilateAlgebra`): none may treat a record term as an application.
4. The faces: `printTerm`'s arms with the three name-class images (identifiers bare and `t.n`;
   others quoted and `t["n"]`; `__proto__` computed, or refused by R-3); `readTerm`'s inverses
   accepting exactly that image; `ts/eff/read.ts`'s `readTerm` object and member arms and
   `typeName`'s `TSTypeLiteral` arm; `Codegen/Types.lean`'s `ofNormalized` record arm and the
   `parseLegacy` object arm (seat R's copy: 46 lines, round trips on eight printed forms).
5. Laws: the packet's L1–L9 in the tree (L5 is row 148's `evalTerm_fits` with its two new arms;
   L8 the weakening lemmas; L9 `read_print`/`read_exact` at the new forms, untyped), and a node
   control for the `__proto__` image in the host lane.
Stop rules: a classifier that puts a record term in a positive class by a catch-all; a generated
path outside the named groups; any existing golden that changes bytes or corpus verdict that
changes. If row 119's positional clause stands (R-1 (b)): `field` carries `(index : Nat)` checked
by the typer, and this commit must also specify and land the resolution step of §6 of the packet,
with its laws, before `read_print` can be claimed; the TypeScript reader then cannot read a record
projection and is refused there by name.

**Commit 7, row 68's vectors over records.** Add a `record` family to `tools/Tools/TyVectors.lean`
generated from the real `Ty`: seat R's 19 pairs (`R/host/assignability/record-vectors.tsv`:
permutations, nested and tagged permutations, width and nested width, depth, the factor rule with
and without literal discriminants, disjoint names, the empty record against `number` and against a
record, record against tuple, `unknown`, `never`, a record against a string map, an option of
permuted records) and the optional-key pairs once the optional flag exists. Add the written-order
record arm as a second red control beside `subMutant`. Expected (seat R's statement reading,
tsgo 7.0.0-dev.20260629.1): 13 agree, 6 incomplete (width, nested width, the literal-discriminant
decomposition, `{}` above `number` and above a record, a record below a string map), 0 defect, the
control caught by the permutation pairs. Run `make check-target`, both readings, then
`make gen-assignability` to promote `generated/assignability.tsv`; a `defect` stops the commit.

**Commit 8, the acceptance: p2's handler end to end.** Copy seat R's
`docs/research/2026-10-01-type-language-probe/R/probes/P2RecordHarness.lean` into `Test/` (reachable
from `Test/All.lean` at the anchor the brief names), fill `parts` with the landed definitions
(`Ty.record`, the two builders, `Schema.encode`/`decode`, `Boundary.adapt`), and flip its pins:
`acceptance = some expected` (checked type `Response` with the infrastructure pair as error; the
three answers equal to rc.112's `{"status":200,"body":"bob"}`, `{"status":404,"body":"no user 9"}`,
`{"status":401,"body":"bad token"}` modulo key order; the printed module reads back as the built
program; the adapter strips `createdAt` and the codec refuses it) and `printedText` equal to the
target module of `R/host/p2/printed-p2-records.ts`. Host check: that file (the printed module, the
prelude atoms, the two rows declared at p2's idiomatic object types with DB-15's `toPair`) passes
`tsgo` 7 (exit 0; without the error adapter it fails with two TS2375, today's positional module with
twelve). The target stays bounded: the handler only, errors as DB-15's literal-tagged pairs, the id's
text threaded by the caller (row 131), the decode in the host (route A), `CurrentUser` as a value
(row 118); the layered program, in-program decoding (row 123) and structured service carriers are
not this commit.

## Decisions rows (proposals; this seat edits no register)

| Row | Proposal | Recommendation and evidence |
| --- | --- | --- |
| **R-1** (row 119 amended: the value clause) | (a) a record value carries its canonical names: `ctor 0 [list names, list values]`, names and values in canonical order, in the carrier's existing frames (no `Val` constructor); membership checks the names exactly; or (b) keep positional `ctor 0 values` | **(a).** Under (b) projection is type-directed and nothing that builds or reads programs has types: no atom and no untyped evaluator projects soundly (`recordGet_unsound`, `recordGetAt_unsound`, `NameOnly.unsound`), the stored position cannot be read back from `t.name` by a type-blind reader (`no_untyped_reader`), and the authoring surface (`TermSrc`, `Program/Authoring.lean:110`), the Lean reader and the TypeScript reader are type-blind; and one positional value fits two branches of a union of records that rc.112 keeps apart (`union_value_ambiguous`, `positional_not_injective`). Under (a) all of these are proved to go away (`Named.sound`, `Named.recordGet_sound`, `Faces.Named.read_print`/`read_exact`, `Named.union_values_distinct`). Cost of (a): one name list per record value, a name search per projection; row 119's three proved facts and exact subtyping are unchanged |
| **R-2** (new: the record term forms) | `Term.record (labels : List String) (args : Terms)` and `Term.field (target : Term) (name : String)` appended to `Term` (wire tags 3, 4), contract first (DI-78); the synthesis's §8 Q8 (atoms) closed against | **Constructors.** The atom route cannot state `NativeAtom.Sound` for projection under (b) (proved), and under either clause a label is type-level data printed as syntax; a map's key is a run-time value, so maps take atoms. With R-1 (b) the projection is `field (target) (index : Nat) (name)` plus a resolution step (packet §6) |
| **R-3** (new: the field-name domain) | every string; printed bare at ASCII identifiers other than `__proto__`, quoted with bracket access otherwise, computed for `__proto__`; the reader accepts exactly that image; until the lean4-typescript bump lands, non-identifiers and `__proto__` refused at formation by name | as stated; `Object.fromEntries` (TS2741) is not a typed record image, and tsgo accepts the plain `__proto__` literal that creates no own property, so the battery keeps a node control |
| **122** (amended: route A's adapter) | `Boundary.adapt (row : Row) : Json → Except AdaptRefusal Val`, the codec's fold with undeclared entries dropped, beside the keyed session before `submit`; laws `codec_sub_adapt` and `adapt_member`; the paired control a fixture; on the TypeScript side rc.112's default decode then the canonical layout, errors through `toPair` | proved on the model (Q4) and matched by rc.112 under bun on the four objects |
| **126** (untouched) | `eq` stays refused at records | falsifier 006 of the packet; under R-1 (a) a later `Val.eqAt` compares names and values |
| **N8** (probe T's dependency bump, amended) | add computed object keys and make element access take an expression key | computed keys are the only typed own-property image of `__proto__` (tsgo green, node own property); maps index by run-time keys |
| **stage 2** (with row 130) | the tag select over records is `Decision.recordTag (tag : String)`, reading `_tag` by name | under R-1 (b) it needs per-branch positions and a discriminant-first field order or a formation refusal of overlapping branches (falsifier 012) |

## Receipt

**First, the one thing the coordinator must know before merging:** the recommendation on the term
forms depends on an owner decision this probe surfaces, the value clause of row 119 (row R-1): under
positional values the forms need a position resolved from types that no reader or builder has; under
names carried in the value they need nothing. Commit 6's brief text is written for R-1 (a) with the
(b) variant stated.

**Base and head.** Branch `probe/R`, base `bff50631` (`git status` clean at the start, tested);
head: the commit that adds this note, the last on `probe/R` (its hash is in the hand-back).
Commits: `8f5fbcd0` (Q1), `1b166e97` (Q2), `de33468f` (Q3), `12d67235` (Q4), `db6ff5d7` (Q5 and the
packet), `90bde46d` (Q1 addendum: the atom's label), then this note. Nothing pushed, merged, checked out or reset.

**Changed paths** (all new, all under `docs/research/2026-10-01-type-language-probe/R/`, force-added):
`note.md`; `run-lean.sh`; `probes/{Q1Positional,Q1Named,Q1NestedTermRed,Q1Bill,Q2Faces,
Q3PrintedTypes,Q4Boundary,P2RecordHarness}.{lean,log}`; `contracts/record-terms.contract.md`;
`host/names/` (`field-names.cjs`, `forms-{green,red,trap}.ts`, `printed-forms.ts`, five tsconfigs,
three logs); `host/types/` (`printed-types{,-red}.ts`, `forms-wave{,-red}.ts`, five tsconfigs, two
logs); `host/assignability/` (`run.ts`, `record-vectors.tsv`, `record-assignability.tsv`, `run.log`,
`pairs/p0.ts`…`p18.ts` and its tsconfig); `host/boundary/` (`rc112-excess.ts`, its log);
`host/p2/` (`printed-p2-records{,-noadapter}.ts`, `today-positional-red.ts` copied from the data
probe's programs seat, four tsconfigs, `typecheck.log`). No tracked file edited.

**Commands and results** (from the worktree root; `R` = this folder):

| Command | Result |
| --- | --- |
| `bash R/run-lean.sh R/probes/Q1Positional.lean` (one thread, `-DwarningAsError=true`) | exit 0, 1 s; 25 axiom lines, all `[propext]` or `[propext, Quot.sound]` |
| `bash R/run-lean.sh R/probes/Q1Named.lean` | exit 0, 2 s; 9 axiom lines, same ceiling; 8 guards |
| `bash R/run-lean.sh R/probes/Q1NestedTermRed.lean` | exit 0; the nested deriving refusal pinned by `#guard_msgs` |
| `bash R/run-lean.sh R/probes/Q1Bill.lean -M6144` | exit 0, 40 s; `Term`/`Terms` 34 matches, 29 with no catch-all; `NativeAtom` 3/3; `CustomScheme` 3/3; `Decision` 7/7 |
| `bash R/run-lean.sh R/probes/Q2Faces.lean` | exit 0, 2 s; 6 axiom lines, same ceiling |
| `bash R/run-lean.sh R/probes/Q3PrintedTypes.lean` | exit 0, 2 s; 26 guards; the 19 vector lines (`VEC`) extracted to `host/assignability/record-vectors.tsv` |
| `bash R/run-lean.sh R/probes/Q4Boundary.lean` | exit 0, 1 s; 6 axiom lines (`MTy.ind'` none; the rest `[propext]` or `[propext, Quot.sound]`) |
| `bash R/run-lean.sh R/probes/P2RecordHarness.lean -M6144` | exit 0, 1 s; the six missing parts pinned; 9 guards over the pair stand-in |
| `node field-names.cjs` (v22.23.2) in `host/names` | exit 0, every control held |
| `/opt/homebrew/bin/tsgo -p tsconfig.{green,red,trap}.json` (7.0.0-dev.20260629.1) in `host/names` | 0; 1 (TS2339, TS2322, TS2741 ×2, TS2353); 0 (the `__proto__` trap) |
| `tsgo -p tsconfig.printed.json`, then `node --experimental-strip-types printed-forms.ts` | 0; 0 (own `__proto__`, every field read) |
| `tsgo -p tsconfig.{green,red}.json` in `host/types` | 0; 1 (TS2345 ×4) |
| `tsgo -p tsconfig.{wave,wave-red}.json` in `host/types` | 0; 1 (TS2322 ×3, TS2493, TS2740) |
| `bun run.ts` (1.4.2) in `host/assignability`, driving tsgo 7 | exit 0: 19 pairs, 13 agree, 6 incomplete, 0 defect; red control caught by 4 |
| `bun rc112-excess.ts` in `host/boundary` (effect 4.0.0-rc.112) | exit 0: default strips, `"error"` refuses, missing refused by both, JSON-text duplicate keeps the last |
| `tsgo -p tsconfig.{green,noadapter,today}.json` in `host/p2` | 0; 1 (TS2375 ×2); 1 (12: TS2345 ×9, TS2375 ×3) |
| `git add -f R/…` and `git commit` per group | six commits, then this note |

Every TypeScript check ran with tsgo 7.0.0-dev.20260629.1 (`/opt/homebrew/bin/tsgo`, the version
`generated/assignability.tsv` records; the coordinator's rule of today); no TypeScript 5.9 or `tsc`
ran at any point. The `effect` package was read by absolute path from the main checkout's
`ts/eff/node_modules` (the data probe's setup); nothing there was written.

**First runs that failed, kept in this note's text** (logs hold the final runs): Q1 (an `if`
rewrite read through `p.1 = q.1`; `Decidable` on `MTy` equality; `omega` reaching
`Classical.choice`), Q1Named (a `match` on a hypothesis; a string disequality by `cases`), Q2 (`scoped`
is a keyword), Q3 (the copied parser's `Store.decodeString` namespace; a duplicate `parseLegacy`; a
structural `sub` through `canon`, replaced by a fuel-bounded comparator with a fuel-independence
`#guard`), Q4 (a `match` inside `do`; a guard's precedence; a `where` binding used in a statement),
the harness (the pinned message's whitespace). The nested-deriving refusal is a pinned diagnostic,
not a failed run.

**Bounded or host-only.** Every theorem is about its model (`MTy` with eight or fewer formers, no
world, no handles, numbers as naturals in the JSON model), not about the tree; `EnvTyped` is seat A's
form without the world. The assignability pairs ran the assignment-statement reading only (the
lane's API reading needs `ts/eff/node_modules` in this worktree); 19 pairs is a finite alphabet. The
p2 target module is hand-written from the printed module of `ProbeTodayP2.log` with the record forms
substituted; the printer does not produce it today. The harness's §7 stand-in is labelled as one. The
cost of R-1 (a) at run time (a name list per value, a name search per projection) is reading, not
measured. Codex's revision-2 probes (`Projection.lean`, `UnionImage.lean`, `RawDuplicates.lean`)
were read, not rerun.

**Proposed decisions rows:** R-1, R-2, R-3, 122 (amended), N8 (amended), the stage-2 select (with
row 130); 126 untouched (table above). **Proposed counterexample rows:** `E4-RECORD-CE-001` through
`012`, the packet's §4. **Brief text:** commits 6, 7 and 8 above, with step 0.

**Not run, and why.** No `lake build`, no `make`, no generator (the brief); no OCaml (no mirror
was touched); no edit to a tracked file. No permission was refused.
