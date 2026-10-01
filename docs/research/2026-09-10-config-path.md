# Config in the program model: the path, the decisions, the cost

Date: 2026-09-10. Read-only. The owner's premise: "we have a clean path to adding Config."
This note says which path is clean, what it reuses, and the five decisions it needs before a
dispatch. Citations are `path:line` at `ac07384`.

Short answer: yes, and the path is the reserved `program` row kind over the context model, with
the ConfigProvider as a context reference carrying a first-order tree. It reuses the whole
Config algebra that landed on 2026-09-05 and has had no consumer since the Surface estate was
retired, it mirrors rc.112's own mechanism instruction for instruction, and it gives the truth
harness a differential over the algebra rather than a tape of opaque answers. The combinators
are the one place the printer needs something new.

## 1. What is already here

- **The algebra.** `src/Effect4/Program/Config.lean` is rc.112's `ConfigProvider` and `Config`
  as a first-order, total model: providers as path transformers over a source, closed under
  `orElse` and `mapInput` (`:122-160`); the reader `eval` over `ConfigTerm` with
  `string`/`nat`/`bool`/`succeed`/`fail`/`withDefault`/`orElse`/`option`/`nested`/`zip`
  (`:743-780`); `Resolution`/`Failure` with the `hasInput` evidence rc.112 keeps
  (`:595-612`); `fromEnvRecord` with the underscore split and constant-case
  (`:452`, `:309-325`); `fromTree` over a record tree (`:505-546`); the requirement row
  `reads`/`provided`/`residual` over `Row ServiceKey` (`:1219-1455`). Twenty-eight theorems,
  six counterexample rows `E4-CONF-CE-001..006`, all at the axiom ceiling because the string
  codecs are a supplied `Scalars` hook (`:633-637`).
- **Its value image.** `src/Effect4/Program/ConfigValue.lean` writes `Config.Val` into the
  shared carrier and reads back exactly those six frames (`:29-64`, `image` at `:112`).
- **Its consumer is gone.** The algebra was built for deployment closure: "the deployment
  closes the config row" (`docs/research/2026-09-04-production-standards-spike.md` §4.7,
  `Deployment.bindings`). The Surface estate, deployments included, was archived at `ac07384`.
  Nothing under `src/Effect4/Program/Eff.lean`, `Compile.lean` or `Typing.lean` names Config.
- **The hook it was waiting for.** `RowKind.program` is documented as "a program of the Layer
  or Context model, run as a nested body" (`src/Effect4/Program/Eff.lean:64`), and the compile
  answers `frontier p` for it (`src/Effect4/Program/Compile.lean:584`): a reserved kind with
  no row in any table but the external placeholder (`Native.lean:162`).
- **The reference mechanism.** `Context.Reference` with a default and `getRef`
  (`src/Effect4/Machine/ContextMap.lean:264-271`), instantiated at `ValU` where every service
  carrier is `Val` (`:596-622`); the machine already reads `maxOpsRef` this way
  (`src/Effect4/Machine/Context.lean:545`). `Effect.service(key)` compiles as a context read
  followed by a lookup (`Compile.lean:633`, `serviceLookupK` at `:850`).

## 2. What rc.112 Config is

`Config<T> extends Effect<T, ConfigError>` (`vendor/effect-4.0.0-rc.112/src/Config.ts:108`).
It is an Effectable primitive whose evaluation is one line: read the `ConfigProvider` reference
off the fiber and parse against it (`:149`, `evaluate(fiber) { return this.parse(fiber.getRef(ConfigProvider.ConfigProvider)) }`).
`ConfigProvider` is a `Context.Reference` whose default is `fromEnv()`
(`ConfigProvider.ts:341-343`). The provider interface is two functions, `load` and `mapInput`
(`:269-306`), which is what the Lean `Provider` transcribes. Evaluation is pure over the
provider: the only effect is the provider's `load`, which may fail with `SourceError`.

The error is one tag: `ConfigError` with a `cause` that is a `SourceError` or a `SchemaError`
(`Config.ts:72-76`). The Lean `ConfigError` keeps three cases with paths
(`Config.lean:585-593`); the header records that as a deliberate refinement.

The scalar readers are `string`, `number`, `int`, `boolean`, `literal(s)`, `port`, `url`,
`duration`, `logLevel`, `redacted`, `date`, plus `nested`, `withDefault`, `orElse`, `option`,
`all`, `map`, `schema` (`Config.ts:1465-1943`). The Lean term covers the three scalars and the
five structural combinators.

## 3. Three routes, and why the second is the clean one

**A. External rows answered by the tape**, the KeyValueStore shape
(`src/Effect4/Program/Packages/KeyValueStoreMemory.lean`). One row per scalar reader, the
host's `ConfigProvider.fromEnv()` answers, the recorder writes the answers. Mechanical and
cheap. Two defects: the algebra stays unused and unchecked against the host, and every
combinator (`withDefault`, `nested`, `all`) needs either its own row or a printable request
that is itself a Config expression, which the row shapes cannot print today (§4, D3). It also
makes replay depend on a tape of answers for something that is a pure function of the
environment snapshot.

**B. Program-kind rows over the context model.** A Config read is a row of kind `program`
whose semantics is: read the `ConfigProvider` reference from the fiber's context (the bound
value, else the default), evaluate the request's `ConfigTerm` against it with `Config.eval`,
succeed with the value or fail with the `ConfigError` image. That is rc.112's `evaluate`
verbatim, over the algebra the tree already has. The provider default is the environment
record the run was loaded with, so replay is a function of the tape header, not of taped
answers. The truth harness then compares Lean's `fromEnvRecord env` against the host's
`ConfigProvider.fromEnvRecord(env)` on the same programs, which is the differential the six
counterexample rows were written for.

**C. Expansion over existing constructors.** Not available: no atom can look a path up in a
tree, and `withDefault` cannot be an Effect-level catch. `E4-CONF-CE-005` is the witness: a
partially supplied group is a failure carrying the group's evidence, not an absence, so a
catch on "missing" would default where rc.112 does not.

Recommend B.

## 4. The five decisions the path needs

**D1. The provider carrier.** A first-order tree as a `Val`: `Config.Tree` (`Config.lean:505`)
gets an `Image` beside `ConfigValue.lean`'s, records as `ctor` nodes, leaves as `str`. The
reference's default is `fromEnvRecord` of the load's environment snapshot, a
`List (String × String)`; the tape header carries it beside the row table. `fromEnvRecord`
walks strings and reaches `Classical.choice`, so the snapshot is converted once at the API
boundary, outside the audited compile, the way `stdScalars` is kept out of every theorem.

**D2. The error image under DB-15.** The column is `prod string string`, tag `"ConfigError"`
(rc.112 has one tag), message from Lean's own rendering of `missing path` / `invalid path msg`
/ `source`. rc.112's message is a `SchemaIssue` rendering that the tree should not try to
match byte for byte. Same ruling shape as G1 for sqlite: the harness compares the tag and
treats the message as the driver's. Under S4b it becomes `prod (lit "ConfigError") string`
with nothing else changing.

**D3. How a Config expression prints and reads.** This is the only new face. rc.112 spells
`yield* Config.string("HOST").pipe(Config.withDefault("x"))` and the data-first
`Config.withDefault(Config.string("HOST"), "x")`; the read is the expression itself, with no
wrapping call. Two candidate shapes:

- *Atoms build the term.* `Config.string`, `Config.number`, `Config.boolean`,
  `Config.withDefault`, `Config.nested`, `Config.orElse`, `Config.option`, `Config.all` as
  native atoms that evaluate to the `ConfigTerm` tree as a `Val`, typed at
  `Ty.handle "Config.Config<T>"` with `T` carried in the target spelling. Atoms already print
  as `name(args)` (`src/Effect4/Codegen/Print.lean:58-61`), so the expression prints for free.
  The read row is then one row family with a bare request: a new `RowShape` that prints the
  request expression and nothing around it. One appended `RowShape` constructor, declared.
- *Config heads in the reader.* Treat `Config.*` as heads of a term-level DSL beside the
  atom table. More code, no wire change, and a second head table to keep in step.

Recommend the atoms. The row family is one row per answer shape (`string`, `number`,
`boolean`, `pair`, `option`), because a row's answer type is fixed and the term's result type
must be known to the checker; the atom typings carry it in the handle target. Under S4b the
`literal` reader becomes typeable at `lit`.

**D4. How a provider is provided.** `ConfigProvider.layer(provider)` and `layerAdd`
(`ConfigProvider.ts:924`, `:970`) bind the reference; `fromEnvRecord(record)` and `fromMap`
build one. In the model: `provideService key tree` with the tree built by atoms
(`ConfigProvider.fromEnvRecord` over `strings`/`pair` pairs), and `provideLayer (.succeed key …)`
only after `litVal`'s string refusal (`Typing.lean:132-137`, `PROV-FB-STRING-VALUE`) is
revisited, since a tree is not a `Lit`. Step 1 needs only the default; step 3 needs this.

**D5. The scalar codecs at the compile boundary.** `stdScalars` uses `String.toNat?`, which
reaches `Classical.choice` on this toolchain (`Config.lean` header, spike §10 finding 1), and
`Test/Audit/AxiomGate.lean` audits every declaration. The evaluator must take `Scalars` as a
supplied hook through the interp, the `LeafSem` position, with `stdScalars` bound at
`Api.run` and in the harness. The spike already made this cut; the compile must not undo it.

## 5. What it costs

- **Lean, program side.** The row family and the `ConfigProvider` key with a fresh type code in
  `nativeServiceTy` (`Native.lean:284-295`, code 10); the `program`-kind compile arm replacing
  `frontier p` at `Compile.lean:584` with a context read and an `EffName.configRead`
  continuation, beside `serviceLookup`; the `Tree` and `ConfigTerm` images; the atoms in
  `NativeAtom` (`NativeAtom.lean:24-27`, `typeOf` at `:120`); the typing rule for `program`
  rows (today `perform` types every kind alike at `Typing.lean:204-210`, so only the request
  type changes); the appended `RowShape`; `Forms` rows for the pipe spellings.
- **Laws.** One agreement theorem: the compiled read's exit is `Config.eval` at the reference,
  in the `Means`/`Agreement` line. The requirement-row payoff the spike wanted now attaches to
  a program: `reads` of every Config term in the program against the snapshot, a
  "what must the operator set" report at `Api.typeOf`'s level. `absent_names_missing`
  (`Config.lean:1355`) is the theorem that makes it mean something and it is already proved.
- **Faces.** The printer and reader gain the bare-request shape and the atom names with dots
  (the reader's atom table is hand-copied fourteen times, three stale — DI-40 — and this adds
  eight names to every copy). The truth harness needs no adapter: `Config.*` and
  `ConfigProvider.fromEnvRecord` are rc.112 exports; the recorder writes the environment
  snapshot into the tape header. Both foreign readers gain the atoms.
- **Mirrors and goldens.** `RowShape` and `NativeAtom` regenerate (`derived`, `eff`, `wire`,
  `ts`); the OCaml hand copies of the atom table and shape alphabet change; new golden
  programs `pConfigString`, `pConfigDefault`, `pConfigNested`, `pConfigAll`, `pConfigMissing`.
- **Gates.** The compatibility gate sees one declared `RowShape` append and one atom append,
  after the removal policy the `choose` removal needs (`2026-09-10-subtyping-errors-scout.md`
  §3.4).

## 6. Sequence

1. **C0, the ruling packet.** D1–D5 above, one design-issue row each, the `RowShape` append
   declared.
2. **C1, scalar reads at the default.** `Config.string/number/boolean(name)`, the `program`
   compile arm, the reference with the environment-snapshot default, the error image, the
   agreement theorem, four goldens, four truth fixtures. No combinators, no provision.
3. **C2, the combinators as atoms.** `withDefault`, `nested`, `orElse`, `option`, `all`; the
   pipe spellings as `Forms` rows; the `E4-CONF-CE-004/005/006` behaviours reproduced by the
   harness on the host.
4. **C3, provision.** `ConfigProvider.fromEnvRecord`/`fromMap` as atoms building a tree,
   `provideService` binding the reference, `ConfigProvider.layer` once the layer leaf admits a
   tree value.
5. **C4, the requirement row.** `reads` lifted to programs and reported beside `EffTy`.

`literal`, `port`, `url`, `duration`, `logLevel`, `redacted`, `date` and `schema` stay out
until a row wants one; `literal` is the first to add after S4b.
