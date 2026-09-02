# Audit: the effects family after the split, and the lowering ecosystem

Date: 2026-09-02. Read at lean4-effects `ec5ef30` (v0.1.0 = `5611c3a`),
lean4-effect4 `de3e2ec`, lean4-whatwg `7f73251`, downstream `5670a7d`.
Evidence: `workshop/ExtensionProbe.lean` (321 lines), compiled against the
Effects v0.1.0 oleans; every theorem in it is within `propext`/`Quot.sound`.

## 1. Verdict

The algebra is nailed down and should stay frozen. What is not nailed down
is everything a lowering consumer touches first: signature reindexing, state
transport through towers, and the named-operation shape that a service class
has. Those three are generic, cheap (one induction each), and belong in
`Effects`. Adding them after a consumer ships is the churn to avoid.

The lowering ecosystem is about to duplicate itself: whatwg's P11 plan
mirrors Effect4's TypeScript target module for module, and EP-9 forbids the
one import that would prevent it. A TypeScript syntax package with no
dependencies fixes that.

## 2. What is settled (no change)

- Effects v0.1.0: nine modules, sixty theorems, 215 constants, ceiling
  `propext`/`Quot.sound`. `CLAIM-BOUNDARY.md` states exactly what is proved.
- Universe policy (answers, results, handler input in one universe) is right.
  `StateT σ (Program T)` needs `σ` in the answer universe; at universe 0 this
  never bites. Record it.
- Effect4's first-order rules (no closures in canonical content, scoped
  children as `BlockId`) are right and must not be relaxed for the target.

## 3. Three generic extensions, measured

| Need | Effect TS counterpart | Probe declarations | Cost |
| --- | --- | --- | --- |
| Signature morphisms, sum isomorphisms, empty signature | `R \| R1` is a set: `Exclude`, reassociation, `R \| R = R` | `Signature.Hom`, `Program.map`, `Handler.pull`, `interpret_map`, `map_id`, `map_comp`, `comm`, `assoc`, `codiag`, `empty` | one induction |
| State transport of handlers | `Layer.provide` with a `Ref`; `through` cannot express it | `MonadHom`, `Handler.mapHom`, `interpret_mapHom`, `interpretHom`, `through = mapHom` by `rfl`, `MonadHom.stateT` | one induction |
| Named-operation family and first-order alphabet embedding | `Context.Service` class shape; DSL output | `Family`, `Family.toSignature` (Σ), `Family.Service` ↔ `Handler` round trip, `Alphabet Ty`, `Alphabet.toFamily` | definitions only |

Today `Effect4/Schema/EffectfulField.lean` builds the third bridge by hand
per consumer (`FieldEffectOps` with an `operationId` map and a `read_answer`
cast). The generic embedding replaces that pattern.

DX rule learned in the probe: the embedding definitions must be `abbrev`.
With `def`, instance synthesis cannot see `Nat` through `Cell.Answer get`
and every `x + 1` fails.

## 4. Coexistence facts

- Exactly one Effect4 module imports `Effects`. The frame machine, scheduler,
  scope, cause and exit carriers never mention `Program`; every bridge row in
  `DESIGN-BASIS.md` is `Pending`. Effect4 reifies rc.112's runtime; Effects
  reifies programs; they meet nowhere yet. This does not block the npm goal,
  because lowering runs Family → Program → TypeScript with the host harness
  as evidence; the frame machine is conformance evidence off that path.
- whatwg requires `effects` and imports nothing from it until P4.
- Errors: Effect's `E` is a row and its `Cause` has four alphabets. In the
  algebra an error signature is a summand with `Answer := Empty`; `catch*` is
  a handler for it; defects and interrupts are runtime, not algebra.
- Scoped operations (`acquireRelease`, `fork`, `race`, scoped catch) fail the
  algebraicity test. Keep them out of `Effects`; `Flow/Region` owns them and
  they lower to `Effect.acquireUseRelease`/`Effect.scoped` from block children.

## 5. Duplication in progress

- `Whatwg/Streams/Target/TypeScript/{Ir,Lower,Render,Decode,Simulation}`,
  `Meta/{Emit,Introspection}`, `Alphabet/Combinators` are stubs with the same
  owners as Effect4's modules. Under EP-9 they would be re-implemented.
- `Effect4/Flow/{Block,Raw,Admission}` (1,700 lines of admission proofs)
  imports only `Std` and is generic in `Ty`. whatwg's alphabet stub is the
  same object.
- Gate machinery is copied three times (axiom gate, trust self-test) and the
  parity script twice.
- TypeScript-side tooling has no home: one `harness/` per repository, and
  the extractors from the language profile live only in a scratchpad.

## 6. Package map

| Package | Owns | Requires |
| --- | --- | --- |
| `effects` | algebra; new: `Signature.Hom` and sum isos, `MonadHom` transport, `Family`/`Alphabet` embedding; `Flow` moved from Effect4 | none |
| `typescript` (new repo `lean4-typescript`) | TS syntax IR (`Expr`, `Stmt`, `Decl`, `Import`, `Module` moved from Effect4), `Render` and `Style`, `Decode` round trip, identifier profile, `HostPin` record | none |
| `hash`, `nlp` | unchanged; nlp exchanges with TS through PTB and CoNLL-U files | none |
| `whatwg` | standards; lowers to plain TS or native streams | effects, hash, typescript |
| `effect4` | Effect TS reification; `Target/EffectV4` idioms (`Service` class, `Effect.gen`, `Layer.provide` = `mapHom (interpretHom)`, `Layer.merge` = `sum`, `Ref` = `StateT`); lowers families, programs and whatwg instances to Effect | effects, typescript, whatwg |
| `effect4-tools` (new npm workspace) | harness driver (tsc, tsgo, node pins), AST export, Effect profile extractors, publish pipeline for generated modules | pinned effect |
| `audit` (later, optional) | one MetaM gate parameterized by tree prefixes | none |

The DSL splits the same way: `effect_signature` core in `Effects/Meta`
emitting a `Family` plus first-order rows (names, arities, type codes);
TypeScript spellings, lexicon and LLM sheets in `Effect4/Target/EffectV4`.
General TypeScript parsing stays in TypeScript; Lean `Decode` covers only
the fragment Lean emits.

## 7. The npm contract

Stable, and therefore frozen by contract before the first publish:

1. the `Family` shape and its Σ-signature;
2. the row projection of a signature to `(R row, E row, A)`;
3. the identifier profile;
4. the Effect v4 idiom pins listed above;
5. the module header provenance: Lean package revision plus `HostPin`.

Everything else may change without breaking a consumer.

## 8. Order

1. Effects v0.2.0: the three extensions, each with a contract packet; move
   `Flow`; parity receipt.
2. `lean4-typescript` v0.1.0 by moving `Expr`/`Render`/identifier profile
   out of Effect4 with a parity receipt; Effect4 re-requires it.
3. `Effect4/Target/EffectV4`: service, program and layer renderers over the
   typescript package; family lowering replaces the `Lower`/`EffectV4` stubs;
   host harness gate.
4. `effect4-tools` and the first published generated module.
5. whatwg P11 against the typescript package; no second IR.

## 9. Not verified

The probe compiled with `lean` against oleans, not through `lake` or the
axiom gate. The `Flow` move was not attempted. whatwg's P11 was read from its
stubs and package plan, not from a P11 contract. No TypeScript was run.

## 10. Standup log (same day, after the audit)

Everything in §8 steps 1–4 was stood up in one pass, verification deferred
by the operator's ruling ("we already know the proofs"):

| Repo | Commit | State |
| --- | --- | --- |
| lean4-effects | `fa3cdc9` tag v0.2.0 | `Effects/{Morphism,Transport,Family}.lean`, `Effects/Flow/*` moved; gate green, 26 modules, 1536 declarations; algebra parity unchanged |
| lean4-typescript (new, local only) | `8f17b88` tag v0.1.1 | `TypeScript/{Syntax,Render,Identifier,HostPin}.lean`; `Expr.generic`, `Stmt.yieldDiscard`, `Decl.classDecl` added for the service idiom |
| lean4-effect4 | this commit | requires both; `Effect4/Flow/*` and `Target/TypeScript/{Expr,Render}` removed; `Target/TypeScript/EffectV4.lean` (rows, scripts, module) and `Meta/Derive.lean` (`effect_signature`, `effect_program`) replace their stubs; `harness/effect-v4-family/check.sh` green end to end: fixture byte-identical, tsc.original, tsgo strict, node run = Lean receipt |
| lean4-whatwg | uncommitted lakefile | pins effects v0.2.0 and typescript v0.1.1; `lake build Whatwg` green |
| downstream | `89ab4f9` | typescript registered |
| effect4-tools (new, local only) | `1b29ade` | harness driver, AST export, Effect profile extractors |

Local builds use `.lake/package-overrides.json` path overrides; manifests
are stale until the new commits are pushed and `lake update` runs in each
consumer (push order: effects, typescript, effect4, whatwg).

Not done, by ruling: contract packets and axiom reports for the new Effects
modules; a gate for lean4-typescript; `scripts/test-flow-admission-mutations.sh`
still names the moved files; Effect4's test root stays in its pre-existing
known-red state.

## 11. Patterns and decisions the standup exposed

Observed while building, in the order they bit:

1. **Namespace shadowing.** `open TypeScript` inside `Effect4.Target.TypeScript.*`
   opens the inner namespace. Rule for now: open the package before the
   `namespace` line. Decision owed: rename Effect4's target namespace
   (`Effect4.Target.EffectV4` is already the new module's home).
2. **Reducibility is part of the interface.** Family embeddings and every
   DSL-emitted shape must be `abbrev`, or instance synthesis cannot see
   `Nat` through `Cell.Answer get`. Rule: shapes are `abbrev`, theorems
   may be `def`.
3. **Three data layers, kept apart.** Algebra (`Family`, `Program`), rows
   (`ServiceRow`, `Script`), target IR (`Module`). The DSL emits the first
   two; every rendering is a pure function over rows. This held without
   strain and is the pattern to keep.
4. **Target idioms live in the profile, never in the family.** Nullary
   operations render as Effect values (tsgo `lazyEffect`); the algebra
   still sees `Param = Unit`. The profile decided, the family did not move.
5. **Handler DX is the weak point.** Writing a `Family.Service` is
   `fun name => match name with | .get => fun _ => … | .put => fun n => …`.
   Candidate abstraction: the DSL emits `structure Cell.Impl (M) where
   get : M Nat; put : Nat → M Unit` with `Cell.Impl.toService`. That record
   is byte-for-byte the object `Layer.succeed(Cell, { get, put })` takes.
6. **Requirement rows need automatic injection.** A program over
   `Cell ⊕ₛ Jobs` must write `Program.map Hom.inl` today; Effect's `R`
   union is silent. Candidate abstraction: a `Member F S` class whose
   instances are `Signature.Hom` chains found by typeclass search, so
   `Cell.get : Program S Nat` for any `S` containing `Cell`. This is the row
   normal form at the type level and the single largest DX decision.
7. **Errors are not in the family yet.** `Effect<A, E, R>` has a per-method
   `E`; `effect_signature` has no error slot. Two designs: (A) per-operation
   `Error name` with `Answer := Except (Error name) (Result name)`, which
   renders as `Effect.Effect<A, E>` per method with no new algebra;
   (B) an error signature summand handled by `catch*`. (A) is the cheaper
   lowering; (B) is the algebraic reading. Decision owed before the second
   family ships.
8. **Straight-line only.** `effect_program` is one block. Control flow is
   `Effects.Flow` (`choose`, `jump`), which now lives beside the algebra;
   the next lowering packet is Flow → `Effect.gen` with `if`/loops, and the
   DSL should emit Flow rather than `Script` once that exists.
9. **Atoms need a declaration.** Pure Lean functions called from programs
   need a pinned host body (`atoms.ts`). Candidate: an `atom` command that
   records the Lean model, the TypeScript spelling, and the import path as
   one row.
10. **Pins churn on every bump.** Exact-commit pins plus path overrides
    work locally; every bump needs the remote and a `lake update`. The
    downstream tree is where cross-package changes should be made first.
