# Scout D — named keys, exact keys, full-key service identity: what the change is and what it costs

Working note, untracked. Scout D, 2026-09-17, at `6545d862` on `refactor/phase1-phase3`.
Research only: no tracked file was edited, no gate was run, no build was started. The
four probes live under the session scratchpad and are quoted below.

Evidence words are used strictly. **proved** = a Lean theorem in the tree. **compiled** = a
`#guard`/`#eval` I ran this session. **reproduced** = a red/green check I ran this session, or
a recorded run in the tree. **tested** = an existing battery. **stamped** = a gate marker.
**assumed** = neither. Every tree claim carries a path and a declaration name and is marked
*read*, *compiled* or *inferred*.

---

## 0. The five-line answer

1. "Full-key service identity" is one defect with one cause: **a printed key has no nominal
   identity on rc.112**, so Lean's requirement row (a set of full keys) maps onto a host `R`
   that identifies a service by its *carrier type*. Everything else in the chain — the key
   data, the wire bytes, the machine's context, the row algebra — is already full-key.
2. I reproduced it both ways this session: in Lean (`requires = [k5_4]` after providing
   `k4_4`) and under the repo's own `tsc` 5.9.2 (`R = never` for the same program), each with
   a red control. I also compiled the repair: with one class per key the same program's `R` is
   exactly `k5_4`, and weakening the annotation to `never` is caught as `TS2375`.
3. The change is **half-landed**: the *measurement* side landed at `38344fcc` (2026-09-13,
   bind each key by its printed shape, refuse a collapse as `noninjective`); the *repair*
   side — printing one nominal class per full key, and spelling `R` — is unstarted.
4. "Named keys" has **no written plan** anywhere in the record as a change to `ServiceKey`'s
   data (a `String` name). What the record does plan is the printed nominal class per full
   key (plan §3.3; DI-24's open half; drift-release R5). I recommend exactly that and no
   core-data change; the key stays two `Nat`s.
5. The cost is smaller than the record implies (§1.5): the pinned `typescript` package already
   carries `ClassDecl` and `Decl.classDecl` written for exactly this Effect idiom,
   `Fold.serviceKeys` already computes the hoist list, and the source-bindings checker already
   admits `class K extends Context.Service<K, …>()("k") {}` with a battery pinning it. The work
   is four printer/reader slices, three theorem restatements, one widened emission type, and one
   owner ruling (the class identifier's spelling). Three unregistered defects fell out along the
   way (§1.6, §5.9).

---

## 1. What the change is (Q1)

### 1.1 Three names, one thing

| name | where | what it means there |
| --- | --- | --- |
| "full-key service identity" | `docs/STATE.md:28`, `:47` (M2 list) | one item of the semantic repairs, unexpanded |
| §3.3 "Service identity is the full key, not the carrier's shape" | `docs/research/2026-09-16-foundational-language-implementation-plan.md:142` | the specification paragraph |
| S3c | same file, `:703` | "full service-key declarations, imports and row/adapter bindings" |
| DI-24's open half | `docs/DESIGN-ISSUES.md:98` | "a hoisted nominal service class per key, a printer and reader change" |
| DI-76 remedy (a) | `docs/DESIGN-ISSUES.md:150`, `:161` (DI-87 ratifies) | bind a key by the shape it prints, *together with* full-key identity |
| R5 of the drift release plan | `docs/research/2026-09-15-drift-release-plan.md:38` | "One nominal service class per full key, hoisted once per module and reused across nested programs, layers and adapters" |
| O16 | `docs/research/2026-09-16-strict-proof-obligations.md:28` | "`R` in the certificate and the declaration is the set of full keys (S3c), never the carrier union"; status "unstated" |
| B15 | `docs/research/2026-09-16-implementation-review-log.md:23` | the correction that made O16 the rule and DI-24's carrier union historical |

*(read)* These are one change. The plan's sentence is the specification; DI-24 holds the
printer half; DI-76 (a) holds the measurement half; O16 is the obligation nobody has stated.

**The brief's framing needs one correction.** "Named keys (the exact keys, or whatever it is
called)" suggests the keys themselves gain names. They do not, in any written plan. The
record's change is entirely about the **printed image**: the key data stays
`⟨ServiceName Nat, ServiceTypeCode Nat⟩`. §2.2 below sets out what "named" could mean and why
only one of the three readings is worth doing.

### 1.2 What identifies a service, site by site

Every site, with its verdict. "full key" means the site distinguishes `⟨4,4⟩` from `⟨5,4⟩`
*and* from `⟨4,5⟩`.

| # | site | declaration | identifies by | verdict |
| --- | --- | --- | --- | --- |
| 1 | `src/Effect4/Machine/Key.lean` | `ServiceKey`, `ServiceKey.Lt`, `DecidableEq` | full key (the pair) | correct *(read, compiled)* |
| 2 | `src/Effect4/Machine/Context.lean:72` | `Requirement := Row ServiceKey` | full key, ordered name-major | correct *(read, compiled: a two-key row has two elements)* |
| 3 | `src/Effect4/Machine/ContextMap.lean:67` | `Context.lookup` — `if h : s.key = key` | full key | correct *(read, compiled: `getV k5_4 = none` after `addV k4_4`)* |
| 4 | `src/Effect4/Machine/Stores.lean:155` | `Ctx.provide` | full key (through `addV`) | correct *(read)* |
| 5 | `src/Effect4/Program/Typing.lean:392,397` | `effTy` `.service` / `.provideService` | full key: `Requirement.single key`, `Row.diff … (single key)` | correct *(read, compiled: `requires = [k5_4]`)* |
| 6 | `src/Effect4/Program/Typing.lean:64` | `Signature.serviceTy : ServiceKey → Option Ty` | full key *as a signature* | correct *(read)* |
| 7 | `src/Effect4/Program/Native.lean:302` | `nativeServiceTy` | **the code alone** above `firstFreeName`; the reserved rows by full key | by design, not a defect — see below *(read, compiled)* |
| 8 | `src/Effect4/Codegen/Print.lean:312` | `printKey` | prints the full key **as a string**, the carrier as the type argument | runtime-correct, **type-conflating** *(read, compiled)* |
| 9 | `src/Effect4/Codegen/Read.lean:353` | `readKey` | the exact canonical text, and the exact type argument | correct *(read, compiled round trip)* |
| 10 | `src/Effect4/Codegen/Print.lean:611` | `declarationType` | omits the annotation entirely when `requires ≠ ∅` | the gap DI-24 names *(read, compiled: `.ok none`)* |
| 11 | `src/Effect4/Program/Derived.lean:997` | `ServiceKeyC` (generated `Canonical`) | full key, both fields on the wire | correct *(read)* |
| 12 | `tools/target/profile.ts:34` | `requirements` | **the carrier**, with an injectivity refusal | the measurement of the defect *(read)* |
| 13 | `tools/target/corpus.ts:55` | `bindings` | the manifest's `shape` per key | half of DI-76 (a) *(read)* |
| 14 | `ts/eff/read.ts:815` | the host key reader | the exact `k<n>_<m>` text | correct *(read)* |
| 15 | `ocaml/engine/e4_program.ml:184` | `of_service_key` | both fields | correct *(read)* |

**Site 7 is not the conflation.** `nativeServiceTy` reads the carrier off the *code*, which is
what a `ServiceTypeCode` is for; the key's identity is still the pair, and two keys with one
code are two services with one carrier. Compiled: `serviceTy ⟨⟨4⟩,⟨4⟩⟩ = serviceTy ⟨⟨5⟩,⟨4⟩⟩
= some Ty.nat` and `serviceTy ⟨⟨99⟩,⟨4⟩⟩ = some Ty.nat`, while `serviceTy ⟨⟨4⟩,⟨5⟩⟩ =
some Ty.bool`. The *signature* type is `ServiceKey → Option Ty`, so a signature is free to
type by the full key; the native one chooses not to. Nothing needs repairing here, but it is
the reason the conflation has teeth: the native alphabet makes same-carrier keys cheap to
draw, and the generator draws them.

**Site 8 is the conflation.** `printKey` emits

```
Context.Service<number>("k4_4")
```

rc.112's function-style overload is
`<Identifier, Shape = Identifier>(key: string, options?): Service<Identifier, Shape>`
(`vendor/effect-4.0.0-rc.112/src/Context.ts:252-258`, *read*). One explicit type argument
therefore binds **`Identifier`**, and `Shape` defaults to it. The requirement channel `R` of
`Effect.service(k)` is `Identifier` (`Key<out Identifier, out Shape> extends
Effect<Shape, never, Identifier>`, `Context.ts:64`, *read*). So the printed key's *type-level*
identity is its carrier, and two printed keys with one carrier are one requirement. The
*runtime* identity is the string, which is the full key ("The string key is the runtime
identity of the service", `Context.ts:219-221`, *read*) — which is why the run agrees and
only the type disagrees.

### 1.3 The conflation, reproduced twice this session

**Probe A, Lean** (`scratchpad/scoutD/KeyProbe.lean`, run with `lake env lean`; every `#guard`
passed, no error). The load-bearing lines:

```lean
def k1 : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩   -- prints "k4_4"
def k2 : ServiceKey := ⟨⟨5⟩, ⟨4⟩⟩   -- prints "k5_4"
def k3 : ServiceKey := ⟨⟨4⟩, ⟨5⟩⟩   -- same name as k1, different code

#guard sig.serviceTy k1 = some Ty.nat
#guard sig.serviceTy k2 = some Ty.nat          -- different name, same carrier
#guard sig.serviceTy ⟨⟨99⟩, ⟨4⟩⟩ = some Ty.nat  -- any free name, same carrier
#guard (printKey sig k1).map render = .ok "Context.Service<number>(\"k4_4\")"
#guard (printKey sig k2).map render = .ok "Context.Service<number>(\"k5_4\")"

def both       : Eff NativeOp := .bind (.service k1) (.service k2)
def providedK1 : Eff NativeOp := .provideService k1 (.lit (.nat 3)) both
#guard (effTy sig [] both).map (fun t => t.requires.elems.length) = some 2
#guard (effTy sig [] providedK1).map (fun t => t.requires.elems) = some [k2]
```

`#eval` output, verbatim:

```
requires = [{ name := { value := 5 }, service := { value := 4 } }], declarationType = some false
getV k1 = some (Val.nat 3)
getV k2 = none
getV k3 = none
Effect.provideService(Effect.flatMap(Effect.service(Context.Service<number>("k4_4")), (a0) => Effect.service(Context.Service<number>("k5_4"))), Context.Service<number>("k4_4"), 3)
```

Read: Lean keeps `k5_4` required; the machine's context does not answer `k5_4` or `k4_5` from
a `k4_4` entry; and `declarationType` produces `.ok none` — the printed module carries **no
declared type at all** for this program. *(compiled)*

**Probe B, TypeScript** (`scratchpad/scoutD/keys.ts`, checked with the repo's own
`ts/eff/node_modules/typescript` 5.9.2 under `--strict --exactOptionalPropertyTypes`,
exit 0). It mirrors `docs/research/2026-09-15-core-algebra-repair-evidence/TargetContract.ts`.

```ts
const F1 = Context.Service<number>("k4_4")
const F2 = Context.Service<number>("k5_4")
const fBoth    = Effect.flatMap(Effect.service(F1), () => Effect.service(F2))
const fAfterF1 = Effect.provideService(fBoth, F1, 3)
true satisfies Same<Requirements<typeof fBoth>, number>     // two printed keys, ONE requirement
true satisfies Same<Requirements<typeof fAfterF1>, never>   // providing k4_4 discharges k5_4

class C1 extends Context.Service<C1, number>()("k4_4") {}
class C2 extends Context.Service<C2, number>()("k5_4") {}
const cBoth    = Effect.flatMap(Effect.service(C1), () => Effect.service(C2))
const cAfterC1 = Effect.provideService(cBoth, C1, 3)
false satisfies Same<C1, C2>
true  satisfies Same<Requirements<typeof cBoth>, C1 | C2>
true  satisfies Same<Requirements<typeof cAfterC1>, C2>     // exactly k5_4 left
```

**Red control** (`keys-red.ts`, two assertions flipped) fails exactly where expected:

```
keys-red.ts(18,9): error TS1360: Type 'false' does not satisfy the expected type 'true'.
keys-red.ts(31,8): error TS1360: Type 'true' does not satisfy the expected type 'false'.
```

*(reproduced, with its red control)* So: the function form conflates, the class form does
not, and the class form's `Exclude` is exact per key. This is the whole repair in one page.

**The same thing is already recorded in the tree.** `harness/truth/corpus-results.tsv` rows
`g50`, `g89`, `g290` carry `types = mismatch-R` with the run agreeing on both faces, and
`harness/truth/corpus-known-differences.md:22` names the reason in DI-24's words. Row `g21`
carries `types = refused` with `Error: noninjective service binding: 8:4 and 11:4 both map to
number`. *(read)* Column tally of that promoted baseline, computed this session: 273 untyped,
110 agree, 8 refused, 6 mismatch-A, 3 mismatch-R. *(compiled — an `awk` count, not a run)*

### 1.4 Landed, half-landed, unstarted

| piece | state | commit / evidence |
| --- | --- | --- |
| Key data is the full pair, ordered, decidable | **landed**, long before this plan | `src/Effect4/Machine/Key.lean`; `Test/Machine/Environment/ContextKeyContract.lean` *(tested)* |
| Requirement row is a set of full keys | **landed** | `src/Effect4/Machine/Context.lean:72`, `src/Effect4/Program/Provision.lean` *(proved: `provide_discharges`, `merge_requires`)* |
| Machine context keyed by the full key | **landed** | `src/Effect4/Machine/ContextMap.lean` *(proved: `lookup_cons_same`, `Context.getV_addV_same`)* |
| Wire codec carries both fields | **landed** | `src/Effect4/Program/Derived.lean:997-1056` (`ServiceKeyC`) |
| Key printed with its full identity in the string | **landed** | `printKey`; `readKey_printKey` *(proved, `src/Effect4/Codegen/Read.lean:1074`)* |
| **Bind a required key by the shape it prints** (DI-76 (a), first clause) | **landed in the corpus lane only** | `38344fcc` (2026-09-13), `harness/truth/Truth.lean:580` `requireJson` emits `shape`; `tools/target/corpus.ts:55` `bindings`; `tools/target/profile.ts:34` `requirements` |
| **Refuse a same-carrier collapse rather than call it agreement** | **landed** | `tools/target/profile.ts:41`; `tools/target/profile.test.ts:36`; reachable since the shape fallback (`docs/research/2026-09-15-dogfood-3-receipt.md:200-213` recorded it unreachable before) |
| **One nominal class per full key, printed** | **unstarted on the printer, built on the admission side** | no printer emits `TypeScript.Decl.classDecl`, but `SourceBindings` already reads one — see §1.5.3 *(read)* |
| **`R` spelled in the declared type** | **unstarted** | `declarationType` returns `none` for a requirement-bearing program *(compiled)* |
| **Both module readers accept class declarations** | **unstarted** | `Program.readModule` refuses any `Decl` that is not `.const` (`src/Effect4/Codegen/Read.lean:672-690`); `layersPlain` (`src/Effect4/Codegen/Admit.lean:48-53`) refuses every non-`const` declaration in the envelope; `ts/eff/read.ts` has no class clause *(read)* |
| **O16 stated as a theorem** | **unstarted** | `docs/research/2026-09-16-strict-proof-obligations.md:28` records "unstated" |

### 1.5 Three things the change needs that already exist

*(read)* The record talks about this repair as if the printed-module machinery had to be
built. Three pieces are already in the tree, which is most of why §6's estimate is small.

1. **The target syntax already has the class form.** The pinned `typescript` package
   (`lakefile.toml:126-129`, rev `6afc9b84`) declares `ClassDecl` with `heritage : Option Expr`
   and `members : List String`, and `Decl.classDecl` beside `Decl.const`, and a `Module` with
   `header`/`imports`/`decls`. Its own docstring says why: *"The heritage is an expression
   because Effect's service classes extend a call, `Context.Service<Self, Shape>()("Name")`."*
   (`.lake/packages/typescript/TypeScript/Syntax.lean:245-266`, `:288-292` — a build artefact
   path, so not a citable source, but it is the pinned rev's content.) So **no package re-pin
   and no new syntax node is needed**; only Effect4's own emission type carries
   `List ConstDecl` where it should carry `List Decl`.
2. **The hoist list is already a fold.** `Fold.serviceKeys` (written in
   `tools/Effect4Gen/guards/fold.lean:42`, appended verbatim into
   `src/Effect4/Program/Fold.lean:3356`) collects every key an `Eff` mentions, through both the
   `Eff` arms (`service`, `provideService`) and the `LayerTerm` arms (`succeed`, `effect`),
   deduplicated. That is exactly "one class per full key of the program, layers included",
   computed by the generated fold rather than a hand list. Its `#guard` at `:64` is the control.
3. **The source-bindings checker already admits exactly this class.**
   `SourceBindings.declarationUses`' `.classDecl` arm
   (`src/Effect4/Codegen/SourceBindings.lean:259-264`) puts the class's own *type* in scope
   inside its heritage expression and not its value, requires a fresh name, and requires
   `members` to be empty — which is precisely `class K extends Context.Service<K, …>()("k") {}`
   and nothing looser. `declarationBinding` (`:246-250`) gives it a `classBinding`.
   `Test/Codegen/SourceBindingsContract.lean:119-128` pins it, comment and all: *"A class's own
   type is in scope in heritage arguments, but its value is not."* — accepting
   `class Service extends Context.Service<Service>()`, refusing `class Service extends Service`
   and refusing a class with members. **This is the half of DI-24's reader that is already
   written and tested.** What is *not* written is the envelope: `layersPlain`
   (`src/Effect4/Codegen/Admit.lean:48-53`) refuses every declaration that is not a plain
   exported `const`, so `admitModule` rejects a module with class declarations today, and
   `Laws/Codegen/Admit.lean:81` proves that refusal. That lemma is the one that must be
   restated, and it already has a `classDecl` case to restate. *(read; not compiled — I did not
   run the `SourceBindingsContract` battery, it is `tested` in the tree's sense.)*

### 1.6 Two live defects, found while reading, registered nowhere I could find

> **(a) The hand-selection lane never got DI-76 (a).** `tools/target/profile.ts:34` gives
> `requirements` a default `bindings = new Map()`, and `queriesFromInputs` calls it at `:156`
> as `requirements(types.requires, scope)` — with no bindings. So in the `check-target` lane
> every required non-scope key still throws `unbound service key <n>:<m>; no fallback from
> service code alone` (`profile.ts:38`), which is precisely the state
> `docs/research/2026-09-15-dogfood-3-receipt.md:206-207` recorded before the remedy. The
> shape fallback landed only in `tools/target/corpus.ts`. Either the two lanes should share one
> binding function or the hand lane's refusals are a false negative for the whole `R` axis.
> *(read; the consequence for `check-target`'s current output is inferred — I did not run it.)*

> **(b) The adapter branch of the corpus lane's key binding is dead code.**
> `tools/target/corpus.ts:47` builds `handles` from `selection.handles`, whose keys are
> *rendered target names* (`Test/fixtures/target/selection.json`: `"Host.Resource"`,
> `"SqlClient.SqlClient"`, `"KeyValueStore.KeyValueStore"`). `bindings` at `:55-63` then does
> `handles.get(id)` with `id = "<name>:<service>"`, which can never hit. Every corpus key is
> therefore bound by its shape, and the docstring's "The selection's adapter handles take
> precedence for the keys they name" (`:20`) is false as written. One map is being used in two
> incompatible key spaces; `bindRendered(text, handles)` at `:77-78` uses the other one
> correctly. *(read; not reproduced — reproducing it needs `bun`, which this brief forbids.)*

---

## 2. Named keys (Q2)

### 2.1 What rc.112 requires for two spellings to be one service

*(read, all from `vendor/effect-4.0.0-rc.112/src/Context.ts`)*

- `Key<out Identifier, out Shape> extends Effect<Shape, never, Identifier>` with
  `readonly key: string` (`:64`, `:68`). The requirement channel is `Identifier`; the runtime
  slot is `key`.
- "The string key is the runtime identity of the service. Reusing the same key string for
  unrelated services makes them occupy the same slot in a `Context`." (`:219-221`).
- Function form: `<Identifier, Shape = Identifier>(key: string, options?) => Service<Identifier, Shape>`
  (`:252-258`). With one type argument, `Identifier = Shape`. **This is what the printer emits.**
- Class form: `<Self, Shape>() => <const Identifier extends string, …>(id: Identifier, …) =>
  ServiceClass<Self, Identifier, Shape> & …` (`:309-324`), where
  `ServiceClass<Self, Identifier extends string, Shape> extends Service<Self, Shape>` with
  `new(_: never): ServiceClass.Shape<Identifier, Shape>` and `readonly key: Identifier`
  (`:123-128`), and `ServiceClass.Shape<Identifier, Service> = { [ServiceTypeId], readonly
  key: Identifier, readonly Service: Service }` (`:144-148`).

So the class form's requirement type is a structure whose `key` field is the **string literal
type** of the key. Two declarations agree exactly when their key strings agree — which is the
identity rule the estate wants, and it is *structural*, so two modules that each declare the
same key are compatible without importing each other. That is what
`docs/research/2026-09-15-core-algebra-repair-evidence/TargetContract.ts:24-34` already
recorded (`Same<K1, K1Again> = true`) and what my probe B confirms independently.

### 2.2 Three readings of "named", and which to take

| reading | what changes | verdict |
| --- | --- | --- |
| **(N1) a nominal class in the printed image**, identifier minted from the key, `class k4_4 extends Context.Service<k4_4, number>()("k4_4") {}` | printer, both readers, the module type, `declarationType` | **take this.** It is the record's plan (§3.3, DI-24, R5), it closes O16, it touches no core datum, no wire byte, no golden program's *semantics*. |
| **(N2) a name table in the signature**, `Signature.serviceName : ServiceKey → Option String`, used only to pick the printed identifier | one signature field, one native table, the profile export | **optional sugar on top of N1.** Costs a `Signature` field and a regeneration of `ts/eff/profile.gen.ts`; buys readable printed programs (`class Db …` instead of `class k8_8 …`). Recommend deferring until an authoring surface exists that can supply the name (§3). |
| **(N3) a `String` in the key**, `ServiceName := String` or an extra field | `ServiceKey` shape, its `Lt` and every order law, `ServiceKeyC` (`Derived.lean`), the OCaml `service_key`, the compat baseline, every golden byte, `Row` canonicality | **do not.** No written plan asks for it; `src/Effect4/Machine/Key.lean:44-52` refuses it with a stated reason ("a `String` name would require irreflexivity, transitivity, and trichotomy for `String.lt` from core alone, with no consumer at `L0`, and would import a persisted spelling question this slice does not own"). Nothing in the repair needs it: the *printed* name is already total and injective from the pair. |

*(read for all three; the N3 costs are inferred from the sites listed in §4 and §5)*

I searched the whole record for a plan that changes the key's data: `docs/DESIGN-ISSUES.md`,
`docs/DESIGN-BASIS.md`, the plan, the obligations note, the review log, the drift notes, and
every `docs/research/*.md` mentioning `ServiceName`. **There is none.** The mentions are all
inventory rows (the generator's type list, the OCaml framing column, DI-14's note that
re-framing `ServiceName` "moves every golden"). Stating this plainly, as the brief asks: *if
the owner meant N3, it is a new proposal with no prior ruling, and the smallest version of it
is N2 — a name table beside the key, not inside it.*

### 2.3 What the printed declaration needs so `R` can be spelled

With N1, `declarationType` becomes total:

```
Effect.Effect<A, E, R>   where R = C₁ | … | Cₙ, Cᵢ the class identifier of the i-th key of
                               ty.requires in row order, and `never` when the row is empty.
```

The row is already canonically ordered (name-major, `ServiceKey.Lt`), so the spelling is
deterministic without a second order notion — the `PORT-MANIFEST.md` canonicality rule
`Key.lean` cites is respected by construction *(inferred from
`src/Effect4/Machine/Key.lean:93-104`, read)*.

**Probe D checks the whole shape end to end**, with the class identifier minted as the key's
own spelling and the three-parameter annotation written out
(`scratchpad/scoutD/names.ts`, tsc 5.9.2, exit 0):

```ts
class k4_4 extends Context.Service<k4_4, number>()("k4_4") {}
class k5_4 extends Context.Service<k5_4, number>()("k5_4") {}
class k4_5 extends Context.Service<k4_5, boolean>()("k4_5") {}

export const main: Effect.Effect<number, never, k5_4> =
  Effect.provideService(
    Effect.flatMap(Effect.service(k4_4), () => Effect.service(k5_4)), k4_4, 3)

false satisfies Same<k4_4, k5_4>
false satisfies Same<k4_4, k4_5>
true  satisfies Same<Requirements<typeof main>, k5_4>
```

So the printed key's own text is a legal class name and a legal `Self` argument, same-carrier
keys stay apart (`k4_4` vs `k5_4`), same-name keys stay apart (`k4_4` vs `k4_5`), and the
declaration Lean would print is accepted by `tsc`. **Red control** (`names-red.ts`, the
annotation weakened to `never`, which is what the host infers today):

```
names-red.ts(10,14): error TS2375: Type 'Effect<number, never, k5_4>' is not assignable to
  type 'Effect<number, never, never>' … Type 'k5_4' is not assignable to type 'never'.
names-red.ts(17,8): error TS1360: Type 'true' does not satisfy the expected type 'false'.
```

*(reproduced, with its red control)* That first diagnostic is the whole point of the change:
under N1 the host **catches** the unprovided key that today's `mismatch-R` rows record as a
disagreement between the two faces.

DI-24's current text still says the `R` spelling is "the union of the requirement row's
service carriers in `printKey` order" and that it "is **not** injective in the key". **That
clause is superseded** by B15 (`docs/research/2026-09-16-implementation-review-log.md:23`)
and O16. The DI-24 row needs amending in the same slice, or the register and the obligations
note disagree on the record.

### 2.4 Against B19 and the R4 template table

- **B19 (types meet source by projection only).** N1 is a projection: the class declaration is
  computed from `(key, sig.serviceTy key)` by a total function, and the requirement spelling is
  computed from the row. Nothing reads a type *out of* source, and no inverse of `ofTy` is
  needed. The reader's job is recognition, not inversion: it checks that the class declaration
  it sees is *exactly* the one the printer would emit for that key, the same premise `readKey`
  already uses (`text = keyText key`, `Read.lean:356`). *(inferred; consistent with
  `docs/research/2026-09-16-typed-surface-integration-analysis.md`'s stance as summarised in
  the memory index — I did not re-read that note.)*
- **R4's template table.** `docs/research/2026-09-17-r4-r5-r6-template-table-ready-packet.md:71`
  lists `ServiceKey` among the **leaf sorts** that "keep their hand printers and readers,
  because they are not skeletons". N1 does not change that: the leaf printer `printKey` keeps
  its shape (it emits an *identifier* instead of a call once the class exists, which is a
  smaller leaf, not a bigger one). What N1 adds is above the table: a module-level declaration
  list, which the table does not model. **R4/R5 and N1 are independent** and can be ordered
  either way; doing N1 *after* R5 means writing the reader clause once instead of twice
  (`Read.lean` is being rewritten at R5).

---

## 3. Authoring and sugar (Q3)

### 3.1 How an author writes a service today

The authoring surface is `src/Effect4/Program/Authoring.lean` plus the **generated** lifts
`src/Effect4/Program/Authoring/Lifts.lean` (generated from `tools/Effect4Gen/binders.json`
and the environment, header lines 1-6, *read*). The service arms are:

```lean
def service {Op : Type} (key : Effect4.ServiceKey) : Src Op                                  -- :134
def provideService {Op : Type} (key : Effect4.ServiceKey) (value : TermSrc) (body : Src Op)  -- :138
def Layer.succeed {Op : Type} (key : Effect4.ServiceKey) (value : Lit) : LayerSrc Op         -- :253
def Layer.effect  {Op : Type} (key : Effect4.ServiceKey) (body : Src Op) : LayerSrc Op       -- :257
```

A key is written as a raw anonymous constructor. The two live examples:

- `Test/Program/LayerSharingContract.lean:16-17`: `def kA : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩`,
  `def kRef : ServiceKey := ⟨⟨6⟩, ⟨7⟩⟩`.
- `src/Effect4/Program/Provision.lean:615-618`: `dbKey`, `rateKey`, `dbBinding`, `rateBinding`,
  four hand-written pairs.

*(read)* Nothing connects a key to its carrier at the authoring site: `kRef`'s carrier
(`Ref.Ref<number>`) is decided elsewhere, by `nativeServiceTy`'s code table
(`src/Effect4/Program/Native.lean:291-293`), and the author is expected to know that `7` means
`Ref`. That is the authoring defect, and it is separate from the printing defect.

### 3.2 The proposed surface

One authoring-only definition, over the existing constructors, in the shape rc.112 uses. It
introduces **no** `Eff` constructor, no wire tag, and no `Signature` field in its first cut.
**Everything in this section is compiled**: probe C (`scratchpad/scoutD/ServiceDefProbe.lean`)
holds exactly this code, every `#guard` passes, `carrier_unique` is proved, and the three
examples of §3.3 elaborate, type and print.

```lean
/-- A service an author declares once: its key, and the carrier the signature types it at. -/
structure ServiceDef where
  key : Effect4.ServiceKey
  carrier : Effect4.Program.Ty
  deriving DecidableEq, Repr

namespace ServiceDef

/-- `Service.define` — the author writes the three facts once: the key's nominal half, the
key's type code, and the carrier the signature must type it at. `Agrees` checks the third
against the signature; nothing here invents a carrier. -/
def define (name : Nat) (code : Nat) (carrier : Ty) : ServiceDef := ⟨⟨⟨name⟩, ⟨code⟩⟩, carrier⟩

/-- The declaration agrees with the signature it is used under. Decidable, checked at the
authoring site by `#guard`, and a premise of the printer's class emission. -/
def Agrees {Op : Type} (sig : Signature Op) (s : ServiceDef) : Bool :=
  sig.serviceTy s.key == some s.carrier

def use   {Op : Type} (s : ServiceDef) : Src Op := Authoring.service s.key
def give  {Op : Type} (s : ServiceDef) (value : TermSrc) (body : Src Op) : Src Op :=
  Authoring.provideService s.key value body
def layer {Op : Type} (s : ServiceDef) (value : Lit) : LayerSrc Op := Authoring.Layer.succeed s.key value
def built {Op : Type} (s : ServiceDef) (body : Src Op) : LayerSrc Op := Authoring.Layer.effect s.key body

end ServiceDef
```

`Agrees` is the piece that matters: it is the **conflicting-carrier refusal** the plan asks
for ("conflicting carriers for one key refuse", `plan:142`) moved to the authoring site, where
it is a `decide` rather than a runtime path. The proof is four lines, and I wrote it:

```lean
/-- Two declarations of one key with different carriers cannot both agree. -/
theorem carrier_unique {Op : Type} {sig : Signature Op} {a b : ServiceDef}
    (hk : a.key = b.key) (ha : Agrees sig a = true) (hb : Agrees sig b = true) :
    a.carrier = b.carrier := by
  simp only [Agrees, beq_iff_eq] at ha hb
  rw [hk] at ha
  exact Option.some.inj (ha.symm.trans hb)
```

*(compiled, probe C — no `sorry`, no axiom beyond Lean's own.)*

### 3.3 Before and after

**(a) A program requiring one service.**

```lean
-- before
def readsRef : Src NativeOp := service ⟨⟨6⟩, ⟨7⟩⟩

-- after
def Cell : ServiceDef := ServiceDef.define (name := 6) (code := 7) (carrier := NativeOp.refTy)
#guard Cell.Agrees (nativeSignature [])
def readsRef : Src NativeOp := Cell.use
```

**(b) Providing it by value.**

```lean
-- before
def withRef : Src NativeOp := provideService ⟨⟨6⟩, ⟨7⟩⟩ (var "r") (service ⟨⟨6⟩, ⟨7⟩⟩)
-- after
def withRef : Src NativeOp := Cell.give (var "r") Cell.use
```

**(c) Providing it by a layer.** (Adapted from `Test/Program/AuthoringContract.lean:130-136`,
*read*.)

```lean
-- before
def counter : LayerSrc NativeOp :=
  Layer.effect ⟨⟨4⟩, ⟨4⟩⟩ <| bind "ref" (service ⟨⟨6⟩, ⟨7⟩⟩) <| …
-- after
def Count : ServiceDef := ServiceDef.define (name := 4) (code := 4) (carrier := .nat)
def counter : LayerSrc NativeOp := Count.built <| bind "ref" Cell.use <| …
```

**(d) Two services sharing a name but not a shape — must stay distinct.**

```lean
def CountA : ServiceDef := ServiceDef.define (name := 4) (code := 4) (carrier := .nat)   -- k4_4
def FlagA  : ServiceDef := ServiceDef.define (name := 4) (code := 5) (carrier := .bool)  -- k4_5
#guard CountA.key ≠ FlagA.key
#guard CountA.Agrees (nativeSignature []) && FlagA.Agrees (nativeSignature [])
```

Compiled this session in probe A: `serviceTy ⟨⟨4⟩,⟨4⟩⟩ = some .nat`,
`serviceTy ⟨⟨4⟩,⟨5⟩⟩ = some .bool`, `k1 ≠ k3`, and `getV k3 = none` after `addV k1`.
*(compiled)*

Probe C's `#eval` output for (a), (b) and (c), verbatim (with `withRef` binding its reference
first, since `var "r"` at the empty environment is correctly refused by the elaborator):

```
readsRef requires = some [{ name := { value := 6 }, service := { value := 7 } }]
withRef  requires = some []
Effect.flatMap(Ref.make(0), (a0) => Effect.provideService(Effect.service(Context.Service<Ref.Ref<number>>("k6_7")), Context.Service<Ref.Ref<number>>("k6_7"), a0))
counter layerTy = some [{ name := { value := 4 }, service := { value := 4 } }]
```

*(compiled)* The layer provides exactly `k4_4` and nothing else; the program discharges
exactly `k6_7`.

**What this does not do.** It does not make the *printed* image distinguish `CountA` from a
different `nat`-carried key; only N1 does that. The two changes are complementary: `ServiceDef`
is where an author says which service they mean, N1 is where the printed program says it.

### 3.4 Does it FEEL like Effect

rc.112's author writes one line per service and then uses a value:

```ts
class Db extends Context.Service<Db, { query: (s: string) => string }>()("Db") {}
const p = Effect.flatMap(Effect.service(Db), db => …)
```

`ServiceDef.define` + `use`/`give`/`layer`/`built` is the same shape: one declaration, then a
value used four ways. With N2's name table the printed image becomes `class Db extends
Context.Service<Db, …>()("Db") {}` and the correspondence is exact. Without N2 the printed
identifier is `k6_7`, which is honest and ugly. *(inferred)*

One sugar to resist: an `Eff` constructor for "declare a service". A declaration is not a
program step; it is a fact about the signature. Keeping it in `ServiceDef` costs no wire tag
and no proof obligation, which is the estate's standing rule for additions.

---

## 4. Proof work (Q4)

Statements that mention a key or a requirement and would move. Difficulty is my estimate,
marked *(inferred)* unless a premise is already in the tree.

| # | declaration | today | after | difficulty |
| --- | --- | --- | --- | --- |
| P1 | `effTy` `.service`/`.provideService`, `src/Effect4/Program/Typing.lean:392-401` | full key already | **unchanged** | none |
| P2 | `HasTy.service`, `HasTy.provideService`, `src/Effect4/Laws/Program/Typing/HasTy.lean:233-245`; `inv_service`, `inv_provideService`, `Typing/Inversion.lean:213-229` | full key already | **unchanged** | none |
| P3 | `LayerTyHasTy.succeed/.effect`, `HasTy.lean:415-427`; `inv_layer_succeed/_effect`, `Inversion.lean:449-462` | full key already | **unchanged** | none |
| P4 | `Provision`'s row algebra: `provide_discharges`, `provide_closed`, `covers_of_provide_closed`, `merge_requires`, `satisfies_single_addV`, `build_total`, `buildAll_total` (`src/Effect4/Program/Provision.lean:86,98,107,143,206,343,475`) | full key already, `Row.diff`/`Row.union` membership | **unchanged** | none — this is the part that was already right |
| P5 | `Context.lookup`/`get?`/`add` laws, `src/Effect4/Machine/ContextMap.lean`; `Env.Context.handleKeys_add`, `Laws/Machine/Handles.lean:278` | full key already | **unchanged** | none |
| P6 | `printKey`, `readKey`, `readKey_printKey` (`src/Effect4/Codegen/Read.lean:1074`), `printKey_readable` (`:1090`), `keyFromText_print`, `keyReadable` (`Read.lean:740`) | key prints as a call, reads from its text | **restated**: the key prints as a bare **identifier** (`classIdent key`), and reads back by looking the identifier up in the module's declared-key environment. `keyReadable` becomes "the module declares this key". | **medium**: the round trip stops being local to the expression and becomes relative to an environment. `readKey` gains a parameter. |
| P7 | `Program.readModule` and `readModule_printModule` (`src/Effect4/Laws/Codegen/Module.lean:162`), `printModule_shape` (`:240`), `printModule_readable` (`:294`), `readModule_printModule_readable` (`:318`) | `List ConstDecl`, last is main, earlier are layers | **restated over three declaration groups**: class declarations (one per key of `Fold.serviceKeys`, in row order), then layer consts, then main. The `getLast?`/`dropLast` split becomes a three-way partition. | **medium-high**: this is the real proof cost. The existing proofs destructure `decls.getLast?` directly. |
| P8 | `ModuleEmission` (`src/Effect4/Codegen/Checked.lean:32-37`) and `ModuleEmission.module` (`:40`) | `declarations : List TypeScript.ConstDecl`; `decls := declarations.map .const` | field becomes `List TypeScript.Decl`; `module` stops mapping | **low**, but it is a structure change with consumers in `Laws/Codegen/Checked.lean` and `Api.lean:185-195` |
| P9 | `declarationType`, `declarationType_ok`, `declarationTypeRepresentable`, `printDecl_fields` (`src/Effect4/Codegen/Print.lean:611-660`) | `none` when `requires ≠ ∅`; representability is trivially true there | total three-parameter annotation; representability becomes "every key of the row is declared" | **low-medium**: `declarationType_ok`'s proof is four lines and gets one more case |
| P10 | `Codegen/Admit.lean`'s envelope check: `layersPlain` (`:48-53`) refuses every non-`const` declaration, `ModuleReading` (`:100`) is "the last declaration exported under that name and annotated exactly as `printDecl` annotates the checked type, and every earlier declaration a plain exported layer constant" (`src/Effect4/Api.lean:211-224`); the refusal is proved in `src/Effect4/Laws/Codegen/Admit.lean:81` | two declaration classes | three; and the annotation comparison now has an `R` to compare. The `classDecl` case already exists in the proof as a refusal and is restated, not added | **medium**: this is where DI-29's oracle finally gets something to check |
| P11 | **O16, new** (`docs/research/2026-09-16-strict-proof-obligations.md:28`): the declared `R` is the requirement row's keys, never the carrier union | unstated | `declarationType ty = .ok (some (.name … [A, E, R]))` with `R` determined by `ty.requires.elems` and injective in it | **low once P9 lands**: injectivity of `classIdent` reduces to injectivity of `keyText`, and `Var.name_inj`/`repr_inj` (`Read.lean:1099-1104`) are the pattern to copy |
| P12 | `Authoring/Lifts.lean`'s `service_scoped`, `provideService_scoped`, `Layer.succeed_scoped`, `Layer.effect_scoped` (`src/Effect4/Laws/Program/Authoring/Lifts.lean:204-414`); `yieldKey_scoped` (`Authoring/Forms.lean:23`) | generated scope lemmas | **unchanged** — `ServiceDef` wraps the lifts, it does not replace them | none |
| P13 | `Scoped.lean`'s `scopedAt_service`, `scopedAt_provideService`, `LayerTerm.scoped_succeed/_effect` (`src/Effect4/Program/Scoped.lean:150-195`) | generated | **unchanged** | none |
| P14 | `Laws/Program/Agreement.lean`'s `compileEff_service`, `compileEff_provideService`, `serviceLookupK_found/_missing`, `bindServiceK_some`, `compileLayer_succeed/_effect` (`:487,492,1173,1180,1218,1051,1059`); `DenoteR`'s `denoteR_service`, `denoteR_provideService`, `denoteLayer_succeed/_effect` (`:1060,1067,1101,1126`) | machine/reference agreement, full key throughout | **unchanged** | none |
| P15 | `Program/Typing/Blame.lean:217-220` `serviceUnknown` | blames a key the signature does not type | gains a second reason, "key not declared in this module", if the printer's premise is checked at blame time | **low, optional** |

**The shape of the cost.** Eleven of the fifteen rows are "unchanged". The change is confined
to the *surface* (P6-P11): the printer, the two readers, the module type and the admission
envelope. That is exactly what scout C's reconciliation says of the surface obligations
(`docs/research/2026-09-16-scout-c-plan-reconciliation.md:412`, *read*), and it is why this
item can run beside the semantic repairs rather than inside them.

**Two traps I would warn an implementer about**, both from the tree's own history
(`docs/research/2026-09-06-lean-proof-traps.md` family, per the memory index; I did not
re-read it):

1. `readModule`'s proofs destructure `decls.getLast?` and `decls.dropLast`. Adding a *prefix*
   group is cheap; adding a group that can be empty *and* whose members are recognised by name
   is where the case split explodes. Partition once, by a decidable classifier on `Decl`, and
   prove the partition's round trip separately from the program's.
2. `keyReadable` (`Read.lean:740`) is a premise of `printKey_readable` and feeds `readable`.
   If it becomes environment-relative, every `readable` guard in
   `Test/Codegen/ReadContract.lean` changes meaning. The R4/R5 packet already pins `readable`
   with a Boolean equality against today's definition (`…r4-r5-r6…-ready-packet.md:45`); do
   this change *after* that pin exists, not before.

---

## 5. Cleanup (Q5)

*(all read)*

1. **`printLayer`'s docstring still forwards to a file that never existed.**
   `src/Effect4/Codegen/Print.lean:456-460`: "The named spelling of a layer — keys as class
   identifiers — is **not printed by any module of this tree** … and the `Codegen/Layer.lean`
   this docstring used to forward to has never existed (DI-51…)". The DI-51 repair was done
   (the sentence now says so) but the sentence itself is the record of a missing feature, not
   a citation. When N1 lands, this paragraph is deleted, not amended.
2. **DI-24's `R` spelling clause is superseded** (§2.3). The row still prescribes the carrier
   union and still says it "is **not** injective in the key". B15 and O16 reverse that. Amend
   the row in the same slice or the register contradicts the obligations note.
3. **`declarationTypeRepresentable`** (`Print.lean:630`) exists only to state that a
   requirement-bearing declaration prints *no* annotation (`ty.requires != Requirement.empty ||
   …`). Once `declarationType` is total the first disjunct is dead and the predicate collapses
   to "both types are representable".
4. **The dead adapter branch in `tools/target/corpus.ts:55-63`** (§1.6b), and the hand lane's
   missing bindings (§1.6a). Either key
   `selection.handles` by `"<name>:<service>"` and keep two maps, or delete the branch. Its
   docstring at `:20` is wrong today either way.
5. **Hand-written key literals a table would generate.** `Test/Program/LayerSharingContract.lean:16-17`
   (2), `src/Effect4/Program/Provision.lean:615-618` (4), `src/Effect4/Program/Fold.lean:3371`
   (`sampleKey`), `src/Effect4/Program/Native.lean:283` (`nativeScopeKey`). Only the last is
   load-bearing; the rest become `ServiceDef.define` calls under §3.
6. **Tests that pin the numeric spelling.** `Test/Codegen/ReadContract.lean:711-714` (three
   `#guard`s on `"k4_4"`/`"k04_4"`, including the leading-zero refusal — keep these, they are
   the canonicality control) and `tools/Tools/Styles.lean:85` (a style fixture that emits
   `const Key = Context.Service<number>("k4_4")`). The style fixture is the ingest side and
   must move with the printer or the style inverse drifts.
7. **`nativeServiceTypes`** (`src/Effect4/Program/Native.lean:291-293`) is a six-row hand list
   of `(code, Ty)` that is also hand-mirrored into `ts/eff/profile.gen.ts`'s
   `services.ordinary`. It is already generated into the profile; it is not generated *from*
   anything. If N2 ever happens, this is the table that gains a name column, and it should be
   a JSON input like `tools/Effect4Gen/wire-tags.json` rather than a Lean literal.
8. **`Signature.scopeKey` versus `nativeReservedServiceTypes`.** The scope key is named twice:
   as a `Signature` field (`Typing.lean:59`) and as the first row of the reserved table
   (`Native.lean:287`). They agree by construction today and nothing checks it.
9. **`PORT-MANIFEST.md` does not exist.** `src/Effect4/Machine/Key.lean:94-99` rests the key
   order's load-bearing status on "`PORT-MANIFEST.md`, 'Canonical row extraction'". There is no
   such file anywhere in the tree (`find . -name PORT-MANIFEST.md` returns nothing,
   `.lake` excluded). It is a DI-51-class dangling citation — bare filename, no repository
   root, so `scripts/check-source-citations.py`'s `TOKEN` pattern (which requires one of the
   `ROOTS` prefixes) never sees it. Either the canonicality rule is restated in a file that
   exists, or the sentence loses its authority. The same class of hole as DI-51's
   `Codegen/Layer.lean`, and the gate is blind to both for the same reason. *(read)*
10. **A naming collision worth a sentence in the glossary.** "the keyed host" / "the one keyed
   route" (`docs/STATE.md:28`, `Test/Api/KeyedHostContract.lean`) has nothing to do with
   service keys — it is the session/reply key of the host tape. `grep ServiceKey
   Test/Api/KeyedHostContract.lean` returns nothing. Two different "key" nouns in one M2 bullet
   is how a reader loses a day.

---

## 6. Order and cost (Q6)

Each slice small, each gated, each committed before the next. Bytes that move are named.

**Owner rulings needed first** — see §7.

| slice | what lands | bytes that move | gates |
| --- | --- | --- | --- |
| **K0** (no dependency) | `ServiceDef` and its four combinators under `src/Effect4/Program/Authoring/`, plus `Agrees`; the two `Test` key literals and `Provision`'s four rewritten through it. Authoring-only: no constructor, no tag. | none | `make check` |
| **K1** | The emission type widens: `ModuleEmission.declarations : List TypeScript.Decl`, `printEntry`/`printModule` return `List Decl`, `ModuleEmission.module` stops mapping. Reader gains a `.const`-only classifier so behaviour is byte-identical. No package change: `Decl` and `ClassDecl` are already in the pinned rev (§1.5). | none — every module still emits only consts | `make check`, `check-ocaml` (the LCNF face sees the type), `check-compat` |
| **K2** | `classIdent : ServiceKey → String` and the class emitter; `printModule` prefixes one `Decl.classDecl` per key of `Fold.serviceKeys` in row order; `printKey` emits the bare identifier. `readModule` gains its class-declaration arm and the key environment; `readKey` becomes environment-relative; `layersPlain` learns the class prefix. P6, P7, P10's refusal lemma restated. `checkSourceBindings` needs nothing (§1.5.3). | **every printed corpus image with a service key changes**; `harness/truth/generated/*.ts`, `generated/corpus-index.tsv`, the tsdiag table | `make check`, `check-truth`, `check-tsdiag` (promote), `check-ingest-smoke`, `check-ocaml` |
| **K3** | `ts/eff/read.ts` learns the same two clauses (or R6 generates them, if R6 has landed). | `ts/eff/read.ts` | `check-ts-reader`, `check-corpus` |
| **K4** | `declarationType` becomes total with `R`; `declarationTypeRepresentable` collapses; P9, P10, O16. `Admit`'s envelope compares three parameters. | every printed module's annotation line | `make check`, `check-target`, `check-corpus` (**the `mismatch-R` and `noninjective` rows are the acceptance test: g21, g50, g89, g290 must move to `agree`**), `check-tsdiag` |
| **K5** | Cleanup §5 items 1-4, 6-9; DI-24 amended; O16 marked proved in the obligations note. | `docs/DESIGN-ISSUES.md`, `tools/target/corpus.ts`, `tools/target/profile.ts`, `tools/Tools/Styles.lean`, `src/Effect4/Machine/Key.lean`'s docstring | `check-citations`, `check-corpus`, `check-target` |
| **K6** (optional, later) | N2's name table, if the owner wants readable printed programs. | the profile, every image again | the full set |

**No wire tag moves in any slice.** `ServiceKey` is a struct in the canonical codec
(`src/Effect4/Program/Derived.lean:997`) and has no family in `tools/Effect4Gen/wire-tags.json`
*(read: the file's `families` map contains no `ServiceKey` or `ServiceName` entry)*. So
`check-compat` should stay green throughout, and that is worth asserting as a control in K1.

**The corpus index and the seed stream do not move.** N1 changes what a program *prints*, not
which programs are drawn. The 400 draws, their bytes and their run outcomes are untouched;
only the printed images and the typing column move. *(inferred from the shape of the change;
the `branch` retirement at S1 is the precedent recorded in `docs/STATE.md:44`.)*

**Sequencing against the rest of the plan.** K2 rewrites the very clauses R5 rewrites. Two
orders work and one does not:

- **Recommended:** R4 → R5 → K1 → K2 → K3 → K4. The reader is written once, in the table, and
  the key's leaf clause is written once in its new form.
- Acceptable: K1 → K2 → K4 now, R5 later, accepting that R5 re-does the key clause.
- **Do not** run K2 and R5 concurrently in one checkout: both own `src/Effect4/Codegen/Read.lean`
  and `Laws/Codegen/Module.lean`. (The estate's standing rule; `docs/STATE.md:67-68`.)

**Effort, honestly.** K0 and K1 are an afternoon each. K2 is the slice with real proof work
(P7) — call it two to three days including the golden promotion. K3 and K4 are a day each.
K5 an hour. *(inferred; I did not attempt any of it.)*

---

## What I did not check

- I did not run any gate: no `make check`, `check-truth`, `check-corpus`, `check-target`,
  `check-tsdiag`, `check-ocaml`, `check-compat`. Every gate statement above is a prediction.
- I did not run either target lane, so the two findings of §1.6 are read from the
  source, not reproduced — reproducing it needs `bun`, which the brief forbids.
- The counts I quote from `harness/truth/corpus-results.tsv` are the **promoted baseline**, not
  a fresh run. `docs/STATE.md:43` records that the live lane currently differs from that
  baseline on 18 untyped rows. None of the four key rows (g21, g50, g89, g290) is among them,
  but I did not verify that.
- I did not read the corpus programs g21, g50, g89, g290 themselves — they are not in
  `harness/truth/generated/`, which holds the hand selection. Their key sets are inferred from
  `harness/truth/corpus-known-differences.md:22` and the `noninjective` message's `8:4` and
  `11:4`.
- I did not check `Layer.ts`'s own `Exclude` rules against N1; §3.4's layer claims are the
  plan's, not mine. `src/Effect4/Program/Typing.lean:386-388` (`provideLayer`'s
  `Row.union l.requires (Row.diff b.requires l.out)`) is full-key and I expect it to need
  nothing, but I did not probe a layer program end to end.
- I did not read `docs/research/2026-09-16-typed-surface-integration-analysis.md` or the proof
  traps note; §2.4 and §4's warnings lean on the memory index's summaries and are marked
  *inferred*.
- I did not examine `src/Effect4/Program/Config.lean` (7 key mentions) or
  `src/Effect4/Schema/Endpoint.lean` (`Endpoint.requires : List ServiceKey`, `:136`). Both may
  need a row in §4; neither is on the printed path.
- I did not check whether `Context.Reference` (`vendor/…/Context.ts:634` has its own
  `readonly key: string`) needs the same treatment. The estate has no `Reference` constructor
  today, so it is out of scope, but it is the same identity question.

## What the owner must rule

1. **Which reading of "named".** N1 alone (printed nominal class per full key, keys stay two
   `Nat`s) is my recommendation and is what the record plans. N2 (a name table in the
   signature, printed identifiers like `Db`) is sugar worth having but costs a `Signature`
   field and a profile regeneration; recommend deferring to K6. **N3 (a `String` inside
   `ServiceKey`) has no written plan, is refused with a stated reason at
   `src/Effect4/Machine/Key.lean:44-52`, and would move every golden byte; recommend no.**
2. **The class identifier's spelling.** With N1 and no name table the identifier is minted from
   the key. Two candidates: `k4_4` (identical to the runtime string — one fact, one spelling,
   and the reader's check is an equality) or `S_k4_4` (unmistakably a declaration, at the cost
   of two spellings to keep in step). **Recommend `k4_4`**: probe D compiles it as both the
   class name and the `Self` argument *(reproduced)*, and `printEntry`
   (`src/Effect4/Codegen/Print.lean:704-710`) already refuses an unsafe export name, which is
   where a collision between a program's name and a key's would be caught. *(The exact
   predicate `exportNameSafe`, `Print.lean:157`, I did not read; whether it already excludes
   the `k<n>_<m>` shape is the one thing to check before committing to this.)*
3. **Whether the class declaration is `Self`-parameterised.** rc.112 allows
   `Context.Service<Self, Shape>()("key")` where `Self` is the class itself. Probes B and D
   both use the self-referential form and both compile *(reproduced)*. The alternative,
   `Context.Service<{ k: "k4_4" }, number>()("k4_4")`, avoids the recursive reference but is not
   the idiom. Recommend the idiom.
4. **Order against R4/R5** (§6). Recommend R4 → R5 → K1..K4, so the reader's key clause is
   written once.
5. **Whether DI-24 is amended or retired.** Its `R`-spelling clause is superseded by B15/O16.
   Recommend: amend in K5, and move the "not injective in the key" sentence into a "historical"
   note beside DI-76, so a later reader does not resurrect the carrier union.
6. **Whether §1.6's two target-lane defects get a DI row now** or are folded into K5. They
   is a real hole in the type oracle's provenance story (DI-29) and I would register it.

---

### The four probes

All live under
`/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/aa7ebaa0-7350-4784-b70e-322956de92e8/scratchpad/scoutD/`
and none is in the repository. If this slice is taken up, probe A's guards and probe C's
`carrier_unique` belong in `Test/Program/` and the two `keys.ts` files in
`Test/fixtures/target/` beside `controls.ts`, red control included.

- `KeyProbe.lean` (probe A) — 18 `#guard`s and 3 `#eval`s. Run:
  `lake env lean -M 4096 <path>/KeyProbe.lean`. Green this session; output quoted in §1.3.
- `ServiceDefProbe.lean` (probe C) — the §3 authoring surface: 4 `#guard`s, the `carrier_unique`
  theorem, and 2 `#eval`s. Run the same way. Green this session; output quoted in §3.3.
- `keys.ts` + `keys-red.ts` (probe B) — 6 `satisfies` assertions and their red control. Run:
  `node ts/eff/node_modules/typescript/bin/tsc --noEmit --strict --exactOptionalPropertyTypes
  --target ES2022 --module ESNext --moduleResolution bundler --skipLibCheck <path>/keys.ts`.
  Green (exit 0) this session; the red control fails with `TS1360` at both flipped lines.
  TypeScript 5.9.2, the repo's own copy.
- `names.ts` + `names-red.ts` (probe D) — the printed class form with the key's own identifier
  and the three-parameter annotation, run the same way. Green this session; the red control
  fails with `TS2375` on the weakened annotation and `TS1360` on the assertion.
