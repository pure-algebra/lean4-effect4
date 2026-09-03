# Contract: the answer-type profile, and atoms as one declaration

Light ceremony. This packet widens the declared answer-type profile from depth
two to depth three and makes a pure atom a single declaration that every face
is a projection of. It replaces the earlier arrangement in which type spellings
were a private string function in the DSL and atoms were three independent
declarations (a Lean function, a hand-written row in an `AtomTable`, and a
hand-written `const` in `atoms.ts`).

Counterexamples: `E4-TARGET-CE-022` (a depth-three answer read by shape, not by
spelling) and `E4-TARGET-CE-023` (an atom declared in one face only).

## Frozen surface (`Effect4/Target/TypeScript/EffectV4.lean`)

| Name | Shape |
| --- | --- |
| `Spelling` | `nat`, `int`, `string`, `bool`, `unit`, `handle`, `option`, `list`, `except`, `prod` |
| `Spelling.render` | the TypeScript spelling of a `Spelling` |
| `Spelling.depth` | constructor nesting; a base type, a handle included, is depth one |
| `Spelling.profileDepth` | `3` |
| `Spelling.admitted` | `depth ≤ profileDepth` |
| `Spelling.wireDefault` | the wire inhabitant, `Spelling → Effects.Trace.Val` |
| `Spelling.mentions`, `Spelling.namespacesOf` | which `effect` namespaces a spelling needs, at any depth |
| `reservedExtra`, `bindingName` | the binding profile, extending `TypeScript.reservedIdentifiers` |
| `ServiceRow.spellings`, `ServiceRow.namespaces`, `ServiceRow.usesResult` | the rows' own spellings |
| `importedNames`, `neededNamespaces` | the module's `effect` import, minus what a supplied import already binds |
| `AtomRow` | name, binder, Lean and TypeScript spellings of request and answer, host body |
| `AtomRow.constSource`, `AtomRow.entry` | the TypeScript face and the flow-embedding face of one row |
| `atomsModule` | the generated `atoms.ts` |
| `OfVal` | the decoding side of `Effects.Trace.ToVal`, one instance per profile type |

## The profile

Depth one is Stratum V: `Nat` and `Int` spell `number`, `String` spells
`string`, `Bool` spells `boolean`, `Unit` spells `void`, and `Handle "T"` — the
opaque host handle of `Effect4/Meta/Derive.lean` — spells `T` verbatim.

Depth two nests one constructor: `Option A` spells `Option.Option<A>`, `List A`
spells `ReadonlyArray<A>`, `A × B` spells `readonly [A, B]`, and `Except E A`
spells `Result.Result<A, E>` — rc.112 has no `Either`, and the data reading of a
returned error is `Result` (`E4-TARGET-CE-009`).

Depth three, admitted by this packet, is one more nesting:

| Lean | TypeScript |
| --- | --- |
| `Option (Except E A)` | `Option.Option<Result.Result<A, E>>` |
| `Except E (Option A)` | `Result.Result<Option.Option<A>, E>` |
| `List (A × B)` | `ReadonlyArray<readonly [A, B]>` |
| `Option (A × B)` | `Option.Option<readonly [A, B]>` |
| `A × Except E B` | `readonly [A, Result.Result<B, E>]` |

Depth four is refused, with its depth in the message:

```text
effect_signature: the answer-type profile admits depth 3 at most; this spelling has depth 4
```

A type outside the grammar is refused separately (``no TypeScript spelling for
`Float`; add a Stratum V row first``). Both refusals are pinned by
`#guard_msgs` in the battery.

The profile applies to parameters and answers alike, and to atom request and
answer types. Parentheses are transparent to the parser and `×` is admitted;
before this packet neither was, which is what capped the DSL at depth two.

`Option (Except Nat Nat)` — the shape of an rc.112 `Exit`, called out as
unavailable in the M3 note in `COORDINATION.md` — is now a spelling the DSL
has. Retiring the `awaitValue`/`awaitError` pair that stood in for it would
change the `Fibers` goldens and is not part of this packet.

## The wire, both faces

The Lean renderer is `Effect4/Target/TypeScript/Trace.lean` over
`Effects.Trace.ToVal`. Its host counterpart is `wireAnswer` in
`harness/trace/tracer.ts`, which now parses the row's declared spelling
(`parseSpelling`) and encodes at it (`wireTyped`) instead of reading the shape
of the host value. Above depth two the value is not enough information: a pair
and a list are both JavaScript arrays. A spelling outside the profile — a
`Handle`'s target type, for one — parses to `null` and falls back to the
untyped encoder, whose handle branch indexes the object; `void` still answers
unit whatever the host hands back (`docs/TRACE-DAG.md` separation 7).

| Value | Lean and host |
| --- | --- |
| `some (ok 7) : Option (Except String Nat)` | `{"some":[true, 7]}` |
| `some (error "boom")` | `{"some":[false, "boom"]}` |
| `none` | `{"none":true}` |
| `ok (some 7) : Except String (Option Nat)` | `[true, {"some":7}]` |
| `[(1, "a"), (2, "b")] : List (Nat × String)` | `[[1, "a"], [[2, "b"], []]]` |
| `(1, ok true) : Nat × Except String Bool` | `[1, [true, true]]` |

`Spelling.wireDefault` gives each spelling its inhabitant, and `ToVal` of the
Lean `Inhabited` default of the same type is exactly that value — which is what
makes the per-program receipt's `X.answerDefault` and this agree. Lean's
`Inhabited (Except ε α)` is the *error* side, so a `Result` spelling's wire
inhabitant is `[false, …]`.

`OfVal` is the converse of `ToVal`, one instance per profile type. It is the
decoding the DSL had no carrier for (`E4-TARGET-CE-016`); being partial, it
closes nothing about `denoteScript` on its own, and that row stays open.

## Atoms

```lean
effect_atoms Atoms where
  | succ (n : Nat) : Nat ⟪ "n + 1" ⟫ := n + 1
  | orZero (e : Except String Nat) : Nat ⟪ "Result.isSuccess(e) ? e.success : 0" ⟫ :=
      (match e with | .ok n => n | .error _ => 0)
```

One declaration emits five projections of the same row list:

- the Lean function `succ`, used in `effect_program` bodies;
- `Atoms.rows : List AtomRow`, the data;
- `Atoms.table`, the `AtomTable` the flow embedding reads
  (`Effect4/Target/TypeScript/ScriptFlow.lean`);
- `Atoms.eval : String → Val → Val`, the wire dispatcher the Flow runner's
  `tableService` takes, built from `OfVal` and `ToVal`;
- `Atoms.source`, the generated `atoms.ts`.

The string is the host body: one TypeScript expression over the binder. The
Lean body comes last, so a `match` body must be parenthesised — its
alternatives would otherwise swallow the next atom. `atoms.ts` imports exactly
the `effect` namespaces the rows' spellings mention.

## The binding profile

`TypeScript.reservedIdentifiers` (lean4-typescript v0.4.2) carries the
ECMAScript reserved words, `delete` and `await` among them. `reservedExtra`
adds the predefined names it does not — `arguments`, `eval`, `undefined`,
`NaN`, `Infinity` — and `bindingName` is the conjunction that
`effect_signature` and `effect_atoms` check.

## Evidence

- `Effect4Test/Target/TypeScript/AnswerProfileContract.lean`: `#guard` on every
  admitted spelling, on the five depth-three rows through `effect_signature`,
  on the rendered wire of each, on `wireDefault` against `X.answerDefault`, on
  the `OfVal` round trip, on the binding profile, and on every face of
  `effect_atoms`; `#guard_msgs` on the refused depth-four spelling, the refused
  foreign type, and two refused bindings.
- `Effect4Test/Counterexamples/Target/AnswerProfile.lean`: the two register
  rows.
- The trace corpus: `harness/trace/Generate.lean` declares
  `Tri.lookup : Nat → Option (Except String Nat)` and the program `probe`;
  `generated/traces/probe.empty.tsv` is its golden, and the host agrees with it
  under every mask through `tail.ts`.
- `harness/trace/atoms.ts` is generated: `scripts/check-trace-host.sh`
  byte-compares it with `Generate.lean atoms`, as it already does for
  `fixture.ts`, `flow-fixture.ts`, `structured-fixture.ts`, `scope-fixture.ts`
  and `fiber-fixture.ts`.
- The five generated modules are byte-identical to what they were before this
  packet, so no existing golden's body moved.

## Acceptance

```text
lake build Effect4
lake env lean Effect4Test/Target/TypeScript/AnswerProfileContract.lean
lake env lean Effect4Test/Counterexamples/Target/AnswerProfile.lean
EFFECT4_PROGRAM=probe node ../effect4-tools/packages/harness/trace.mjs harness/trace \
  --golden generated/traces/probe.empty.tsv --masks generated/traces/masks.tsv --tail tail.ts
./scripts/check-trace-goldens.sh
./scripts/check-trace-host.sh
./scripts/test-trust-gate.sh
```
