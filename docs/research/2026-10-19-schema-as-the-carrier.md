# Schema as the type language: the carrier of every value that leaves a program

Status: design note, 2026-10-19, after the to-do dogfood (`2026-10-19-todo-as-a-user/`). The
library is at `639d78ed2`, the project `effect4-todo` at `822ac23`. The owner's question is the
early principle: one universal type language, Schema. Every value a program outputs is then
parsable from the outside, with Effect's type semantics. That seemed lost. This note says where
it stands, what its semantics are, how the tree models it, and what one probe showed.

## 1. The one thing to know

The principle stands in the tree, in pieces. `Ty` is the one type language, and `Ty.exitOf`
types an effect's outcome. The type-directed codec writes a value of any `Ty` as rc.112's own
`toCodecJson` JSON and reads it back exactly. The Schema code generator prints the same `Ty` as
the Effect Schema a consumer parses with. What was lost is one wire: nothing on the run path
calls the codec. A run's exit leaves as the machine's positional image, so the dogfood needed a
hand decoder to compare with Effect. Today's probe closed that gap in the project. With the exit
encoded at the certificate's type, Lean and Effect print the same eleven lines, with no decoder.

## 2. The principle, as the early notes state it

- Decisions row 13, the schema/program rule. Schema is a data language. Every effectful slot
  is a hole filled by an `Eff` program with a typing certificate.
- `docs/research/2026-09-04-eff-language-directions.md` §2, item 2: values are schema values,
  "one value language, and the schema is the type".
- `docs/research/2026-09-04-substrate-thesis-and-production-model.md` §3: Schema is the data
  plane, canonical through persisted JSON.
- `docs/research/2026-09-04-production-standards-spike.md` §1: "Schema is the lingua franca";
  every platform package that carries data across a boundary types that data as a codec.
- `docs/research/2026-09-10-program-as-schema.md`: the program as one schema document, with
  `Schema.Exit` at each node.
- The owner, 2026-10-19: every value output from a program is in a schema parsable from the
  outside, in some form, using Effect's type semantics.

## 3. What the tree holds

| Piece | Where | Its law or status |
| --- | --- | --- |
| The type language `Ty`: `unit`, `nat`, `string`, `record`, `map`, `tuple`, `union`, `lit`, `option`, `list`, `except`, `exitOf`, `causeOf`, the handles | `src/Effect4/Program/TyCore.lean` | the hub of every type carrier (`docs/research/2026-10-11-type-interface/README.md`) |
| Membership: does a value fit a type | `Val.memberIn` (`src/Effect4/Program/TyDecls.lean`); `Fits`, `fits_hasTy` (`src/Effect4/Laws/Program/Typed/Membership.lean`) | concept 1 |
| The certificate: a built program's answer, error and requirement | `Api.Built`, `Built.ty` (`src/Effect4/Api/Built.lean`, `src/Effect4/Api/Author.lean`) | admission |
| Every exit fits the certificate | `run_typed` (`src/Effect4/Laws/Program/MeaningSound.lean`) on `Straight`; `typedState_reachable` (`src/Effect4/Laws/Program/Typed/Commands/Clauses/All.lean`) on the reference machine | M7, proved 2026-10-13 |
| The type-directed codec: a fold of `Ty`, exact modulo key order | `wireAlgebra`, `encode`, `decode`, `isValue` (`src/Effect4/Schema/Codec.lean`); `decode_iff` (`src/Effect4/Laws/Schema/Codec.lean`) | concept 5, row 128; codec admission is one of the seven judgments |
| The codec's profile is Effect's own | the docstring of `src/Effect4/Schema/Codec.lean`: rc.112 `Schema.toCodecJson`, `Option`, `Result`, `Cause`, `Exit`, `Defect` by line | pinned |
| The Schema bridge: `Ty` as a Schema representation, `exitOf` as `Exit(value, error, Defect)` | `Bridge.schemaAlg` (`src/Effect4/Schema/Bridge.lean`); `ofSchema_exact` | exact modulo `normS`, row 128 |
| The Schema code: the Effect expression an Effect user writes | `SchemaCode.ofTy` (`src/Effect4/Codegen/SchemaCode.lean`) | checked at rc.112 by `make check-schema-codec` |
| The surface: each method's Schemas and decoding at entry | `ModuleEmission.surface` (`src/Effect4/Codegen/Surface.lean`) | CR-4, row 373 (11) |
| Reply admission: host data enters by membership at the row | `admitAnswer` (`src/Effect4/Program/Admit.lean`), Route A | concept 9 |

Three folds leave the one carrier, one for each face.

```mermaid
flowchart LR
  T["Ty, the one type language"] --> J["wireAlgebra: the JSON codec (Lean, and lowered to OCaml)"]
  T --> S["schemaAlg then codeAlgebra: the Effect Schema code"]
  T --> M["hasTy: membership"]
  J --> X["JSON text, rc.112's toCodecJson profile"]
  S --> E["Schema.toCodecJson(Schema.Exit(A, E, Defect)) at rc.112"]
  X <-->|"the same text, modulo key order"| E
```

## 4. Where it was lost

**Nothing on the run path calls the codec.** A search of `src/Effect4` for `Codec.encode`,
`Codec.decode` and `isCodecValue` finds three kinds of caller. They are the law graph, the codec
lane (`harness/truth/schema-codec/Emit.lean`) and the batteries. No run, no tool method and no
kit entry calls it.

**An exit leaves four ways.**

1. `Run.Observation.exit` is the raw `ExitV`. The kit prints it under the carrier's own shape,
   `Kit.Json.exit_json` at `exitShape`, and a value under `valShape`: the positional image, with
   `_ctor` keys. The tool's `CodecProfile` prints carriers the same way, by `Canonical.print`.
2. The truth harness writes exits by hand: `exitJson` and `exitJsonAt`
   (`harness/truth/Truth.lean`), with the fiber renumbering.
3. The session fixtures write a failure as `{"fail": {"payload": hex}}`
   (`harness/truth/session/Session.lean`).
4. `Ty.encode` at `Ty.exitOf`, the proved one, which no run uses.

That is the coherence audit's cause D, one fact spelled per face, at the exit. The dogfood met
it as finding 3.5: the exit printed as `Val.ctor 1 […]`, and the comparison with Effect needed
`ts/lean-lines.ts`, 53 lines of decoding.

The inbound direction did not lose it. A host's reply is admitted by membership at the row
(Route A), and a typed host's images are typed by `Modeled.ty`, a `Ty`. So replies cross typed,
and exits cross untyped.

## 5. The semantics

Two definitions, in the tree's own words.

- **D1, the observation of a run.** For a built program `b` and a run that ends with the exit
  `e`, the observation is `Ty.encode (Ty.exitOf b.ty.answer b.ty.error) (exitImage.toVal e)`.
- **D2, parsable from the outside.** A consumer holding `b.ty` alone reads the observation: in
  Lean and in the lowered OCaml by `Ty.decode` at the same type; in TypeScript by
  `Schema.toCodecJson(Schema.Exit(ofTy answer, ofTy error, Schema.Defect()))`.

Four properties. Each is placed before it is worked (AGENTS.md, Trust).

- **P1, every observation is defined.** Let `b.ty.answer` and `b.ty.error` be codec-supported:
  `Codec.isSupported`, no handle, fiber, ref, deferred, variable or `unknown`. Then every exit
  of every run of `b` encodes at `Ty.exitOf`. Its parts stand. The exit fits the certificate:
  `run_typed` on `Straight`, M7 on the reference machine. Membership erases to the shape check,
  `fits_hasTy`. The codec admits a shape-decided value: `fits_of_hasTy_shapeDecides` and
  `decode_encode`. The composed statement is in no registry claim. Concept 5, serving R3; its
  consumer is move A below. It inherits its parts' fragments.
- **P2, exact.** `decode_iff`: what decodes at `t` is what `encode` wrote at `t`, modulo
  `normJ`, the key-order normaliser. Landed, row 128.
- **P3, the two faces agree.** Lean's `encode` at `t` and rc.112's `toCodecJson` of
  `SchemaCode.ofTy t` write the same text modulo `normJ`, and each reads what the other wrote.
  Host evidence, never a theorem: the codec lane holds it for values, and today's probe holds it
  for exits on eleven requests. A lane for exits is owed.
- **P4, one printer.** The kit, the tool, the truth lane and the session print an exit by D1. A
  consolidation move, not a theorem.

What the semantics do not cover. A handle has no JSON, so a program whose answer is a `Ref` or
a `Fiber` has no outside observation by D1. A defect carries Lean's closed payload
(`encodeDefect`), where rc.112's slot is `unknown`. An interrupt carries fiber ids, which the
truth lane renumbers before it prints. The cause's annotations are dropped on both faces.

## 6. The model: the common carrier and its algebra

The carrier of types is `Ty`, a free object: its algebra is `TyAlgebra`, and its fold is
`cata_ty`. The carrier of values is `Val`, the one value tree, and membership relates the two.
Every face is a fold of `Ty`, and never a second definition. The JSON codec is `wireAlgebra`.
The Effect Schema is `schemaAlg` into the representation, then `codeAlgebra` into code. The
OCaml face is the same `wireAlgebra`, lowered by the LCNF route, so no second codec exists.
Agreement is never a pairwise theorem. The TypeScript face agrees by the lane that runs rc.112,
and the OCaml face by the lowering's simulation of the same fold.

"Effect's type semantics" is then exact, because the encodings are rc.112's own. An Effect user
reads a Lean program's answer with Effect's Schema. A Lean program reads an Effect program's
answer with the codec. The exit type closes the type language under outcomes: `Exit<A, E>` is a schema
in Effect, and `Ty.exitOf` is a type in Lean. An observation is a value of the language, not a
side alphabet.

## 7. The probe

In the project, `lake exe todo --typed` prints each exit by D1, and `bun ts/run.ts --typed`
prints the Effect exit under `Schema.toCodecJson(Schema.Exit(answer, error, Schema.Defect()))`,
with the Schemas of the printed surface (`ts/todo.surface.gen.ts`). The comparison is a diff:

```
lake exe todo --typed | diff - <(bun ts/run.ts --typed) && echo SAME
SAME
```

Two lines of it:

```
add("") {"_tag":"Failure","cause":[{"_tag":"Fail","error":["EmptyTitle","a title is required"]}]}
complete(7) {"_tag":"Failure","cause":[{"_tag":"Fail","error":{"_tag":"NotFound","id":7}}]}
```

Two things the probe found on the way. The codec's `Json` has no text renderer. `jsonSource`
writes a number as a JavaScript bit literal, and the path to text is `NatJson.ofBinary64` then
`NatJson.render`, which answers bytes. And `Schema.Exit` alone encodes to an `Exit` object;
only `Schema.toCodecJson` of it writes the JSON the codec writes.

## 8. The faces, dogfooded

`probe/Faces.lean` beside this note builds 28 programs, one for each outcome form that Effect's
standard library has a schema for. It runs each on the Lean machine and prints its exit by D1.
It writes each program as Effect TypeScript. Then `probe/run.ts` runs the printed program under
Bun on rc.112. It encodes the exit with the case's own codec, `Schema.toCodecJson(Schema.Exit(
answer, error, Schema.Defect()))`, from the same types. The lines are diffed with fiber ids
masked. The commands, from the library's root:

```
lake env lean --run docs/research/2026-10-19-schema-as-the-carrier/probe/Faces.lean docs/research/2026-10-19-schema-as-the-carrier/probe/out ../../../../../harness/truth/prelude.ts
bun docs/research/2026-10-19-schema-as-the-carrier/probe/run.ts
```

The outputs are `probe/out/lean.txt` and `probe/out/bun.txt`, and the certificate types are
`probe/out/types.tsv`. tsgo 7 accepts every printed module.

| Form | Cases | Result |
| --- | --- | --- |
| Success: unit, nat, bool, string with escapes and non-ASCII, option some and none, list, pair, tuple, record with and without its optional field, map, union | 13 | equal |
| Success: an exit as the value (`Effect.exit` of a failure and of a success), a cause as the value (`catchCause` answering it) | 3 | equal |
| Failure, `Fail`: a string, a number, a tagged pair, a tagged record | 4 | equal |
| Failure, `Interrupt`: no interruptor; as a value under `exit` | 2 | equal |
| Failure, `Interrupt`: a forked child interrupted and joined | 1 | equal modulo the fiber id (Lean `0`, rc.112 `29`), and only after the annotations are dropped (finding 8.2) |
| Failure from a forked child: its typed failure joined | 1 | equal |
| Failure, `Die`: a number, a string, and a forked child's number | 3 | differ: the defect carrier (finding 8.1) |
| A fiber as the answer | 1 | refused on both faces: Lean's codec has no wire for `Fiber`, and the Schema code generator has no `Fiber` declaration |

Four things the probe established.

### 8.1 The defect carrier is not Effect's

Lean's `Defect` is a closed alphabet: `user n`, `error e`, and four machine defects. The codec
writes `user 7` as `{"user":7}`. It writes `error (text "boom")` as `{"error":"boom"}`. Both are
`encodeDefect` (`src/Effect4/Schema/Codec.lean`). rc.112's `Schema.Defect()` is `Json` decoded
to `Unknown` (`vendor/effect-4.0.0-rc.112/src/Schema.ts`, `Defect`). So a defect encodes as the
raw JSON of the thrown value, `7` and `"boom"`, and an `Error` as its name and message. The
truth harness bridges the two by a hand projection in TypeScript, `defectWire`
(`harness/truth/run-truth.ts`), which turns a safe natural into `{ user: n }`. That projection is
the fourth spelling of a defect, and the probe sees through it:

```
dieNat    Lean {"_tag":"Die","defect":{"user":7}}    rc.112 {"_tag":"Die","defect":7}
dieString Lean {"_tag":"Die","defect":{"error":"boom"}}  rc.112 {"_tag":"Die","defect":"boom"}
```

### 8.2 The exact codec refuses an annotated cause

An interrupted fiber's reason carries stack annotations, as the raw image shows:
`ctor 2 [some (ctor 0 [nat 0]), ctor 0 [list [pair "stack1" unit, pair "stack0" unit]]]`. The
codec's membership check passes it, and its raw encoder writes it, dropping the annotations as
`encodeReason` does. Then `Prepared.encode` decodes the JSON, reads the reason back without its
annotations, finds another value, and refuses: the exactness guard `decode j = some v`. So the
exact codec admits no cause with annotations, while rc.112's `toCodecJson` drops them by design.
The probe's observation strips every reason's annotations first (`Faces.bare`), and then the
case agrees. That strip is the named normaliser the exit codec's exactness law needs, as
`normJ` is for key order.

### 8.3 Fiber ids are compared modulo a renaming

An interruptor's id is the run's own numbering on each face. The typed observation carries it as
Effect does, `{"_tag":"Interrupt","fiberId":n}`, and the comparison renames, as the truth lane's
`fiber : Nat → Nat` does today.

### 8.4 A handle has no outside observation, on both faces

`fork (succeed unit)` answers `Fiber.Fiber<void, never>`. Lean's codec refuses the type, and
the Schema code generator refuses the declaration `effect/schema/Fiber`. The refusal is the same
fact in two places, which is what R4 asks for.

One more thing the probe met: `NatJson.render` answers bytes, and `String.ofList` over them
splits a non-ASCII character. The text form is `String.fromUTF8!` over the bytes.

## 9. The moves

| Move | What it does | Owner |
| --- | --- | --- |
| A | `Run.observe` answers D1 beside the raw exit: one function in Lean, lowered into the kit, so `Kit.Json.exit_json` and the tool's run replies print by type | §9.1 item 5, M8 one observation |
| B | The truth lane's `exitJson`, `exitJsonAt`, its `defectWire`, and the session's `fail/payload` fold into `Ty.encode`; the fiber renumbering stays a function on the exit before it encodes | item 5; §9.2 item 1 for the protocol |
| C | One text renderer of the codec's `Json`, `normJ` then `NatJson.ofBinary64` then `render` then UTF-8, named once | item 10, small |
| D | The composed claim P1 in the registry under concept 5, with its planned goal; move A is its consumer | new; semantics generation is paused, so a receipt proposes the row |
| E | The kit's trace prints each call's request and reply by the row's columns, not by `valShape` | item 5 |
| F | The surface carries `exit: Schema.toCodecJson(Schema.Exit(answer, error, Schema.Defect()))` per method, so a consumer composes nothing by hand | new, small |
| G | The defect carrier follows Effect: `user n` encodes as the number `n`, `error e` as its error payload, and the four machine defects as one tagged object; the harness's `defectWire` goes | new, small; concept 5 |
| H | The exit codec's exactness law gains the annotation normaliser: `Prepared.encode` compares against the value with its annotations dropped, and D1 encodes that value | new, small; concept 5, row 128 |

Not a move: `exitShape` and `valShape` stay the tool's wire for carriers that are no program
value, such as programs, types and refusals.

The order for the consolidation push. H and G come first, since they change what the codec
admits and writes. Then A with C, which makes the observation one function on every face. Then
B, which deletes the hand spellings. Then E and F. D rides with A.

## 10. What the owner decides

| Id | Question | Recommended |
| --- | --- | --- |
| R1 | Is D1 the observation of a run, and does §9.1 item 5 say so? | yes |
| R2 | Does P1 enter the registry now, as a claim with a planned goal, while generation is paused? | yes, by a proposed row |
| R3 | Does the surface carry the exit codec per method (move F)? | yes |
| R4 | A program whose answer is a handle: no outside observation, with the tool's carrier wire for it, or a refusal at the public face? | the carrier wire, marked internal |
| R5 | Does the defect carrier follow Effect's raw JSON (move G), or does the TypeScript face keep projecting into Lean's alphabet? | Effect's, by the principle |
| R6 | Is an exit observed without its annotations (move H), as Effect's codec does? | yes; the annotations stay in the tool's carrier wire |

## 11. What this does not establish

- No theorem landed. The to-do probe is eleven requests, and the faces probe is 28 programs,
  each on one machine under one host.
- P1 is stated here and in no claim. Its parts are proved on their fragments.
- The faces probe runs no host row, no clock advance and no parallel failure. rc.112's `all`
  with unbounded concurrency fails with its first reason. So a cause with several reasons came
  from no program here, and the codec lane holds it at the value level.
- The OCaml face printed nothing by D1: the native run still prints the value tree, and move A
  is what lowers D1 into the kit.
