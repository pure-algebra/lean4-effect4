# 2026-10-08 seat MODULES, revision 3: the carrier contract and the grading, repaired

Status: a revision with one new probe and a corrected runner. It answers Codex's second review
(`docs/research/2026-10-08-modules-r2-review.md`, `59074f2c`) of revision 2
(`docs/research/2026-10-08-seat-MODULES-r2.md`). This note changes no decisions row. Its files are
in `docs/research/2026-10-08-seat-MODULES-r3/`, and the reviewed packets stay unchanged.

## 1. The one thing to know first

Both concrete problems of the review are repaired, and each repair has its red controls.

- **The carrier contract (R2-F1, R2-F5).** A `Ty` is in the checked domain when one refusal
  fold answers `none`. Membership holds for every value of every checked `Ty`, by one theorem
  (`Carrier3.member`). An instance of `Modeled` must prove its `Ty` checked, and its carrier and
  image are the fold's, so the review's malformed instances do not compile. The deriving
  command validates its declaration before it writes anything.
- **The grading (R2-F2).** The native runner compares typed observations, so `true` and `1`
  differ. A signed difference must name a ruled decisions row. The clients are declared with
  their expected outcomes, and pins and time limits are enforced.

The owner relayed the review's answers to the four questions (§5). The next step is the first
connected slice, in the tree (§6).

## 2. The carrier contract (MODS-12)

`docs/research/2026-10-08-seat-MODULES-r3/Carrier.lean` compiles with no error and no warning.
It keeps MODS-11's carrier fold and `Image.record` unchanged, and adds four parts.

**The checked domain.** The refusal fold (`refusalAlg`) answers a reason or `none`. Revision 3
adds two refusals to MODS-11's: a record whose names are not strictly ascending by their bytes,
and an optional field. So "canonical", "supported" and "every field supported" are one check: a
fold of the generated `Ty` signature.

**Membership, once.** `Carrier3.member`, at `[propext, Quot.sound]`:

```lean
theorem member : (t : Ty) → refusal t = none → ∀ (x : Carrier t) (alloc : List String),
    Val.hasTy ((image t).toVal x) t alloc = true
```

It is one structural recursion on `Ty`, with a companion for a record's fields. The record arm
reuses `Field.canonBy_of_ascending`: on ascending names, `Ty.canon` of the field checks is the
identity, so `namedHasTy` reads the fields in order.

**A class that cannot be cheated.** `Modeled α` holds a `Ty`, a proof `refusal ty = none`, and an
equivalence with the fold's carrier. `Modeled.member` follows from `member` in one line, so an
instance owes no membership proof and cannot supply a wrong one.

**The codec, as its own obligation.** `Modeled.codec_roundtrip`, at `[propext, Quot.sound]`: a
modeled value survives JSON and back, under the premise `Ty.isCodecValue` at the normal form of
its type. Membership comes from `Modeled.member` and `hasTy_normalize`. The premise stays,
because a number above 2^53 inhabits `nat` and has no exact JSON image. A check in the file shows
the premise false there and true for the example cell.

**Deriving, validated.** `derive_modeled` refuses, at the syntax, before it writes a declaration:

- a rename of a field that does not exist;
- a field renamed twice;
- two fields with one spelling;
- a structure with parameters (the first profile is monomorphic);
- a field that depends on another field;
- a field type with no `Modeled` instance.

It then writes the `Ty`, `checked` (by `decide`), the two maps, the two inverse equations and the
instance.

**The example: an ordinary nested record.** `LatchCell` holds a list of `Waiter` records, a
Boolean renamed `open`, and an optional label of type `Option String`. Both structures derive.
Every cell value inhabits the derived type at every allocation table, with no proof of its own.

**The review's controls, refused for their reasons** (each a `#guard_msgs` in the file):

| Control | Refusal |
| --- | --- |
| a hand instance with record names `z`, then `a` | `decide` shows `refusal … = none` false |
| a hand instance at an identity type | `decide` shows `refusal (Ty.handle …) = none` false |
| a rename of a missing field | "has no field misspelled" |
| two fields spelled `flag` | "two fields … are spelled flag" |
| one field renamed twice | "field left is renamed twice" |
| a structure with a parameter | "has parameters; the first profile is monomorphic" |
| a field of type `Int` | "field type Int has no Modeled instance" |

**What MODS-12 does not cover:**

- identity types: they need their role-specific tables and allocation premises;
- optional properties, distinct from required `Option` fields, and the arms `int`, `union`,
  `except` and `tuple`;
- the connection to the step language: `StepData.Step` still uses MODS-9's `Sy` (R2-F3);
- a live TypeScript codec. `Codegen.Schema.representation` renders a description, and the live
  conversion `SchemaRepresentation.fromRepresentation` needs revivers (R2-F4).

## 3. The grading (native runner, revision 3)

`docs/research/2026-10-08-seat-MODULES-r3/native.py` replaces revision 2's runner:

| Correction | How |
| --- | --- |
| typed equality | observations agree when their canonical JSON texts agree, so `true` and `1` differ |
| failures | two failures are unresolved; rendered causes are not structured cause equality |
| rulings | a signed difference names "decisions row N", and row N is ruled in `docs/core/decisions.md` |
| clients | declared with their expected outcomes; an empty, missing or extra client is refused |
| the reverse join | a difference row that no client uses is refused |
| pins and limits | the versions of Effect, tsgo and bun are enforced, and every run has a time limit |
| digests | the runner and the prelude enter the input digests beside the bodies |

The original Latch's batch client stays as a regression witness: its expected outcome is a
counterexample. `differences.json` is empty, because the coalescing Latch removes the difference.

Its run on 2026-10-08 (Effect `4.0.0-rc.112`, tsgo `7.0.0-dev.20260629.1`, bun `1.4.2`) exits 0:

| Client | Ours | Effect's | Outcome (expected) |
| --- | --- | --- | --- |
| d1 | `[3,1,2]` | `[3,1,2]` | pass (pass) |
| d2 | `[3,1,2]` | `[3,1,2]` | pass (pass) |
| d3 | `[true,[3]]` | `[true,[3]]` | pass (pass) |
| batch over the coalescing Latch | `[1,2,9]` | `[1,2,9]` | pass (pass) |
| batch over the original Latch | `[1,9,2]` | `[1,2,9]` | counterexample (counterexample) |

`--self-test` reports six failure paths. They are `true` against `1`, a crash, a ruling that
names no ruled row, no client, a stale difference row, and wrong pins.

The rest of the review's grading list belongs to the Conform driver (slice L5). It holds
structured causes, broader provenance, and `Conform.Report.complete` and `exitCode` as the one
report.

## 4. The other findings

| Finding | Response |
| --- | --- |
| R2-F3, two separate probes | `Sy` stays in the research probe. The step syntax lands over the checked `Ty` domain (§6, slice L2) |
| R2-F4, no live codec | the JSON codec is now its own obligation with its premise (§2). The live TypeScript codec is slice L4 |
| R2-F6, Semaphore carries handles | the first Semaphore slice migrates the field reads and the update over the existing cell and its table encoding (`cellTy`, `Model.cellVal tb s`); whole-cell deriving waits for the identity context |
| generic deriving | not tied to goal G8. The `List` and `Option` instances are already generic; the first structure command stays monomorphic by choice |

## 5. The four answers, as relayed

The owner relayed Codex's answers on 2026-10-08. This note records them as the design's direction.
A decisions row records a ruling only when the owner confirms it.

| Question | Answer |
| --- | --- |
| 1. steps as data over `Ty`, tied to Lean structures by deriving | yes; the checked connection is still to land |
| 2. Latch's wake | match Effect's batching; add cancellation and reentrant controls before the component's law |
| 3. the run law's clients | a precisely checked client subset and an abstract model; interruption and cleanup stay observable; numeric identity inspection is excluded |
| 4. compatibility | four separate results, with these endpoints |

The four results:

| Result | Claim |
| --- | --- |
| shared-model conformance | each implementation's behaviours lie inside the model's |
| directed compatibility | one implementation's behaviours lie inside the other's, in a named direction, under a named observation and profile |
| equal observations | both directions hold, or the finite named clients agree when the evidence is tested |
| signed differences | each accepted unequal observation matches a validated ruling and its exact predicted pair |

Finite results stay labelled tested.

## 6. The first connected slice

Each obligation is placed before its proof.

| Obligation | Concept | Question | Reach | Not established | Unlocks |
| --- | --- | --- | --- | --- | --- |
| `member` | `store-typing`: encoded values inhabit their types | a new claim `modeled-membership` | every value of every checked `Ty`, every allocation table | identities; codec admission | every derived type's membership; R10 |
| `codec_roundtrip` | `exact-codecs`: the codec's retraction | a new claim `modeled-codec` | modeled values under `isCodecValue` | the TypeScript codec; target execution | the authoring surface's JSON boundary |
| step soundness over `Ty` | `translation-simulation` | `step-language-sound` | well-formed steps over checked records | a step's specification; runs | each module's `*-steps-agree` as a corollary |
| the field laws over `Image.record` | `exact-codecs` | helpers of `step-language-sound` | canonical records | optional fields | the frame law |

| Slice | What lands | Depends on |
| --- | --- | --- |
| L1 | the carrier fold, `Image.record`, the refusal fold and `Modeled` in the core; `member` and `codec_roundtrip` in the law graph; `deriving Modeled` registered as a deriving handler; a battery with the red controls | the claims placed |
| L2 | the step language over the checked `Ty` domain: field references into `Ty.record`, the term, model and footprint folds, `Step.sound` and the field laws | L1 |
| L3 | Semaphore's `takeIfAvailableStep` as a step of L2 over the existing cell and table, with its connector to `takeIfAvailableStep_agrees` and `takeIfAvailable_attempt` | L2 |
| L4 | the live TypeScript codec through `SchemaRepresentation.fromRepresentation`, with its revivers, checked on the pin | L1 |
| L5 | the Conform driver for the search and the native comparison | none |
| L6 | the identity context: role-specific encodings through tables, then whole-cell deriving for Semaphore | L1, L3 |

## 7. Reproduce

Run from the repository root:

```sh
scratch/lean-slot.sh lake env lean docs/research/2026-10-08-seat-MODULES-r3/Carrier.lean
python3 docs/research/2026-10-08-seat-MODULES-r3/native.py
python3 docs/research/2026-10-08-seat-MODULES-r3/native.py --self-test
scratch/lean-slot.sh python3 docs/research/2026-10-08-modules-r2-review/review.py
```

The review's command rewrites its `results.json`; restore the committed copy after the run.
