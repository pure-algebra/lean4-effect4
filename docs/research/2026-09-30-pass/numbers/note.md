Floats do not fix natural-number exactness; DI-56 already ruled the fix (every target has a bounded number profile and refuses outside it, intermediates included, with no wrapping and no saturation), but neither face implements it, so one checked, closed program returns three different answers today (reproduced) — the main decision left for the owner is whether the native face should instead be exact.

# Numbers, and what to learn from FloatLib

Seat: numbers. Base `be15b062`, branch `refactor/phase1-phase3`, 2026-09-30. Everything this seat
wrote is in `docs/research/2026-09-30-pass/numbers/`. Nothing else was touched.

Evidence words, used exactly:

- **proved**: a Lean theorem in a probe file, its `#print axioms` shown in §9;
- **reproduced**: the real engine or runtime was run and printed the value;
- **tested**: a finite differential, with its counts and a red control;
- **finite**: a `#guard` in a probe file;
- **reading**: what the code or paper says; not run.

## 1. The answer to the owner's question

**Should the floating-point library handle the natural-number issue?** No. A double
(IEEE binary64) holds every natural only up to 2^53. Above that it keeps 53 significant bits
and rounds the rest away. So a float can only make the natural problem worse. FloatLib also
has wide and arbitrary-width formats, but a float wide enough to hold every natural you care
about is a big natural number with an exponent attached: the exactness would come from the
big natural, not from the float.

**What does fix it.** One of two things, per face:

1. **A bounded profile with checked arithmetic that refuses.** Every intermediate result is
   checked against the face's largest exact natural; outside it the run stops with a
   distinguished "outside the profile" outcome. This is what DI-56 ruled on 2026-09-09
   (`docs/DESIGN-ISSUES.md:128`): bounded, explicit refusal, intermediates included, no
   wrapping, no saturation, Lean's `Nat` stays unbounded. It is not implemented (§3).
2. **An exact representation on the native face.** A natural that grows as needed: small
   values in one machine word, large ones in several (a "bignum"). Lean's own runtime does
   exactly this (a small scalar, or a GMP number). On OCaml the same thing is Zarith, which
   is already installed in the `effect4` switch and linked by the engine for the exact clock
   (`ocaml/clock/dune`, `ocaml/clock/e4_clock.ml`). FloatLib's contribution here is a method,
   not a dependency: its limb kernels are exactly "a natural in several words, proved equal to
   `Nat`" (§6).

The TypeScript face cannot be exact without changing its type from `number` to `bigint`,
which would change every printed program and every Effect API it calls. So the TypeScript
face is bounded by nature (2^53 - 1); the question is only whether the native face is
bounded too (option 1) or exact (option 2).

**Where binary64 is actually needed.** Only on the TypeScript face, and only if the
language models rc.112 APIs whose values are JavaScript doubles: `Duration` (milliseconds as
a double, infinite durations), `Schedule` (exponential, fibonacci, jittered delays), `Random`
(doubles in [0, 1)) and `Number`. Today the language models none of that arithmetic (§5), so
today binary64 is needed nowhere in the semantics. The data plane already carries binary64
values exactly, as bit patterns, with no arithmetic (`Float64`,
`src/Effect4/Data/Json.lean`).

## 2. One program, three faces

The program (`Faces.lean`, `program`) is five `succeed` bindings and a result. It type-checks
closed (`Api.typeOf program [] = some (EffTy.pure (prod nat (prod bool (prod nat (prod nat
nat)))))`, finite). Every literal is at most 2^53 - 1, so every literal is inside rc.112's
profile (finite, `rc112.admitsNat`). There is no host row. The intermediates pass 2^53 (first
binding, 2^52 + (2^52 + 1)) and then 2^62 (fourth binding, 2^61 + (2^61 + 5); fifth binding,
(2^53 + 1) · 512).

| face | `a1` | `lt(a3, 1)` | `div(a3, 2)` | `(a3 - a2) - a2` | `mod(a4, 1000)` | evidence |
| --- | --- | --- | --- | --- | --- | --- |
| Lean reference (`Api.run`) | 2 | false | 2305843009213693954 | 5 | 416 | finite, `Faces.lean` |
| OCaml engine, `Fast` and `Ref` | 2 | **true** | **-2305843009213693949** | 5 | **903** | reproduced, `ocaml/faces.log` |
| rc.112 (`Effect.runSyncExit`, bun 1.4.2) | **1** | false | **2305843009213693952** | **0** | **904** | reproduced, `ts/faces-run.log` |

Every face "finished". No face refused. The OCaml engine's generated `Api.run` also says
`finished`. The OCaml answer holds a negative number in a `Val_nat`, a value no natural has.
JavaScript prints its third component as `2305843009213694000` (its shortest round-trip
spelling); the double holds `2305843009213693952`.

Why each number is what it is:

- OCaml: `Nat.add` is raw `+` (`src/OCaml5/Lcnf/Translate.lean:162`; generated at
  `ocaml/engine/api_engine.ml:3039`), so 2^61 + (2^61 + 5) wraps to -4611686018427387899;
  `lt` then says true, `div` truncates a negative number; `Nat.mul` saturates at `max_int`
  (`Translate.lean:163-169`; `api_engine.ml:3314`), so (2^53 + 1) · 512 is 4611686018427387903
  and its remainder is 903. `(a3 - a2) - a2` is 5 because wrapping arithmetic is arithmetic
  modulo 2^63 and the wraps cancel: the right answer, by accident.
- TypeScript: the prelude's `add` is `a + b` on doubles
  (`harness/truth/prelude-atoms.gen.ts:39`, generated from `NativeAtom.row`,
  `src/Effect4/Machine/Term.lean:211-212`), so 2^52 + (2^52 + 1) rounds to 2^53 (a tie, to
  even) and `a1` is 1; 2^61 + 5 rounds to 2^61, so `a3` is 2^62 and the subtractions give 0;
  (2^53) · 512 is 2^62 exactly, whose remainder is 904.

The three answers are also **predicted** by two Lean models of the targets (`Models.lean`,
`Face.run`; finite): `exact.run` equals the machine's own run, `ocaml.run` gives the OCaml
row, `typescript.run` gives the rc.112 row. The models are checked against the real engines
on 50,000 random operations (§4). Inside each face's bound the models provably agree with the
machine on every term of this fragment (§7: `Face.sim`, `ocaml_matches_machine`), so the
disagreement above is exactly the leaving of the bound, nothing else.

Two more facts on the same channels (finite and reproduced):

- **A literal above 2^53 is admitted, printed and read back unchanged, and means something
  else in JavaScript.** `succeed(9007199254740995)` type-checks, runs to 9007199254740995 in
  Lean, prints as `Effect.succeed(9007199254740995)`, and `Api.read` gives the same program
  back (`Faces.lean`, `bigLiteral`). JavaScript reads that literal as 9007199254740996
  (`ts/faces-run.log`). The store's JSON number for the same natural is 9007199254740994,
  because `Arch.binary64OfNat` truncates (`src/Effect4/Data/JsonNumber.lean:37-41`). One
  natural, three values: Lean ...995, program text ...996, JSON datum ...994.
- **A literal at 2^62 cannot reach the OCaml engine.** Lean runs `succeed(2^62)`; the engine's
  decoder refuses the program's bytes (`Fast decode refused`, `Ref decode refused`,
  `ocaml/faces.log`), as `ocaml/eff/eff_frame.ml` refuses naturals at 2^62 and above
  (`ocaml/engine/e4_nat.mli`, D1). The refusal has no location.

DI-56's own measured case still holds: at `M = Number.MAX_SAFE_INTEGER`,
`eq(add(M, 2), succ(M))` is true and `lt(succ M, succ(succ M))` is false (reproduced,
`ts/faces-run.log`).

## 3. Findings

**F1. DI-56 is ruled and not implemented on either face.** (reading, reproduced)
`ProfileData.natBound` (`src/Effect4/Program/Profile.lean:90-93`) is checked in two places
only: the scalar model's boundary (`src/Effect4/Program/HostBoundary.lean:57-64`, namespace
`Profile.Scalar`) and the harness recorder (`harness/truth/session/record.ts:21`,
`protocol.ts:57`, `Session.lean:66,77,107`). It is not checked by admission, the printer
(`Codegen/PrintLeaf.lean:158` prints any literal; `TypeScript/Render.lean:125` renders it with
`toString`), the reader (`Codegen/Read.lean:149` reads any non-negative literal), the prelude
atoms (`prelude-atoms.gen.ts`: `add`, `mul`, `succ` unchecked), or the OCaml lowering
(`Translate.lean:158-198`). §2 is the consequence.

**F2. The OCaml lowering wraps on addition and saturates on multiplication; a saturating or
wrapping result can steer a branch.** (reading, reproduced, proved in a model) Raw `+` for
`Nat.add` and `Nat.succ` (`Translate.lean:162`, `:175`), saturating `Nat.mul`, `Nat.pow`,
`Nat.shiftLeft` (`:163-169`, `:182-191`), literals at or above 2^62 become `max_int`
(`:724`). In the engine cut: 36 lines with a raw `+`, 29 with `max 0 (a - b)`, 2 saturating
products (`ocaml/engine/api_engine.ml`, counted). The model theorems `mlAdd_wraps` and
`mlMul_saturates` state exactly when; `mlAdd_postcheck_blind` shows a check made after the
addition cannot see the overflow (the wrapped sum is below every bound).

**F3. The "63-bit rule" note argues from lengths, but program values reach 2^62 from a few
small literals.** (reading, reproduced) `ocaml/gen/NOTES.md:223-249` justifies saturation because
"a program whose payload really is longer than `max_int` bytes cannot exist", and its gap
table says the `Nat → int` caveat is "not hit by `Fibers.lean` (counters, tokens,
priorities) either way" (`:255`). Since the atoms entered the engine closure, program
arithmetic is in it (`program_native_atom_eval`, `api_engine.ml:2969`; its `add` arm at `:3034-3051`), and §2 hits it.

**F4. `E4_nat` is stale and unused for the operations that matter.** (reading)
`ocaml/engine/e4_nat.mli` says `add`/`mul` saturate in the module but the generator "emits raw
`+` and `*`" (D3; `*` now saturates), that division by zero is "the ONE place the generated
code is wrong today" (N2; it is guarded, `Translate.lean:170-171`, and routed to `E4_nat.div`
/ `E4_nat.rem` by `ocaml/engine/externs.txt:163-164`), and cites `Translate.lean:120-174`,
`:429`, `:148`, `:166`, which no longer point at those rows. Only `E4_nat.div` and `E4_nat.rem`
appear in the generated engine (counted: 1 each).

**F5. The engine already has the refusal plumbing a bounded OCaml profile needs.** (reading)
`E4_engine.step` catches `E4_clock.Profile_refusal`, keeps the input machine, and answers
`Outside_profile` (`ocaml/engine/e4_engine.ml:332-341`, `:629-638`; `e4_engine.mli:21-25`).
Today only the clock observation raises it (`ocaml/clock/e4_clock.ml`, `to_profile_nat`). A
checked `Nat.add` that raises the same exception would be caught with no engine change.

**F6. An exact target carrier already exists for one type, and shows the cost of doing it
per type.** (reading, counted) `ClockMillis` is a two-constructor nominal type so mono LCNF
keeps it (`src/Effect4/Data/ClockMillis.lean:1-12`); only it "lowers to arbitrary precision
target arithmetic" (Zarith, `ocaml/clock/e4_clock.ml`), through a flow analysis that tracks
which OCaml values came from saturated literals (`src/OCaml5/Lcnf/ClockFlow.lean`, 450 lines,
plus `Clock.lean` 42, `e4_clock.ml` 42, `ClockMillis.lean` 143: 677 lines for one carrier).
The 2026-09-20 landing review called it a scope decision (F4 there). Doing the same for
program naturals would repeat that per type; switching every `Nat` would not (§7, option N2).

**F7. On the TypeScript face a check after the operation is exact; on OCaml it is blind.**
(proved in the models, reproduced through the translator) A double rounds monotonically, so
the double a result becomes is safe exactly when the exact result is (`roundNat_safe_iff`):
`Number.isSafeInteger(a + b)` decides the profile (`jsAdd_checked`, `jsMul_checked`). OCaml
wraps, so the check must come before the operation (`mlAddChecked_exact`,
`mlAdd_under_check`, `mlMul_under_check`), or use the exact carrier. The project's own
translator (`translateClosure`, `Lower.lean`) lowers a post-checked addition to
`let s = a + b in if s <= bound ...` and a pre-checked one to
`let _x_1 = max 0 (bound - b) in if a <= _x_1 then a + b ...` (`lower.log`); compiled and run
at the bound `max_int` on 2^61 + (2^61 + 5), the post-checked one answers
`Some -4611686018427387899` and the pre-checked one `None` (`ocaml/lower.log`).

**F8. The prelude's `div` is exact on safe inputs, and not above them.** (tested, reading)
`Math.floor(a / b)` agreed with exact division on 1,016,384 safe pairs: 1,000,000 random,
every divisor up to 4096 against the largest safe dividend, the 4096 divisors just below it,
and the 4096 dividends just below it divided by 3 and by 4 (0 differences, `ts/faces-run.log`;
`div` and `mod` both). Above 2^53 it differs in 163 of 100,000 pairs, and in 183 of
the model's 4,000 division vectors. Why it is exact below (an argument, not a proof): the gap
between `a / b` and the next integer `q + 1` is at least `1 / b`; rounding could reach `q + 1`
only if that gap were at most half the spacing of doubles just below `q + 1`, and working out
that spacing gives `a ≥ 2^53` in both cases (`q + 1` a power of two or not). A prelude `div` of
`(a - a % b) / b` would be exact by construction, since the quotient is then an exactly
representable integer (`jsDivExact_exact`, proved in the model).

**F9. `Json.ofNat` says it is "the binary64 the host would parse"; it truncates, the host
rounds to nearest.** (reading, tested) `src/Effect4/Data/JsonNumber.lean:37-44`. The two
differ on 787 of 4,000 random naturals above 2^53 (the red control of §4). No wrong value
crosses the public boundary, because `Schema.encode` accepts only values that decode back
exactly (`src/Effect4/Schema/Codec.lean:230-236`, the owner's amendment to
`E4-SCHEMA-CE-056`). The docstring should say "truncated toward zero; equal to the host's
reading on exactly representable naturals, the only ones the codec admits".

**F10. The truth comparator is protected, the manifest side is not checked.** (reading)
rc.112's side throws on an unsafe integer (`harness/truth/run-truth.ts:345-349`), so a false
agreement cannot come from a rounded host number. Lean's side is written with exact digits
(`Truth.lean:407-409`, `toJson n`) and parsed by `JSON.parse`, which rounds above 2^53; the host
check above is what keeps that from mattering.

## 4. How the models were checked (tested, with red controls)

The models are Lean functions written from the code that runs (`Models.lean`, header). They
are checked against the real engines on random operations from a fixed generator:

| check | inputs | result | red control |
| --- | --- | --- | --- |
| TypeScript model vs bun's JavaScript (`ts/model-check.ts`, the generated prelude atoms) | 20,000 lines: 4,000 each of rounding a natural (to 2^90), `add`, `mul`, `sub`, `div` on doubles (to 2^80) | 0 differences | the tree's truncating conversion in place of the model: 787 of 4,000 differ |
| OCaml model vs the generated atom evaluator (`ocaml/model_check.ml`, `Api_engine_inst.program_native_atom_eval`) | 30,000 lines: 5,000 each of `add`, `sub`, `mul`, `div`, `mod`, `lt` on all 63-bit ints, negatives included | 0 differences | exact natural answers in place of the model: 1,000 of 1,000 overflowing sums and 460 of 1,000 products differ |

The red controls show each check can fail. The vectors are regenerated by compiling
`Models.lean` (same seed, same files).

## 5. Where rc.112 depends on float behaviour, and what the language does there

| rc.112 site | float behaviour | this language today |
| --- | --- | --- |
| `Duration.ts:110-114` `DurationValue` | milliseconds are a double; nanoseconds a bigint; two infinite values | `Ty.duration` is an opaque host handle (`src/Effect4/Program/Ty.lean:229-231`); no duration arithmetic |
| `Duration.ts:38-41`, `:402-420` `make` | a fractional millisecond becomes nanoseconds by rounding ties away from zero; `NaN`, `0` and `-0` become zero; a non-finite double becomes an infinite duration | not modelled; `sleep` takes whole milliseconds as `nat` (`src/Effect4/Program/Native.lean:214-215`) |
| `Duration.ts:1920`, `:1831`, `:1752`, `:1550` (`sum`, `subtract`, `times`, `divide`) | two millisecond durations add, subtract, multiply, divide as doubles (rounding above 2^53, overflow to an infinite duration) | not modelled |
| `Duration.ts:788` `toMillis` | nanoseconds become `Number(nanos) / 1_000_000` | not modelled |
| `internal/effect.ts:6037-6066` `ClockImpl` | `currentTimeMillis` is `Date.now()`; `sleep` reads `toMillis`, yields at `<= 0`, never resumes on a non-finite value, and splits long delays into chunks of 2^31 - 1 ms | `clockNow` answers the exact `ClockMillis` as a `nat` (`src/Effect4/Machine/Stores.lean:1956`), refused on OCaml above 2^53 - 1 (`e4_clock.ml`); sleeps run on the logical timer store (`src/Effect4/Machine/Timer.lean`) |
| `internal/effect.ts:6078` | the `performance.now()` fallback rounds a double to nanoseconds | not modelled |
| `Schedule.ts:1090-1098` `exponential` | `base * Math.pow(factor, n)`; ECMAScript leaves `Math.pow` implementation-approximated, and 2^1024 overflows to an infinite delay | no Schedule rows |
| `Schedule.ts:1122-1134` `fibonacci` | double `a + b` (inexact past 2^53, near the 79th term for 1 ms) | none |
| `Schedule.ts:1441-1448` `jittered` | `millis * 0.8 * (1 - r) + millis * 1.2 * r`, `r` a random double | none |
| `Random.ts:79`, `:177-184`, `:210`, `:251` | `next` is a double in [0, 1); `nextIntBetween`, `shuffle`, `choice` floor a double product | no Random rows |
| `Number.ts:88`, `:153`, `:279`, `:1209-1275`, `:1383-1426` | double `sum`, `multiply`, `divide`; `remainder` rescales by decimal digits (`toFixed`, `parseInt`); `round` multiplies by 10^precision | none; the atoms are the language's own arithmetic |

So binary64 enters the semantics only when one of these is modelled. When it is, two limits
apply. First, a full binary64 model is the right shape (FloatLib's `Binary` with 11 exponent
and 52 fraction bits, signed zeros, infinities, NaN), and this repository already has the bit
carrier for it (`Float64`). Second, `Math.pow` is not correctly rounded by the standard, so no
specification reproduces `Schedule.exponential` bit for bit for an arbitrary factor; that value
must be a host answer on the tape, or the profile must restrict the factor to exact cases.

## 6. FloatLib: what it is, and what transfers

Sources: the arXiv abstract and HTML (2609.19352v1, "FloatLib: Verified Floating-Point
Arithmetic in Lean", George, Adkisson, Anandkumar, submitted 2026-09-16), and through WebFetch
the repository's README, `lakefile.lean`, `lean-toolchain`, `lake-manifest.json`, `LICENSE`,
`FloatLib.lean`, `FloatLib/{Numerics,Kernels,Floats}.lean`, `FloatLib/Kernels/FixedWord.lean`
and `FloatLib/Floats/THEOREMS.md`. Nothing was cloned, downloaded or run, so every statement in
this section is a **reading** of those pages, paraphrased.

**What it is.** A Lean 4 library of number formats with proofs: IEEE binary and decimal
(with subnormals, signed zeros, infinities, NaN and the rounding modes), posits with exact
quire accumulation, P3109, small machine-learning formats, fixed point, logarithmic,
codebook and user-defined formats, plus intervals.

- **Layers.** `FloatLib/Numerics`: meaning that does not depend on a representation (exact
  dyadic and rational values, contracts, enclosures). `FloatLib/Kernels`: `FixedWord`
  (algorithms on one, two and four 64-bit words), `LimbArray` (runtime-sized arrays of 32-bit
  limbs), `IntegerRoot`; each refined to a natural-number specification. `FloatLib/Floats`:
  the `ExecFloat` carriers and contracts, one directory per format family, intervals.
- **Specification versus certified backends.** The reference operation computes the exact
  intermediate (for a fused multiply-add, the exact dyadic x·y + z) and rounds once. A fast
  backend is a value that carries a proof that it returns the reference's encoded result: the
  paper's `ExecFloat.Backend.Certified` has the fields `spec`, `estimate` (a cost),
  `run` and `run_eq_spec : run = spec`, so the equation is part of the value (§3.1). The
  user-facing form is `ExecFloat.Proof.add_eq_spec` and its siblings; the README's example
  proves `x + y = ExecFloat.Spec.add x y` for a configured binary32.
- **Interchangeable backends.** A planner chooses among certified alternatives by a cost
  model: complete tables for 4-8 bit formats, word kernels for 16-64 bits, limb kernels above.
  A wrong cost estimate can make it slow, never wrong, because every alternative carries the
  same equation.
- **Limb kernels.** A guard-and-sticky ("jamming") lemma: shift right, and if any dropped bit
  was nonzero set the lowest kept bit; with two spare bits the rounding decision is unchanged
  (paper §3.3, Theorem 4). So long intermediates need not be kept whole.
- **Checked quotients.** Division runs an unproved algorithm (Knuth's Algorithm D) that
  proposes a quotient and remainder, and accepts them only after a cheap runtime check
  (q·d + r = n·2^s and r < d); only the check is proved (§3.4, Theorem 5).
- **Tables.** For formats of at most 8 bits, a binary operation has at most 2^16 input pairs; a
  complete table replaces decoding, arithmetic and rounding, and each entry is proved equal to
  the reference.
- **Execution preservation** (the paper's words are "backend refinement"; it does not use
  this phrase). The proofs are equations between Lean functions; compiled code runs the same
  functions with the proofs erased. `@[csimp]` equations swap in faster
  functions at compile time, each justified by a proved equation; `FloatLib/Kernels.lean`
  routes `Numerics.roundShiftRightEven`, `Numerics.roundQuotientEven` and `Nat.sqrt` to
  native-word kernels below 2^64 this way. The stated trust boundary is Lean's compiler,
  runtime and hardware (§3.7).
- **Differential testing.** The TestFloat adapter runs the reference *model* (not every
  backend) against Berkeley TestFloat: 102,454,320 evaluations, zero differences, under a
  stated relation (result words and the five IEEE flags; NaNs compared by quiet or signalling
  class only), four rounding directions, tininess after rounding (§5.2). The backends are tied
  to the model by the proofs, not by the tests. Comparisons with MPFR and FLoPS agree; the
  SoftPosit comparison found differences the paper traces to a SoftPosit rounding defect.
- **Native floats.** Theorems relate the library to Lean's own `Float` and `Float32` logical
  models on finite inputs, including how a natural becomes a `Float`
  (`ExecFloat.Binary.toModel_ofFloat_ofNat`, listed in `THEOREMS.md`).
- **Toolchain, dependencies, license.** `leanprover/lean4:v4.34.0`; `require mathlib` at
  `v4.34.0` (manifest revision `5ed2965`), which brings plausible, LeanSearchClient,
  import-graph, ProofWidgets4, aesop, Qq, batteries; also `Cli` at `v4.34.0`;
  `fixedToolchain := true`; the Lean module system (`public import`); version 0.1.0; MIT
  license. The paper reports speedups over FLoPS and Universal and slower binary32 arithmetic
  than MPFR and SoftFloat.

**Fit with this repository.** (reading) This repository is on `leanprover/lean4:v4.33.1`
with no Mathlib (`lean-toolchain`, `lake-manifest.json`: aesop, batteries, hash, typescript,
effects). Using FloatLib means a toolchain bump and Mathlib in the build. The axiom gate holds
every `Effect4.*` and `Test.*` declaration to `[propext, Quot.sound]`; FloatLib's numerical
theorems are about Mathlib's real numbers, which need `Classical.choice`. Whether its
executable specification stays inside the ceiling is unknown until someone runs
`#print axioms` on it, which this seat was not allowed to do. So FloatLib could enter today only
as an outside oracle (a tool root, like the TypeScript harness), not inside the gated roots.

**What transfers.** Each item names the connection of the external runtime contract (§8
there) it serves.

1. **Every compile-time substitution carries its equation** ("admitted compiler IR to target
   semantics"). `Translate.builtin?` is a table of substitutions (`Nat.add` becomes `+`, and so
   on) with no equations; FloatLib's `@[csimp]` rule is that each one needs a proved equation on
   a stated domain. `Models.lean` writes those equations for the natural-number rows, in a
   model of OCaml's `int`, and checks the model against the generated code (§4). That is the
   first piece of a certified builtin table.
2. **A backend is a value with its proof** ("abstract storage to backing implementation").
   The engine's `Fast` and `Ref` carriers are tied by a differential (`ocaml/engine/test`).
   FloatLib's shape would put a refinement proof beside each Lean-side carrier, so choosing a
   faster one cannot change an answer.
3. **Propose, then check** (the contract's "independently checked certificate"). This
   repository already has two instances: `Schema.encode` accepts only what decodes back
   exactly, and the host-answer check (path C, `fitsB`). For numbers, the pre-check
   `a ≤ bound - b` is the certificate that makes a raw target `+` exact
   (`mlAdd_under_check`). For compilation, validating each translated declaration is an
   alternative to proving the translator.
4. **Whole small domains, decided.** Where a domain is small (a byte, a pair of bytes, an
   alphabet), check all of it with `decide` instead of sampling (the owner's
   `decide +kernel` note agrees).
5. **Test the specification against the outside oracle, under a named relation; tie the
   backends by proof.** The truth harness tests the Lean reference against rc.112; the OCaml
   engine should be tied to the reference by proof or certificate, with the differential as a
   check. The number observation should be stated as FloatLib states its NaN rule: "exact
   natural equality inside the profile; outside it, both faces refuse at the same located
   point".
6. **Say the trust boundary.** FloatLib's is Lean's compiler, runtime and hardware. It gets
   exact naturals for free from Lean's runtime; this repository's native face lost them at
   the translation table. That is the whole of the natural-number issue.
7. **A verified multi-word natural is a known method.** If the owner wants the native face
   exact and made from LCNF, FloatLib's limb kernels show how: a Lean natural in several
   words, refined to `Nat`, with a one-word fast path substituted by a proved equation (§7,
   option N3).

## 7. Proposal: the number policy for the three faces

The rule for all three: **the Lean reference is exact; each target has a profile (its largest
exact natural); inside the profile a target equals the reference; outside it, the target
refuses at a located point.** This is DI-56 made checkable. The relation between two faces is
then a simulation on one observation: equal values on in-profile runs, the same refusal point
on out-of-profile runs.

### The Lean judgment ("in profile"), proved in `Checked.lean`

```lean
inductive Refusal where
  | outsideProfile (path : List Nat) (value : Nat)
  | stuck (path : List Nat)

def evalChecked (bound : Nat) (env : List Val) (path : List Nat) : Term → Except Refusal Val
def InProfile (bound : Nat) (env : List Val) : Term → Prop

theorem evalChecked_ok_iff (bound : Nat) (env : List Val) (path : List Nat) (t : Term) (v : Val) :
    evalChecked bound env path t = .ok v ↔ evalTerm env t = some v ∧ InProfile bound env t
theorem evalChecked_refusal_outside (bound : Nat) (env : List Val) (path q : List Nat) (t : Term)
    (n : Nat) (h : evalChecked bound env path t = .error (.outsideProfile q n)) : bound < n
```

It is a located refusal in this repository's sense: total, the refusal names a path and a
value, and it is complete against the judgment. On the faces program it refuses the first
binding at path `[]` with 2^53 + 1 under rc.112's bound, and only the two 2^62 bindings under
the OCaml bound (finite, `verdicts`).

### The implementation form, proved in `Models.lean`

```lean
def evalIn (bound : Nat) : NativeAtom → List Val → Except AtomRefusal Val
  | .add, [.nat a, .nat b] =>
    if a ≤ bound - b then .ok (.nat (a + b)) else .error (.grows .add [a, b])
  | .succ, [.nat a] => if a < bound then .ok (.nat (a + 1)) else .error (.grows .succ [a])
  | .mul, [.nat a, .nat b] =>
    if b = 0 ∨ a ≤ bound / b then .ok (.nat (a * b)) else .error (.grows .mul [a, b])
  | atom, vs => guardOpt bound (atom.eval vs)

theorem evalIn_ok_iff (bound : Nat) (atom : NativeAtom) (vs : List Val)
    (hvs : ∀ n, Val.nat n ∈ vs → n ≤ bound) (v : Val) :
    evalIn bound atom vs = .ok v ↔ atom.eval vs = some v ∧ Within bound v
```

It checks before each operation that can grow and reports operands, never an overflowing
result, so its own lowering never overflows: under its checks every operation it performs is
exact in the OCaml model (`mlAdd_under_check`, `mlMul_under_check`, for any bound up to
`max_int`), and the translator lowers the check the way the model says (`Lower.lean`,
`lower.log`: `max 0 (bound - b)`, then `<=`, then `+`; the product's check divides under the
`Nat.div` row's zero guard). If the machine's term evaluation called it, the OCaml engine would
inherit the refusal through LCNF with no new extern rows for the atoms.

### The simulation inside the profile, proved in `Models.lean`

For the fragment the faces program uses (naturals, Booleans, pairs; `add`, `sub`, `mul`,
`div`, `mod`, `lt`, `pair`), one theorem for any number system:

```lean
structure Face (α : Type) where
  lit : Nat → α
  add sub mul div mod : α → α → α
  lt : α → α → Bool

structure Agrees {α : Type} (F : Face α) (B : Nat) : Prop  -- exact on operands and results ≤ B

theorem Face.sim {α : Type} {F : Face α} {B : Nat} (hF : Agrees F B) (env : List (MV Nat))
    (henv : ∀ v ∈ env, MV.Le B v) (t : Term) (ht : InProfileM B env t) :
    F.eval (env.map (MV.map F.lit)) t = (exact.eval env t).map (MV.map F.lit) ∧
      ∀ w, exact.eval env t = some w → MV.Le B w

theorem exact_eval_toVal (env : List (MV Nat)) (t : Term) (w : MV Nat)
    (h : exact.eval env t = some w) : evalTerm (env.map MV.toVal) t = some (MV.toVal w)
```

Instances: `ocaml_agrees : Agrees ocaml (2^62 - 1)`; `typescript_agrees` at `2^53 - 1`
given the one tested lemma about `Math.floor(a / b)` (F8); `typescriptExactDiv_agrees`
outright for the proposed `(a - a % b) / b`. Together: `ocaml_matches_machine` and
`typescriptExactDiv_matches_machine` (inside the bound, the target model computes the image of
the machine's own value). This is "two folds agree when their algebras do" for numbers: each
face owes only the six per-operation lemmas.

### Options per face

| face | option | what it is | cost | status |
| --- | --- | --- | --- | --- |
| Lean | L0 | exact `Nat`, plus the judgment above | two definitions, the proved iff | ready (`Checked.lean`) |
| Lean | L1 | the machine's term evaluation parameterized by `Option NumberProfile` (`none` = today's `evalTerm`), so the refusal is defined once, in Lean | one parameter through `Compile.lean`'s 31 `evalTerm` call sites (`src/Effect4/Program/Compile.lean:429-1339`), a theorem that `none` is `evalTerm` | owner decision |
| TypeScript | T1 (DI-56) | prelude `add`, `succ`, `mul` check the result with `Number.isSafeInteger` and throw the harness's `ProfileRefusal`; the printer refuses a literal above 2^53 - 1 (a new `PrintRefusal`, located); the reader refuses one (a `ReadRefusal`); the comparator classifies such runs "outside the profile" | three `NativeAtom.row` prelude strings, two refusal constructors, one comparator branch | ready; exactness of the check proved (`jsAdd_checked`, `jsMul_checked`) |
| TypeScript | T2 | naturals as `bigint` | every printed program and every Effect API call that takes a `number` changes | not recommended for the rc.112 profile |
| OCaml | N1 (DI-56) | checked `Nat.add`, `Nat.succ`, `Nat.mul`, `Nat.pow`, `Nat.shiftLeft` raising `Profile_refusal` (already caught, F5); a literal at or above 2^62 is a generation-time refusal (no current cut has one) | about seven table rows, `E4_nat` repaired (F4), one regeneration (`make gen-lcnf`, measured at 14m38s, `Makefile:116`); about 1 ns per addition against 0.3-0.8 ns raw (measured, `ocaml/bench_add.log`) | ready |
| OCaml | N2 | exact: every `Nat` is Zarith's `Z.t` (what Lean's own runtime does with GMP) | the translator's type map and every `Nat` row; every seam that types a Lean natural as `int` in `e4_engine.mli`'s `INSTANCE` (values, tags, fiber ids, tokens, counts); about 1.07 ns per addition (measured, same file); removes the 63-bit rule, the literal clamp and the clock special case (F6); trusts Zarith and GMP | owner decision |
| OCaml | N3 | exact and made from LCNF: a Lean multi-word natural refined to `Nat`, one-word fast path by a proved equation (FloatLib's method) | the largest: arithmetic and proofs in Lean, and a real array carrier (the translator's `Array` is a list today, `Translate.lean:240-245`) | later |

**Recommendation.** L0 + T1 + N1 now; decide L1 and N2 with the owner. N1 and T1 are what DI-56
already ruled. N2 is the only way to claim unbounded naturals on the native face (the
contract's §8: "prefer exact representation for an unbounded claim"); it costs a wide seam
change, not a new idea.

### First slice (one branch, no OCaml regeneration)

1. `src/Effect4/Program/`: the judgment (`evalChecked`, `InProfile`) and `evalIn`; their laws
   (`evalChecked_ok_iff`, `evalChecked_refusal_outside`, `evalIn_ok_iff`) in the Laws graph.
2. `NativeAtom.row` prelude strings for `add`, `succ`, `mul`: result checked with
   `Number.isSafeInteger`, a `ProfileRefusal` thrown; regenerate the prelude group.
3. Printer and reader: refuse a natural literal above `rc112.natBound`, with its path.
4. The comparator: an "outside the profile" class.
5. Fixtures: this seat's faces program (expected: the rc.112 face refuses at the first binding
   with operands 2^52 and 2^52 + 1; `evalChecked` at 2^53 - 1 refuses there too), the
   `bigLiteral` program (refused by the printer), and DI-56's `M = MAX_SAFE_INTEGER` pair.

The OCaml slice (N1) follows as its own commit with its regeneration; its fixture is the same
program, expected `Outside_profile` at the fourth binding under the native bound.

## 8. Open questions for the owner

1. **Native face: bounded (N1) or exact (N2)?** Recommendation: N1 now, because DI-56 ruled
   it and it is small; N2 when a use needs naturals above 2^62 on the native face. Both keep
   the Lean reference exact.
2. **Where does the refusal live: in Lean (L1, one definition lowered to OCaml) or only in
   the targets?** Recommendation: L1, because the OCaml engine then inherits the check from
   the same definition the proofs are about, and the TypeScript prelude is the one hand
   implementation left (proved exact in the model).
3. **Which bound does the OCaml engine use for program values when it runs a program that
   will be compared with rc.112: rc.112's 2^53 - 1, or its own 2^62 - 1?** Recommendation: the
   profile the program was admitted under, as data (`ProfileData.natBound`), so the two faces
   refuse at the same point.
4. **Does the language plan to model `Duration`, `Schedule` or `Random` arithmetic?** If yes, a
   binary64 specification is needed, and FloatLib is the reference for its shape; `Math.pow`
   must stay a host answer. If no, binary64 stays a data-plane carrier only.
5. **FloatLib as an oracle.** If binary64 arithmetic is modelled, run FloatLib (or TestFloat)
   outside the gated roots as the oracle for that model, the way FloatLib uses TestFloat.
   Needs someone allowed to fetch and build it (Lean v4.34.0 and Mathlib).

Proposed decisions rows (for the coordinator's register, not written there): "number profile
per target: which of N1/N2 on the native face"; "profile refusal defined in Lean (L1) or per
target"; "OCaml bound for rc.112-compared runs".

## 9. What was run

All Lean runs used the lock, from the repository root:
`bash /private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/0b88b41e-40ac-47c3-a942-8b02c701bb13/scratchpad/serial.sh lake env lean -M6144 -DwarningAsError=true docs/research/2026-09-30-pass/numbers/<File>.lean`.
All OCaml compiles and runs went through the same lock; they read the built libraries in
`ocaml/_build` (built with `be15b062`'s engine cut, 15:39) and wrote only into this folder.
`git status --short ocaml harness` stayed empty. The engine drivers were compiled with:

```
serial.sh bash -c 'cd ocaml && opam exec --switch=effect4 -- ocamlfind ocamlopt \
  -package zarith,unix,threads.posix -thread -linkpkg \
  -I _build/default/clock/.effect4_clock.objs/byte -I _build/default/clock/.effect4_clock.objs/native \
  -I _build/default/eff/.effect4_eff.objs/byte -I _build/default/eff/.effect4_eff.objs/native \
  -I _build/default/engine/.effect4_engine.objs/byte -I _build/default/engine/.effect4_engine.objs/native \
  _build/default/clock/effect4_clock.cmxa _build/default/eff/effect4_eff.cmxa \
  _build/default/engine/effect4_engine.cmxa \
  ../docs/research/2026-09-30-pass/numbers/ocaml/<driver>.ml \
  -o ../docs/research/2026-09-30-pass/numbers/ocaml/<driver>.exe'
```

| command | exit | result |
| --- | --- | --- |
| lean `numbers/Faces.lean` | 0 | all `#guard`s pass; printed TypeScript, 2324 program bytes, `literal62` bytes (`faces.log`) |
| lean `numbers/Checked.lean` | 0 | all `#guard`s pass; axioms below (`checked.log`) |
| lean `numbers/Models.lean` | 0 | all `#guard`s pass; wrote 20,000 TypeScript vectors, 4,000 red-control vectors, 3,000 OCaml red-control vectors, 30,000 OCaml vectors; 183 of 4,000 division vectors floor differently from exact; axioms below (`models.log`) |
| the driver compile above, `<driver>` = `faces` | 0 | built |
| `numbers/ocaml/faces.exe <hex>` (program, then `literal62`) | 0, 0 | §2 row; `decode refused` on both instances for 2^62 (`ocaml/faces.log`) |
| the driver compile above, `<driver>` = `model_check`; run on `ml-vectors.txt`, then `exact-vectors.txt` | 0, 0, 0 | 0 of 30,000 differ; red: 1,000/1,000 sums, 460/1,000 products (`ocaml/model_check.log`) |
| `ocamlfind ocamlopt -package zarith,unix -linkpkg bench_add.ml` in `numbers/ocaml`; run | 0, 0 | ns per addition, median of 5: raw 0.27 (0.80 with a mask), checked 1.07, Zarith 1.07 (1.61) (`ocaml/bench_add.log`; arm64, OCaml 5.1.1, Zarith 1.14; a measurement, not a gate) |
| lean `numbers/Lower.lean` | 0 | the translator's OCaml for `plainAdd`, `postAdd`, `preAdd`, `preMul` (4 translated, none missing, no todos; `lower.log`), written with a driver to `ocaml/lower.ml` |
| `ocamlfind ocamlopt -w -a lower.ml -o lower.exe` in `numbers/ocaml`; run | 0, 0 | post-check `Some -4611686018427387899`, pre-check `None` at `max_int`; both `None` at 2^53 - 1; `pre_mul` refuses (2^53 + 1) · 512 and computes 2^31 · 2^30 exactly (`ocaml/lower.log`) |
| `cd harness/truth && bun -e "$(cat …/numbers/ts/faces-run.ts)"` | 0 | §2 row; literal and JSON channels; DI-56 pair; `div`/`mod` differential (`ts/faces-run.log`) |
| `cd harness/truth && bun -e "$(cat …/numbers/ts/model-check.ts)"`, then with `VECTORS=…/trunc-vectors.txt` | 0, 0 | 0 of 20,000 differ; red: 787 of 4,000 (`ts/model-check.log`) |

Axioms (every theorem in the probe files; none reaches `Classical.choice`, `sorryAx` or any
other axiom):

- `Checked.lean` (9 theorems): `guardNat_nat`, `guardNat_ok`, `guardNat_of_within`, `guardNat_refusal`,
  `evalChecked_sound`, `evalChecked_inProfile`, `evalChecked_refusal_outside` depend on
  `[propext]`; `evalChecked_complete`, `evalChecked_ok_iff` on `[propext, Quot.sound]`.
- `Models.lean` (44 theorems): `roundNat_of_le`, `jsAdd_exact`, `jsMul_exact`, `jsLt_exact`,
  `maxInt_eq`, `mlAdd_postcheck_blind` depend on no axioms; `jsSub_exact`, `jsMod_exact`,
  `mlLt_exact`, `guardOpt_nat`, `guardOpt_ok_iff`, `mul_check_iff`, `atom_sim`, `atom_toVal`
  on `[propext]`; `roundNat_ge`, `roundNat_safe_iff`, `wrap_of_range`, `mlAdd_exact`,
  `mlAdd_wraps`, `mlSub_exact`, `mlDiv_exact`, `mlMod_exact`, `mlMul_exact`,
  `mlMul_saturates`, `mlAddChecked_exact`, `mlAddChecked_complete`, `evalIn_ok_iff`,
  `mlAdd_under_check`, `mlMul_under_check`, `jsAdd_checked`, `jsMul_checked`, `Face.sim`,
  `ocaml_agrees`, `typescript_agrees`, `jsDivExact_exact`, `typescriptExactDiv_agrees`,
  `ts_add`, `ts_sub`, `ts_mul`, `ts_mod`, `ts_lt`, `exact_eval_toVal`,
  `ocaml_matches_machine`, `typescriptExactDiv_matches_machine` on `[propext, Quot.sound]`.

What the proofs are about: `Checked.lean` is about the machine's own `Term`, `Val`,
`evalTerm` and `nativeAtom`. `Models.lean` is about Lean models of the two targets' number
systems and their tie to the machine's `evalTerm` on a fragment; the models are tested, not
proved, to match the targets (§4), and nothing here is a proof about the OCaml compiler, a
processor or a JavaScript engine. `typescript_agrees` carries one hypothesis, the division
lemma, which is tested (F8) and not proved.

Web sources (WebFetch, read only): `arxiv.org/abs/2609.19352`, `arxiv.org/html/2609.19352v1`,
`github.com/lean-dojo/FloatLib` and its raw `README.md`, `lakefile.lean`, `lean-toolchain`,
`lake-manifest.json`, `LICENSE`, `FloatLib.lean`, `FloatLib/Numerics.lean`,
`FloatLib/Kernels.lean`, `FloatLib/Floats.lean`, `FloatLib/Kernels/FixedWord.lean`,
`FloatLib/Floats/THEOREMS.md`, and the directory listings of `FloatLib/`, `FloatLib/Kernels`,
`FloatLib/Kernels/LimbArray`, `FloatLib/Floats`.

## 10. Limits and open obligations

- The OCaml runs used the `Fast` and `Ref` instances and each instance's generated `Api.run`
  outcome; the test-only `Api_gen` instance (`ocaml/engine/test/test_diff.ml`) was not run.
  js_of_ocaml was not run (DI-56 names it as a separate target).
- The model fragment has seven atoms (`add`, `sub`, `mul`, `div`, `mod`, `lt`, `pair`);
  `succ`, `pred`, `eq`, `isZero` and `length` are not in `Face`. `Checked.lean` and `evalIn`
  cover every atom.
- `typescript_agrees` assumes the division lemma (tested, F8). Proving it needs a lemma about
  `floorRoundDiv` that this seat did not write.
- The benchmark is one machine and three loops; it prices an addition, not an engine run.
- Nothing about FloatLib was run; §6 is a reading.

## 11. Files

| file | what |
| --- | --- |
| `Faces.lean`, `faces.log` | the program, its type, the Lean answer, the printed TypeScript, the bytes; the `2^53 + 3` literal and the `2^62` literal |
| `Checked.lean`, `checked.log` | the profile judgment as a located refusal; the faces program's verdicts under two bounds |
| `Models.lean`, `models.log` | the TypeScript and OCaml number models and their theorems; `evalIn`; the simulation `Face.sim` and its instances; the tie to `evalTerm`; the three predictions; the vector writers |
| `Lower.lean`, `lower.log`, `ocaml/lower.ml`, `ocaml/lower.log` | three additions and a product through the project's LCNF translator, then compiled and run |
| `ocaml/faces.ml`, `ocaml/faces.log` | the OCaml engine on the program's bytes |
| `ocaml/model_check.ml`, `ocaml/model_check.log`, `ocaml/ml-vectors.txt`, `ocaml/exact-vectors.txt` | the OCaml model against the generated atom evaluator, and its red control |
| `ocaml/bench_add.ml`, `ocaml/bench_add.log` | the cost of one addition, three ways |
| `ts/faces-run.ts`, `ts/faces-run.log` | the printed program under rc.112, and the channel checks |
| `ts/model-check.ts`, `ts/model-check.log`, `ts/model-vectors.txt`, `ts/trunc-vectors.txt` | the TypeScript model against JavaScript, and its red control |

The OCaml build products (`.cmi`, `.cmx`, `.o`, `.exe`) were deleted after the runs; the
commands above rebuild them.
