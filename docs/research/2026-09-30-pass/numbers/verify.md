The seat's evidence holds: every probe reruns byte-identically and the three faces really disagree. But the plan it recommends (L0 + T1 + N1) does not give the "same refusal point" its §7 promises. T1 and N1 refuse at different bounds, T1's throw carries no location, and N1's refusal would escape the generated `Api.run`.

# Numbers seat: adversarial verification

Verifier for seat `numbers`. Base `be15b062` (HEAD `6f7f6601` changes only docs, `AGENTS.md` and
one tools file; `src/`, `ocaml/` and `harness/` are the same as at the base). 2026-09-30.

I wrote only `verify.md`, `verify-edges.lean`, `verify-div.lean` and `verify-omega.lean` in this
folder. My scratch drivers, copies and logs are in the session scratchpad (`verify-numbers/`).

**Good news beyond the seat's claims.** The one unproved hypothesis of `typescript_agrees` (the
division lemma) is now proved for the seat's model, byte-identical definitions restated
(`verify-div.lean`, `hdiv`, `[propext, Quot.sound]`). With it, the TypeScript model agrees with
the machine up to 2^53 - 1 with no assumption, and the prelude `div` does not need to change for
the proof. The model's tie to JavaScript is still the seat's test.

**One side effect of rerunning.** Rerunning the seat's `Models.lean` and `Lower.lean` rewrote five
of the seat's files: `ts/model-vectors.txt`, `ts/trunc-vectors.txt`, `ocaml/ml-vectors.txt`,
`ocaml/exact-vectors.txt` and `ocaml/lower.ml`. The probes write these files each time they run.
I backed them up and took SHA-256 sums of all 26 seat files before the reruns. Afterwards all 26
matched, so the rewritten files have exactly the same bytes; only their timestamps changed (18:36).

Evidence words used here: **proved** (a Lean theorem, axioms shown), **reproduced** (the real
engine or runtime was run again and printed the value), **tested** (a finite differential with a
red control), **finite** (a `#guard`), **reading** (code or paper read, not run).

## Verdicts

| # | claim (short) | verdict |
| --- | --- | --- |
| 1 | one closed, checked program, three answers | confirmed |
| 2 | DI-56 ruled, implemented on neither face | confirmed (its list of places that check is incomplete) |
| 3 | `evalChecked` is a located refusal (`Checked.lean`) | confirmed; path now proved |
| 4 | post-check exact on TS, blind on OCaml; pre-check exact; `evalIn` | partly |
| 5 | `Face.sim`, `ocaml_matches_machine`, TS with or without the division lemma | confirmed; the lemma is now proved |
| 6 | the Lean models match the real engines | partly |
| 7 | the project's own LCNF translator lowers the pre- and post-checks | confirmed |
| 8 | a literal above 2^53 is admitted and means something else in JS; 2^62 refused with no location | confirmed |
| 9 | the engine already has the refusal plumbing N1 needs | partly |
| 10 | the exact clock carrier cost 677 lines | confirmed |
| 11 | stale documentation (`e4_nat.mli`, NOTES §5, `Json.ofNat`) | confirmed |
| 12 | prelude `div` exact on safe inputs, not above | confirmed |
| 13 | FloatLib reading | confirmed, two small corrections |
| 14 | where rc.112 depends on float behaviour | confirmed |
| 15 | cost of one addition | confirmed |

### 1. One program, three answers: confirmed (reproduced)

I reran all three faces and got the seat's rows exactly:

- Lean: `Faces.lean` exits 0 and its output is identical to `faces.log`.
- OCaml: I compiled a copy of `ocaml/faces.ml` against the built engine and ran it on the printed
  hex. `Fast` and `Ref` both print `finished` and
  `list[2,list[true,list[-2305843009213693949,list[5,903]]]]`.
- rc.112: `ts/faces-run.ts` under bun 1.4.2 prints output identical to `ts/faces-run.log`.

I checked that the expression pasted into `ts/faces-run.ts` is byte-equal to line 1 of `faces.log`,
the printer's output. I also checked that it imports the generated atoms
(`harness/truth/prelude-atoms.gen.ts:39` is `a + b`). The causes the seat cites are the code:

- `Translate.lean:162` gives `Nat.add` a raw `+`; the engine has it at `api_engine.ml:3039`.
- `Translate.lean:163-169` gives `Nat.mul` a saturating product; the engine has it at `api_engine.ml:3314`.

I checked the arithmetic of each row by hand, and it matches.

One nuance. "No refusal anywhere" is true of the three runtimes. It is not true of the truth
harness. `harness/truth/run-truth.ts:348` throws `not a safe integer` when it writes the rc.112
value (it holds 2305843009213693952). That is an unclassified error, not a profile refusal, and it
fires only because an unsafe number reaches the final value. (Reading.)

### 2. DI-56 ruled and not implemented: confirmed (reading)

The ruling is at `docs/DESIGN-ISSUES.md:128`, as the seat cites. For the program-arithmetic
conclusion, I confirmed each place the seat says has no check:

- admission: no `natBound`, `admitsNat` or `isSafeInteger` in the typing or `Codegen/Admit.lean`;
- the printer: `PrintLeaf.lean:158`;
- rendering: the typescript package's `Render.lean:125`;
- the reader: `Read.lean:149`;
- the prelude: `prelude-atoms.gen.ts`;
- the lowering: `Translate.lean:158-198`.

The live Lean host admission does not check the bound either. `Program/Admit.lean:59-74` checks
type and liveness only.

The list of places that *do* check is incomplete. The rc.112 bound is also enforced in these places:

- the clock boundaries: `harness/truth/session/clock.ts:20-27` (`ProfileRefusal`, which already
  exists) and `ocaml/clock/e4_clock.ml:38-42` (`number_bound` = 2^53 - 1);
- the truth value wire: `run-truth.ts:348`;
- the keyed recorder: `keyed-recorder.ts:18`, `Keyed.lean:75`;
- `protocol.ts:52`.

None of them touches program arithmetic, so the finding stands.

### 3. `evalChecked`: confirmed (proved), and its path is now proved too

I reran `Checked.lean`: exit 0, output identical to `checked.log`. The axioms match: seven
theorems use `[propext]`; `evalChecked_complete` and `evalChecked_ok_iff` use `[propext, Quot.sound]`.

- The iff is not vacuous. `InProfile` is defined from the exact evaluator, separately from
  `evalChecked`.
- The `verdicts` guards hold: at the rc.112 bound the checker refuses binding 0 at `[]` on 2^53 + 1.
  At the OCaml bound it refuses only the two 2^62 bindings. (Finite.)
- A point the seat did not prove: that the refusal's path is the right path. It had only the
  finite `verdicts` guards (paths `[]` and `[1]`). I proved it: `verify-edges.lean`, `evalChecked_refusal_located`,
  `[propext]`. It says that if `evalChecked bound env path t` refuses with
  `outsideProfile q n`, then `q = path ++ s` for some `s`, the subterm of `t` at `s` exists, and
  its exact value (`evalTerm`) is `.nat n`.

Two limits the note should state:

- **Values from the environment are trusted.** A natural above the bound that comes from the
  environment passes through a pair unchecked:
  `evalChecked (2^53-1) [.nat (2^60)] [] (pair(var 0, 1)) = .ok (list [2^60, 1])`
  (finite, `verify-edges.lean`). The judgment is only as good as the checks where environment
  values are made. Some naturals are made outside terms: `clockNow` is `Val.nat
  st.timers.now.toNat` (`Machine/Stores.lean:1956`, total in Lean), and host answers are admitted
  without a number check (above). Neither passes through `evalChecked` or through L1.
- **`Within` reads only the top of a value.** That is enough today. I read all 33 atoms
  (`Machine/Term.lean:365-412`). Every atom that makes a new natural (`succ`, `pred`, `add`,
  `mul`, `sub`, `div`, `mod`, `length`) returns it at the top. Every atom that returns a pair,
  list or option only rearranges existing values. A future atom that builds a natural inside a
  list would slip past it.

### 4. Where the check goes, per target: partly (the theorems are proved; one conclusion is too broad)

I reran `Models.lean`: exit 0, output identical to `models.log`. Its 44 `#print axioms` lines match
the note's grouping: 6 use no axioms, 8 use `[propext]`, 30 use `[propext, Quot.sound]`.
`roundNat_safe_iff`, `jsAdd_checked`, `jsMul_checked`, `mlAddChecked_exact`, `mlAdd_under_check`,
`mlMul_under_check`, `evalIn_ok_iff`, `mlAdd_wraps` and `mlMul_saturates` say what the seat says.

Three corrections:

- **`mlAdd_postcheck_blind` is one instance, closed by `decide`.** The general statement ("the
  wrapped sum passes every bound") follows from `mlAdd_wraps`: an overflowing sum is negative.
- **"A check after the operation is blind on OCaml" is true only of the check `s <= bound` on
  `+`.** I proved two exact checks made after the operation:
  - `mlAdd_signcheck_exact`: with the sign tested (`0 <= s && s <= B`), a check after the wrapping
    `+` decides `a + b <= B` exactly, for every `B <= max_int` and operands `<= B`.
  - `mlMul_postcheck_exact`: a plain check after the saturating `*` decides `a * b <= B` exactly
    for every `B < max_int`, for any natural operands. At `B = max_int` itself it is blind
    (`mlMul_postcheck_blind_at_maxInt`).

  Both are in `verify-edges.lean`, within `[propext, Quot.sound]`. So F7's "the check must come
  before the operation" holds for a check written on Lean's `Nat`: there a sign test does not
  exist, which is the translator route and L1. It does not hold for a hand-written OCaml table
  row (N1).
- **`evalIn` is not a checker on its own.** With one input already above the bound, its pre-check
  passes and the result is above the bound: `evalIn 10 .add [.nat 0, .nat 11] = .ok (.nat 11)`
  (`evalIn_add_passes_outside`, `rfl`, `[propext]`). `evalIn_ok_iff`'s hypothesis on the inputs is
  load-bearing. The seat states the hypothesis, but the proposal presents `evalIn` as "the
  implementation form" without saying it needs the environment invariant from item 3.

### 5. The simulation inside the profile: confirmed (proved)

`Face.sim`, `atom_sim`, `ocaml_agrees`, `typescript_agrees` (it has the one hypothesis `hdiv`),
`typescriptExactDiv_agrees`, `exact_eval_toVal`, `ocaml_matches_machine` and
`typescriptExactDiv_matches_machine` compile. They are not vacuous: `Agrees` and `InProfileM` are
satisfiable, and `exact.run` meets them. As the seat says, they are about the Lean models of the
two targets. The tie to the real engines is the test in item 6.

`typescript_agrees`'s hypothesis is now discharged. `verify-div.lean` proves
`hdiv : ∀ a b, a ≤ 2 ^ 53 - 1 → b ≤ 2 ^ 53 - 1 → jsDiv a b = a / b`, the exact type of the
hypothesis, over `floorRoundDiv` and `jsDiv` restated byte for byte (I compared the definition
text). It holds for every divisor, not only safe ones: `jsDiv_exact` needs only
`a ≤ 2^53 - 1`. So `typescript_agrees hdiv : Agrees typescript (2^53 - 1)` holds with no
assumption. The files cannot import each other, so this link is made by matching the types, not
by the compiler.

One small scope point. `ocaml.lit` clamps literals at or above 2^62 to `max_int`, as the
translator's row does for Lean source literals (`Translate.lean:724`). A *program* literal at 2^62
is instead refused by the decoder (item 8). Inside the bound this makes no difference.

### 6. The models match the engines: partly (reproduced, but sampled, and one input differs)

I reran both checks:

- TypeScript: `ts/model-check.ts` finds 0 of 20,000 differ, and its red control 787 of 4,000.
- OCaml: I compiled a copy of `ocaml/model_check.ml` against the built engine. It finds 0 of
  30,000 differ, and its red control 1,000 of 1,000 sums and 460 of 1,000 products.

The seat's red controls exercise less of each checker than the note implies:

- The TypeScript red control has only `round` lines. It shows nothing about the checker's `add`,
  `mul`, `sub` and `div` branches.
- The OCaml red control has only `add`, `mul` and `sub`, and its `sub` lines cannot differ,
  because the exact truncated subtraction equals `max 0 (a - b)` on nonnegative operands.

So I added red controls for the uncovered branches (scratch files, the seat's checkers unchanged):

| added red control | result |
| --- | --- |
| TS: the same 16,000 `add`/`mul`/`sub`/`div` lines with the exact answer in place of the model's | 2,048 / 2,891 / 994 / 183 differ |
| OCaml: floor division and floor remainder in place of truncation, and the negated comparison | `div` 4,695, `mod` 4,708, `lt` 5,000 of 5,000 each differ |

The checkers are live on every branch. I also counted rounding ties in the TS vectors (68 `round`,
80 `add`, 57 `mul`, 35 `sub`), so the ties-to-even branch of `roundNat` is exercised.

**Counterexample to "the model matches the engine on all 63-bit ints".** At `min_int / -1` the OCaml
model answers 2^62, which is not an OCaml int. The engine's `program_native_atom_eval` answers
`min_int`. OCaml's division wraps there, and `Int.tdiv` does not.

- The line `div -4611686018427387904 -1 4611686018427387904` comes from `verify-edges.lean`
  (finite: `mlDiv (-2^62) (-1) = 2^62`).
- Run through the seat's own `model_check` driver, it prints
  `div 2 lines, 1 differ ... ocaml=-4611686018427387904`.
- The other five edge lines agree: `mod`, both `mul` orders, `add` at `max_int + 1`, and
  `div max_int (-1)`.

This input is reachable only after a wrap, so no in-profile theorem is affected. But it shows the
match is a sampled test, not an exhaustive one. A second stated limit, from the model's own
docstring: `roundNat` never overflows. JavaScript's `2^600 * 2^600` is `Infinity`, while the model
gives a finite number.

### 7. The LCNF translator: confirmed (reproduced)

I reran `Lower.lean`: output identical to `lower.log`. The translator's OCaml has the shapes the seat
describes:

- the post-check: `let s = a + b in ... s <= bound`;
- the pre-check: `max 0 (bound - b)`, then `a <= _x_1`, then `a + b`;
- `pre_mul`: guarded by `b = 0`, then `bound / b`.

I compiled a copy of `ocaml/lower.ml` and ran it. The output is identical to `ocaml/lower.log`
(post `Some -4611686018427387899`, pre `None`, `pre_mul` refuses (2^53 + 1) * 512 and computes 2^61).

### 8. Literal channels: confirmed (finite and reproduced)

- `bigLiteral` checks, runs, prints `Effect.succeed(9007199254740995)` and reads back (`Faces.lean`
  guards).
- JavaScript reads that literal as ...996 (reproduced).
- `truncOf (2^53 + 3) = 2^53 + 2` (the `Models.lean` guard) is the JSON datum ...994.
- The literal62 bytes end `08 40 00 ...`. `eff_frame.ml:199-214` `decode_nat` returns `None` for 8
  bytes with a top byte `>= 0x40`, so the refusal carries no location, as claimed. Both instances
  print `decode refused` (reproduced).

### 9. Engine refusal plumbing: partly (reading)

`E4_engine.step` does catch `E4_clock.Profile_refusal`, keep the input machine, and answer
`Outside_profile` (`e4_engine.ml:332-341`, `:629-638`; `e4_engine.mli:21-25`). `drive`, `replay_to` and `replay_positions`
all go through `step`, so the refusal is caught on those paths.

It is not caught everywhere. `api_run` (`e4_engine.ml:681-683`) calls the generated
`Effect4.Api.run` through `Api_engine_inst.run_api`, and generated code has no handler. The engine's
own EN1 check compares `run` with `api_run` on the corpus (`e4_engine.mli:37-40`), and the seat's
own faces driver calls it too.

So with a raising `Nat.add` (N1), the faces fixture would answer `Outside_profile` through `drive`
but escape as an OCaml exception through `api_run`. "Would be caught with no engine change" (note F5)
holds for the drive path only. The exact clock has the same gap today: `test_engine.ml:644-667`
exercises the refusal through `step`/`replay_to`, not `api_run`.

### 10. The clock carrier's cost: confirmed (reading)

`wc -l` gives 143 + 42 + 450 + 42 = 677 lines. `ClockFlow.lean` is a mono-LCNF dependency analysis
for the clock boundary (its header).

### 11. Stale documentation: confirmed (reading)

The seat's reading of `e4_nat.mli` is right:

- N2 says division by zero is unguarded; it is guarded at `Translate.lean:170-171`.
- D3 says `*` wraps; it saturates.
- The citations `Translate.lean:120-174`, `:127-137`, `:429`, `:148`, `:166` are dead: the rows
  are now at `:155-198`, `:141-151` and `:724`.

Also confirmed:

- `E4_nat.div` and `E4_nat.rem` are the only `E4_nat` calls in `api_engine.ml`, one each, at
  `:3434` and `:3453`.
- `ocaml/gen/NOTES.md:223-255` says what the seat quotes (the length argument at `:246-249`, the
  gap row at `:255`).
- The `Json.ofNat` docstring claims the host's parse, but the function truncates. The lines are
  at `JsonNumber.lean:45-46` and `binary64OfNat` at `:34-43`; the seat's `:37-41` and `:37-44`
  are off by a few lines. The module header (`:16-19`) already says it truncates.
- `Schema.encode` (`Codec.lean:228-236`) admits only values that decode back exactly.

### 12. The prelude's division: confirmed (reproduced)

The seat's counts reproduce: 1,016,384 safe pairs with 0 differences for `div` and `mod`, 163 of
100,000 above 2^53, and 183 of 4,000 model vectors. The DI-56 pair reproduces too. (The probe
writes `succ`, `eq` and `lt` inline as `M + 1`, `===` and `<`. That is the same arithmetic as the
prelude's.)

F8's argument is right, and it is now proved on the seat's model (`verify-div.lean`).

- `core` is the heart. Scale by `P = 2^k`, round half to even, divide by `P` again: the result
  is `a / b` whenever `b * 2^52 <= a * P` and `a < 2^53`. A round up can move the final quotient
  only when the scaled quotient sits one below a multiple of `P`. The algebra then forces
  `b >= 2P`, and so `a >= 2^53`.
- `chooseE_le` and `chooseE_atLeast` show the model's exponent is at most 52 and satisfies
  `core`'s bound. They use `Nat.log2_self_le` and `Nat.log2_lt`.
- `jsDiv_exact` puts the pieces together.

This answers the seat's open question 6: the lemma is proved, so switching the prelude to
`(a - a % b) / b` is not needed for the proof. It would still remove the need to trust
`floorRoundDiv` as a model of `Math.floor(a / b)`, which is tested, not proved.

### 13. FloatLib: confirmed (reading, WebFetch), two small corrections

Checked against the arXiv abstract and HTML (2609.19352v1) and the repository's raw files:

- title, authors and date (2026-09-16) are right;
- `ExecFloat.Backend.Certified` has `spec`, `estimate`, `run`, `run_eq_spec` (§3.1);
- "Backend refinement" is the paper's phrase, and "execution preservation" does not appear;
- Theorem 4 (jamming, §3.3) and Theorem 5 (the quotient check, §3.4);
- 102,454,320 TestFloat evaluations under the stated relation; the adapter calls
  `Model.*WithStatus`, not every timed backend;
- the trust boundary (§3.7);
- `lean-toolchain` v4.34.0;
- Mathlib v4.34.0 at `5ed2965`, with plausible, LeanSearchClient, importGraph, proofwidgets,
  aesop, Qq, batteries and Cli (`v4.34.0`), all inherited;
- MIT, v0.1.0, `fixedToolchain`, `public import`.

This repository is on v4.33.1 without Mathlib (`lean-toolchain`, `lake-manifest.json`).

The corrections:

- The paper's planner regimes are tables (4-8 bits), word kernels (16-64), a fixed-limb kernel
  (128) and an exact baseline (256-4096). The note says "limb kernels above" and "32-bit limb
  kernels".
- Per the `Kernels.lean` doc block, `roundQuotientEven` routes natively only for a numerator below
  2^63; the note says below 2^64 for all three.

### 14. rc.112 float dependence: confirmed (reading)

Every citation was read at the cited lines:

- Duration: `:38-41`, `:110-114`, `:402-420`, `:788`, `sum` `:1920` (the millis branch is
  `make(self + that)`), `divide` (`make(millis / by)`);
- `internal/effect.ts:6037-6066` and `:6078`;
- Schedule: `:1090-1098`, `:1122-1134`, `:1441-1448`;
- Random: `:79`, `:177-184`, `:210`, `:251`;
- Number: `:88`, `:153`, `:279`, `:1209-1275`, `:1383-1426`;
- this repository: `Ty.lean:229-231`, `Native.lean:214-215`, `Stores.lean:1956`.

### 15. Cost of one addition: confirmed (reproduced, one machine)

I compiled a copy of `ocaml/bench_add.ml` and ran it on an Apple M3 (arm64). Nanoseconds per
addition, median of 5:

| loop | masked | add only |
| --- | --- | --- |
| raw | 0.80 | 0.27 |
| checked | 1.06 | 1.06 |
| Zarith | 1.59 | 1.07 |

These are within 2% of the seat's numbers. A measurement, not a gate.

## What the seat missed

1. **The promised relation does not hold for the recommended plan.** §7 promises "the same refusal
   point on out-of-profile runs". But T1 refuses at 2^53 - 1 and N1 (as written, with the fixture
   "expected `Outside_profile` at the fourth binding") at 2^62 - 1. The seat's own `verdicts`
   guards show the faces program refused at binding 0 by one and binding 3 by the other.

   Open question 3 recommends the bound as data (`ProfileData.natBound`). A table row in
   `Translate.builtin?` is a fixed OCaml expression. It can carry a run-time bound only through a
   new global the engine sets at load, and that global would then govern every `Nat.add` in the
   engine (fuel, counters, names: the 36 raw `+` lines), or else through L1. So N1 and Q3 need to
   be decided together.
2. **T1's refusal has no location, and it surfaces in two different ways.** I ran a scratch bun
   probe with a prelude `add` that throws on an unsafe result:
   - In the first binding, it throws while the program value is built, because
     `Effect.succeed(add(...))` evaluates its argument eagerly. This is before `runSyncExit`.
   - In a later binding, it becomes a defect (`Cause.hasDies` true, `hasFails` false).

   DI-56 itself notes that a thrown exception inside Effect is a defect. So T1 needs the harness to
   classify both forms and to recover a position. This is more than "one comparator branch", and
   the refusal is not located the way `evalChecked`'s is.
3. **A printer refusal is static; the judgment is dynamic.** T1's printer refuses a literal above
   the bound anywhere in the program. `evalChecked` refuses only literals the run evaluates. A
   literal in a branch that never runs gives different refusal points on the two sides.
4. **`api_run` would not catch N1's exception** (item 9).
5. **L1 covers terms only.** `clockNow` (`Stores.lean:1956`) and host answers (`Admit.lean`) make
   naturals outside term evaluation. The OCaml clock already refuses at 2^53 - 1
   (`e4_clock.ml:38-42`), while program arithmetic is unchecked today. So the engine already mixes
   two bounds, and N1 at `max_int` would keep a mix.
6. **N1's raising `Nat.pow` and `Nat.shiftLeft` conflict with the reason those rows saturate.** The
   clamps exist so that `Val.wf`'s `… < 2 ^ 64` means what it means in Lean
   (`Translate.lean:177-181`, `ocaml/gen/NOTES.md` §5, `e4_nat.mli` N1). No generated file has a
   power today (no `_pow_clamped` in `ocaml/`), so nothing breaks now. But if `Val.wf` ever enters
   a cut, a raising power, or a generation-time refusal of the folded `2 ^ 64` literal, would
   refuse every value.
7. **The OCaml model is wrong at `min_int / -1`**, and the red controls were narrower than they
   look (item 6).
8. **`evalIn` needs its inputs inside the bound** (item 4). As "the implementation form" it depends
   on the environment invariant, and that invariant is not established for machine-made naturals
   (item 3).
9. **A trap for landing L0 under the axiom gate.** A bare `omega` on an `↔` goal reaches
   `Classical.choice`. The first draft of `verify-edges.lean` hit this. `verify-omega.lean`
   isolates it: `iff_by_omega` gives `[propext, Classical.choice, Quot.sound]`; the same fact with
   the `↔` split by hand (`iff_split`) gives `[propext, Quot.sound]`. The seat's theorems avoided
   it, but anyone moving them into `src/` should split `↔` goals before `omega`.

## Reruns and commands

The lock is `serial.sh` (session scratchpad). Lean runs are
`serial.sh lake env lean -M6144 -DwarningAsError=true docs/research/2026-09-30-pass/numbers/<File>`.

| what | exit | result |
| --- | --- | --- |
| `Faces.lean` | 0 | identical to `faces.log` |
| `Checked.lean` | 0 | identical to `checked.log` (axioms as in item 3) |
| `Models.lean` | 0 | identical to `models.log`; rewrote the four vector files with identical bytes |
| `Lower.lean` | 0 | identical to `lower.log`; rewrote `ocaml/lower.ml` with identical bytes |
| `cd harness/truth && bun -e "$(cat …/ts/faces-run.ts)"` (bun 1.4.2) | 0 | identical to `ts/faces-run.log` |
| `bun -e "$(cat …/ts/model-check.ts)"`, then `VECTORS=<backup>/trunc-vectors.txt` | 0, 0 | 0 of 20,000; 787 of 4,000 |
| the same checker, `VECTORS=<scratch>/ts-exact-red.txt` (added red control) | 0 | 2,048 / 2,891 / 994 / 183 differ |
| driver compiles (copies of `faces.ml`, `model_check.ml`, `bench_add.ml`, `lower.ml` into the scratchpad), each `serial.sh bash -c 'cd ocaml && opam exec --switch=effect4 -- ocamlfind ocamlopt … <scratch>/<d>.ml -o <scratch>/<d>.exe'` with the seat's flags | 0, 0, 0, 0 | built against `ocaml/_build` (its `api_engine.ml` is byte-equal to `ocaml/engine/api_engine.ml`) |
| `serial.sh <scratch>/faces.exe <program hex>`, then `<literal62 hex>` | 0, 0 | item 1 row; `decode refused` twice |
| `serial.sh <scratch>/model_check.exe …/ocaml/ml-vectors.txt`, then `…/exact-vectors.txt` | 0, 0 | 0 of 30,000; 1,000 / 460 of 1,000 |
| `model_check.exe <scratch>/ml-red2.txt` (added red control) | 0 | `div` 4,695, `mod` 4,708, `lt` 5,000 of 5,000 differ |
| `model_check.exe <scratch>/edge-vectors.txt` (from `verify-edges.lean`) | 0 | 1 of 6 differ: `div min_int -1` |
| `serial.sh <scratch>/lower.exe` | 0 | identical to `ocaml/lower.log` |
| `serial.sh <scratch>/bench_add.exe` | 0 | item 15 |
| `verify-edges.lean` | 0 | first draft exit 1 (a `#guard` on `Except` equality, one wrong rewrite; two bare-`omega` `↔` proofs reached `Classical.choice`); fixed |
| `verify-div.lean` | 0 | first drafts exit 1 (`let` and `if` unfolding in `tail_eq` and `chooseE_*`); fixed; `core` compiled first time |
| `verify-omega.lean` | 0 | axioms below |
| `cd harness/truth && bun -e "$(cat <scratch>/t1-throw.ts)"` | 0 | first binding: thrown while building; later binding: a defect |

Axioms, `verify-edges.lean`:

- no axioms: `mlMul_postcheck_blind_at_maxInt`;
- `[propext]`: `evalIn_add_passes_outside`, `guardNat_nat`, `guardNat_ok`, `guardNat_refusal_at`,
  `evalChecked_sound`, `evalChecked_refusal_located`;
- `[propext, Quot.sound]`: `mlAdd_signcheck_exact`, `wrap_of_range`, `mlMul_exact`,
  `mlMul_saturates`, `mlMul_postcheck_exact`.

Axioms, `verify-div.lean`:

- no axioms: `atLeastB_iff`;
- `[propext, Quot.sound]`: `core`, `tail_eq`, `chooseE_le`, `chooseE_atLeast`, `atLeast_low`,
  `jsDiv_exact`, `hdiv`.

Its three `#guard`s pass: `jsDiv (2^53 - 1) 3` is exact, and `jsDiv (2^54 - 2) 3` is one above
the exact quotient, as the seat found.

Axioms, `verify-omega.lean`:

- `iff_by_omega`: `[propext, Classical.choice, Quot.sound]`. This is the trap it isolates; it is
  not a claim of this note.
- `iff_split`, `atomic_by_omega`: `[propext, Quot.sound]`.

The definitions in `verify-edges.lean` and `verify-div.lean` are restated from the seat's
`Models.lean` and `Checked.lean`, because those files are not modules and cannot be imported. I
compared them definition by definition with a script: all are identical, except that the seat's
`Refusal` and `AtomRefusal` have docstrings on their constructors.

Web reads (WebFetch, read only):

- `arxiv.org/abs/2609.19352` and `arxiv.org/html/2609.19352v1` (twice);
- raw GitHub `lean-dojo/FloatLib`: `lakefile.lean`, `lake-manifest.json`, `lean-toolchain`,
  `FloatLib/Kernels.lean`, `FloatLib/Floats/THEOREMS.md` (it does list
  `ExecFloat.Binary.toModel_ofFloat_ofNat`).

Not checked: the note's performance comparisons beyond the abstract ("slower binary32 than MPFR
and SoftFloat", "agrees with MPFR and FLoPS").
