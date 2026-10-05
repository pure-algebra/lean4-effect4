# 2026-10-05 seat LOWER receipt: four follow-ups of the OCaml route

**The one thing to know before merging:** slice 4 landed the theorem, not a planned goal, and not
in the file the brief named. `Conform.Lcnf.Target.let_return_outcome`
(`tools/Conform/Lcnf/TargetLaws.lean`) is kernel-checked. Its axiom list is
`[propext, Classical.choice, Quot.sound]`, so it is outside the trust ceiling.

The cause is in the evaluator, not in the proof. `Target.evalT`
(`tools/Conform/Lcnf/SemanticsTarget.lean`) reaches `Classical.choice` by its own definition.
Two rules of `Target.applyPrim` traverse a `String`: `String.length` in the rule
`lcnf_utf8_length`, and the order of two strings in `cmp?`. Every statement about the evaluator
inherits that axiom, as a theorem or as a `proof_goal`. The axiom gate would refuse either one
as a declaration of a `Test.*` module. So `Test/Audit/LetReturn.lean` declares nothing (0
constants, tested). It pins the statement and the axiom lists, and it holds the finite control.

Two more points. The default `lake build` and the gates of `Test/All.lean` ran at the tree of
slice 1 only. Slices 2 to 4 have their narrow builds, as the coordinator's message of 2026-10-05
asked.

## Base and head

Branch `seat/lower`. Base `2ba1775c`. The head is the commit of this receipt.

| Slice | Commit |
| --- | --- |
| 1. The conformance runner | `e9e310c5` |
| 2. Callback functions in the target evaluator | `ab90dffc` |
| 3. `E4_be` forwards to `Eff_frame` | `c17e5ee7` |
| 4. The law of `let x = e in x` | `c2782956` |

## Changed files

| File | Change |
| --- | --- |
| `scripts/lib/conform_report.py` | `fresh_run` takes declared roles; `retain_attempt`; `validate` takes `expected_tool` |
| `scripts/check-conform.py` | profiles with roles; `selection.json` as the request; `processes.json`; `MUTATIONS` by fixture name |
| `scripts/test-conform-runner.py` | new: Codex's controls as 61 tests |
| `tools/Conform/Effect4/Normalization.lean` | stable fixture names; the selection; the builtin controls on the evaluator |
| `tools/Conform/Effect4/CompilerControls.lean` | `Expect`, `onTarget`, six new host checks, the callback and label controls |
| `tools/Conform/Lcnf/SemanticsTarget.lean` | `primT`, `scanT`, `scanStop?`, `Option.value~default`, `TExpect`, `judgeT`; the header corrected |
| `tools/Conform/Effect4/LcnfMl.lean` | the reader admits `Option.value o ~default:d`; `expected := .value …` |
| `src/OCaml5/Lcnf/Builtins.lean` | five rows name their new controls; no form, class or domain changed |
| `ocaml/engine/e4_be.ml`, `ocaml/engine/e4_be.mli` | each operation forwards to `Eff_frame`; `D1` corrected; `B7` added |
| `ocaml/engine/test/test_math.ml` | the old transcription as the reference `Transcribed`; 14 new checks |
| `tools/Conform/Lcnf/TargetLaws.lean` | new: the law, its three steps and its red control |
| `Test/Audit/LetReturn.lean`, `Test/All.lean` | new battery; one import after `Test.Audit.ClockLowering` |
| `tools/Conform/README.md`, `docs/core/lcnf-route.md` | the runner's roles, attempts and selection; §9 of the route |

## Commands and results

Every Lean command ran through `scratch/lean-slot.sh`. The logs are in the scratch folder
`scratchpad/lower/`.

| Slice | Command | Result |
| --- | --- | --- |
| base | `python3 scripts/check-conform.py compiler` | PASS: 123 observations, two mutations |
| 1 | `python3 scripts/test-conform-runner.py` | 60 tests, OK |
| 1 | `lake build Conform` | passed |
| 1 | `python3 scripts/check-conform.py compiler` | PASS: 123 observations, 2 mutations |
| 1 | the same with `OCAMLOPT=/usr/bin/false` | INVALID, exit 2; the attempt kept; the earlier receipt byte-identical |
| 1 | `make check-cases check-native` | PASS, PASS; it also ran the default `lake build` (907 jobs, passed) |
| 1 | `make check-docs check-language` | PASS, PASS |
| 2 | `lake build Conform OCaml5`; `lake build Test.Audit.ClockLowering` | passed; passed |
| 2 | `python3 scripts/check-conform.py compiler` | PASS: 129 observations, 3 mutations |
| 2 | the vector lane of `LcnfMl`, through a scratch driver | 20387 cases, all pass |
| 2 | `python3 scripts/generate.py --only lcnf`, then `git status` | PASS; no file changed |
| 2 | `python3 scripts/test-conform-runner.py` | 61 tests, OK |
| 2 | `make -o build check-cases check-native` | PASS, PASS |
| 2 | `make check-docs check-language` | PASS, PASS |
| 3 | `make -o build -o ts/eff/node_modules corpus` | 408 programs; `generated/corpus-index.tsv` unchanged |
| 3 | `dune build`; `dune test --force eff engine` | exit 0; exit 0, every test program `ALL PASS` |
| 3 | `git status` after the tests | the three files of the slice only: no golden changed |
| 4 | `lake build Conform OCaml5 Test.Audit.LetReturn` | passed (260 jobs) |

The gate lines of `Test/All.lean`, at the tree of slice 1:

```text
Effect4 library-root gate: 163 API/utility modules, 275 Laws-only modules; every library source is reachable; Effect4 never reaches Laws
Effect4 module and axiom gate: checked 665 modules and 81910 declarations; phases (ms): sources and closure 25, library roots 235, declarations 3566, resolution 1362, axioms 22539, exemptions 497; semantic/test axioms are [propext, Quot.sound]; exact implementation boundary (17 module(s), 23 declaration(s)) additionally allows Classical.choice
Effect4 goal gate: 13 planned goal(s), each a theorem whose body is `sorry` outside the Effect4 root; 7 declaration(s) rest on goals; no other declaration reaches sorryAx
```

Not run, as the coordinator's message asked:

- the default `lake build` and the gates of `Test/All.lean` on the trees of slices 2 to 4;
- `make check-cases` and `make check-native` after slice 2;
- a second `python3 scripts/generate.py --only lcnf`;
- `make check-docs` and `make check-language` after slices 3 and 4;
- `dune test --force gen clock`;
- `python3 scripts/check-conform.py compiler` after slice 4.

## Axiom output

`#guard_msgs` pins these four lines in `Test/Audit/LetReturn.lean`:

```text
'Conform.Lcnf.Target.evalT' depends on axioms: [propext, Classical.choice, Quot.sound]
'Conform.Lcnf.Target.let_return_outcome' depends on axioms: [propext, Classical.choice, Quot.sound]
'Conform.Lcnf.Target.let_return_same_fuel_refuted' depends on axioms: [propext, Classical.choice, Quot.sound]
'Conform.Lcnf.Target.TEnv.find?_head' does not depend on any axioms
```

The law's list is the evaluator's own: the proof adds no axiom. A scratch probe measured the
source. `String.length` and `<` on two strings reach `Classical.choice`. The byte size, the
UTF-8 bytes, `==` on strings, `++`, the map lookup and the integer rules do not.

## Evidence

- The law and its red control: kernel-checked, outside the trust ceiling. Not proved in the
  dictionary's sense.
- The finite control of the law: tested. `mulCap` runs with the `let` and without it at related
  fuels, under three binder names, on fuels 0 to 15. Two altered copies go red.
- The runner: tested, 61 controls with no Lean and no compiler. A scratch script put each
  repaired fault back, and each time named tests went red.
- A refused run keeps its evidence: tested, one host run with a compiler that fails.
- The evaluator's callback rules: tested, finite. `#guard`s on the evaluator, 16 builtin controls
  on the evaluator and in compiled OCaml 5.1.1. The 20387 vector cases all pass on the changed
  evaluator. I did not run them at the base.
- `E4_be`: tested, finite. Each forward equals the old transcription on edge and random inputs.
  `nat_of_digits` equals it on all 65793 digit strings of at most two bytes.
- Host-only: every compiled OCaml result is of one machine, macOS, OCaml 5.1.1, Lean 4.33.1.

## Landed theorems and their placement

`let_return_outcome` (`tools/Conform/Lcnf/TargetLaws.lean`):

- Concept: `translation-simulation`; property: an equal-observation law of one local rewrite of
  the LCNF route.
- Question: the proposed registry claim `ocaml-let-return-outcome` (role simulation); consumer:
  the identity-continuation case of `OCaml5.Lcnf.code` (`src/OCaml5/Lcnf/Translate.lean`).
- Reach: every outcome of `Target.evalT`, under the fuels `n + 2` and `n + 1`, for every
  program, environment, name and expression. `x` may be bound before or not. Row 28 is open.
- Does not establish: the emitted bytes, the cost, any other rule of the translation, or the
  agreement of the evaluator with compiled OCaml. The same-fuel statement is false.
- Unlocks: R8, its open part on the typed lowering of the LCNF route.

Its steps are `TEnv.find?_head`, `evalT_letIn` and `evalT_var_bound`, in the same file.

The proposed registry claim, for the coordinator to place:

```lean
{ id := "ocaml-let-return-outcome", concept := "translation-simulation", role := .simulation
  title := "The target evaluator gives `let x = e in x` at fuel n + 2 the outcome of `e` at fuel n + 1"
  pointer := .witness `Conform.Lcnf.Target.let_return_outcome }
```

Two cautions. The registry's roots do not load `Conform.Lcnf.TargetLaws` today. The plan would
derive the status proved from a theorem whose axiom list is outside the ceiling. Until the
evaluator is under the ceiling, a pointer `.absent` with that reason is the safer form.

## Choices, and where I left Codex's advice

- **The law's place.** Codex and the brief put it in a `Test` fixture. The gate forbids that
  for any statement about `Target.evalT`. I put the constant in the tool library.
- **Identities.** A fixture's row is `fixture:[name]` in all three lanes. The two mutations of
  compiled OCaml are rows of kind `mutation`, check `normalization.ocaml.control`.
- **The selection.** The Lean driver writes `selection.json` before it evaluates. Codex asked for
  one named selection and no second hand list. The closure report gets its roots checked, not
  its identities: a walk finds its declarations.
- **Attempts.** The runner keeps the latest refused run of a profile, not every one. Disk is
  tight, and a failed compiler run holds compiled programs.
- **`processes.json`.** A new artifact of the compiler profile: each process with its command and
  full result. Codex's runner review, §5, asked for the exact commands.
- **A third mutation.** `contains-mutation` swaps the instance's two arguments in the emitted
  prelude. It must fail `contains-order` in compiled OCaml.
- **Controls in the table.** Five rows of `builtins` name their new controls. The brief excludes
  a row's meaning and class. This changes neither.
- **`nat_of_digits`.** It frames the digits and reads them with `Eff_frame.decode_nat`. One
  implementation holds the digit rule. The cost is one small copy, not measured.
- **Not taken from Codex.** No structured refusal reasons: no new case needed them. No requested
  digests for the `cases` profile: it has no fixture selection.

## Open obligations

1. **The owner's decision on the evaluator and the ceiling.** Three options:
   - keep the law in tooling, as landed;
   - rewrite the two `String` rules in their byte forms, then move the law into a battery as a
     declaration with `@[semantics "translation-simulation" (requirement := R8)]`;
   - exempt the law by its exact name in the gate.

   I recommend the second, as its own slice. The byte forms are the target's own meaning: the
   emitted helper counts the bytes that are not continuation bytes, and OCaml orders strings by
   bytes. No control reaches `cmp?` on strings today, so that slice needs one.
2. Seven callback names of the builtin table have no rule in the evaluator. A call is a refusal.
3. Nothing runs the runner's tests or the compiler profile but a person. The owner retired the
   script-test lanes, so I added no target.
4. The label of the compiler step in `.github/workflows/lean_action_ci.yml` says one mutation.
   There are three.
5. The header of `tools/Conform/Effect4/LcnfMl.lean` names a `--run` command that finds no
   `main`: it is inside the namespace. A three-line scratch driver ran the vector lane.
6. `make check-cases` runs the default `lake build` first, through the rule of `$(CORE)`. In
   this worktree that build compiled 435 modules: 203 of `Effect4.Laws`, the others batteries.
   The `make` run took 22 minutes 41 seconds. The cache held the core, not the Laws or the
   batteries. `make -o build` avoids the build.

## Proposed decisions rows (proposals only)

1. The target evaluator comes under the trust ceiling: the two `String` rules of `applyPrim` in
   byte form, with a control for the order of strings. A lowering law is then a declaration of
   a battery. Owner: the owner.
2. `python3 scripts/test-conform-runner.py` and the `compiler` profile join one lane that runs
   without a person. Owner: the owner.
3. The registry claim `ocaml-let-return-outcome`, in the form the first row decides.
