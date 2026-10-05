# 2026-10-05 the builtin table as data: a capture fault, its repair, and what checks it

Status: research note (history, not authority). Base: `182312f3` (`refactor/phase1-phase3`).
The change it describes is in the same commit. The authority text is `docs/core/lcnf-route.md`
§9.

**The one thing to know first.** The LCNF route to OCaml gave wrong answers for a Lean binder
named `_mula`, `_shift_scale` or `_b1`. No generated module held such a binder. The owner asked
for the robust repair on 2026-10-05: the builtin table as data. The table is data now. A builtin
form binds no name at a call site. The name supply reserves every name that a form uses. A
check reads each translated declaration. The numbers did not move.

## Question

Codex's scout of the OCaml route reported that three builtin forms bind fixed names outside
the name supply. Is that a fault of a real Lean source? What is the repair that removes the cause?

## What was read or run

| Item | How |
| --- | --- |
| `src/OCaml5/Lcnf/Translate.lean`, `Naming.lean`, `Externs.lean`, `Clock.lean`, `Native.lean` | read |
| `src/OCaml5/Ml/Check.lean`, `src/OCaml5/Tools/LcnfGen.lean`, `tools/Conform/Effect4/*`, `tools/Conform/Lcnf/SemanticsTarget.lean` | read |
| Codex's three packets (`docs/research/2026-10-05-codex-foundation-packet/implementation-audit/ocaml-lowering-scout/`, `builtin-table-review/`, `conformance-api-review/`) | read; each source claim checked in the tree |
| `before/CaptureProbe.lean`, at `182312f3` | run: Lean 4.33.1, the tree's translator and target evaluator |
| `before/capture_probe.ml`, the OCaml that probe emitted | run: OCaml 5.1.1 of the `effect4` switch |
| The compiler checkpoint at `182312f3` (`before/compiler-checkpoint-at-182312f3.log`) | run: red before this change |
| `python3 scripts/generate.py --only lcnf`, `dune build`, `dune test --force eff gen clock`, `dune test --force engine` | run after the change (`after/`) |
| `python3 scripts/check-conform.py compiler` | run after the change: PASS |

## Findings

### F1. The fault is real for a Lean source

Three definitions, each with one binder named as a form's own temporary
(`before/CaptureProbe.lean`). Their mono LCNF keeps the binder's name.

| Definition | Lean | The translator's target evaluator | Compiled OCaml 5.1.1 |
| --- | --- | --- | --- |
| `mulCap (x _mula) := x * _mula` at 3, 5 | 15 | 9 | 9 |
| `shiftCap (_shift_scale b) := _shift_scale <<< b` at 3, 2 | 12 | 16 | 16 |
| `addCap (_b1 y) := applyTo (Nat.add _b1) y` at 3, 5 | 8 | 10 | 10 |
| the same three with ordinary names | 15, 12, 8 | 15, 12, 8 | 15, 12, 8 |

The emitted OCaml type-checks. The product read `let _mula = x in let _mulb = _mula in …`
under the parameter `_mula`. `List.contains` has the same form, and the compiler inlines it
before mono, so no source reached it here.

Evidence: tested, three programs. Codex's scout predicted the three pairs from the source.

### F2. The fault had four parts, not one

| Part | Before | Reached by a source |
| --- | --- | --- |
| A form binds a fixed name at its call site (`_mula`, `_mulb`, `_shift_scale`, `_elem`, `_b1`…) | not reserved | yes (F1) |
| A form leaves a name free that no list reserved (`min`, `lcnf_utf8_bytes`, `lcnf_utf8_length`) | a hand list, `preUsed`, held some of them | by reading: a binder `min` of function type |
| A body calls a generated declaration, and a binder has that declaration's OCaml name | nothing | yes: `globalCap` in the fixtures |
| An extern row is under-applied with the binders `_ex1`… | not reserved | by reading |

The four generated modules held none of the four on 2026-10-05 (measured: `hygieneProblems`
answers no problem for each, `after/generation.txt`).

### F3. The repair: a row is data, and it denotes a closed function

`builtins` in `src/OCaml5/Lcnf/Builtins.lean` has 106 rows. A row holds the Lean constant, its
form and its contract.

- **Three forms.** An inline body that binds nothing, a support function of the prelude, or a
  function of the target's library. A form that binds a name or calls itself is a support
  function: `lcnf_nat_mul`, `lcnf_nat_pow`, `lcnf_nat_shift_left`, `lcnf_list_contains`.
- **No binder at a call site.** A builtin application adds a binder only by eta-expansion. The
  eta binders are computed from the table's largest arity and reserved.
- **Computed, not listed.** The lookup, the prelude, the reserved names and the fidelity
  inventory are computed from the rows. `preUsed` and the copied fidelity table are deleted.
- **A contract on every row.** Its fields have no default. Thirteen rows had no fidelity entry
  before: nine of the exact clock and four of `UInt64`. Each has one now.

Each support body is the form the route had, with parameters for its operands. The generated
text changed at two call sites and in the prelude (`git diff --stat`: 56 lines added, 12
removed, four files).

### F4. Names: construction first, then a check that does not trust it

1. `fresh` names every binder and never gives a reserved name.
2. `translateDecl` records each unqualified name a body leaves free. When a binder took one,
   the next pass reserves them all. The free names do not depend on a binder's spelling, so one
   more pass settles it.
3. `hygieneProblems` reads the translated declarations. It refuses a binder that hides another
   binder of its declaration, or that takes a recorded name. `LcnfGen` and the checkpoint stop
   on a refusal.

The check is per declaration. A binder may share a name with a declaration that its body does
not call. That keeps the accepted sources as they were.

One extern row names a binder of its only caller: `fn Effect4.Program.rootPoint 2
sh_root_point root`. Its literal is outside the check, as the row intends. A literal that names
a generated declaration is inside it.

### F5. Arguments: a value, or a place that is evaluated once

Codex's review corrected the first argument for inline forms. A body that binds nothing and
uses each parameter at most once is not enough. An unused parameter drops its argument. An arm
or a lazy operand defers it.

- An argument is a variable or a literal in every case but one: a carrier turned back into its
  list (`useAsList`).
- `Form.strict` holds when the body evaluates each parameter exactly once. The call of a
  support or library function is strict.
- `Translate.applyBuiltin` leaves a carrier conversion in place only in a strict form with all
  its arguments. Anywhere else it binds the conversion first, in Lean's argument order. An
  eta-expansion then closes over a value.

No generated module has a carrier conversion as a builtin's argument today, so this path
changed no text. The evidence is a reading of the 27 `to_list` lines of `api_engine.ml`, and
the regenerated text itself.

### F6. The checkpoint runs the support bodies, and it was red before

- The target program is assembled as the emitted module is: `supportBinds`, then the
  declarations (`Conform.Effect4.LcnfMl.assemble`). Each support body is read from the
  definition that the prelude emits. `max_int` is a binding of the program.
- A wrong body is what runs. `lcnf_nat_mul` altered to `a * a` answers 9 for 3 and 5 on the
  evaluator. In compiled OCaml it fails the fixture `names/mulCap`, and every earlier
  observation still passes.
- A missing definition, a body outside the reader's fragment and a primitive's name are
  refusals with their reason.
- **The checkpoint was red at `182312f3`.** Its source interpreter had no rule for five
  constants that its closure reaches: `Nat.sub`, `Array.uget`, `USize.ofNat`, `USize.decEq` and
  `USize.sub`. Four merge cases were refused, and the compiled lane did not run. The last
  receipt before this change is of 2026-09-13 (`.lake/conform/compiler.json`). The five source rules are added, with one new rule
  (`uintSub`). The profile passes: 123 observations of compiled OCaml and two mutations.
- The two mutations now name the observation that must fail, and require the expected output
  before it. Before, any line ending in `FAIL` satisfied the control.

### F7. Three changes of content, each small

| Change | Reason |
| --- | --- |
| `Array.push` and `Array.size` move from `approximate` to `exact`, and gain a `cost` | Their notes said "denotationally exact"; the class held a cost. Codex asked for cost apart from meaning |
| The note of `Nat.mul` says "saturating" | The copied table said "as `Nat.add`", which wraps. The form saturated since the clamp of the product |
| The fidelity inventory spells a form from the form | The copied spellings had drifted (`_lean_utf8_length`, `_pow_clamped`) |

## What the change is, by file

| File | Change |
| --- | --- |
| `src/OCaml5/Lcnf/Builtins.lean` | New: the table, the forms, the support functions, the library list, `problemsOf` and its controls |
| `src/OCaml5/Lcnf/Translate.lean` | The old table removed; `reservedFor`, `noteFree`, `applyBuiltin`, the second naming pass, `hygieneProblems`; the prelude from the table |
| `src/OCaml5/Lcnf/Externs.lean`, `Clock.lean` | The extern eta binders by name; the clock's rows moved to the table |
| `src/OCaml5/Ml/Check.lean` | `shadowed-value`, off unless the environment asks; `shadowDiags` |
| `src/OCaml5/Tools/LcnfGen.lean` | The name check is fatal |
| `tools/Conform/Effect4/*` | The inventory from the table; `assemble`; the controls; the name fixtures; the support mutation |
| `tools/Conform/Lcnf/Semantics.lean`, `Effect4/LcnfSemantics.lean` | Five source rules (F6) |
| `scripts/check-conform.py` | Mutations that name their failure; the support mutation |
| `ocaml/gen/*.ml`, `ocaml/engine/api_engine.ml` | Regenerated: the prelude, two call sites |

## Proposals (not rulings)

1. **Four obligations under `translation-simulation`, R8's typed-lowering open part** (Codex's
   table, `builtin-table-review/recommendations.md`). None is a goal yet.

   | Proposed claim | States | Leaves open |
   | --- | --- | --- |
   | `builtin-table-lookup` | the lookup agrees with the row list under unique normalized keys | a row's meaning |
   | `builtin-application-hygiene` | application adds no binder that changes an operand's value, under the reservation | host callbacks |
   | `builtin-support-agreement` | a support call has its row's target value on the row's domain, under related fuel | cost; the whole runtime |
   | `builtin-inline-agreement` | an inline form agrees with the function it denotes, for values and for strict places | cost |

2. **The evaluator gains callback library functions**, `List.exists` first, so that
   `lcnf_list_contains` runs on the evaluator too. With it: the labelled call of `Option.getD`,
   and an expected exception in a target case (Codex's conformance review, §4).
3. **Three runner repairs** (the same review, §2): `fresh_run` with two expected reports, the
   scratch files of a failed producer, and `actual.txt` on a mismatch.
4. **The scout's other slices**, each small and apart.
   - `E4_be` forwards to `Eff_frame`.
   - The law of `let x = e in x`, as a placed fixture.
   - The emitted OCaml text, read back by the compiler's own parser.
5. **Decisions row 108 stays apart.** The numeric policy becomes an edit of support bodies and
   of one row's form. This change made no such edit.

## What this does not establish

- No theorem relates a row to its Lean constant. A class is a reading, and a control is finite.
- `hygieneProblems` refuses a capture. It does not prove that every source translates.
- The evaluator refuses `lcnf_list_contains`: it has no rule for `List.exists`. Compiled OCaml
  runs that body, in one host check.
- A carrier's `to_list` is taken as total and pure. The observation excludes allocation and
  cost.
- The cost of the four support calls against the forms they replace is not measured. One
  product and one power are the only such calls in the four generated modules.
- The name fixtures are ten entries. They cover the four parts of F2 once each, not every
  form.
- `translateDecl` stops its passes at sixteen without a refusal of its own, as before (the
  scout's note). No source that needs more was found.
- The receipts are of one machine: macOS, Lean 4.33.1, OCaml 5.1.1.
