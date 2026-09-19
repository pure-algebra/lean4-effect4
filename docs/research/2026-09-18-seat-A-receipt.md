# Seat A — the atom table (tooling plan 2.1, 2.2, 2.5)

Branch `seat/A-atom-table`, worktree `.claude/worktrees/agent-ac6830377ceb57c9f`, cut from
`4b4e6aa3` on `refactor/phase1-phase3`. Nothing pushed, nothing rebased, working tree clean.

Evidence words are the project's: **proved** = a Lean theorem exists; **tested** = a check or
`#guard` exists; **stamped** = a generator wrote it and the drift check holds it; **measured** =
a number this seat read off a run; **assumed** = neither.

---

## 0. The one thing to know before merging

`scripts/generate.py --only lcnf` cannot be run at this commit, and that is not this slice's
doing. Regenerating `ocaml/engine/api_engine.ml` makes `dune build` fail:

    Ty_refOf / Ty_deferredOf / Ty_var / Ty_unknown … is not included in
    type ty = Ty_never | … | Ty_lit of string
    17.-20. An extra constructor … is provided in the first declaration.
    File "engine/e4_program_layout.ml", lines 3-18 — Expected declaration

`ocaml/engine/e4_program_layout.ml` declares `ty` with sixteen constructors; the source has
twenty since L5. The engine's own mirror **records** the divergence instead of refusing it —
`ocaml/engine/e4_program_layout.json` carries `{"family": "Effect4.Program.Ty", "reason":
"source-append-unavailable-in-frozen-engine", "engine": 16, "source": 20}` — which is exactly
the defect plan item 4.2 exists to fix, and why `make check-gen` (hermetic groups only) has
never caught it.

So the four LCNF outputs are left **exactly as committed**, the engine compiles as it did
(`cd ocaml && opam exec --switch=effect4 -- dune build`, exit 0, **measured** after restoring
them), and the atom changes below are not reflected in the engine face until someone unfreezes
that mirror. Second **measured** number from the attempt: the engine generator ran **14m38s**,
past `scripts/generate.py`'s own `timeout 600`, so `make gen-lcnf` cannot complete under the
current cap on this machine either.

Base-commit red, **answered**: `Test.All` fails at `4b4e6aa3` before any edit of mine, because
the `declare_aesop_rule_sets` initializer reaches `Classical.choice` (plan 1.1 predicted it).
I applied the one-entry fix to `auditImplementationModules`, then reverted it: the file is
outside my scope and the edit widens the axiom ceiling, which is not a seat's call. The
coordinator confirmed seat I lands it (`897e45b1`). Until the merge, `lake build Test` is red
for every seat; every individual `Test.*` module builds green.

---

## 1. Commits

| # | sha | what |
| --- | --- | --- |
| 1 | `ec3d572c` | `program`: the atom inventory generated, the table's structure decided (2.1) |
| 2 | `9f7e1a58` | `laws`: the `Effect4.Atoms` bank registered (2.2) |
| 3 | `4542ef63` | `machine`: the table's runtime half — one `AtomRow`, four matches become one (2.5) |
| 4 | `df0a5898` | `program`: the table's typing half — `Spec`/`Scheme`, soundness once per scheme (2.5) |
| 5 | `50aa8422` | `harness`: the prelude's atom block generated from the table (2.5, D-E) |

Each landed after a narrow `lake build` of the modules it changed; 1, 3 and 4 also after a
build of `Effect4 Effect4Laws Effect4Gen Tools OCaml5 Conform Test`, green but for the
`Test.All` entry above.

---

## 2. What landed

### 2.1 — `atom_table_wf`, and `NativeAtom.all` generated (`ec3d572c`)

**Generated.** Group `AtomInventory` (`tools/Effect4Gen/Atoms.lean`, manifest entry,
`tools/Effect4Gen/guards/atominventory.lean`) reads `NativeAtom`'s constructor list off the
environment — refusing a constructor with fields, or a name that is not a plain identifier —
and emits `src/Effect4/Program/AtomInventory.lean`: `all`, `names`, `covers`, with
`all_complete` and `covers_iff` appended verbatim as the acceptance guards, statements and
proofs unchanged. Twenty atoms, same order, so no face moved. **Stamped**: the whole `derived`
family re-ran through `python3 scripts/generate.py --only derived` and no other generated file
changed.

**Retired.** The hand-written `all`, and `ofName?`'s scan of it. `ofName?` is now a match on the
string — needed to put the generated inventory *above* the alphabet (`Term.lean` declares the
inductive, so it cannot import a module that lists it), and right anyway: `evalTerm` resolves an
atom at every term application, and OCaml compiles a string match to a decision tree where it
compiled the scan to twenty name computations and compares (`ocaml/gen/api_gen.ml:1477-1493`).
The second spelling of the name table is pinned both ways by `ofName?_name` and `ofName?_sound`,
each still one tactic line (`unfold ofName? at h; split at h <;> cases h <;> rfl`), all three
lookup lemmas **proved** at no axioms at all.

**Decided.** `atomWellFormed` + `theorem atom_table_wf : NativeAtom.all.all atomWellFormed =
true := by decide +kernel`.

**Measured `decide +kernel`: 0.647 s**, of which 0.646 s is `[Kernel] typechecking
declarations` (`lake env lean -D trace.profiler=true -D trace.profiler.threshold=5` over
`src/Effect4/Program/NativeAtom.lean`). So the per-atom `names.count` stayed and the plan's
`List.Nodup` fallback was not needed. After commit 4 restated the predicate over the scheme it
**fell to 0.118 s**, because a scheme answering at its own parameters is reflexivity where the
old clause ran the whole `typeOf` match. `atom_table_wf` is at `[propext, Quot.sound]`.

**Red control** (`Test/Program/AtomTable.lean`, imported by `Test.All`): at commit 1 a fixture
alphabet repeating the four clauses over its own columns; at commit 4 rebuilt so it calls the
**shipped** predicate. See 2.5 below.

### 2.2 — the `Effect4.Atoms` bank (`9f7e1a58`)

`src/Effect4/Laws/Program/AtomRules.lean` registers `Fits.singleton_inv`, `Fits.pair_inv`,
`Val.hasTy_nat_inv`, `_bool_inv`, `_string_inv` as `safe destruct` and `Fits.all_sub_string` as
`safe forward`, in `Effect4.Atoms`. `destruct` for the five because each consumes the hypothesis
it inverts and keeping it would let aesop re-derive the same frame for ever; `forward` for
`all_sub_string`, whose conclusion is a universal statement about the members and whose
hypothesis stays useful. Nothing moved out of `default`, so no existing proof changed.

**Red control, both halves, both exercised.** Positive: `Effect4.Program.pair_inv_closes`
(`Fits vs [nat, nat] → ∃ m n, vs = [Val.nat m, Val.nat n]`) closes with
`aesop (rule_sets := [Effect4.Atoms])`. Negative: `Test/Program/AtomRulesRed.lean` (imported by
`Test.All`) is the same goal with **no clause at all** — omitted, never negated, because
`-Effect4.Atoms` errors at the clause when the set is not active and would say nothing about the
goal — with `#guard_msgs (error)` pinning aesop's refusal verbatim (`Tactic `aesop` failed, made
no progress`, with the goal). **Measured sensitivity**: putting the clause back makes
`#guard_msgs` report a message mismatch, so the fixture goes red exactly when the bank starts
closing the goal unasked.

### 2.5 — the table (`4542ef63`, `df0a5898`, `50aa8422`)

**Runtime half** (`src/Effect4/Machine/Term.lean`). `structure AtomRow` (`name`, `arity`,
`constGeneric`, `prelude`) and `def row`, one exhaustive match, with `name`, `arity` and
`constGeneric` as projections. Four matches became one, and `constGeneric` moved down out of the
typing half where it never belonged. No function field (it would take `eval` off the enum and
with it the exhaustiveness error and the engine's jump table), no `Ty` (the machine's closure
does not carry the checker), no citation (it belongs with the typing rule). `eval` is untouched,
so `MeaningSound.eval_validIn` and `Handles/Term.lean`'s row-order proof are untouched.

**Typing half** (`src/Effect4/Program/NativeAtom.lean`). `Scheme` is
`mono | variadic | poly | alts | custom`; `Spec` carries it with its `cite`; `spec` is one
exhaustive match; `typeOf` and `mono` are projections. Each custom rule is its own definition
(`projectRule`, `causeTestRule`, `causeErrorRule`, `optionPresenceRule`, `optionDefaultRule`), so
"one rule, one definition" is literally true and a proof splits that rule's arms and no others.
`Ty.matchTemplateArgs` is the list-level fold of the rows' `matchTemplate`, with
`matchTemplateArgs_length` **proved**. Every row answers exactly what its hand arm answered, at
every argument list; `poly` deliberately does **not** normalise the instantiated answer, because
`normalize` distributes a product over a union and that would move the checker's verdicts (L4's
business, plan 1.8).

One deliberate semantic-metadata change: **`tagIs` is `mono [.string, .unknown] .bool`**. Now
that the language has a top (row 46, landed at L5), the arm that ignored its second argument
*is* a monomorphic signature, and it is the one the prelude's own `(tag: string, e: unknown)`
already spelled. `typeOf` answers what it answered; `NativeAtom.mono .tagIs` moves `none` →
`some ([.string, .unknown], .bool)`, `typeOf_mono` now covers the row, and the profile's
`args`/`answer` for `tagIs` stop being null. **Measured**: comparing the profile's twenty atom
rows before and after, the names and order are identical and `tagIs` is the only row that moved.

**Soundness** (`src/Effect4/Laws/Program/Typed.lean`). `NativeAtom.Sound` is the obligation;
`sound_of_mono` discharges subsumption at every parameter through the new `Fits.sub`;
`sound_of_variadic` through the generalised `Fits.all_sub` (`Fits.all_sub_string`, which the
bank registers, keeps its statement as its corollary); `sound_of_alts` picks the alternative
`findSome?` hit; `sound_of_custom` routes to the named rule; `sound_of_poly` hands the atom the
substitution the match produced. `Shape` names the seven evaluation shapes the monomorphic atoms
have and `sound_of_shape` inverts each shape's fit once.

**Before/after size of `nativeAtom_typed`**, **measured**:

| | lines |
| --- | --- |
| before: `nativeAtom_typed`, twenty hand blocks | **164** |
| after: `nativeAtom_typed` | **7** |
| after: `NativeAtom.sound`, the dispatch it calls, same twenty atoms | 132 |
| after: the generic scheme lemmas + `Shape`, written once | 195 |

Per atom is the number that matters: **8.2 lines per atom before; 1 line for each of the nine
monomorphic atoms after** (`exact sound_of_shape .nat1 rfl (fun _ => ⟨_, rfl⟩)`). The blocks
that stayed blocks are the ones whose rule is their own: `fst`/`snd` (8), the four cause queries
(10 each), `isSome` (9), `getOrElse` (13), plus `strings` (14), `eq` (13) and `pair` (16). No
`first`, no `try`, no `simp_all` in any new text. Every new theorem is at `[propext,
Quot.sound]`; `Fits.sub` first reached `Classical.choice` through a bare `simp` on a length
disequality and is written `simp only [List.length_cons, List.length_nil]; exact nofun` instead
— **measured** with a four-way probe, `by simp` classical, `simp only … ; exact nofun`
axiom-free.

**Red control, rebuilt to bite harder.** `specWellFormed` takes `(inventory, AtomRow, Spec)`, so
`Test/Program/AtomTable.lean` judges hand-built rows with the code the core ships rather than a
copy of it. Five defects, each refused on its own: arity against the signature; a template whose
answer names a parameter nothing binds; const-generic with a monomorphic signature; alternatives
of unequal arity under one declared arity; a repeated name. Five good rows pass and between them
cover every `Scheme` constructor, so the predicate is not vacuous; and the real table's rows pass
the same predicate row by row.

**The prelude's atom block** (`50aa8422`). Group `PreludeAtoms`
(`tools/Effect4Gen/PreludeAtoms.lean`) writes `harness/truth/prelude-atoms.gen.ts`: one export
per atom, the body from `AtomRow.prelude`, the doc from `Spec.cite`. `prelude.ts` re-exports it
and reaches the atoms through `Atoms.` in its self-test table, which stays hand-written. A file
of its own rather than a second group of `Atoms.lean`, because the prelude group reads the
typing half and the typing half imports what `Atoms.lean` writes: one emitter for both would be
a module importing the file it produces.

**Receipts for the faces.** `--only derived` through the real driver, no other generated file
moved; `--only eff`, `--only wire`, `--only cas`, `--only ts`, `--only readme` green with
`ts/eff/profile.gen.ts` the only change; `cd harness/truth && bun test` **36 pass**, and
`tsc --noEmit -p tsconfig.json` clean under the pinned compiler; `cd ocaml && opam exec
--switch=effect4 -- dune build` exit 0. `--only lcnf` is §0.

---

## 3. What was not done, and why

1. **`--only lcnf` and a regenerated engine face.** §0. The engine's frozen layout mirror is
   four `Ty` constructors behind since L5, so a regenerated `api_engine.ml` does not compile.
   Next command, after someone unfreezes `ocaml/engine/e4_program_layout.ml` (plan 4.1/4.2):
   `python3 scripts/generate.py --only lcnf && cd ocaml && opam exec --switch=effect4 -- dune build`.
2. **`make check-gen`.** It depends on `| build`, i.e. `lake build` including `Test`, which is
   red on the pre-existing gate entry. The drift it would check was run by hand instead: every
   hermetic family regenerated, `ts/eff/profile.gen.ts` the only change. Next command after seat
   I's commit merges: `make check-gen`.
3. **The strong form of `sound_of_poly`.** The premise is stated at the substitution the match
   produced, not at "the arguments fit the parameters instantiated at the final σ". The stronger
   form needs `instantiate` to be monotone along the threading and it is not: an unbound
   parameter instantiates to `never`, which only widens in covariant positions, and
   `refOf`/`deferredOf` are invariant (row 55). That is the anchored completeness the plan puts
   at L4. Nothing is weakened by this — it is a new statement at the strength that is provable —
   but a `poly` atom reads its own σ until L4 lands.
4. **`Ty.matchTemplateArgs` lives in `Program/NativeAtom.lean`, in `namespace Ty`, not in
   `Ty.lean`.** `src/Effect4/Program/Ty.lean` is seat T2's file. The name is the one the plan
   asked for; moving the definition into `Ty.lean` is a one-line cut whenever T2's work settles.
5. **`ts/eff`'s ingest lane.** `bun test` in `ts/eff` has 19 failures, every one a test that
   spawns `node`/`bun` subprocesses (`ingest/test/runtime.test.ts` hangs past 120 s). None of
   them reads the atom metadata — `atomNames` is the profile's only consumer, and only `tagIs`'s
   `args`/`answer` moved. Whether they pass at `4b4e6aa3` in this worktree is **assumed**, not
   established; the worktree's `node_modules` are a fresh clone and several Lean compilers were
   running. Next command: `cd ts/eff && bun test ingest/test/runtime.test.ts` on a quiet machine,
   at the base commit and at the tip.
6. **`NativeAtom.isSome_validIn` / `getOrElse_validIn` (`Laws/Program/Progress.lean:50-66`) did
   not move.** They unfold `eval`, which is unchanged, so they needed nothing. Their pre-existing
   `first | exact hfallback | exact hinput` is left alone: it is not new text, and rewriting it
   is the proof-shape ratchet's business (plan 1.7).

---

## 4. Files touched outside the seat's scope

Three, one forced line each, each the smallest edit that works.

| file | the line | why it was forced |
| --- | --- | --- |
| `scripts/generate.py` | guard the derived loop's `lake build <module>` on `src/**.lean` | the loop named a Lake target for every group's output; the prelude group's output is a `.ts` file and has no module, so the unguarded call names a target that does not exist |
| `scripts/check-truth.py` | one `shutil.copyfile` of `prelude-atoms.gen.ts` beside `prelude.ts` | the temporary run copies `prelude.ts` into a work directory; without the generated block beside it the copy does not resolve |
| `Test/Audit/AxiomGate.lean` | **reverted, nothing committed** | §0 — applied and backed out; seat I owns it |

`Makefile` is in scope and was edited three times, each per the coordinator's instruction:
`src/Effect4/Program/AtomInventory.lean` at the **end** of `DERIVED_OUT`;
`harness/truth/prelude-atoms.gen.ts` on the **harness line** of `GENERATED_PATHS`, never the
first line, and in `TRUTH_SOURCES`; `Machine/Term.trace` and `Program/NativeAtom.trace` at the
end of `DERIVED_TRACES`. `tools/Effect4Gen/manifest.json` has the two new groups adjacent,
`AtomInventory` then `PreludeAtoms`, inserted before the `Forms` entry.

---

## 5. Proposed rows for `docs/core/decisions.md` (not edited by this seat)

The coordinator drafted rows 64 and 65. What this seat would have them say, corrected against
what landed:

**Row 64 — the atom table has two halves, and `eval` is not in either.** An atom's *data* is one
`AtomRow` in `Machine/Term.lean` (`name`, `arity`, `constGeneric`, `prelude`), read by one
exhaustive `row` match, with every per-atom projection defined from it. An atom's *typing* is one
`Spec` in `Program/NativeAtom.lean` (`scheme`, `cite`), read by one exhaustive `spec` match, with
`typeOf` and `mono` defined from it. Neither record holds a function and neither holds a `Ty` on
the runtime side: `eval` stays a `match` on the enum so the compiler's exhaustiveness check keeps
firing and the OCaml engine keeps its jump table, and the type language stays above the stores so
the machine's LCNF cut does not carry the checker. A new atom is one constructor, one `row`, one
`spec`, and one line of soundness when its scheme has a `Shape`.

**Row 65 — a named aesop bank is registered with a control on both sides.** A bank is declared in
`Laws/Auto/RuleSets.lean` and registered in a module of its own; it ships with a theorem that
closes *with* the clause, and a `Test` fixture holding the same goal with the clause **omitted**
inside `#guard_msgs (error)`. The clause is omitted, never negated: `(rule_sets := [-Bank])`
errors at the clause when the set is not active, so it would prove nothing about the goal.

**Row 66 (this seat would add) — `ofName?` is a match on the string, not a scan of `all`.**
The alphabet's name lookup is on the machine's path (`evalTerm` resolves an atom at every term
application), and OCaml compiles a string match to a decision tree. The second spelling of the
name table it introduces is pinned in both directions, by `ofName?_name` and `ofName?_sound`,
each one tactic line and neither reaching an axiom. The same rule applies to any later alphabet
whose names the machine resolves.

**A ruling this seat took and would like recorded either way**: `tagIs` is typed
`mono [.string, .unknown] .bool` rather than kept as a custom rule, which moves
`NativeAtom.mono .tagIs` from `none` to a signature and makes the generated profile's
`args`/`answer` for that atom non-null. `typeOf`'s answers do not change. The argument for it is
that `unknown` is the top the language gained at L5 and the prelude already spelled the signature
that way; the argument against is that it moves a committed generated face for metadata alone.
