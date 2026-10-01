# Seat Q (type-language probe, 2026-10-01): the generated machinery, the lowering, and conservativity

Seat Q of the type-language probe. Brief: `../brief-Q.md`; rules: `../README.md`. Research only:
no tracked file was edited; every generator change is a copy under `Q/tools/` with its diff under
`Q/patches/`; every generator run wrote under `Q/generated/`.

## The one thing

**The generator work the wave needs is measured on copies (tested), and on today's `Ty` every
copy writes today's bytes (reproduced), so it can land alone before the append (T's commit 2).**
It is one new emission for the
eliminator, the equality and the `Repr` (`Fold.lean` +355/−1), the view at variable arity with the
order's exceptional rules as one table (`View.lean` +713/−48, `Variances.lean` +165/−1), `fold_of`'s
product case (+28/−1; its sibling extension assumed at 60 to 120 lines), and a four-line LCNF
translator row without which the wave's `sub` lowers to OCaml that `ocamlopt` refuses while the
translator's own check passes it (tested). The canonical sort and R's paired value sort need no
new extern, and the lowered code agrees with Lean on 18 vectors (tested). Conservativity is one
command over committed files (`Q/check-conservativity.sh`, 10 of 10 controls, green at the base;
tested); on history it refuses
both previous `Ty` appends on one clause, because the baseline policy has named no `Ty` constructor
since `lit`: the owner must promote or waive `refOf`, `deferredOf`, `var` and `unknown` before the
wave. The `Val` append is optional: `Int` and binary64 already have exact images (reading; the
frames themselves are measured, +138/−7 and the regenerated groups, tested).

---

## 0. Base, setup, evidence words

- **Base.** Worktree `/Users/pooks/Dev/lean4-effect4-probe-Q`, branch `probe/Q`, head `bff50631`
  (`git rev-parse HEAD`, tested). `.lake` current at the start (the coordinator's statement; no
  `lake build` was run by this seat).
- **Evidence words** (as the README and DI-32 use them). **proved**: a kernel theorem compiled here
  with its `#print axioms` at or below `[propext, Quot.sound]`. **reproduced**: a byte comparison
  against a fresh producer run. **tested**: a finite check run here (a `#guard`, a `#guard_msgs`, a
  generator run with its exit code, a `git grep`, a script). **reading**: read in code, not run.
  **assumed**: not checked. Every Lean check is a finite probe of a model unless it names a tree
  declaration.
- **How the probes run.** The probe family is compiled to `.olean`s outside the worktree (the
  session scratchpad, `$QBUILD`) so the generators can `importModules` it; nothing built is
  committed. Three wrappers, all in `Q/bin/`:
  - `olean.sh <root> <file>`: `LEAN_PATH=$QBUILD lake env lean -R <root> -DwarningAsError=true
    -M6144 -o … -i … <file>`, `LEAN_NUM_THREADS=1`;
  - `qlean.sh <args>`: `LEAN_PATH=$QBUILD lake env lean <args>` from the worktree, one thread;
  - `logrun.sh <log> -- <command>`: runs one command from the worktree root and writes the command,
    its output and `# exit=… seconds=…` to `Q/logs/<log>`.
  One compiler process at a time throughout.
- **The probe family.** `ProbeQ.Ty` (`Q/probe/ProbeQ/TyCore.lean`): today's `Ty` (20 constructors,
  same order, same field names, `src/Effect4/Program/Ty.lean:37-75`) plus row 119's constructor
  appended, `record (fields : List (String × Ty))`. The variant `ProbeQFull.Ty`
  (`Q/probe/ProbeQFull/TyCore.lean`): the optional-field modifier inside the field list,
  `record (fields : List (String × Ty × Bool))` (seat P's `(name, τ, optional)`), and row 125's
  `map (key value : Ty)`. The namespace is `ProbeQ` so every generated name (`TyFam`,
  `TyAlgebra`, `cata_ty`, `Ty.args`, …) lands under `ProbeQ` exactly as it lands under
  `Effect4.Program` in the tree. Later families: `ProbeQW.Ty`, the whole wave (Q2's opening);
  `ProbeQMap.Ty` and `ProbeQNum.Ty`, the red controls of Q2; `ProbeQ5.Lower`, the lowering roots
  (Q5); `ProbeQV.Val`, `Store.Val` with the two frames (the `Val` append).

---

## Q1. The nested eliminator and equality, generated

### Finding: there is no generator to run

The brief asks to run "the generator that made `Store.Val.ind` and `Val.beq`". **None exists**
(tested): `git grep -n 'Val.ind\|Json.ind' tools src` finds only uses and the two hand
declarations; `tools/` contains no `motive_2`, `beqList`, `.rec` or `elab_as_elim` emission
(`git grep` over `tools`). The three nested companions are hand-written, twice:

| Family | Eliminator | Equality (`beq`, its iff, the instance) | `Repr` |
| --- | --- | --- | --- |
| `Store.Val` | `Val.ind`, `Store/Carrier/Val.lean:265-287` (23 lines) | `Val.beq`/`beqList`/`beq_iff`/`beqList_iff`/`instDecidableEq`, `:1111-1154` (44) | `render`/`renderList`/`instRepr`, `:171-198` (28) |
| `Json` | `Json.ind` (private), `Data/Json.lean:304-339` (36) | `beq`/`beqList`/`beqEntries` and their iffs, `instDecidableEqJson`, `:362-451` (90) | none |

(line ranges: reading; counts: `sed -n … | wc -l`, tested.) Row 119's "eliminator and equality
generated, not hand-written a third time" is therefore a **new emission**, not an extension of an
existing one. The tree seat's hand model for `Ty` was 31 + 32 lines plus a hand `Repr`
(`2026-10-01-data-probe/tree/note.md` §4.2).

### Why the companions are forced (tested, red controls kept as a fixture)

`Q/probes/Q1/NestedInstruments.lean` imports only the bare declaration and asserts, with
`#guard_msgs`, what Lean 4.33.1 does on the nested `ProbeQ.Ty` (exit 0 means every refusal is as
written; log `Q/logs/probes/Q1-NestedInstruments.log`):

- `deriving instance DecidableEq` → "None of the deriving handlers for class `DecidableEq` applied
  to `ProbeQ.Ty`" (the handler's own line, reading: `Lean/Elab/Deriving/DecEq.lean`,
  `if indVal.isNested then return false -- nested inductive types are not supported yet`);
- `induction t` → "The `induction` tactic does not support the type `ProbeQ.Ty` because it is a
  nested inductive type";
- `deriving instance Repr` elaborates, but its `repr` is an `opaque` over a `partial def
  …_unsafe_rec` (read off the environment and asserted), the shape the trust gate refuses
  (`Store/Carrier/Val.lean:173-177`).

`Ty.lean` itself needs `DecidableEq Ty` before its first function: `insertMember`'s `if t = u`
(`Ty.lean:179`), `sub`'s `if a = b` (`:438`), and `Effect4.Row.normalize`'s `[DecidableEq α]`
(`Data/Row.lean:45-66`) (reading). So a generated equality cannot sit in a module downstream of
`Ty.lean` (as the Fold group's `Program/Fold.lean` does): **the declaration moves to its own
module** (`Program/TyCore.lean`), the generated companions land in `Program/TyEq.lean`, and
`Ty.lean` imports that. The probe has exactly this shape: `ProbeQ.TyCore` → `ProbeQ.TyEq`
(generated) → `ProbeQ.Ty`.

### The change, on a copy of the tool

The new emission is a section of the fold generator, reusing its position language (`Pos`,
`posOf`, `composites`, `suffix`) rather than a fourth reader of constructor fields; a type is
routed to it by the manifest's existing `Kinds` field (`--kind <Type>=elim`), so the driver and the
manifest format do not change.

- Copy: `Q/tools/Effect4Gen/Fold.lean`; diff: `Q/patches/Fold-elim.patch`, **+355 / −1** against
  `tools/Effect4Gen/Fold.lean` at `bff50631` (tested: `grep -c '^+[^+]'` / `'^-[^-]'`;
  `git apply --check` passes, nothing applied). Hunks: the section `Elim` inserted before
  `structure Args` (`Fold.lean:1243`), the dispatch in `run` (`:1281`), and no empty receipts
  section for an elim-only file (`:1350`).
- What it emits for a one-member nested family `T` (refusing by name a parameterised or indexed
  family, a mutual block, a family with no nested position, a one-parameter-structure position):
  1. `T.ind`, `@[elab_as_elim, induction_eliminator]`, in membership form: one hypothesis per
     constructor, a member under a container as `∀ x ∈ xs, motive x`, a product's member side
     projected (`motive x.2`, `motive x.2.1`). Built from `T.rec` as the environment declares it:
     one motive per auxiliary type (each read back to a `Pos`), each container constructor's
     minor premise discharged by a fixed term (`List.nil`/`Option.none`: `nomatch`;
     `List.cons`: a `cases` on membership; `Prod.mk`: the side hypotheses; `Option.some`).
  2. `T.beq` and one helper per composite position (`T.beq_pos_<suffix>`), structural, leaves by
     `decide` (never `==`: `View.lean:277-278`'s note on `LawfulBEq` and `Classical.choice`);
     `T.beq_pos_<suffix>_iff` per position; `T.beq_iff` by `induction … using T.ind`, every case
     `cases b <;> simp only […]` with an explicit lemma list; the instance `instDecidableEqT :=
     decidable_of_iff _ (T.beq_iff a b)` (computation and proof kept apart, as Codex asked).
  3. `T.repr`, structural, printing the derived `Repr`'s text (`Lean/Elab/Deriving/Repr.lean`'s
     `mkBodyForInduct`) and a container as core prints it (`List.repr`, `Prod.repr`'s
     `ReprTuple` flattening, `Option.repr`; `Init/Data/Repr.lean:119-150, 431-437`).

### Runs and results

| Run (command in `Q/logs/gen/*.log`, compiled by `olean.sh`) | Output | Result |
| --- | --- | --- |
| `--kind ProbeQ.Ty=elim ProbeQ.Ty` | `Q/generated/ProbeQ/TyEq.lean` (251 lines) | exit 0; compiles with `-DwarningAsError=true` (`Q/logs/build/TyEq.log`) |
| `--kind ProbeQFull.Ty=elim ProbeQFull.Ty` | `Q/generated/ProbeQFull/TyEq.lean` (274) | exit 0; compiles (`build/Full-TyEq.log`) |
| `--kind Effect4.Store.Val=elim:QCheck.Val Effect4.Store.Val` (control) | `Q/generated/QCheck/ValElim.lean` (172) | exit 0; compiles (`build/ValElim.log`) |
| `--kind Effect4.Json=elim:QCheck.Json Effect4.Json` (control) | `Q/generated/QCheck/JsonElim.lean` (178) | exit 0; compiles (`build/JsonElim.log`) |
| `--kind Effect4.Program.Ty=elim` (red control: not nested) | none | exit 1: "elim: Effect4.Program.Ty has no member under a container; derive …" (`gen/red-TyElim-notNested.log`) |
| `--kind Effect4.Program.Eff=elim` (red control: parameterised) | none | exit 1: "elim: Effect4.Program.Eff has parameters or indices …" (`gen/red-EffElim-param.log`) |

Axioms (proved; verbatim from the build logs):

```text
'ProbeQ.Ty.ind' does not depend on any axioms
'ProbeQ.Ty.beq_iff' depends on axioms: [propext]
'ProbeQ.instDecidableEqTy' depends on axioms: [propext]
'ProbeQ.instReprTy' depends on axioms: [propext]
'ProbeQ.Ty.beq_pos_prod_string_ty_iff' depends on axioms: [propext]
'ProbeQ.Ty.beq_pos_list_prod_string_ty_iff' depends on axioms: [propext]
'ProbeQFull.Ty.ind' does not depend on any axioms
'ProbeQFull.Ty.beq_iff' depends on axioms: [propext]
'ProbeQFull.instDecidableEqTy' depends on axioms: [propext]
'ProbeQFull.instReprTy' depends on axioms: [propext]
'ProbeQFull.Ty.beq_pos_prod_ty_bool_iff' depends on axioms: [propext]
'ProbeQFull.Ty.beq_pos_prod_string_prod_ty_bool_iff' depends on axioms: [propext]
'ProbeQFull.Ty.beq_pos_list_prod_string_prod_ty_bool_iff' depends on axioms: [propext]
'Effect4.Store.QCheck.Val.ind' does not depend on any axioms
'Effect4.Store.QCheck.Val.beq_iff' depends on axioms: [propext]
'Effect4.QCheck.Json.ind' does not depend on any axioms
'Effect4.QCheck.Json.beq_iff' depends on axioms: [propext]
```

The emitted record hypothesis, as the brief asks to see it:

```lean
(record : ∀ (fields : List (Prod String ProbeQ.Ty)), (∀ x0 ∈ fields, motive x0.2) → motive (.record fields))
```

and on the variant, `(∀ x0 ∈ fields, motive x0.2.1)` for `List (String × Ty × Bool)`, `map` a plain
two-child hypothesis.

**On the whole wave** (after T's census; `ProbeQW.Ty`, Q2's opening): `--kind ProbeQW.Ty=elim`
writes `Q/generated/ProbeQW/TyEq.lean`, which compiles (`Q/logs/build/W-TyEq.log`) with four
auxiliary positions (the field triple `String × Ty × Bool`, its inner `Ty × Bool`, the field list,
and one `List Ty` shared by `tuple` and `app`): `ProbeQW.Ty.ind` uses no axiom; `beq_iff`, the
four position lemmas, `instDecidableEqTy` and `instReprTy` use `[propext]`. The eliminator's new
hypotheses:

```lean
(record : ∀ (fields : List (Prod String (Prod ProbeQW.Ty Bool))), (∀ x0 ∈ fields, motive x0.2.1) → motive (.record fields))
(map : ∀ (key : ProbeQW.Ty) (value : ProbeQW.Ty), motive key → motive value → motive (.map key value))
(tuple : ∀ (items : List ProbeQW.Ty), (∀ x0 ∈ items, motive x0) → motive (.tuple items))
(app : ∀ (name : String) (args : List ProbeQW.Ty), (∀ x0 ∈ args, motive x0) → motive (.app name args))
```

`sub_unknown` keeps its text over the whole wave too (`Q/probe/ProbeQW/Ty.lean`, `[propext,
Quot.sound]`).

### The generated text against the hand text (tested and proved; `Q/probes/Q1/ElimControls.lean`, exit 0)

1. `example : @Effect4.Store.QCheck.Val.ind = @Effect4.Store.Val.ind := rfl` elaborates: the
   generated eliminator has exactly the statement of the hand one (tested).
2. `Q1.val_beq_agrees : QCheck.Val.beq a b = Store.Val.beq a b` (proved, `[propext]`).
3. `Q1.json_beq_decides : QCheck.Json.beq a b = decide (a = b)` (proved, `[propext]`; the hand
   `Json` companions are private, so the comparison is with the public instance).
4. The generated `Repr` of `ProbeQ.Ty` prints, on 24 record-free samples (three of them deep
   enough to break lines), the text Lean's **derived** `Repr` of today's `Effect4.Program.Ty`
   prints (prefix renamed, compared at an unbounded width since the shorter probe names move the
   line breaks), and at the default width exactly what the `partial` derived `Repr` of
   `ProbeQ.Ty` itself prints, records included (`#guard`, tested). On the variant,
   `Q/probes/Q1/FullControls.lean` checks the same for records with the optional flag (tuple
   flattening) and that `beq` agrees with `decide (t = u)` on all pairs of samples (tested).

So a generated `Repr` keeps every existing printed `Ty` byte-identical (the conservativity
concern for `#eval`/`#guard_msgs` outputs; Q6), which the hand `Val.render` style would not.

### The tree's `Ty` theorems on the copy (proved; `Q/probe/ProbeQ/Ty.lean`, exit 0)

With `ProbeQ.Ty.ind` registered, plain `induction t` reaches the nested family, and the copied
theorems keep their text verbatim:

- `members_isMember` (`Ty.lean:410-414`, its `induction t <;> simp only … at h`,
  `all_goals try …` unchanged): `[propext]`;
- `sub_unknown` (`Ty.lean:767-770`, `induction t with | union … | _ => …` unchanged): `[propext,
  Quot.sound]`; and `sub_unknown'`, the same text with `induction t using ProbeQ.Ty.ind`, as the
  brief asks: `[propext, Quot.sound]`;
- `members_atom`, `sub_refl`, `sub_union_left`, `sub_union_right`, `sub_lit_string` (copied,
  unchanged): `[propext]` to `[propext, Quot.sound]`.

No proof in `src`, `Test` or `tools` names an auto-generated recursor hypothesis (`left_ih`,
`inner_ih`, …) or uses `Ty.rec`/`recOn`/`brecOn`/`casesOn` directly (tested: `git grep`, 0 hits),
so registering the eliminator changes no existing proof text by itself.

### What the change costs in the tree (reading, measured on the copy)

- `tools/Effect4Gen/Fold.lean`: +355 lines (the patch).
- `tools/Effect4Gen/manifest.json`: one group, `TyEq`, tool `Fold.lean`, `Kinds:
  ["Effect4.Program.Ty=elim"]`, imports `Effect4.Program.TyCore`, out
  `src/Effect4/Program/TyEq.lean`, first in the manifest: every other group's imports reach
  `Ty.lean`, which now imports it (its own import, `TyCore`, does not).
- `Makefile`: `DERIVED_OUT` gains `src/Effect4/Program/TyEq.lean`; `DERIVED_TRACES` gains
  `Program/TyCore.trace`.
- `src/Effect4/Program/Ty.lean` splits: the inductive (and the carrier-rule docstring, whose
  sentence "a `List Ty` argument would make `Ty` nested and cost the derived equality and every
  `induction` on it" becomes "costs a generated companion module") moves to `TyCore.lean`;
  `deriving DecidableEq, Repr` is removed; `Ty.lean` imports `TyEq`.
- `tools/Conform/Effect4/cases-policy.json`: the rows `Effect4.Program.instDecidableEqTy.decEq`
  (14 sites) and `Effect4.Program.instReprTy.repr` go stale (the instances no longer have those
  auxiliary functions); `Ty.beq` and `Ty.repr` are new case sites (Q4).
- Hand lines removed against the alternative: the third hand copy (63 lines plus a `Repr`, the tree
  seat's model) is not written; the two existing hand copies could later move to the same emission
  (their statements agree, controls 1–3), which is a separate, optional slice.

---

## Q2. `TyView` at variable arity

Mid-task the coordinator widened the family after seat T's census (`T/note.md` §2.1, §2.4): the
wave appends `record` (with optionality), `map`, `tuple (items : List Ty)`, `app (name : String)
(args : List Ty)` and the leaves `null`, `undefined`, `number`, `bytes` in one commit. Every
result below is measured on the stage-1 family `ProbeQ.Ty` (record only) and on the wave family
`ProbeQW.Ty` (`Q/probe/ProbeQW/TyCore.lean`: today's 20, then `record (fields : List (String × Ty
× Bool))`, `map`, `tuple`, `app`, `null`, `undefined`, `number`, `bytes`, tags 20–27).

### Red controls with the unmodified generator (tested, kept as fixtures)

1. `tools/Effect4Gen/View.lean` on `ProbeQ.Ty` refuses at `readCtors` (`View.lean:160-165`):
   "constructor ProbeQ.Ty.record field fields has type List (Prod String ProbeQ.Ty), which
   `sameHead` does not know how to compare" (`Q/logs/gen/red-View-record.log`, exit 1).
2. **A fixed-arity append breaks it too.** The view's dispatch writes `sub`'s catch-all as
   `case case16 => rfl` (`View.lean:591`): the number of the last `fun_cases` case today. On
   `ProbeQMap.Ty` (today's 20 plus `map (key value : Ty)` alone, a plain two-child head, its
   variance row present; generator copy `View-ns.lean`, which only derives the namespace) the
   emitted file does not compile: `case16` is now the `map` arm (`rfl` cannot close `k1.sub k2 &&
   k2.sub k1 && v1.sub v2 = false`) and the real catch-all `case17` is left unsolved
   (`Q/logs/build/red-Map-TyView-ns.log`). The view was added on 2026-09-19 (`f2a6aa71`), the day
   after the last `Ty` append, so no append has met this yet.
3. **A rule beside the congruences breaks the law.** On `ProbeQNum.Ty` (today's 20 plus `number`,
   with one rule of T's number tower, `nat` below `number`) the emitted file does not compile
   either: `sub nat number = true` at different heads, so `sub_eq_args` as stated (only the
   literal rule and the top excluded, `View.lean:291-305`, `:581-592`) is false at that pair
   (`Q/logs/build/red-Num-TyView.log`). Repaired below by one rule table ("The order's exceptional
   rules as one table").

### The change, on copies

- `Q/tools/Effect4Gen/View-ns.lean` (`Q/patches/View-namespace.patch`, +9/−5): the emitted
  namespace from the type's prefix (as `Fold.lean`'s `run` does) and `{ns}.Extends` instead of
  `Effect4.Program.Extends`; needed to point the tool at any family but `Effect4.Program.Ty`.
- `Q/tools/Effect4Gen/View.lean` (`Q/patches/View-variable-arity.patch`, **+713/−48** with the
  rule table below, +486/−37 without it; checks clean): three variable kinds, read from the declaration, each needing a row with an arity word:

| Kind | Constructor shape | `args` | `sameHead` (where the names live) | Variance row |
| --- | --- | --- | --- | --- |
| field list | `record (fields : List (String × Ty × P…))` | `(canon fs).map fun p => (.co, p.2.1)` | `decide ((canon fs1).map (fun p => (p.1, p.2.2)) = (canon fs2).map …)`: the names (and any modifier) in canonical order are the head's payload | `"arity": "each"`, `["co"]` |
| item list | `tuple (items : List Ty)` | `xs.map fun x => (.co, x)` | `decide (xs1.length = xs2.length)`: the arity is the head | `"arity": "each"`, `["co"]` |
| applied | `app (name : String) (args : List Ty)` | `xs.zipIdx.map fun p => (argVariance n p.2, p.1)` | `decide (n1 = n2) && decide (xs1.length = xs2.length)` | `"arity": "byName"`: each argument at the named declaration's variance |

  Fixed heads are unchanged; `rows`' length check (`View.lean:182-205`) applies to them only, and
  a variable head must carry its arity word (`each` with the one variance `co`, or `byName`).
  **The catch-all case number is computed** (seven plus the congruence heads: 16 today, 17 with
  `map`, 20 on the wave), and each variable head gets its own `fun_cases` case. The generator
  checks, and refuses by name, that `Ty.lean` provides what a variable head reads:
  `canon`, `mem_canon`, `canon_eq_nil` for a field list; `argVariance`, `Variance.select`,
  `Variance.holds_eq_select` for an applied head.
- **`app` moves variance into the core** (`Q/patches/Variances-variable-arity.patch`, +165/−1
  with the rule table, +107/−1 without it; checks clean). An `app` argument's variance depends on the name, so `sub` itself must read the
  declared variances: the variances producer copy (`Q/tools/Tools/Variances.lean`) also writes a
  core module (`--lean-out`, here `Q/generated/ProbeQW/TyVariance.lean`) declaring
  `Ty.Variance`, `Variance.holds`, `Variance.select`, `holds_eq_select`, `declaredVariance` (41
  generic rc.112 declarations by `Module.Name`, e.g. `"Layer.Layer" => [.contra, .co, .co]`) and
  `argVariance` (invariant where nothing is declared). It declares them under `<ns>.Ty`, so the 16
  references to `Ty.Variance`/`Ty.Variance.holds` in `src`, `Test` and the guards (tested, `git
  grep`) keep their text; the view stops emitting its own `Variance` when the core has one.
  `sub`'s `app` arm calls `select` because a well-founded definition cannot pass itself to
  `holds` unapplied. The table also gains rows `record`, `tuple` (`each`, co), `app` (`byName`)
  and `map` (`[inv, co]`, a printer row: rc.112's `HashMap` declares `<out Key, out Value>`,
  `HashMap.ts:50`, which would make the key covariant; R's printed spelling decides).

### The law the view yields (proved; `Q/probes/Q2/ViewLaws.lean`, `WaveViewLaws.lean`, exit 0)

`sub_eq_args` keeps its statement exactly, on both families:

```lean
sub_eq_args : ∀ (a b : Ty), a.isMember = true → b.isMember = true →
  a.litRule b = false → a.topRule b = false → a.sub b = (a.sameHead b && argsBelow sub a b)
```

Each variable head adds one arm lemma with the head as a premise, e.g.

```lean
sub_args_app : ∀ (n1 : String) (xs : List Ty) (n2 : String) (ys : List Ty),
  (app n1 xs).sameHead (app n2 ys) = true → (app n1 xs).sub (app n2 ys) = argsBelow sub (app n1 xs) (app n2 ys)
```

**Two laws change their statement** (the consumers' cost): the node law is false at a field
list, because a permuted record has its canonical record's head and children and is another term.
`eq_of_sameHead` and `argsBelow_antisymm` gain `headCanon a = true → headCanon b = true` (with
`headCanon (record fs) = decide (canon fs = fs)`, `true` at every other head, tuples and
references included since position is their order). The red controls
`eq_of_sameHead_needs_canon` and `wave_eq_of_sameHead_needs_canon` prove the unpremised law false
(`[propext]`). `argsBelow_antisymm`'s one consumer, `sub_antisymm_normal`
(`Laws/Program/TypeAlgebra.lean:657`), states over normal types, whose records P's `Normal` keeps
canonical, so it can discharge the premises (assumed until P's `Normal` record case lands).
`eq_of_sameHead_nil` keeps its statement (`headCanon_of_args_nil` discharges it through
`canon_eq_nil`). The guard file `tools/Effect4Gen/guards/tyview.lean`'s
`example … := Ty.eq_of_sameHead h hx` needs the two premises (reading).

The arm lemmas read `sub`'s variable arms in one form: `decide (head) && (zip).attach.all fun
⟨pq, h⟩ => have …; sub …` (a field list in canonical order, `Variance.select` at an applied
head), the termination by an in-body `have`, since `List.all` over a `zip` gives no membership
hypothesis (tested: `failed to prove termination`, the scratch run before the `attach`). That form
is a contract between `Ty.lean` and the generator; P's production arms should take it or the arm
lemma's emitted proof changes with them.

Axioms (verbatim, the wave; the stage-1 family's are the same or fewer):

```text
'ProbeQW.Ty.sub_eq_args' depends on axioms: [propext, Quot.sound]
'ProbeQW.Ty.sub_eq_false_of_not_sameHead' depends on axioms: [propext, Quot.sound]
'ProbeQW.Ty.sub_eq_argsBelow_of_sameHead' depends on axioms: [propext, Quot.sound]
'ProbeQW.Ty.sub_args_record' depends on axioms: [propext, Quot.sound]
'ProbeQW.Ty.sub_args_tuple' depends on axioms: [propext, Quot.sound]
'ProbeQW.Ty.sub_args_app' depends on axioms: [propext, Quot.sound]
'ProbeQW.Ty.sub_args_map' depends on axioms: [propext, Quot.sound]
'ProbeQW.Ty.eq_of_sameHead' depends on axioms: [propext, Quot.sound]
'ProbeQW.Ty.eq_of_sameHead_nil' depends on axioms: [propext, Quot.sound]
'ProbeQW.Ty.argsBelow_antisymm' depends on axioms: [propext, Quot.sound]
'ProbeQW.Ty.argsBelow_trans' depends on axioms: [propext, Quot.sound]
'ProbeQW.Ty.argsBelow_refl' depends on axioms: [propext, Quot.sound]
'ProbeQW.Ty.args_congr' depends on axioms: [propext, Quot.sound]
'ProbeQW.Ty.sameHead_refl' depends on axioms: [propext]
'ProbeQW.Ty.sameHead_symm' depends on axioms: [propext]
'ProbeQW.Ty.sameHead_trans' depends on axioms: [propext]
'ProbeQW.Ty.sizeOf_args' depends on axioms: [propext, Quot.sound]
'wave_eq_of_sameHead_needs_canon' depends on axioms: [propext]
```

Computed controls in the same files (tested, `#guard`): `args (app "Layer.Layer" [nat, bool,
unit]) = [(contra, nat), (co, bool), (co, unit)]`; an undeclared name reads `inv`; a permuted
record is below its canonical order both ways (TY-10's positive control, emitted as a variance
probe); a required field is not below an optional one (the modifier is payload under the exact
rule, an incompleteness against TypeScript to register with P's rule); width is refused.

### The order's exceptional rules as one table (proved, tested)

The wave declares cross-head leaf edges that are not congruences: `undefined ⊑ unit` (row 160) and
the number tower `nat ⊑ int ⊑ number` (rows 121, 109; seat P's question 3). At such a pair both
types are members, the literal rule and the top do not apply and the heads differ, so today's
different-head theorem (`sub_eq_false_of_not_sameHead`, which concludes `false`) cannot keep its
statement (red control 3). The change:

- **One table.** `variances.json` gains a `rules` section, written by the variances producer from
  one hand list beside its head map (`Q/tools/Tools/Variances.lean`, `rules`): the five structural
  cases in the order `sub`'s arms take them (`refl`, `never`, `unionLeft`, `unionRight`, `top`),
  then the leaf edges as pattern pairs (`lit _ ⊑ string`, today's literal rule, now a row;
  `undefined ⊑ unit`; `nat ⊑ int`; `int ⊑ number`; `nat ⊑ number`). The producer refuses a table
  that is not transitively closed (red control: dropping `nat ⊑ number` gives "the order's edges
  are not transitively closed: nat ⊑ int ⊑ number lacks nat ⊑ number",
  `Q/logs/gen/red-variances-unclosed.log`, from `Q/red/Variances-unclosed.lean`).
- **The edges are data for `sub` too.** The same producer writes `Ty.edgeRule` (one arm per edge)
  into the core module (`Q/generated/ProbeQW/TyVariance.lean`); `ProbeQW`'s `sub` drops its
  literal arm and its catch-all answers `edgeRule a b` (`Q/probe/ProbeQW/Ty.lean`). **A new edge
  is a row of the table**: no arm of `sub`, no line of either generator.
- **The view reads the same table** (`Q/tools/Effect4Gen/View.lean`, `readRules`,
  `emitDispatchTable`, `emitEdgeLaws`, `emitEdgeProbes`): the structural rows number `sub`'s first
  cases, the edges add none (they are in the catch-all), the congruences follow (case 6 to 18 on
  the wave), the catch-all is computed (case 19). With no `rules` section the view is today's,
  byte for byte (reproduced, `Q/logs/gen/today-TyView-patched.log`).

What it yields on the wave (`Q/probes/Q2/WaveViewLaws.lean`, exit 0; axioms in the log):

```lean
-- the different-head theorem: `sub` is the declared edge, false exactly where none is declared
sub_eq_edgeRule_of_not_sameHead : ∀ (a b : Ty), a.isMember = true → b.isMember = true →
  a.topRule b = false → a.sameHead b = false → a.sub b = a.edgeRule b
-- the law: one hypothesis fewer than today's (the literal rule is an edge)
sub_eq_args : ∀ (a b : Ty), a.isMember = true → b.isMember = true → a.topRule b = false →
  a.sub b = (a.sameHead b && argsBelow sub a b || a.edgeRule b)
-- transitivity through a leaf: the closure certificate (red if the table is not closed)
edgeRule_trans : ∀ {a b c : Ty}, a.edgeRule b = true → b.edgeRule c = true → a.edgeRule c = true
-- the inversion a transitivity proof splits on, one disjunct per row
edgeRule_eq_true : ∀ {a b : Ty}, a.edgeRule b = true → (∃ x0l, a = lit x0l ∧ b = string) ∨
  a = undefined ∧ b = unit ∨ a = nat ∧ b = int ∨ a = int ∧ b = number ∨ a = nat ∧ b = number
```

`sub_eq_edgeRule_of_not_sameHead`, `sub_eq_args`: `[propext, Quot.sound]`;
`edgeRule_eq_false_of_sameHead`, `edgeRule_eq_true`, `edgeRule_trans`: `[propext]` (proved). The
two controls, proved through the restated laws: `nat_sub_number : Ty.sub .nat .number = true`
(the accepted cross-head case, by `sub_eq_args`) and `number_not_sub_nat : Ty.sub .number .nat =
false` (its converse, by the different-head theorem), both `[propext, Quot.sound]`. The view also
emits, per edge, the accepted pair and its refused converse as `#guard`s, and every two-step chain
(`#guard Ty.sub .nat .number  -- through int`).

**The law to watch.** `sub_trans_core` (`Laws/Program/TypeAlgebra.lean:36-90`) composes two steps;
through a leaf the cases are edge∘edge (`edgeRule_trans`), edge∘congruence and congruence∘edge (a
leaf's only congruence partner is itself: `eq_of_sameHead_nil`, kept), and edge∘top. The view
supplies each piece; the re-proof is seat P's (assumed until it lands).

**The lines.** The rule table's part, against this seat's previous commit `6f0e9d7a`: `View.lean`
**+236/−13**, `Variances.lean` **+70/−5** (tested, `diff`). The consumers in the tree of today's
literal-rule vocabulary (`litRule`, `litRule_eq_false`, `litRule_eq_true`,
`litRule_eq_false_of_head`, `sub_eq_false_of_not_sameHead`): **22 lines in 5 files**
(`Laws/Program/TypeAlgebra.lean`, `Laws/Program/Template.lean`,
`Test/Counterexamples/Machine/Semantics/ValueMembership.lean`, `Test/Program/TyViewContract.lean`,
`tools/Effect4Gen/guards/tyview.lean`; tested, `git grep`), which move to the edge vocabulary in the
wave's append. Totals of the two copies against the base: `View.lean` **+713/−48**,
`Variances.lean` **+165/−1** (both `git apply --check` clean).

### Conservativity of the change itself (reproduced)

Each copy, run on today's `Effect4.Program.Ty` with the production table and `--header-out`,
writes `src/Effect4/Laws/Program/TyView.lean` byte for byte: the unmodified tool
(`Q/logs/gen/today-TyView.log`), `View-ns.lean` (`today-TyView-ns.log`) and the full copy
(`today-TyView-patched.log`). Likewise the unmodified variances producer reproduces
`tools/Effect4Gen/variances.json` (`today/variances.json`, `gen/variances-today.log`). The
patched producer writes the wave's head rows and rules, so for a byte-neutral generator commit its
mechanism is split from those rows: `Q/patches/Variances-commit2-mechanism.patch` (+148/−2,
`Q/tools/Commit2/Variances.lean`: today's head list, an empty rule list, the `rules` section
omitted when empty) writes today's table byte for byte (reproduced,
`gen/commit2-variances-today.log`), and the `elim`-patched fold generator writes today's
`Program/Fold.lean` and `Store/Carrier/Fold.lean` byte for byte (reproduced,
`gen/commit2-Fold-today.log`, `gen/commit2-ValFold-today.log`).

---

## Q3. The fold group (taken before Q2: the view reads the fold's `TyAlgebra`)

### The fold generator needs no change (reproduced, tested)

- **Zero control (reproduced).** The unmodified `tools/Effect4Gen/Fold.lean`, run with the Fold
  group's exact arguments (`lake env lean --run tools/Effect4Gen/Driver.lean --commands --group
  Fold`) and `--out` redirected (`--header-out src/Effect4/Program/Fold.lean`), writes
  `Q/generated/today/Program/Fold.lean`, byte-identical to the committed
  `src/Effect4/Program/Fold.lean` (`cmp`, `Q/logs/gen/today-Fold.log`).
- **On the probe (tested).** The same unmodified tool on `ProbeQ.Ty` writes
  `Q/generated/ProbeQ/Fold.lean` (517 lines) and on `ProbeQFull.Ty`
  `Q/generated/ProbeQFull/Fold.lean` (574); both compile with warnings as errors
  (`Q/logs/build/Fold.log`, `Full-Fold.log`; every receipt `[propext]` or none, no
  `Classical.choice`, no `sorryAx`). `blockNested` (`Fold.lean:312-317`) sends the family to the
  nested emission (`Fold.lean:619-627` and on), which already reads `List (String × Ty)` as
  `.list (.prod (.leaf String) (.direct ty))`. What it yields:

```lean
structure TyAlgebra (R : TyFam → Type u) where
  …
  ty_record : List (String × R .ty) → R .ty

def cata_ty … | .record a0 => alg.ty_record (cata_pos_list_prod_string_ty alg a0)

@[simp] theorem cata_ty_record … :
    cata_ty alg (.record a0) = alg.ty_record (a0.map (prodMapSnd (cata_ty alg)))

structure TyHom … where … h_ty_record : ∀ a0, f_ty (.record a0) = alg.ty_record (a0.map (prodMapSnd f_ty))
theorem hom_eq_cata_ty …   -- [propext]
```

- **The declaration delta of the `Ty` block** (tested, `Q/logs/gen/Fold-decl-delta.log`): 18
  declarations today, 42 on the probe. **Lost** (the nested emission has no monadic half and no
  path fold): `foldMapAt_ty`, `TyMAlgebra`, `TyAlgebra.toM`, `TyMAlgebra.map`,
  `TyMAlgebra.toSeq`, `foldM_ty`, `foldM_eq_cata_ty`, `foldM_id_ty`, `foldM_natural_ty`.
  **New**: `prodMapSnd`, `prodMapSnd_mk`, `cata_pos_*` and their `_eq` lemmas, one `@[simp]
  cata_ty_<ctor>` equation per constructor (21), `hom_pos_*`, `cata_id_pos_*`, `foldMap_pos_*`.
  `foldMap_ty` and `cata_id_ty`, `TyAlgebra.id` survive.
- **Consumers of what is lost** (tested, `Q/logs/gen/Fold-consumers.log`): `git grep -nwE
  'foldMapAt_ty|TyMAlgebra|foldM_ty|foldM_eq_cata_ty|foldM_id_ty|foldM_natural_ty|foldMap_ty' --
  src Test tools ':!src/Effect4/Program/Fold.lean'` finds nothing (exit 1). `TyAlgebra.id` has
  one consumer, the appended guard `tools/Effect4Gen/guards/fold.lean:220`, and survives. So **no
  consumer needs the record arm of the monadic half**; losing it is an API decision to record
  (Codex reached the same reading), not a broken consumer. The other blocks of the file (`Term`,
  `CauseTerm`, `Eff`) are not nested and keep their monadic halves, so `MonadMorphism` is still
  emitted in the tree's file.

- **On the whole wave** (tested): the same unmodified tool on `ProbeQW.Ty` writes
  `Q/generated/ProbeQW/Fold.lean` (719 lines; 42 receipts, none reaching `Classical.choice` or
  `sorryAx`, `Q/logs/build/W-Fold.log`), with `ty_record : List (String × (R .ty) × Bool) → R .ty`,
  `ty_tuple : List (R .ty) → R .ty`, `ty_app : (String) → List (R .ty) → R .ty`. The Program
  group's tool (`tools/Effect4Gen/Main.lean`, unmodified, under a probe group name since `Program`
  runs the program-structure check) writes `Q/generated/ProbeQW/Canonical.lean`, whose `TyC` block
  gains the eight shape rows (`("tuple", 22, [("items", .list (.named "Ty"))])`, `("app", 23,
  [("name", …), ("args", .list (.named "Ty"))])`, …) and compiles (`toValTy`, `rawTy_toValTy`
  `[propext]`; `fitsTy`, `instCanonicalTy` `[propext, Quot.sound]`; `Q/logs/build/W-Canonical.log`).
  So **the fold and Canonical generators need no change for any wave constructor**.

### The `fold_of` connectors: refused on a nested family, all of them (tested)

`fold_of` (`src/Effect4/Program/FoldOf.lean`) is the command behind the 16 registrations of
`Laws/Program/Folds/Ty.lean`. On the probe (`Q/probes/Q3/FoldOfScan.lean`, the tree's command
unchanged, exit 1, `Q/logs/probes/Q3-FoldOfScan.log`), every traversal shape fails:

| Probe traversal | Its record arm | `fold_of` today |
| --- | --- | --- |
| `members` | `[.record fields]` (uses the value: a paramorphism) | error: "AppBuilder for `mkAppM`, result contains metavariables `Prod.map Prod.fst`" |
| `isNever` | `false` (listed) | the same error |
| `isMember` | `true` (listed) | the same error |
| `renderRaw` | recurses through a sibling `renderFields : List (String × Ty) → String` | "fold_of: ProbeQ.Ty.renderFields takes no value of the family" |
| `closed` | recurses through `closedFields` | "fold_of: ProbeQ.Ty.closedFields takes no value of the family" |

Two causes, both in `FoldOf.lean` (reading, then tested on a copy):

1. **`mapThrough` has no product case** (`FoldOf.lean:340-356`). A `Prod` position falls to the
   "one-parameter wrapper with a `W.map`" branch because core declares `Prod.map`, which takes two
   functions; `mkAppM` is given one and leaves a metavariable. The read-back (`readBack`, `:767`)
   is computed for every constructor with a container child, paramorphism or not, so every
   traversal of a family with a `List (String × M)` position fails, including those whose record
   arm never looks inside. **Fix on a copy** (`Q/probe/ProbeQ/FoldOf.lean`, diff
   `Q/patches/FoldOf-prod.patch`, **+28/−1**, `git apply --check` clean): a `Prod` case in
   `mapThrough` using the fold generator's own `prodMapSnd`/`prodMapFst`/`prodMapBoth` (the leaf
   side's type passed explicitly) and in `identThrough` componentwise by `Prod.ext`; the family's
   namespace added to `Positions`. With it (`Q/probes/Q3/FoldOfScanPatched.lean`,
   `Q3-FoldOfScanPatched.log`) `members` (as a paramorphism, the field list read back through
   `prodMapSnd`), `isNever` and `isMember` are accepted with their `eq_cata` connectors.
2. **A sibling over `List (A × M)` is refused** (`familyArgsOf`/`memberOf`, `:112-133`, read only
   `List M`), and nothing abstracts a recursive call on a field inside a pair. Still refused after
   fix 1 (same log). Not fixed here. The extension is the `List M` sibling generalised to an element
   position: the cons node instantiated with `Prod.mk n t :: rest` so the pair split reduces,
   `List.foldr` over `xs.map (prodMapSnd fv)`, `eq_foldr` by `List.rec`, and `eq_cata` through the
   generated `cata_pos_list_prod_string_ty_eq`. Its size is **assumed** at 60 to 120 lines; it is
   the larger half of the data wave's generator commit.

Which of the tree's 16 registrations meet which cause (reading each definition's record arm as row
119 and stage 1 need it): **all 16 meet cause 1**. **10 also meet cause 2** because their record
arm must recurse into the fields: `renderRaw`, `key`, `normalize`, `findInt`, `Val.hasTy`,
`Bridge.schema`, `Codec.layout` (its `| t => t` would silently keep a literal field's literal
layout), `Codec.isSupported`, `Codec.encodeRaw`, `Codec.decodeRaw`. **6 do not**: `members`,
`isNever`, `isMember`, `isTagTy` (`| _ => false`), `NativeAtom.projectProduct` (`| _ => none`),
`rawSupportedErrTy` (`false` until row 120 admits record payloads; then it recurses).

**The "5 `.hom`s compile-forced"** are the exhaustive inventory's rows for the `fold_of`-generated
homs of the five hand definitions with no catch-all (`members.hom`, `Val.hasTy.hom`,
`findInt.hom`, `rawSupportedErrTy.hom`, `Typed.Fits.hom`; reading of
`2026-10-01-data-probe/programs/ProbeBill.log:3-23`; rerun in Q4). They are rebuilt by `fold_of`
from their source definition, so they cost no edit of their own once `fold_of` accepts the nested
family; today it does not (cause 1).

**The alternative to extending `fold_of`** for the 10 recursing traversals is to write them as
algebras (`def renderRaw := cata_ty renderAlg`), whose record field receives the folded field
list (`List (String × A)`); they then need no connector (`eq_cata` is `rfl`), at the price of
every existing proof that unfolds them by their own equations moving to the `cata_ty_<ctor>`
lemmas. Recommendation: extend `fold_of` (cause 2), because it keeps the hand definitions' text
and their proofs, and the extension is the same one the `List M` sibling already made once.

---

## Q4. The hand tables and the exhaustive readers

### The exhaustive gate at the base (tested)

`Q/probes/Q4/ExhaustiveTy.lean` runs the tree's instrument (`#exhaustive_gate`,
`src/Effect4/Laws/Auto/Exhaustive.lean`, decisions row 61) over the core and the three estates
outside it (log `Q/logs/probes/Q4-ExhaustiveTy.log`; counted by `Q/bin/exhaustive-count.py`,
`Q4-ExhaustiveTy-count.log`):

| `Ty` under | Matcher rows | No catch-all (compile-forced) | Catch-all (compile-silent) |
| --- | --- | --- | --- |
| `Effect4` | 66 | 28 rows, 28 definitions | 38 rows, 31 definitions |
| `OCaml5` | 2 | `OCaml5.Eff.tyO`, `tyV` | none |
| `Tools` | 3 | `Tools.ProfileJson.tyJson` | `Tools.TyVectors.subMutant` (2 rows) |
| `Conform` | 3 | `LcnfMl.tyOcaml`, `LcnfMl.tyT`, `LcnfSemantics.tyValue` | none |
| `Test` | 3 | `ExhaustiveFixture.catchAllAbsent` | `catchAllPresent`, `privateCatchAll` |

The 28 compile-forced definitions in the core (the log's list): `Codegen.Types.ofNormalized`,
`Ty.args`, `Ty.closed`, `Ty.instantiate`, `Ty.isMember`, `Ty.isNever`, `Ty.key`, `Ty.members` and
`.hom`, `Ty.normalize`, `Ty.renderRaw`, `Ty.templateAdmissible`, `Ty.varsOf`, `Typed.Fits` and
`.hom`, `Val.hasTy` and `.hom`, `cata_ty`, `findInt` and `.hom`, `foldM_ty`, `foldMapAt_ty`,
`foldMap_ty`, `instReprTy.repr`, `rawSupportedErrTy` and `.hom`, `Bridge.schema`,
`ProgramGen.TyC.toValTy`. Of these, `cata_ty`, `foldMap_ty`, `Ty.args`, `TyC.toValTy` and the five
`.hom`s are generated or derived; `foldM_ty` and `foldMapAt_ty` disappear with the nested emission
(Q3); `instReprTy.repr` is replaced by the generated `Repr` (Q1).

**The 31 catch-all definitions, classified by name for the wave's eight constructors** (reading of
each definition's default arm; the cover column is what `cases-policy.json` then records):

| Definitions | The default answers | For `record`, `map`, `tuple`, `app`, `null`, `undefined`, `number`, `bytes` | Class |
| --- | --- | --- | --- |
| `Ty.Variance.holds`, `Ty.litRule`, `Ty.topRule`, `Ty.sameHead` (4) | generated by the view | regenerated (Q2); `litRule` becomes an edge row of the table | generated |
| `NativeAtom.projectProduct.hom`, `Codec.decodeRaw.hom`, `Codec.encodeRaw.hom`, `Codec.layout.hom` (4) | `fold_of` connectors | follow their definitions once `fold_of` takes the nested family (Q3) | generated |
| `Checker.exitOf?`, `Checker.listOf?`, `fiberTy`, `Ty.factors`, `Ty.isFactor`, `causeInputError?`, `isTagTy`, `Decision.arms`, `selectRefusal` (9) | a projection or classifier of named heads; `none`, `false` or the type itself elsewhere (`selectRefusal` cases on the decision and passes the type through; `Decision.arms`'s tag arm goes through `taggedColumn`, below) | right for all eight: the covers gain the names | cover |
| `Ty.infer` (11 sites) | `σ` unchanged: the walk stops | `record`, `map`, `tuple`, `app` must descend, or a template variable under them is never bound (silently); the leaves keep the default | arms (4) |
| `Typed.FlatFits` (`Laws/Program/Typed/Membership.lean:64`) | `False`: no value is a member | the four leaves need their value images (the `Val` question below); the four heads with children their structural membership (seat P) | arms (8) |
| `Ty.sub` (12 sites) | `false` today; `edgeRule a b` on the wave (Q2) | congruence arms for the four heads with children; the leaves through the rule table | table |
| `Ty.isTagged`, `Ty.payloadOf`, `Ty.taggedColumn` (3) | a tagged member is `prod (lit t) _` | a record with a literal tag field is TypeScript's discriminated member: seats R and P decide | design |
| `NativeAtom.projectProduct` | projects `prod` | `tuple` is an n-ary product: decide | design |
| `Authoring.ServiceDef.receiver` | the first factor of a product request, else the request | a `tuple` request: decide | design |
| `methodArgsRow` (`Codegen/PrintLeaf.lean:228`) | `prod` prints a tuple call, the rest a call | `tuple` presumably a tuple call: decide | design |
| `externalValue` (`Program/Compile.lean:1371`) | marshals a host value by its type, else the fallback | a record, number, bytes, null or undefined from the host: the host boundary's decision | design |
| `Codec.encodeRaw`, `Codec.decodeRaw`, `Codec.isSupported`, `Codec.layout` (4) | `none` or `false`: unsupported | refused by name until the codec's own commit (T's N6): the covers gain the names in the append, arms in T's commit 5 | cover, then arms |

So of the 23 hand catch-alls, 9 are right as they stand, 2 need arms whose absence would be
silent (`infer`, `FlatFits`), 1 is the rule table (`sub`), 7 wait on a decision by another seat,
and 4 refuse by name until their commit.

### `cases-policy.json`: what `make check-cases` demands for a new constructor

Reading of `tools/Conform/Lcnf/Cases.lean:417-421, 580-665`, then tested at the base:

- **At the base (tested).** `make check-cases`'s configuration (`tools/Conform/Effect4/cases.json`)
  passes: 174/174 subjects, exit 0 (`Q/logs/probes/Q4-cases-base.log`). The `Ty` family has 36
  function rows over 73 case sites: **55 `default` sites with a cover list** (25 at function level,
  30 at site level in six functions: `payloadOf` 2, the derived `decEq` 1 of its 14, `infer` 11,
  `methodArgsRow` 2, `isTagged` 2, `sub` 12), 18 `exhaustive` sites, `unlisted: refuse`; 24 of the
  covers absorb 19 or 20 constructors, pure catch-alls (`Q4-cases-policy-count.log`). The brief's
  "25 cover lists" are the function-level ones.
- **A new constructor.** At every `default` site Lean compiles the wildcard to a default arm that
  absorbs it, and `withDefault cover` requires the absorbed set to equal the cover (`:621-632`):
  each of the 55 covers is a counterexample naming the constructor until the cover lists it or the
  function gains an arm. An `exhaustive` site passes when Lean forced an arm (a wildcard added
  instead is a counterexample, `:602-606`). A function that newly cases on `Ty` is
  `lcnf.cases.unlisted`, refused (`:580-593`); a row whose function no longer has a site is
  `lcnf.cases.stale`, refused (`:658-665`). For the wave in particular: the derived
  `instDecidableEqTy.decEq` (14 site entries) and `instReprTy.repr` rows go stale when the
  generated companions replace the derived instances (Q1), and `Ty.beq`, its position helpers and
  `Ty.repr` are new, unlisted sites.
- **Regeneration (tested).** `--seed-policy` (`tools/Conform/Cli/Audit.lean:182-183`) at the base
  writes `Q/generated/conform/seed-base.json`: the same 9 families and 110 rows, equal to the
  committed policy as JSON values except the 9 row notes and the top-level note
  (`Q4-seed-base.log`). A 14-line change to a copy of the driver (`keepNotes`,
  `Q/patches/Audit-seed-keeps-notes.patch`, `git apply --check` clean) carries the row notes over
  by family and function name: then **every family, row, cover and row note is equal** as JSON
  values (`Q/generated/conform/seed-keep-notes.json`, `Q4-seed-keep-notes.diff`). The top-level
  note (1,051 characters) is neither read nor written by `CasesPolicy` (reading): it moves to a
  README beside the file, or the structure gains the field. The byte layout differs (Lean's
  `Json.pretty` against the committed two-space layout), so the cut-over reformats the file once.
- **What regeneration does to the check.** Re-seeded in the commit that changes the code, the policy
  cannot refuse that commit; its diff is the review surface instead (every cover that gains a wave
  name is a decision visible by name). Later commits are checked exactly as today.

### `wire-tags.json` and its loader (tested; `Q/probes/Q4/WireTagsProbe.lean`, `Q4-wiretags.log`)

The loader (`tools/Tools/WireTags.lean`) run on local strings, never on the tracked file:

1. The wave's tags 20–27 after today's 0–19, against a 28-constructor declaration: accepted, in
   declaration order.
2. A repeated tag (`map` given `record`'s 20): refused by `parse` ("gives the tags [20] twice",
   `:88-90`), as the brief says.
3. **A repeated name inside one JSON object is not refused**: `"record": 20, "record": 21` loads as
   `record = 21`, because `Lean.Json.parse` keeps the last key (`{"a": 1, "a": 2}` parses to
   `{"a":2}`), so the name check (`:91-93`) never sees the repetition. Python's `json` does the
   same, so the conservativity check now refuses a repeated key itself (Q6, control R9).
4. A declared constructor with no row: refused ("declared but has no active tag", `:126`).
5. A row with no declared constructor: refused (`:119`).
6. A gap in the tags (21 skipped): accepted; density is not a rule.
7. A new row reusing a retired tag: refused (the tags of active and retired rows together).

### `Metadata.lean:52-60` and the two pins (reading, and the census above)

- `src/OCaml5/Eff/Metadata.lean:52-60` is a **list**, `types : List (String × Ty)`, one sample per
  constructor in its own order (`never`, `unknown`, `unit`, …), which feeds one row each of
  `ocaml/eff/goldens/metadata.tsv` (the `unknown` append inserted its row second: `0a2cb898`'s
  diff). Nothing forces a new entry: a forgotten constructor has no golden row, silently. The wave
  adds eight sample lines (a record with an optional field; an `app` at a declared name).
- `Test/Audit/ExhaustiveFixture.lean:19-42`: `catchAllAbsent`, twenty arms and no wildcard,
  compile-forced (+8 arms); `Test/Audit/TraversalCensus.lean:72` pins the gate's report of it,
  "`alts 20`" (+1 line, "`alts 28`"). Both test the gate, not `Ty`; they restate the count only
  because `Ty` is their subject.

### Generating every per-constructor artefact once (the owner's cut-over steer)

For each hand table and mirror: generatable by an existing tool with a small change (the tool and
its lines), only with a new emitter (measured or estimated), or a hand table that must stay (why).
The wave's hand cost is measured on copies (Q5): 12 lines for the eight arms of each Lean mirror,
the record arm's five lines including a termination `have`.

| Artefact (today's lines) | The wave by hand (measured) | Class | Tool, lines, evidence |
| --- | --- | --- | --- |
| `tools/Conform/Effect4/cases-policy.json`, the `Ty` family (36 rows, 55 covers, 18 exhaustive) | 55 covers decided, 2 stale rows (15 site entries), 4 or more new rows | existing tool, small change | `tools/Conform/Cli/Audit.lean:182-183` `--seed-policy` with `keepNotes`, **+14/−1** (tested: the whole policy equal as JSON); the top-level note, about 2 lines in `CasesPolicy.toJson` (reading) |
| `ocaml/engine/e4_program.ml:127-154`, `of_ty` and its `= 20` | +8 arms, `20 → 28` (tested on a copy) | delete, or an existing tool | the module is a declared stopgap deleted by the runner plan's step 1 (`e4_program.ml:119-126`); kept, `scripts/generate-engine-structure.py:29-50`, which already emits `PROGRAM_TYPES` and both name tables, would emit `of_<label>` per family from `program-structure.json`'s payload shapes (+25 to 40 lines, **assumed**) |
| `ocaml/eff/test/prop_wire.ml:155-171`, `rand_ty` | rewritten: 28 arms, 13 new (the eight and the five it never draws today: `lit`, `refOf`, `deferredOf`, `var`, `unknown`), leaves first (tested: 28 of 28 drawn in 5,000 samples) | new emitter | a `rand_<family>` emitter in `src/OCaml5/Eff/Emit.lean` beside `jsonOf`/`emitJsonFn` (`:202-226`, 24 lines, the analogue: one generator call per `OTy` where the printer has one printer call), writing `ocaml/eff/eff_rand.ml` in the eff group: **assumed** 25 to 35 lines |
| `src/OCaml5/Eff/Emit.lean:366-386`, `tyO` | 12 | new emitter (one interpreter) | the OCaml literal of a value is a function of EffGen's family description (`Family`, `Ctor`, `OTy`) and the value's canonical image: one `ocamlValue` over `Store.Val` replaces `tyO` and its siblings `kindO`, `shapeO`, … (**assumed** about 40 lines); seat U measures the spelling folds |
| `src/OCaml5/Eff/Goldens.lean:89-109`, `tyV` | 12 | new emitter (one interpreter) | `V` is the canonical image with constructor names: `vOfVal` by the same description (**assumed** about 30) |
| `tools/Tools/ProfileJson.lean:21-41`, `tyJson` | 12 (the record's spelling assumed; seat S owns it) | new emitter | no derived tagged JSON of `Ty` exists (tested: no `_tag` under `src/Effect4/Store/Domain/Derived/`); a derived group writing the `_tag` object from the declaration's field names (**assumed** 40 to 60) |
| `tools/Conform/Effect4/LcnfMl.lean:164-184`, `tyT` | 12 | new emitter (one interpreter) | the target value of a Lean value is the description plus `OCaml5.Lcnf.ctorName` (**assumed** about 30) |
| `tools/Conform/Effect4/LcnfMl.lean:270-290`, `tyOcaml` | 12 | delete | `TValue.render ∘ tyT` (`Conform/Lcnf/SemanticsTarget.lean:145`) prints the same OCaml up to a space before each parenthesis (tested on 21 samples: byte-equal on the 7 leaves, whitespace apart elsewhere; `Q4-tyOcaml-vs-render.log`); the rung's printed driver bytes change once |
| `tools/Conform/Effect4/LcnfSemantics.lean:40-60`, `tyValue`, and `valueTy?` (`:63-`) | 12, and the inverse's eight branches | new emitter (one interpreter) | the mono-LCNF value of a Lean value (`Value.ctor name #[fields]`, lists `List.cons`, pairs `Prod.mk`, `Value.bool`) is a function of the declaration (**assumed** about 40, and the inverse by the same table) |
| `src/OCaml5/Eff/Metadata.lean:52-60`, `types` | +8 samples, silent if forgotten | new emitter (small), or a guard | a sample per constructor from the description (EffGen's `witnessOf`, `Emit.lean:291`, already computes a least witness per constructor for OCaml; a Lean-side twin, **assumed** 20 to 30); the cheapest repair is a coverage guard over the constructor indices (one line, **assumed**) |
| `Test/Audit/ExhaustiveFixture.lean:19-42` and `TraversalCensus.lean:72` | +8 arms; `alts 28` | neither: re-point | point both at a fixture-local inductive (a one-time change of about 20 lines, reading); they never move with `Ty` again |
| `tools/Effect4Gen/wire-tags.json`, the `Ty` rows | +8 rows | hand table that stays | the tag assignment is the decision every byte producer reads (DI-79; since S1 tags are not declaration positions); its loader misses a repeated key (above) |
| `tools/Tools/Variances.lean`, the head map and the rules | +4 head rows (`record`, `tuple`: `each`; `app`: `byName`; `map`: `[inv, co]`), +5 edge rows | hand table that stays | which rc.112 declaration a head prints as, and which edges the order declares, are decisions; `variances.json` and the core module are generated from it (Q2) |

**What the table gains.** Eight of the thirteen stop being hand-maintained per constructor: the
policy by an existing tool (+14/−1, tested), `of_ty` by deletion or an existing tool, `tyOcaml` by
deletion, and five by new emission (one generic interpreter over the canonical image can serve
`tyO`, `tyV`, `tyT` and `tyValue` together; `tyJson` and `rand_ty` each need their own emitter).
The two pins stop depending on `Ty`. Two tables stay by design (the tags, the head map), and the
`Metadata` list wants at least a guard.

---

## Q5. The lowering and the OCaml mirrors

### The canonical sort lowers with no new extern, and so does R's paired sort (tested)

The route (`docs/core/lcnf-route.md` §1; the command each `ocaml/gen` header carries):
`lean -M4096 --run src/OCaml5/Tools/LcnfGen.lean --out <file.ml> --import <module> --cap <n>
<roots…>`. The roots, in `Q/probe/ProbeQ5/Lower.lean` (compiled, its two `#guard`s pass):

- `ProbeQ5.canonFields`: `ProbeQW.Ty.canon` at the record's field triple (insertion by `ltKey` on
  the UTF-8 bytes of the name, `nameKey s = s.toUTF8.data.toList.map UInt8.toNat`);
- `ProbeQ5.canonRecord` and `canonRecordVal`: R's row 165, a record value `ctor 0 [list names, list
  values]` with its names sorted and the values carried in step (`(canon (names.zip
  values)).unzip`), over `Effect4.Store.Val`;
- `ProbeQW.Ty.sub` itself, because today's `Ty.sub`, `normalize`, `normalizeRow` and `members` are
  in the closures of `ocaml/gen/api_gen.ml` and `ocaml/engine/api_engine.ml` (16 `Ty`
  declarations in each closure manifest; none in `fibers_gen`'s or `machine_gen`'s; tested by
  `grep` of the four `closure-*.tsv`), so the wave's `sub` is lowered by `make gen-lcnf`.

Run (`Q/logs/gen/lcnf-canon.log`, exit 0): **36 declarations, 0 missing mono declarations,
0 todos, `Ml.checkModule: PASS`**; types in full `Store.Val`, `ProbeQW.Ty`,
`Ty.Variance`. Read in the output (`Q/generated/lcnf/canon_gen.ml`): `nameKey` lowers through two
existing builtin rows, `String.toUTF8 → lcnf_utf8_bytes` and `ByteArray.data → identity`
(`src/OCaml5/Lcnf/Translate.lean:215-216`); `ltKey` is `Nat` comparison; `insertField` and the
`foldl` are translated from their own mono declarations; the paired sort adds only the mono
declarations of `List.zipWith`, `List.unzipTR` and (reading the frame back) the `mapM` and `mapTR`
loops, so **neither sort needs a new extern**, the brief's question and R's. The lowered `ty` has the shape EffGen's types would have
(`Ty_record of (string * (ty * bool)) list`, `Ty_tuple of ty list`, `Ty_app of string * ty
list`): EffGen's `projectShape` (`src/OCaml5/Eff/World.lean:105-118`) maps `List`, `Prod`,
`String`, `Bool` and a selected nominal already (reading), so **EffGen needs no change** for the
wave's fields.

**But `ocamlopt` refuses the file (tested).** `dune build` on it (`Q/ocaml/lcnf/`, via `opam exec
--switch=effect4`, `Q/logs/gen/lcnf-canon-dune.log`): "`Unbound record field to_list`" at
`canon_gen.ml:601`, `let as_ = ({ to_list = l } : _ array)`. It is `List.zipIdxTR`, which the
wave's `sub` reaches through its `app` arm (`xs.zipIdx`, the form the view's arm lemma reads, Q2):
its mono declaration builds `Array.mk l`, the translator renders a structure constructor as a
record (`Translate.lean:618-621`), and the Array-as-list shim (`Types.lean:61`, the rows at
`Translate.lean:240-245`) has no row for the constructor. The translator's own check passes it.
**Repair (on a copy, `Q/patches/Translate-array-mk.patch`, +4/−0, clean):** in `ctorApp`,
`Array.mk l` is `l`. With it (`Q/generated/lcnf/patched/`, `lcnf-canon-patched.log`) the file
builds (`lcnf-canon-patched-dune.log`), and an executable over 18 vectors (two sorts, one record
value, fifteen `sub` pairs: the leaf edges both ways, `undefined ⊑ unit`, record order and the
optional flag, map key invariance, tuple arity, `app` at a declared, an undeclared and a different
name) prints **exactly what Lean prints** (`Q/probes/Q5/LowerVectors.lean`,
`Q/ocaml/lcnf/canon_check.ml`; `diff` exit 0, `Q/logs/probes/Q5-agree.log`). The alternative,
writing the `app` arm without `zipIdx`, changes the form the generated view reads; the row is the
smaller change and covers every later `zipIdx`.

**A tool fact, and an incident.** `LcnfGen` writes its closure manifest to the fixed path
`ocaml/gen/closure-<stem>.tsv` whatever `--out` says (`src/OCaml5/Tools/LcnfGen.lean:182`). The
first run therefore wrote `ocaml/gen/closure-canon_gen.tsv` (a new, untracked file); it was moved
at once to `Q/generated/lcnf/closure-canon_gen.tsv` and `git status` under `ocaml src generated
tools Test scripts` was empty after. The later runs used a copy that writes the manifest beside
`--out` (`Q/patches/LcnfGen-manifest-beside-out.patch`, +2/−1; a convenience for redirected runs,
not needed by the tree's own).

### The mirrors: the exact arms, measured on copies (tested)

| Mirror | Copy | The wave's arms | Result |
| --- | --- | --- | --- |
| `OCaml5.Eff.tyO`, `tyV`; `ProfileJson.tyJson`; `LcnfMl.tyT`, `tyOcaml`; `LcnfSemantics.tyValue` | `Q/probes/Q5/Mirrors.lean` (the twenty arms copied, the eight added over `ProbeQW.Ty`) | 12 lines per mirror: `map` and the four leaves one line each, `tuple` and `app` one line each through `attach`, `record` five lines | compiles with warnings as errors (`Q5-mirrors.log`) |
| red control: `tyV` with the record arm written as the other list arms (`attach` alone, no `have`) | `Q/red/MirrorTyVNoHave.lean` | | refused, "fail to show termination" with the goal `sizeOf t < 1 + sizeOf fs` (`Q5-red-mirror-no-have.log`, exit 1 as expected) |
| `e4_program.ml`'s `of_ty` | `Q/ocaml/mirrors/of_ty_copy.ml` | 8 arms (`List.map` through the field triple), the count `= 28` | builds; the identity instance returns every one of 5,000 samples unchanged (`Q5-ocaml-mirrors.log`) |
| `prop_wire.ml`'s `rand_ty` | `Q/ocaml/mirrors/rand_ty_copy.ml` | 28 arms, leaves first (`ri 14` at depth 0) | builds; draws all 28 constructors in 5,000 samples |
| the text `tyO` and `tyOcaml` print for a wave sample | `canon_check.ml`'s two `let _ : ty = …` | | type-checks against the lowered `ty` (`Q5-mirror-text-dune.log`) |

The record arm's termination evidence is the field-size lemma (`sizeOf_field_lt`, here in
`Q/probe/ProbeQW/Ty.lean`): it must live in the core, not in the `Laws` graph, since `OCaml5`,
`Tools` and `Conform` import the core (reading of the root rules in `AGENTS.md`). The string arms
of `tyOcaml` keep the tree's form, `"\"" ++ n ++ "\""` with no escaping: a field name with a quote
inherits the open defect `handle` and `lit` already have there.

### The producers the append reaches, in the fixed order (reading GENERATED.md's inputs column, Makefile:68-212; tested where marked)

| # | Producer | Reached? | Outputs that change |
| --- | --- | --- | --- |
| 0 | `variances` (`make gen-variances`) | yes, by its hand head list and (with Q2's patch) the rules table | `tools/Effect4Gen/variances.json`; with the patch the core module (`Program/TyVariance.lean`) |
| 1 | `derived` (`make gen-derived`) | yes | the new `TyEq` group; `Program/Fold.lean`; `Laws/Program/TyView.lean`; `Store/Domain/Derived/Program.lean` (`TyC`, eight shape rows, tested in Q3) |
| 2 | `lcnf`, by name (`make gen-lcnf`) | yes (tested: 16 `Ty` declarations in each of the two API closures) | `ocaml/gen/api_gen.ml`, `ocaml/engine/api_engine.ml` and their two closure manifests (the engine cut is the slow one, 14 m 38 s by the Makefile's note) |
| 3 | `eff` (`make gen-eff`) | yes (tested on history: 9 of `0a2cb898`'s files) | `eff_{types,wire,json,layout}.ml`, `eff_manifest.txt`, `program-structure.json`, `goldens/metadata.tsv`, `goldens/coverage-metadata.txt`, `e4_program_layout.{ml,json}` |
| 4 | `wire` (`make gen-wire`) | yes (tested on history) | `ocaml/goldens/eff/manifest.txt`, `wire-tags.txt`; no `.hex` vector |
| 5 | `cas` (`make gen-cas`) | inputs not reached (no CAS golden moved in either previous append, C1) | none expected; run in order so the check proves it |
| 6 | `ts` (`make gen-ts`) | yes (tested on history) | `ts/eff/eff.gen.ts`, `json.gen.ts`, `wire.gen.ts` |
| 7 | `readme` (host producer, `bun`) | no: `README.md`, `profile.gen.ts`, `forms.gen.ts`, `taxonomy.gen.ts` spell no `Ty` constructor (tested, `grep`) | none, unless a profile row's type uses a wave constructor |
| — | `make corpus` (a promoted projection outside `make gen`) | must run | `generated/corpus-index.tsv`, the verdicts the conservativity check's C3 reads |

---

## The `Val` append (T's commit 3), measured

On a copy of `src/Effect4/Store/Carrier/Val.lean` (`Q/probe/ProbeQV/Val.lean`, namespace
`ProbeQV`, every change marked `seat Q`): `int (i : Int)` with tag 13 (a sign byte, 0 for `ofNat`
and 1 for `negSucc`, then the magnitude's digits, the `nat` frame's rule) and `float (bits :
UInt64)` with tag 14 (the binary64 bit pattern, eight bytes big-endian, `be64`).

- **The codec module (tested, proved).** The tree patch is `Q/patches/Val-two-frames.patch`,
  **+138/−7** (non-blank lines; `git apply --check` clean): two tags and two `Code` rows; two
  constructors; arms in `render`, `encode`, `tag`, `payload`, `WF`, `wf`, `beq`; the eliminator's two
  premises; one case each in `encode_eq`, `wf_iff`, `WF_payload_lt`; two dispatch branches with their
  `rfl` equations; two cases of `decodeBody_encode`; two hypotheses of `decodeBody_unknown`; two
  blocks of `decodeBody_exact`. Every law keeps its statement: `decode_encode`, `decode_exact`,
  `encode_injective` `[propext, Quot.sound]`, `beq_iff` `[propext]`, `ind` none
  (`Q/logs/probes/ValAppend-frames.log`). Guards: the frames' bytes (`int 5` is `13, len 2, 0, 5`;
  `int (-1)` is `13, len 1, 1`; `float 1.0` is `14, len 8, 3F F0 0…`), round trips of seven values,
  and three refusals (a sign byte 2, a leading zero digit, a seven-byte binary64); `nat 256` keeps
  the tree's bytes. Old readers refuse the new tags (`decodeBody_unknown`).
- **The `Val` groups regenerated once (tested).** `ValFold` (`tools/Effect4Gen/Fold.lean`): on
  today's `Val` the unmodified tool writes `src/Effect4/Store/Carrier/Fold.lean` but for the `--out`
  path in its header (`Q/logs/gen/today-ValFold.log`), and byte for byte with `--header-out` (the
  `elim`-patched tool, `gen/commit2-ValFold-today.log`, reproduced); on the copy it adds 36 lines
  (`val_int`, `val_float`, their `cata` equations, hom fields and cases; `diff`, the header's lines
  aside) and builds (`build/V-Fold.log`). The
  `Value` group's tool (`Main.lean`, unmodified) writes the copy's canonical image with `int` and
  `float` as constructors 12 and 13 over `Canonical Int` and `Canonical UInt64` (53 diff lines
  against today's, 5 of them the header; `gen/V-ValC.log`), which builds (`build/V-ValC.log`; `instCanonicalVal`
  `[propext, Quot.sound]`). Q1's `elim` kind regenerates the eliminator, equality and `Repr` with
  the two frames (`Q/generated/QCheckV/ValElim.lean`, builds).
- **The eight `fold_of` registrations over `Val` that live in the codec module** (`render`, `encode`,
  `tag`, `handles`, `beq`, `WF`, `wf`, `payload`; `src/Effect4/Laws/Store/Folds/Val.lean:26-38`)
  **re-derive unchanged** on the copy, including the arms that split on `Int`'s constructors
  (`Q/probes/ValAppend/FoldOfVal.lean`; `encode.hom` no axiom, `WF.hom`, `payload.hom`, `beq.hom`
  `[propext, Quot.sound]`).
- **Outside the module (reading).** Of the 16 compile-forced definitions over `Val` (the gate at the
  base, `Q4-ExhaustiveTy-count.log`), the six in `Val.lean` are measured above, `ValC.toValVal`,
  `cata_val`, `foldMap_val` are generated, and `printIn` (`Store/Domain/Shape.lean:383`) needs two
  hand arms (how a shape printer shows a signed and a binary64 frame as JSON: a decision). The 162
  definitions with a catch-all over `Val` refuse the new frames by default, which is right for the
  decoders (`*.ofVal`, `raw*`); the ones that must accept them are `Program.Val.hasTy` and
  `Typed.Fits` (an `int` or `number` member), `Schema.Codec.encodeRaw`, `Store.acceptsAt`, and the
  machine's value helpers, each coupled to commit 4's arms.

**The finding that matters for the ruling: both images already exist (reading).** `Canonical Int`
is `ctor 0 [nat n]` / `ctor 1 [nat n]` with its exactness proved (`Store/Domain/Canonical.lean:357-393`),
and `Effect4.Float64` (the binary64 bit pattern, `Data/Json.lean:136`) is `ctor 0 [UInt64]` in the
generated JSON group (`Store/Domain/Derived/Json.lean:26-77`). Schema's literal values already store
both through them (`Store/Domain/Derived/Schema.lean:200-215`, `number` and `bigint`). So:

- **(a) no `Val` append** (recommended): signed and binary64 values ride the existing images; the
  codec, the `Val` groups and every stored byte are unchanged; commit 4's `hasTy`/`Fits` arms for
  `int` and `number` read those images; LCNF `Int` builtins and floats in OCaml are needed either way
  (T's rows, unaffected);
- **(b) frames, and `Canonical Int`/`Float64` re-pointed to them**: the measured cost above, and the
  bytes of every stored `Int` or `Float64` change (Schema literals included), a named promotion the
  conservativity check's C1 would list file by file;
- **(c) frames without the re-point**: two encodings of one number (`int 5` and `ctor 0 [nat 5]`), so
  "one byte string per value" fails across carriers; refuse.

The choice is the owner's (rows 121 and 109). With (a), T's commit 3 is empty.

---

## Q6. Conservativity (DI-47, R3.8): the check as one command

**Today's instrument (tested, reading).** The comparator was deleted at `243ca0dd` (its message: "the
compatibility lane (`tools/Compatibility`, script, library, test)" deleted; `scripts/` has no
`check-compatibility*` and the Makefile no `check-compat` today). What remains: the frozen baseline
(`Test/fixtures/baseline/66ee4657/`, its supplement, and the policy file
`66ee4657-supplement-v1.policy.json`, whose comment still names `make check-compat`), and the mirror
census, which reads the baseline. At the base the full conform audit is **234 subjects, 228 pass, 3
counterexamples, 3 unresolved, exit 2** (`Q/logs/probes/Q4-audit-base.log`): the counterexamples
are the frozen baseline's `Ty` lists ("absent from the artefact: lit, refOf, deferredOf, var,
unknown", in `families.json` and `eff_manifest.txt`) and its `Eff` list, which predate the
appends; the unresolved are the three declared holes (`rand_ty`, `typeName`, the engine's name
list). So the census is red at the base by construction and cannot by itself say that an append
was conservative. The policy file names `Ty.lit` and no later `Ty` constructor.

**The check** (`Q/check-conservativity.sh BASE [CAND] [--strict]`, the clauses in
`Q/bin/conservativity.py`'s docstring; CAND a revision, or the working tree when omitted). It reads
committed files only (git blobs, or the candidate's files), runs no producer and no build, so it is
the step after the producers of the append commit:

- **C1 goldens**: every byte vector at BASE (`.bin .json .ty .hex` under `ocaml/eff/goldens`,
  `ocaml/goldens/eff`, `ocaml/engine/cas/goldens`, and every file of the
  `Test/fixtures/baseline/<commit>/` directories: 295 at the base) is byte-identical in CAND, unless
  CAND's policy names it (`vector_migrations`, `vector_removals`); new vectors are listed.
- **C2 alphabets**: in `wire-tags.json` every BASE row keeps its tag, no tag is given twice, a row
  leaves the active set only into `retired` under a policy name, and no key is given twice inside
  one object; in the three generated manifests (`ocaml/eff/eff_manifest.txt`,
  `ocaml/goldens/eff/manifest.txt`, `ocaml/goldens/eff/wire-tags.txt`) every BASE family line is a
  prefix of CAND's, names and argument shapes, so an existing constructor is neither moved nor
  re-typed.
- **C3 verdicts**: every BASE row of `generated/corpus-index.tsv` (Lean's `wellTyped`/`readable` per
  program), `ocaml/eff/goldens/corpus.txt` (the golden programs' typing verdicts) and
  `harness/truth/corpus-results.tsv` (the host lane, as committed) is in CAND unchanged (862 rows at
  the base); the golden tables keep every BASE line in order (`metadata.tsv`, `cases.txt`, the CAS
  manifest, `same-programs.txt`) and the coverage tables every BASE key at a count no smaller.
- **C4 policy**: every constructor added or retired between BASE and CAND (read off `wire-tags.json`)
  is named in CAND's policy file; reported, refused only with `--strict`: the additions since the
  frozen baseline that the policy does not name.
- **C5 record**: `git diff --stat` of the Makefile's `GENERATED_PATHS` (61 entries, expanded from the
  Makefile) between BASE and CAND.

**Runs (tested; logs under `Q/logs/probes/`).**

| Run | Result |
| --- | --- |
| zero control, `bff50631 bff50631` (`Q6-zero-base-base.log`) | **PASS**, 4 of 4: 295 vectors, 21 tag families, 3 manifests, 862 verdict rows unchanged; C4's report: 4 constructors appended since the frozen baseline and never named, `Ty.refOf`, `Ty.deferredOf`, `Ty.var`, `Ty.unknown` |
| zero control against the working tree, `bff50631` (`Q6-zero-base-worktree.log`) | PASS, the same |
| `--strict` at the base (`Q6-zero-base-strict.log`) | REFUSE on C4 (the four), exit 1 |
| history: the `unknown` append, `0a2cb898^ 0a2cb898` (`Q6-history-unknown.log`) | C1–C3 PASS (no vector moved, `unknown` appended last, no verdict moved); **C4 REFUSE**: `Ty.unknown` not named; C5: 15 generated files, +45/−9 |
| history: `7db30c8a^ 7db30c8a` (`refOf`, `deferredOf`, `var`; `Q6-history-refOf.log`) | C1–C3 PASS; **C4 REFUSE**: the three not named |
| the controls, `--self-test` (`Q6-self-test.log`; fixtures `Q/fixtures/conservativity/mutations.json`, applied to a scratch extract of the base) | **10 of 10 as expected**: R1 a golden byte flipped (C1); R2 a frozen baseline file edited (C1); R3 a constructor moved in a manifest (C2); R4 a constructor re-typed (C2); R5 a new constructor reusing a tag (C2); R6 a corpus verdict moved (C3); R7 a golden program's verdict moved (C3); R8 an appended constructor the policy does not name (C4); R9 a tag key given twice in one object (C2); G1 the wave's eight appended, named, manifests extended, a metadata row inserted: PASS |

The green control was refused by the first version (8 of 9 then): C1 froze the policy file itself,
which sits beside the baseline directories and is the one file an append must change. C1 now
freezes only the `<commit>/` directories, C4 judges the policy, and its diff is the review event
(the 8-of-9 log was overwritten by the rerun; the change is C1's file filter in
`conservativity.py`).

**What it cannot see** (bounded). It judges files, so the producers must have run: commit 4 runs the
fixed order and `make corpus` first (Q5's table); `harness/truth/corpus-results.tsv` is the host
lane and is only compared as committed (host-only); `Test/Program/TypedCorpus.lean`'s pins are
judged by its build, not by this script. C4 is a comparator against the baseline policy, which the
owner deleted with the compatibility lane as testing bloat on 2026-09-19 (AGENTS.md: "no comparator
runs against" the baseline); the check reads the policy, not the reflected descriptions, and makes
the refusal optional (`--strict`). Whether the wave's first alphabet commit names the four stale
`Ty` constructors in the policy (a promotion, a review event) is the owner's call.

---

## Q7. The size, measured

`0a2cb898` (`unknown`): **44 files, +1,192/−488** (tested, `git show --stat`); `7db30c8a` (`refOf`,
`deferredOf`, `var`, three constructors): 43 files, +700/−238, of which a meta-estate refactor is
about a quarter (12 files: the `Laws/Auto` and typed-state emitters). Every file of `0a2cb898` by area, with whether
it recurs in the wave's `Ty` append (T's commit 4), and every file born since that restates or pins
the alphabet, are in `Q/generated/q7/append-files.tsv` (one row each, the reason in the row); the
counts come from it (`Q/logs/probes/Q7-count.log`, tested; the "recurs" marks are reading).

| `0a2cb898`'s 44 by area | Files | Recur in the wave |
| --- | --- | --- |
| core (`Ty`, `Typed`, `Checker`, `Eff`, `Admission`, `Blame`, `Diagnostics`, `Codegen/Types`, `Bridge`, `Codec`; `Program/Derived.lean`) | 11 | 10 (`Program/Derived.lean`'s `Ty` content is generated since) |
| laws (`TypeAlgebra`, `Typed`, `CheckInversion`, `CheckSound`, `HasTy`) | 5 | 4 (`Laws/Program/Typed.lean`'s part moved to `Typed/Membership.lean`) |
| generated (Fold; eff ×9; wire ×2; ts ×3) | 15 | 15 |
| hand mirrors (`tyO`, `tyV`, `Metadata`, `tyT`/`tyOcaml`, `tyValue`, `tyJson`, `of_ty`) | 7 | 7 (8 with `rand_ty`, which `unknown` skipped) |
| tables (`wire-tags.json`, `cases-policy.json` at +954/−423) | 2 | 2 |
| test (`Test/Counterexamples/Schema/Codec.lean`, the codec's refusal by name) | 1 | 1 |
| docs (`DESIGN-ISSUES.md`, `decisions.md`, `language-cut.md`) | 3 | the two registers |

Born since `0a2cb898` and recurring (19): generated 8 (`Laws/Program/TyView.lean`,
`Store/Domain/Derived/Program.lean`, `variances.json`, the two LCNF outputs and their two closure
manifests, `e4_program_layout.ml`); laws 3 (`Typed/Membership.lean`, `Template.lean`,
`Admits.lean`); the head map `tools/Tools/Variances.lean`; tests 7 (`guards/tyview.lean`,
`TyViewContract.lean`, `ValueMembership.lean`, `TraversalFixture.lean`, `ExhaustiveFixture.lean`,
`TraversalCensus.lean`, `TyVectors.lean`). Touched by the wave and by neither earlier append (5):
`Program/TyCore.lean` (the
declaration moved, Q1), the generated `Program/TyEq.lean` and `Program/TyVariance.lean`, the
baseline policy file (C4), `prop_wire.ml` (or the generated `eff_rand.ml`).

**The wave's `Ty` append touches 63 files plus the 2 registers** (tested count over the table):
25 generated, 38 by hand (11 core, 7 laws, 8 mirrors, 4 tables, 8 tests). That is one commit for
eight constructors against 44 for one: the generated half and the tables do not grow with the
constructor count, and the hand half grows in lines, not files (each mirror +12 lines, Q5). With the
cut-over table of Q4 applied, the 8 mirrors and the policy become generator outputs or deletions,
and the two pins leave the list. The `record`, `map` and optional-modifier question of the brief
reads the same file by file: every recurring file recurs for `record` (a head with a child list),
the ones that hold per-head content for `map` as for any two-child head, and the optional modifier
is a payload of `record`'s field triple with no file of its own (the `sub` arm, the view's head
payload, the mirrors' triple and the `TyEq` position for `Ty × Bool`). The generator commit (T's
commit 2) is separate: `Fold.lean`, `View.lean`, `Variances.lean`, `FoldOf.lean`, `Translate.lean`,
the audit driver, `manifest.json` and the `Makefile` (8 files).

---

## Proposed decisions rows (for the coordinator's register; this seat edits no register)

**Generator row (row 119's "generated, not hand-written a third time", extended to variable
arity).** "The eliminator, the computational equality with its iff and instance, and the `Repr` of
a nested one-member family are emitted by the fold generator's `elim` kind
(`tools/Effect4Gen/Fold.lean`, the manifest's `Kinds`), into a module between the declaration and
its functions (`Program/TyCore.lean` → generated `Program/TyEq.lean` → `Program/Ty.lean`); the
derived `DecidableEq` and `Repr` of `Ty` are removed. The view generator (`View.lean`) reads three
variable kinds (a field list whose names and modifiers are head payload in canonical order; an item
list whose length is the head; an applied head whose arguments take the named declaration's
variances), each with an arity word in `variances.json` (`each`, `byName`); it computes its
dispatch case numbers; and it reads the order's exceptional rules from one table, `variances.json`'s
`rules` (the five structural cases in `sub`'s order, then the declared leaf edges, today's literal
rule among them), which the variances producer also writes into the core as `Ty.edgeRule` beside
`Ty.Variance`, `declaredVariance` and `argVariance`. A new edge is a row; the producer refuses a
table that is not transitively closed. The laws: `sub_eq_args` gains the edge disjunct, the
different-head theorem becomes `sub_eq_edgeRule_of_not_sameHead`, `edgeRule_trans` and
`edgeRule_eq_true` are emitted, `eq_of_sameHead` and `argsBelow_antisymm` gain the canonical-head
premises. `fold_of` gains a product position and a sibling over `List (A × M)`. On today's `Ty`
every producer writes today's bytes. Evidence: `docs/research/2026-10-01-type-language-probe/Q/`
(reproduced, tested, proved; the sibling extension assumed)."

**Conservativity row (DI-47's instrument, R3.8).** "An alphabet commit runs, after its producers and
`make corpus`, `scripts/check-conservativity.sh <base>` (seat Q's check): goldens byte-identical
unless the policy names them, tags and manifests append-only, every corpus and golden verdict
unchanged, every addition and retirement named in the baseline policy; the generated diff
recorded. The policy is promoted once to name `Ty.refOf`, `Ty.deferredOf`, `Ty.var` and
`Ty.unknown`, appended since the comparator's deletion and never named; whether the frozen-baseline
report refuses (`--strict`) is the owner's." Recommendation: adopt, with the promotion in the
wave's first alphabet commit and `--strict` on from then.

**The `Val` append (amends rows 121 and 109).** "Signed integers and binary64 numbers use the
existing exact images (`Canonical Int`: constructors 0 and 1 over `nat`; `Float64`: constructor 0
over the `UInt64` bit pattern); no `Val` frame is appended." Recommendation: (a) above; the frames
are measured (+138/−7 and the regenerated groups) if the owner wants them, with the re-point as a
named byte promotion.

**The cut-over of the per-constructor tables (the owner's steer, as a row).** "`cases-policy.json`
is regenerated by `--seed-policy` with its notes kept, in the commit that changes the code, and
reviewed by its diff; `LcnfMl.tyOcaml` is deleted for `TValue.render ∘ tyT`; `of_ty` goes with the
runner plan's step 1 or is emitted by `generate-engine-structure.py`; `rand_<family>` is emitted
into the eff group; `tyO`, `tyV`, `tyT`, `tyValue` become one interpreter over the canonical image
and the family description, `tyJson` a derived tagged-JSON group; the exhaustive fixture and its
census pin are re-pointed at a fixture-local inductive; `wire-tags.json` and the variance head map
stay hand authorities." Recommendation: adopt the first three in the wave; the emitters as their own
slice (seat U's measurement decides their shape).

---

## Brief text for the data wave

The synthesis numbers the generator extensions 3 and the `Ty` append 4 (§7); seat T's series numbers
them 2 and 4 and puts the `Val` append at 3 (`T/note.md` §2.6). Both are given.

**T's commit 2 (the synthesis's commit 3): generator extensions for nested families of variable
arity.** "Base: the coordinator's integration head. No `Ty` change. Apply, from
`docs/research/2026-10-01-type-language-probe/Q/patches/` (each `git apply --check` clean at
`bff50631`): `Fold-elim.patch` (`tools/Effect4Gen/Fold.lean`, +355/−1: the `elim` kind),
`View-variable-arity.patch` (`View.lean`, +713/−48: the variable kinds, the computed dispatch, the
rule table and edge laws; it contains `View-namespace.patch`'s change),
`Variances-commit2-mechanism.patch` (`tools/Tools/Variances.lean`, +148/−2: arity words, the rule
type, its closure check and writer, the core module writer, with today's head list and an empty rule
list, the section omitted when empty; the wave's data rows, the rest of
`Variances-variable-arity.patch`, land in commit 4), `FoldOf-prod.patch`
(`src/Effect4/Program/FoldOf.lean`, +28/−1), then write
`fold_of`'s sibling over `List (A × M)` (Q3, assumed 60 to 120 lines), `Translate-array-mk.patch`
(`src/OCaml5/Lcnf/Translate.lean`, +4) and `Audit-seed-keeps-notes.patch`
(`tools/Conform/Cli/Audit.lean`, +14/−1). Leave `variances.json` without a `rules` section and
`manifest.json` without the `TyEq` group in this commit, so every producer writes today's bytes:
`LEAN_NUM_THREADS=1 make gen-variances gen-derived` and `git diff --exit-code` over
`GENERATED_PATHS` (reproduced with the patched copies: `Q/logs/gen/today-TyView-patched.log` for
the view, `commit2-variances-today.log` for the producer, `commit2-Fold-today.log` and
`commit2-ValFold-today.log` for the `elim`-patched fold generator, each byte for byte). Keep as fixtures: the `elim` kind's
refusals of a family with no nested position and of a parameterised family, the view's refusal of a
variable head with no arity word, the producer's refusal of an unclosed edge table, `fold_of`'s
refusal of a pair position before the patch (`Q/probes/Q3/FoldOfScan.lean`), and the LCNF
lowering of `List.zipIdx` (`Q/probe/ProbeQ5/Lower.lean`'s roots: `dune` refuses the unpatched
output). Narrow builds: `lake build Effect4.Program.FoldOf` and the modules importing it; `lake env
lean` each changed tool once; `make check-cases`."

**T's commit 3: the `Val` append, only if rows 121 and 109 rule frames.** "If the owner rules (a),
nothing: commit 4 reads the existing images. If (b): apply `Val-two-frames.patch`
(`src/Effect4/Store/Carrier/Val.lean`, +138/−7), add `printIn`'s two arms
(`Store/Domain/Shape.lean:383`), re-point `Canonical Int` and `Float64` at the frames, regenerate
the `Value` and `ValFold` groups once (`make gen-derived`), and run
`scripts/check-conservativity.sh <base>`: C1 lists every stored `Int` and `Float64` vector, which
the policy names as migrations before the commit; the eight `fold_of` registrations over `Val`
need no edit (tested)."

**T's commit 4 (the synthesis's commit 4): the producer runs, in order.** "Before the producers:
the eight rows appended to `tools/Effect4Gen/wire-tags.json` (tags 20–27); the head rows
(`record`, `tuple`: `each`; `app`: `byName`; `map`: `[inv, co]`) and the `rules` section (the five
structural rows, `lit ⊑ string`, `undefined ⊑ unit`, `nat ⊑ int`, `int ⊑ number`, `nat ⊑
number`) in `tools/Tools/Variances.lean` (the data rows of `Variances-variable-arity.patch`); the `TyEq` group first in `manifest.json` with
`Kinds: ["Effect4.Program.Ty=elim"]`, `DERIVED_OUT`/`DERIVED_TRACES` in the `Makefile`; the policy
file naming the eight (and the four stale `Ty` constructors, if the owner promotes them). Then, one at a time with `LEAN_NUM_THREADS=1`:

    make gen-variances     # variances.json and the core Program/TyVariance.lean
    make gen-derived       # TyEq (new), Fold, TyView, Program (TyC)
    make gen-lcnf          # by name: api_gen.ml, api_engine.ml and their closure manifests
    make gen-eff           # eff_*.ml, eff_manifest.txt, program-structure.json, the metadata goldens, e4_program_layout.{ml,json}
    make gen-wire          # ocaml/goldens/eff/manifest.txt and wire-tags.txt; no .hex moves
    make gen-cas           # no change expected
    make gen-ts            # eff.gen.ts, json.gen.ts, wire.gen.ts
    make gen-readme        # no change expected (host producer)
    make corpus            # generated/corpus-index.tsv, the verdicts C3 reads
    lake env lean -M4096 --run tools/Conform/Cli/Audit.lean --config tools/Conform/Effect4/audit.json \
      --seed-policy tools/Conform/Effect4/cases-policy.json   # the policy re-seeded, notes kept
    make check-cases
    scripts/check-conservativity.sh <base>                     # C1–C4 PASS; C5 recorded in the receipt

Stop if C1, C2 or C3 refuses: an existing golden moved, an existing constructor moved or re-typed,
or a verdict changed. Every new constructor is refused by name in the codec, Schema and printer
until its own commit (the four codec covers gain the eight names). The consumers of the literal-rule
vocabulary (22 lines in 5 files, Q2) move to the edge vocabulary in this commit."

---

## Receipt

**The one thing first.** The generator extensions are byte-neutral on today's tree and can land
alone first; the LCNF translator needs a four-line row (`Array.mk`) or the wave's `sub` lowers to
OCaml that `ocamlopt` refuses; the conservativity check is one command (green at the base, 10 of 10
controls) and shows the baseline policy stale by four `Ty` constructors, which the owner must
promote or waive; the `Val` append is optional (the images exist).

- **Base** `bff50631`; **head** the commit that adds this note (parent `d3d0637d`), branch
  `probe/Q`, worktree `/Users/pooks/Dev/lean4-effect4-probe-Q`. Nothing pushed, merged or reset.
- **Commits** (all under `docs/research/2026-10-01-type-language-probe/Q/`, force-added):
  `7deff4e5` Q1, `703b9d33` Q3, `c4da1ffe` Q2 (record), `6f0e9d7a` Q1–Q3 on the wave, `97571cfa` the
  number-tower red control, `e36dabc3` the rule table, `6c2037a1` Q4, `2d22b4cb` Q5, `0394b6bc` Q6,
  `8994a1cf` the `Val` append, `1087b829` Q4 (notes kept), `6f77dd57` Q6 hardened and Q4's renderer
  comparison, `d3d0637d` the tree-path patches and Q7, then this note with the last red controls (the view
  without an arity word, the mirror without its termination evidence) and the commit-2
  reproductions (`Q/tools/Commit2/`, `Variances-commit2-mechanism.patch`).
- **Changed paths**: only this folder (tested: `git diff --stat bff50631..HEAD -- .
  ':!docs/research/2026-10-01-type-language-probe/Q'` is empty). No tracked file was edited.
  Patches (all `git apply --check` clean at the base): `Fold-elim` +355/−1, `View-namespace` +9/−5,
  `View-variable-arity` +713/−48, `Variances-variable-arity` +165/−1 (its mechanism alone,
  `Variances-commit2-mechanism`, +148/−2, reproduces today's table), `FoldOf-prod` +28/−1,
  `Translate-array-mk` +4/−0, `LcnfGen-manifest-beside-out` +2/−1, `Audit-seed-keeps-notes`
  +14/−1, `Val-two-frames` +138/−7 (non-blank lines).
- **Commands and results** (each log under `Q/logs/` starts with its command and ends with `#
  exit=… seconds=…`; one compiler at a time, `LEAN_NUM_THREADS=1`, `-DwarningAsError=true` on every
  probe):
  - generators: `Fold.lean` (`elim` kind) on `ProbeQ`, `ProbeQFull`, `ProbeQW`, `Store.Val`, `Json`,
    `ProbeQV.Val`: exit 0, outputs build; refusals as kept (`gen/red-*.log`); the view and variances
    copies on today's `Ty` reproduce the committed files byte for byte; on the families, outputs build;
    `gen/red-View-no-arity.log` exit 1 as expected;
  - Q4: `#exhaustive_gate` (`probes/Q4-ExhaustiveTy.log`); `make check-cases`'s configuration 174/174
    (`Q4-cases-base.log`); the full audit 234 subjects, exit 2 at the base (`Q4-audit-base.log`);
    `--seed-policy` (`Q4-seed-base.log`), with notes kept (`Q4-seed-keep-notes.log`, equal as JSON);
    the wire-tag loader probe (`Q4-wiretags.log`); `tyOcaml` against `render ∘ tyT` (7 of 21
    byte-equal);
  - Q5: `LcnfGen` on four roots, 36 declarations, 0 todos (`gen/lcnf-canon.log`); `dune` refuses the
    unpatched output, builds the patched one (`gen/lcnf-canon*-dune.log`); 18 vectors agree
    (`probes/Q5-agree.log`, diff exit 0); the six Lean mirrors compile (`Q5-mirrors.log`), the red
    control without the termination `have` fails as expected (`Q5-red-mirror-no-have.log`); the OCaml
    mirrors build and run (`Q5-ocaml-mirrors.log`: 28 of 28 drawn, identity holds);
  - the `Val` append: the copy builds (`build/ProbeQV.Val.log`), guards and axioms
    (`probes/ValAppend-frames.log`), `fold_of` (`ValAppend-foldof.log`), the three groups regenerated
    and built (`gen/V-*.log`, `build/V-*.log`), today's `ValFold` reproduced (`gen/today-ValFold.log`);
  - Q6: zero control PASS (`Q6-zero-base-base.log`, `Q6-zero-base-worktree.log`), strict REFUSE (C4),
    the two historical appends REFUSE on C4 only, self-test 10 of 10 (`Q6-self-test.log`);
  - Q7: `git show --stat` of `0a2cb898` and `7db30c8a`; the count over `generated/q7/append-files.tsv`
    (`Q7-count.log`).
- **Axioms**: every theorem printed is at or below `[propext, Quot.sound]`; none reaches
  `Classical.choice` or `sorryAx` (the build logs' `#print axioms` lines; Q1's, Q2's and the `Val`
  append's are quoted above). No `sorry`, `native_decide`, `partial`, `unsafe`, `simp_all`, `first |`
  or `try` was written in a probe that proposes production text.
- **Bounded and host-only.** Every Lean result is a finite probe on a copy of the family
  (`ProbeQ`, `ProbeQFull`, `ProbeQW`, `ProbeQV`), not the tree's declaration; the LCNF run lowered
  this seat's four roots, not the engine closure (the 15-minute engine cut was not run); `dune` ran
  only on this folder; the host lanes (`harness/truth/corpus-results.tsv`, the readme producer) were
  read as committed, not run; no `lake build` of any root.
- **Open obligations.** `fold_of`'s sibling over `List (A × M)` (assumed 60 to 120 lines); P's
  re-proof of `sub_trans_core` through the leaf edges, and the record cases of `Normal`; the emitters
  of Q4's table whose sizes are assumed (`rand_<family>`, the one interpreter for `tyO`/`tyV`/`tyT`/
  `tyValue`, the tagged-JSON group, the `Metadata` samples, `of_<label>` if kept); the seven
  catch-alls that wait on another seat's decision (Q4).
- **Decisions for the owner** (rows above): the generator row; the conservativity row with the
  policy promotion of the four stale `Ty` constructors and `--strict`; the `Val` append (a, b or c;
  (a) recommended); the cut-over of the per-constructor tables.
- **Incident.** `LcnfGen` writes its closure manifest to `ocaml/gen/closure-<stem>.tsv` whatever
  `--out` says (`LcnfGen.lean:182`); the first lowering run wrote `ocaml/gen/closure-canon_gen.tsv`
  (new, untracked). It was moved at once into `Q/generated/lcnf/`; `git status` under `ocaml src
  generated tools Test scripts` was empty after, and later runs used a copy that writes beside
  `--out`. A `PreToolUse` hook (the lean4 plugin's guardrail) refused one shell command for
  redirecting stderr to `/dev/null`; it was rerun without the redirection. No permission was refused.
