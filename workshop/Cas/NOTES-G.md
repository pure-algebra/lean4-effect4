# Lane G notes — the generator of `Canonical` instances

Running notes of lane G (the generator of the CAS-trait spike). One dated entry per
deliverable. General rules `BRIEF.md`; the lane's brief `BRIEF-G.md`; the oracle
`Cas/Templates.lean` and `Cas/Program.lean`, frozen by lane S1.

Lane discipline observed throughout: PowerShell only, backslash paths; no `git` command; no
`lake build`, `lake clean`, `lake update` or `lake exe` (lane S2 owns the machine's one build);
every probe `lake env lean -M 4096 <file>`, every run
`lake env lean -M 4096 --run workshop\Cas\gen\Main.lean …`, each with a ten-minute timeout.
Nothing written outside `workshop\Cas\gen\`, `workshop\Cas\Gen-out\`, `workshop\Cas\tools\` and
this file. No `lean.exe` came near the memory cap or the timeout: the slowest run so far is the
`Program` group's check at 12 s.

## 2026-09-05 ~01:20 — the tool: `workshop\Cas\gen\Main.lean`

`import Lean`, module `gen.Main`, outside the `Cas` library's glob (`lakefile.toml:35-40` roots
`Cas` at `workshop/Cas` with globs `Cas`, `Cas.+`), so a broken file of mine can never break
lane S2's build. It imports `Cas.Templates`, `Cas.Program` and `Effect4.Schema.Document` at
startup and reads the carriers out of that environment; it writes only the file named by
`--out`.

    lake env lean -M 4096 --run workshop\Cas\gen\Main.lean --group <G> --imports <M,…>
      --out <path> [--append <path>] <type>…

A `<type>` is a Lean type expression in one shell word: `@` reads as a space, so
`Effect4.Program.Eff@Effect4.Program.NativeOp` is the applied `Eff NativeOp`. (Parentheses are
supported too, but PowerShell's `Start-Process -ArgumentList` splits a spaced argument into two
argv entries, which is how the first `Eff NativeOp` run failed with a bare `Eff` and no
parameters — the `@` spelling exists so a script never has to fight the shell.)

### What it does

1. **Reads the block.** `getConstInfoInduct` on the head; `InductiveVal.all` gives the mutual
   block, each member applied to the requested arguments. Then a fixpoint: every applied
   *nominal* carrier appearing inside a constructor argument that mentions a member (and is not
   `List`, `Option` or `×`) becomes a member of the same block too, with its own name in `defs`
   and its own `.named` reference — that is how `ElementOf Representation` and kin join the
   `Representation`/`Check` block, since none of them can have an instance of its own before
   `Representation` does.
2. **Classifies every constructor argument** into a *slot*: another member; a *foreign* type
   (one with its own instance — `Nat`, `Option Term`, `Json`, an item emitted earlier in the
   same file); or a `List`/`Option`/`×` over something that mentions a member, which gets a
   companion function inside the block.
3. **Emits**, per item, in the house voice: `<m>Shape` per member, one `defs` table (the
   members by name, then the field types' `(shape F).defs` appended), `toVal…`, `raw…`,
   `raw…_toVal…`, `mem_…`, `lift_…`, `fits…` and the instances.

### The two proof shapes, and why only two

- **Recursive item** (any constructor argument mentions a member): `ofVal` is
  `guarded toVal raw` — lane S1's recipe (`Cas/Canonical.lean:250-273`,
  `NOTES.md` M4). `ofVal_toVal` is then `guarded_toVal _ _ a (raw_toVal a)` and needs only the
  left inverse, one mutual structural induction, one `simp [toVal…, raw…, …]` per constructor;
  `ofVal_exact` is `guarded_exact h`, free. `fits` is a mutual structural theorem:
  `accepts_named_of_mem` for the root, `acceptsAt_sum`/`acceptsAt_struct` per constructor,
  `acceptsFields_cons` down the fields, foreign fields lifted by a `lift_<F>` lemma built from
  `acceptsIn_mono_of_subset` and an explicit `List.Mem.tail`/`mem_append_of_left`/`_right`
  chain (never a string comparison, never `simp` on the table).
- **Non-recursive item**: the structural readers and S1's template scripts verbatim — the
  `first`-combinator script of `LitC` for a sum whose constructors take at most one argument,
  the bullet script of `Entry`/`ForkOptions` for a structure. Anything else falls back to
  `guarded`.

`toVal` is the same function under both, so the bytes are the same under both. The generated
`ofVal` of a recursive type is extensionally the hand `ofVal` of `Cas/Templates.lean` even
where the hand file reads structurally: both are exact readers of the same image, so each
returns `some a` exactly when the value is `toVal a`.

### Toolchain notes for whoever edits the tool

- `instantiateForall` did **not** substitute the block parameter into the constructor's binder
  types on this toolchain: `Eff.perform`'s first field came back as the free variable `Op` and
  `whnf` then failed with `unknown free variable`. The tool now runs `forallTelescope` on the
  raw constructor type, splits at `ConstructorVal.numParams`, and substitutes with
  `Expr.replaceFVars`. (A size mismatch there produces loose bvars and a `whnf` panic, so the
  tool checks `args.size = numParams` first and reports it.)
- Argument types are normalised with `withReducible (whnf …)`, so the abbreviations
  `Var := Nat` and `Annotations := Option (List AnnotationEntry)` reach the classifier already
  unfolded.
- A foreign type is printed **parenthesised** (`(_root_.Option (_root_.Effect4.Program.Term))`),
  because it stands as one argument of `shape`, of `Canonical.ofVal (α := …)` and of every
  binder; the first version emitted `shape _root_.Option (_root_.…)` and parsed as two
  arguments. Every emitted type is `_root_.`-qualified so `namespace Effect4.Store` cannot
  capture it.
- `s!"…{{…}}…"` does not escape a brace; the two `theorem ofVal_exact {v : Val} {a : T}`
  signatures are built with `++`.
- A `cases a <;> simp [toVal, ofVal, Canonical.ofVal_toVal]` over a sum with nullary cases
  trips `linter.unusedSimpArgs`; the emitted file disables that linter for that one theorem
  and says why.

## 2026-09-05 ~01:40 — acceptance against the hand oracle: `Json`, `Float64`, `Program`

Both groups regenerated into `Gen-out\` and compiled with `lake env lean -M 4096`, exit 0, no
error, every receipt at the ceiling.

    lake env lean -M 4096 --run workshop\Cas\gen\Main.lean --group Json --imports Cas.Templates
      --out workshop\Cas\Gen-out\Json.lean --append workshop\Cas\gen\guards-json.lean
      Effect4.Float64 Effect4.Json

    lake env lean -M 4096 --run workshop\Cas\gen\Main.lean --group Program --imports Cas.Program
      --out workshop\Cas\Gen-out\Program.lean --append workshop\Cas\gen\guards-program.lean
      Effect4.Program.Lit Effect4.Machine.FnName Effect4.FinalizerStrategy
      Effect4.Supervision.MaskMode Effect4.Supervision.ObserverMode Effect4.Program.NativeOp
      Effect4.Supervision.ForkOptions Effect4.Program.Term Effect4.Program.CauseTerm
      Effect4.Program.Eff@Effect4.Program.NativeOp

`--append` copies a hand-written guards file verbatim after the generated declarations and
before the receipts; the header names it, so a reader can tell the generated half from the
checked half. The guards import nothing: each generated file already imports the hand oracle
(`Cas.Templates`, `Cas.Program`), and the guards call the hand functions by name rather than
through the class, so the second instance in scope cannot answer for the first.

- `Json` (9 receipts): 1 `[propext]`-and-under group and the rest `[propext, Quot.sound]`.
  `Float64` is the structure script, `Json` the nested recursion (companions over
  `List Json` and `List (String × Json)` — a `×` companion the hand file inlines; both are
  structural and both take `termination_by structural`).
- `Program` (67 receipts): 45 in the plain scripts, 22 in the two recursive families.
  `Term`/`Terms` and the five-type `Eff NativeOp` block came out with the same shapes and the
  same `defs` order as the hand file, except that duplicate foreign tables are emitted once
  (`ForkOptions` lists `(shape Bool).defs` once, not twice — both are `[]`, so `accepts` and
  `document` are unchanged).

Guards that pass (`gen\guards-json.lean`, `gen\guards-program.lean`):

- tree identity with the hand instance: `ProgramGen.EffC.toValEff p = ProgramCanonical.EffC.toValEff p`
  on all eight corpus programs, and the same for `Lit`, `FnName`, `MaskMode`, `ObserverMode`,
  `FinalizerStrategy`, all twenty `NativeOp`s, `ForkOptions`, `Term`, `CauseTerm`;
  `JsonGen.JsonC.toValJson j = JsonCanonical.toVal j` on twelve `Json` samples including the
  facts note's, and `Float64` on five bit patterns;
- byte identity with `ocaml\goldens\eff\*.hex`: `genHex ProgramCanonical.Corpus.<p>` equals the
  golden for `p42`, `pBind`, `pFork`, `pAwait`, `pGen`, `pLoop`, `pCatch`, `pScope` (the hex
  literals are copied out of the golden files, not out of `Cas/Program.lean`);
- the facts note §6 receipts on the generated image: `p42` is 66 bytes and digests to
  `fa5f40f054198e91b2446522308e197b0a02c4edfe823f894763d3aa63ad62a3`;
- round trip and refusals through the generated reader: `decode (encode p) = some p` on the
  corpus, a byte appended refused, a byte dropped refused, a leading-zero constructor index
  refused (`Wire.lean:628` restated);
- shape: every corpus tree fits the generated `defs`, **and** fits the hand `defs`; every
  `Json` sample fits both.

One guard of mine was wrong on the first run and the compiler caught it: I had written the
`ctor` frame of `Json.str "A"` with payload length 21 instead of 20 (the `nat 3` tag frame is
ten bytes, not nine). The generated file was not touched; only the guards file was.

## 2026-09-05 ~02:20 — the real deliverable: the `Schema` group and `Canonical Document`

    lake env lean -M 4096 --run workshop\Cas\gen\Main.lean --group Schema --imports Cas.Templates
      --out workshop\Cas\Gen-out\Schema.lean --append workshop\Cas\gen\guards-schema.lean
      Effect4.ReferenceKey Effect4.GlobalSymbolKey Effect4.AnnotationEntry Effect4.LiteralValue
      Effect4.EnumValue Effect4.EnumEntry Effect4.PropertyKey Effect4.RepresentationAnnotation
      Effect4.UnionMode Effect4.Representation Effect4.ReferenceEntry Effect4.Document
      Effect4.MultiDocument

Green under `lake env lean -M 4096` in 14 s, 84 receipts, one with no axioms, 10 `[propext]`,
73 `[propext, Quot.sound]`, none other; no `sorryAx`, no `Classical.choice`. **`Canonical
Document` exists** (`SchemaGen.DocumentC.instCanonical`), and with it `Canonical
Representation`, `Canonical Check`, `Canonical MultiDocument` and the eleven leaf carriers.
The whole group needs only `import Cas.Templates`: `Cas.Canonical` → `Cas.Shape` →
`Effect4.Schema.Authoring` already drags in `Effect4.Schema.{Check,Document,Annotations,
Representation,Payload}`, so nothing new enters the environment and no old-store module can.

### The block the generator found by itself

`Effect4.Representation` and `Effect4.Check` are one mutual nested inductive with **two**
recursion edges (`FilterGroup.checks` and `Filter.representation.schemas`,
`Representation.lean:686-694`), and neither `ElementOf Representation` nor its three siblings
can have an instance before `Representation` does. The fixpoint in `blockMembers` pulls them
into the block automatically, so the emitted `defs` binds six names —

    Representation, Check, CheckRepresentationAnnotationOf, ElementOf,
    PropertySignatureOf, IndexSignatureOf

— and eleven foreign tables after them. Seven container companions come with it:
`List Representation`, `List Check`, `List (ElementOf …)`, `List (PropertySignatureOf …)`,
`List (IndexSignatureOf …)`, `Option (CheckRepresentationAnnotationOf …)` and
`Option (List Representation)`, the last two being the `Option` companions the `Filter` and
`FilterGroup` fields need. That decomposition is the same one `Representation.beq` reaches for
by hand (`Representation.lean:826-955`), which is the evidence that `termination_by structural`
can carry it: every one of the thirteen `toVal`s, thirteen `raw`s, thirteen `raw_toVal`s and
thirteen `fits` theorems is structural on this toolchain, first try.

Two generator bugs the group found, both fixed in the emitter and never in the output:

1. an `Option` whose payload is a `List` needs the nested pattern `.some (.list v)`, not
   `.some v` — the reader was passing a `Val` to a `List Val → Option …` companion. The
   argument pattern for a `list` slot is now `(.list v)` **everywhere** it is destructured: a
   constructor argument, an `Option`'s payload, a `×` component, a list element (with the
   catch-all clause that a nested pattern then needs).
2. the same pattern has to be parenthesised inside `.some (…)`; unparenthesised it read as
   `Val.some Val.list`.

### The acceptance guards for a group with no hand oracle

`gen\guards-schema.lean` makes the laws executable on real values instead: the `Document` that
`Cas/Shape.lean` derives for the census entry (`entryDoc.document`), a `Representation`
touching every awkward corner (an empty `$ref`, a bigint literal, a non-finite number literal,
a nested `FilterGroup` carrying a `schemas` list, a global-symbol property key, an index
signature, a duplicate reference key), and **the meta-schema** `Canonical.document Document`.
All pass:

- `decode (encode d) = some d` on five documents including the meta-schema;
- `(shape Document).accepts (toVal d)` on all five (`fits` made executable);
- a byte appended and a byte dropped refused on all five;
- the meta-schema is a fixed point: the spec of `Document` is itself a stored `Document`, with
  a 64-character address distinct from the entry spec's;
- `Representation`, `Check` and `MultiDocument` round trips; every constructor of
  `LiteralValue`, `EnumValue`, `PropertyKey`, `UnionMode`;
- `Annotations`: absence and a present empty bag keep different bytes (`Payload.lean:38`);
- the frame of `ReferenceKey.mk "A"` written out byte by byte.

Two of my hand-written byte guards were wrong before the compiler corrected them (payload
lengths 21 and 20 instead of 20 and 19); no generated file was touched to fix either.

## 2026-09-05 ~02:45 — the projection guard and the regeneration script

`workshop\Cas\gen\Check.lean` (`--run`, `import Lean`) re-derives every carrier's constructor
and field list from the environment and compares it with what the generated text says. It is
deliberately a *second* implementation: it reads the file, not the generator's intermediate
representation, and finds each carrier by its own search over `env.constants`, so the two have
to agree.

    lake env lean -M 4096 --run workshop\Cas\gen\Check.lean workshop\Cas\Gen-out\Json.lean
      workshop\Cas\Gen-out\Program.lean workshop\Cas\Gen-out\Schema.lean

What it compares, per shape: `struct` versus `sum`; the case names **in order**; each case's
field names **in order** and their arity; and the constructor index every `toVal` clause
writes, keyed by the member so that `Eff.fail` (index 1) and `CauseTerm.fail` (index 0) do not
answer for each other. It says `ok` per shape and exits 1 on the first difference. It agrees on
all **35** shapes of the three groups. It does not check field *types*, the proofs or the
bytes; those are the receipts and the acceptance guards.

The shape scan needs no parser: a field's shape is only `.named`, `(shape T).root`, `.list`,
`.option` or `.pair`, none of which contains a bracket, so the bracket depth alone separates a
sum's cases (depth 1) from their fields (depth 2), and a struct's fields (depth 1).

Refusal measured on three corrupted copies in the scratchpad (never on the real files):

| corruption | verdict |
| --- | --- |
| a case renamed `yieldError` → `yieldErrorX` in `EffShape` | REFUSED: shape "Eff" projects no carrier; no `toVal` clause for `Eff.yieldErrorX` |
| `toVal` writes `.ctor 4` for `Eff.yieldError` | REFUSED: `toVal` writes .ctor 4 for Eff.yieldError, which is constructor 3 |
| two fields of `ElementOfShape` swapped | REFUSED: shape "ElementOf" projects no carrier |

`workshop\Cas\tools\generate-derived.ps1` holds the manifest (group → imports, guards, carriers
in dependency order) and runs the tool once per group, hashing each file before and after:

    pwsh -File workshop\Cas\tools\generate-derived.ps1            # regenerate, report changes
    pwsh -File workshop\Cas\tools\generate-derived.ps1 -Check     # + compile each file, + the guard
    pwsh -File workshop\Cas\tools\generate-derived.ps1 -Verify    # + exit 1 if anything changed

`-Verify` is the landing's `git diff --exit-code` before the files are tracked. `-Check` also
counts the receipts and fails if any of them reaches `sorryAx` or `Classical.choice`. It never
runs `lake build`; every invocation is `lake env lean -M 4096` with a ten-minute timeout that
kills the `lean.exe` tree on expiry. Two consecutive runs report `changed: nothing`, so the
generator is idempotent on this environment.

### Open

- The emitted files still carry some long lines: a field entry whose shape is
  `(shape (_root_.Option (_root_.List (_root_.Effect4.AnnotationEntry)))).root` is 95 columns
  before its indent, and `_root_.`-qualification is what makes it so. 71 lines of `Schema.lean`
  and 8 of `Program.lean` pass 100 columns; the wrapping breaks at every separator it can. A
  per-group `open` prelude would fix it and is the obvious next improvement.
- `Cas/Templates.lean`'s `Templates.Entry`/`Templates.ExportKind` are not regenerated: they are
  declared inside `Cas.Templates` itself, so a generated file that redeclared them in the same
  namespace would collide with the oracle it is being checked against. Their shapes are the
  structure and all-nullary-sum scripts, both of which `Float64`/`ReferenceKey` and
  `UnionMode`/`MaskMode` exercise.
- The generator refuses a *bare* parameterised type (`Effect4.ElementOf` with no argument):
  every group here applies its parameters, and an instance binder `[Canonical α]` version was
  not needed. It is the one rule of `BRIEF-G.md` §"the rules the emitted code follows" that is
  unexercised.
- `termination_by structural` on an `Option`/`×` companion draws "unused `termination_by`,
  function is not recursive"; the block compiles and the warning is Lean telling us the
  companion did not need to join the recursion.

## 2026-09-05 ~03:00 — close

Final state, from `pwsh -File workshop\Cas\tools\generate-derived.ps1 -Verify -Check`:
`same` for all three groups (the generator is idempotent), `green` for all three compiles
(9 / 67 / 84 receipts), `the projection guard agrees (35 shapes)`, exit 0. No `lean.exe` or
`lake.exe` left running. `git status` shows only the coordinator's `lakefile.toml` hunk;
nothing of mine is tracked, and `workshop\Cas\Cas\` was never touched.

Receipt census over the three emitted files: 160 `#print axioms` lines — 5 with no axioms,
36 `[propext]`, 119 `[propext, Quot.sound]`, none other; no `sorryAx`, no `Classical.choice`.

As with lane S1, the tool harness refused to write `REPORT-G.md`; the report is delivered as
this lane's closing message to the coordinator. Its content is this file's five entries plus
the acceptance table and the command log above.
