# 2026-10-06 seat SKETCH design: a program with its hole table

Status: a design note (history, not authority). Brief:
`docs/research/2026-10-05-claude-lead/briefs/seat-sketch-brief.md`. Base: `ea0f584a`. It is
stage 1 of the study `docs/research/2026-10-06-seat-GAP-study.md`, under decisions rows 282 and
288. Lean elaborates each declaration below, and the kernel accepts each proof at
`[propext, Quot.sound]`, in the scratch file filed as
`docs/research/2026-10-06-seat-SKETCH-design-probe.lean.txt`. No file of the tree holds one yet.

## 1. The types, as Lean elaborates them

```lean
structure Sketch where                      -- a program with its hole table
  program : NativeEff
  holes : RowTable := []
instance : Coe NativeEff Sketch             -- a program is a sketch with no hole

SigApp.withHoles : SigApp → RowTable → SigApp    -- the hole table, after the application's rows
Row.hole : String → Ty → optParam Ty Ty.never → optParam (List ServiceKey) [] → Row
Sketch.hole : SigApp → Nat → NativeEff           -- hole k: perform (external (rows.length + k)) ()
Sketch.check : Sketch → optParam SigApp {} → Except TypeRefusal EffTy
```

`Row.hole name answer error requires` is a host row with a unit request and three declared
columns. `Sketch.check s app` is `Checker.check (app.withHoles s.holes).signature [] [] s.program`.

## 2. Three decisions

**What a sketch holds, and what its check answers.** A sketch holds its program and its hole
table, and nothing else. The application's tables are a parameter of the check, as they are of
`admitProgram` (`src/Effect4/Program/Admission.lean`). A session owns them, and a second copy in
each sketch could disagree with it. The check answers the checker's own answer: the type of
the program at the root, or the located refusal. "Admitted modulo its holes at `t`" is
`s.check app = .ok t`. The type shows that a program is a sketch in two ways. The hole table
has the default `[]`, and a program coerces to a sketch, as it coerces to a `ProgramSource`.
`Sketch.check_program` then says that the check of a coerced program is the checker's answer,
refusals included.

**How a hole is named: by its position in an append-only hole table.** `Eff` can write a host
row by its position only, so the stored name is the position `k`. No edit moves a position,
because the table only grows while the sketch is open. Declaring a hole appends a row, and H2
keeps the verdict. Filling a hole leaves its row in place, and H3 says that the checker no
longer reads it. A hole is given another type by declaring a new hole, as decisions row 210
re-types a wire constructor. So an edit keeps every other hole's position, row and occurrence.
The row's spelling is the label that the printer prints and that an author calls, as for every
host row (`Row.call`, `src/Effect4/Program/Authoring.lean`). A sketch is pinned to the row count
of its application, as a program is pinned to its table (row 115). Removing rows, or growing the
application's table under an open sketch, renumbers operations. Both wait for a consumer.

**The request of a hole row: a unit, in this slice.** The hole's rule then holds in every
environment, and the row does not change when the program before the hole changes. The tuple
of the variables in scope would change four things. The rule would hold only in an environment
below the declared request. The row would record the hole's environment, so the table alone
would answer what a filling can read. A waiting hole's frontier would carry the environment's
values. And an edit before the hole would make the row stale. The environment is the checker's
to compute (slice TRACE), so a row that stores it is a second owner. A hole that runs can derive
that request from the traced environment, when a run has a consumer.

## 3. Lean's own tools

A term-level notation can write a hole, in two steps. Neither is implemented here: the four
controls are written as data and do not pay for a notation.

1. **With no metaprogramming.** The authoring surface resolves a host row's spelling to its
   position already (`Row.call`, `Module.rowNames`). A hole written there is a call of a declared
   hole row, and the module's elaborator appends the hole table after the row table. It costs
   one field of `Module`.
2. **With the elaborator.** A term elaborator can elaborate an authored program in which each
   `?h` is a metavariable of type `NativeEff`. It then assigns each one `Sketch.hole app k` and
   returns the hole table, named by the metavariables. `proof_sketch` collects a script's open
   goals in the same way (`tools/ProofGraph/Sketch.lean`). Lean can place and name a hole. It
   cannot type one, because the three columns are data of our type language. So a hole carries
   its declaration, or it is declared at `never` (row 288, point 5).

The first consumer is a battery or a scenario that writes many sketches in Lean. A tool reads a
sketch as data and needs neither step.

## 4. The modules

- `src/Effect4/Program/Sketch.lean`: the five declarations of section 1, and the head comment.
  It is not a Lean module (row 200): it imports `Program/SigApp.lean`, which is not one, because
  `Program/Columns.lean` imports a specialization site of row 202.
- `src/Effect4/Laws/Program/Sketch.lean`: the statements of section 5.
- `Test/Program/SketchControls.lean`: the plan's example with a hole at `number`, and the three
  red controls of the study's section 9.7.

## 5. The statements

Each is stated once, at the typing signature of an application (`SigApp.signature`). The form
at a row table alone is its instance at `⟨t, []⟩`: `SigApp.signature_nil` is `rfl`, and a control
shows it.

```lean
-- a program is a sketch with no hole: the same answer, refusals included
theorem Sketch.check_program (app : SigApp) (e : NativeEff) :
    Sketch.check (e : Sketch) app = Checker.check app.signature [] [] e
-- H1: a program that performs no hole row is checked the same with any hole table
theorem holes_conservative (app : SigApp) (holes : RowTable) {e : NativeEff}
    (hp : SigProgram app.signature e) (env : TyEnv) (p : List Nat) :
    Checker.check (app.withHoles holes).signature env p e = Checker.check app.signature env p e
-- H2: a sketch stays admitted, at the same type, when more holes are declared
theorem sketch_more_holes (app : SigApp) (holes more : RowTable) {e : NativeEff} {env : TyEnv}
    {p : List Nat} {t : EffTy}
    (h : Checker.check (app.withHoles holes).signature env p e = .ok t) :
    Checker.check (app.withHoles (holes ++ more)).signature env p e = .ok t
-- H3: the verdict reads the rows of the holes that the sketch performs, and no later row
theorem sketch_reads_its_holes (app : SigApp) (holes more : RowTable) {e : NativeEff}
    (hp : SigProgram (app.withHoles holes).signature e) (env : TyEnv) (p : List Nat) :
    Checker.check (app.withHoles (holes ++ more)).signature env p e =
      Checker.check (app.withHoles holes).signature env p e
-- the hole's rule: `HasTy.perform` with `rowTy_closed`; no rule is added to `HasTy`
theorem Sketch.hole_hasTy (app : SigApp) (holes : RowTable) (k : Nat) {name : String}
    {answer error : Ty} {requires : List ServiceKey} (env : TyEnv)
    (hk : holes[k]? = some (Row.hole name answer error requires))
    (hans : answer.closed = true) (herr : error.closed = true)
    (formed : Formation.Formed
      (Formation.instantiatedSites (Row.hole name answer error requires).normalizeTypes [])) :
    HasTy (app.withHoles holes).signature env (Sketch.hole app k)
      ⟨answer.normalize, error.normalize, Requirement.ofList requires⟩
```

Against the study's section 5.7 the hole's rule is more general in one way. It holds for hole
`k` of any hole table, and not only for the last row. H1 to H3 are one line each from
`check_restrict`, `check_ext` and `SigApp.rows_append`. Each carries
`@[semantics "initial-algebras-folds" (requirement := R14)]`.

## 6. What this slice does not land

The replacement law (slice REPLACE). A gap. A term hole. A run of a sketch. A located refusal
for a hole table: a hole row that runs is judged by `admitSig` at `app.withHoles holes`, as any
host row is. Any change of `Row`, `Eff`, `Ty`, `Term`, the checker or the wire tags.
