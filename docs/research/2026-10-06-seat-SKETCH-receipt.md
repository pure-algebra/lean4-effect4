# 2026-10-06 seat SKETCH receipt: a program with its hole table

**The one thing to know before merging:** the slice adds three files and three root imports,
and it changes no existing declaration. `Sketch.check` is the checker's answer, and it admits no
sketch to a later stage. It does not decide raw formation of a hole row. It does not refuse a
stale hole after the application gains a row.

Status: a receipt (history, not authority). Brief:
`docs/research/2026-10-05-claude-lead/briefs/seat-sketch-brief.md`. Design:
`docs/research/2026-10-06-seat-SKETCH-design.md`, accepted by the coordinator as sent. Study:
`docs/research/2026-10-06-seat-GAP-study.md`, sections 5.7 and 9.7. Decisions rows 282 and 288.

## Base and head

Branch `seat/sketch`, in the worktree `/Users/pooks/Dev/lean4-effect4-t3b`. Base `ea0f584a`.
The head is the commit that adds this receipt.

| Commit | What |
| --- | --- |
| `93db1fae` | the design note, with its scratch file as text |
| `aa01617e` | the core module and its root import |
| `bc9ca284` | the law module and its root import |
| `005817f0` | the battery and its root import |
| the head | this receipt |

## Changed files

| File | Change |
| --- | --- |
| `src/Effect4/Program/Sketch.lean` | new: `Sketch`, the coercion from a program, `SigApp.withHoles`, `Row.hole`, `Sketch.hole`, `Sketch.check`, and the head comment |
| `src/Effect4.lean` | one import with its comment, directly after `import Effect4.Program.Typing.Blame` |
| `src/Effect4/Laws/Program/Sketch.lean` | new: twelve theorems |
| `src/Effect4/Laws.lean` | one import, directly after `import Effect4.Laws.Program.Signature` |
| `Test/Program/SketchControls.lean` | new: the controls |
| `Test/All.lean` | one import, directly after `import Test.Program.SignatureControls` |
| `docs/research/2026-10-06-seat-SKETCH-design.md` | new: the design note |
| `docs/research/2026-10-06-seat-SKETCH-design-probe.lean.txt` | new: the design's scratch file |
| `docs/research/2026-10-06-seat-SKETCH-receipt.md` | new: this receipt |

No definition is unused: each of the six declarations of the core module is read by a statement
or by a control. The core module is not a Lean module. It imports `Program/SigApp.lean`, which
is not one, because `Program/Columns.lean` imports a specialization site of decisions row 202.

## Commands and results

Each Lean, Lake and `make` command ran from the worktree's root, through
`/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`. `SCRATCH` is the seat's scratch folder.
`FLAGS` is `-o build -o ts/eff/node_modules -o harness/truth/node_modules`.

| # | Command | Result |
| --- | --- | --- |
| 1 | `lake build`, at the base | `Build completed successfully (1037 jobs).`, exit 0 |
| 2 | `lake env lean -M6144 SCRATCH/design_probe.lean` | exit 0; five theorems print `[propext, Quot.sound]` |
| 3 | `env LEAN_NUM_THREADS=2 lake build Effect4.Program.Sketch` | `Build completed successfully (60 jobs).`, exit 0 |
| 4 | `lake build Effect4.Laws.Program.Sketch` | `Build completed successfully (281 jobs).`, exit 0 |
| 5 | `lake env lean -M6144 Test/Program/SketchControls.lean`, first run | exit 1: one guard did not hold; see below |
| 6 | the same, after the repair | exit 0, no message |
| 7 | `lake build Test.Program.SketchControls Effect4` | `Build completed successfully (396 jobs).`, exit 0 |
| 8 | `lake build`, at the head's sources | `Build completed successfully (1040 jobs).`, exit 0; the gate lines are below |
| 9 | `make FLAGS gen-fixtures` | `PASS generate: requested producers ran in dependency order`, exit 0; no file changed |
| 10 | `make FLAGS check-cases` | `conform cases: PASS, exit 0; .lake/conform/cases.json`, exit 0 |
| 11 | `make FLAGS check-docs` | `PASS check-docs: every path, link, citation and make target in 76 documents resolves`, exit 0 |
| 12 | `make FLAGS check-proof-style` | exit 0; the ratchet names no line of the new modules |
| 13 | `lake env lean -M6144 SCRATCH/status.lean` | exit 0: the axioms, the plan status and the census below |
| 14 | `python3 scripts/check-language.py --show` on the design note and on this receipt | no finding |

Command 5 found my own error, and it is a result. I expected the row check to refuse a hole
whose answer is a record with one field name twice. The checker reads a row's columns in
normal form, and the normalizer drops the repeated name, so the checker types that hole. Raw
formation refuses the row (`Formation.checkInput`). The control now shows both facts, and the
premise `formed` has another red control, a map whose key is a number.

Not run: `check-gen`, `check-slow`, `check-corpus`, `check-target`, `check-truth`, the
conservativity script, `gen-semantics`, `gen-architecture`. No TypeScript ran and no OCaml ran.
`make gen-fixtures` runs Lean writers only.

## Axiom output

The gate lines of command 8:

```text
Effect4 library-root gate: 180 API/utility modules, 323 Laws-only modules; every library source is reachable; Effect4 never reaches Laws
Effect4 module and axiom gate: checked 790 modules and 91580 declarations; … semantic/test axioms are [propext, Quot.sound]; exact implementation boundary (17 module(s), 23 declaration(s)) additionally allows Classical.choice
Effect4 goal gate: 28 planned goal(s), each a theorem whose body is `sorry` outside the Effect4 root; 12 declaration(s) rest on goals; no other declaration reaches sorryAx
```

The slice adds no planned goal and no exemption. Command 13, for each theorem of the law module:

| Theorem | Axioms | Plan status |
| --- | --- | --- |
| `SigApp.withHoles_extends` | `[propext, Quot.sound]` | proved |
| `SigApp.withHoles_withHoles` | `[propext]` | proved |
| `SigApp.withHoles_nil` | `[propext]` | proved |
| `SigApp.withHoles_rowOf` | `[propext, Quot.sound]` | proved |
| `Sketch.check_program` | `[propext, Quot.sound]` | proved |
| `holes_conservative` | `[propext, Quot.sound]` | proved |
| `Sketch.check_filled` | `[propext, Quot.sound]` | proved |
| `sketch_more_holes` | `[propext, Quot.sound]` | proved |
| `sketch_reads_its_holes` | `[propext, Quot.sound]` | proved |
| `sketch_weakening` | `[propext, Quot.sound]` | proved |
| `Sketch.check_more_holes` | `[propext, Quot.sound]` | proved |
| `Sketch.hole_hasTy` | `[propext, Quot.sound]` | proved |

`#plan_status` ends with `next goals: 0`. `#semantics_census Effect4.Laws.Program.Sketch` lists
the twelve under `initial-algebras-folds`, and it ends with `untagged: 0 theorems in 0 modules`.

## Evidence

- **Proved**: the twelve theorems of `src/Effect4/Laws/Program/Sketch.lean`. The axiom gate read
  them in command 8.
- **Proved**: the seven theorems of the battery. They are the laws at the plan's example, H1 at
  a row table alone, the hole's rule at a cell, and `hole_before_not_extends`.
- **Tested**: the battery's 25 `#guard` lines. Each is a finite check on named programs.
- **Reading**: the head comment's sentence on a run. No session ran, and no law states a run.
- Bounded evidence: every control is one program or one table. No evidence is host-only.

## The statements as compiled

Each is stated once, at the typing signature of an application. The form at a row table alone
is the instance at `⟨table, []⟩`, because `SigApp.signature_nil` holds by definition
(`holes_conservative_table` in the battery).

```lean
theorem SigApp.withHoles_extends (app : SigApp) (holes : RowTable) :
    SigExtends app.signature (app.withHoles holes).signature

theorem Sketch.check_program (app : SigApp) (e : NativeEff) :
    Sketch.check (e : Sketch) app = Checker.check app.signature [] [] e

theorem holes_conservative (app : SigApp) (holes : RowTable) {e : NativeEff}
    (hp : SigProgram app.signature e) (env : TyEnv) (p : List Nat) :
    Checker.check (app.withHoles holes).signature env p e = Checker.check app.signature env p e

theorem sketch_more_holes (app : SigApp) (holes more : RowTable) {e : NativeEff} {env : TyEnv}
    {p : List Nat} {t : EffTy}
    (h : Checker.check (app.withHoles holes).signature env p e = .ok t) :
    Checker.check (app.withHoles (holes ++ more)).signature env p e = .ok t

theorem sketch_reads_its_holes (app : SigApp) (holes more : RowTable) {e : NativeEff}
    (hp : SigProgram (app.withHoles holes).signature e) (env : TyEnv) (p : List Nat) :
    Checker.check (app.withHoles (holes ++ more)).signature env p e =
      Checker.check (app.withHoles holes).signature env p e

theorem Sketch.hole_hasTy (app : SigApp) (holes : RowTable) (k : Nat) {name : String}
    {answer error : Ty} {requires : List ServiceKey} (env : TyEnv)
    (hk : holes[k]? = some (Row.hole name answer error requires))
    (hans : answer.closed = true) (herr : error.closed = true)
    (formed : Formation.Formed
      (Formation.instantiatedSites (Row.hole name answer error requires).normalizeTypes [])) :
    HasTy (app.withHoles holes).signature env (Sketch.hole app k)
      ⟨answer.normalize, error.normalize, Requirement.ofList requires⟩
```

`sketch_weakening` is the conjunction of H2 and H3, as the pointer of one claim.
`Sketch.check_filled` and `Sketch.check_more_holes` are H1 and H2 on a `Sketch` value.

## Landed theorems and their placement

All twelve carry `@[semantics "initial-algebras-folds" (requirement := R14)]`.

**`holes_conservative`, with `Sketch.check_program` and `Sketch.check_filled`.**

- Concept: `initial-algebras-folds`; property: fold congruence on a program's reads
  (`cata-eff-congr-on`), which C3's reflection `check_restrict` instantiates.
- Question: registry claim `sketch-conservative` (role compatibility), proposed; pointer
  `holes_conservative`; consumer: a sketch whose holes are all filled is an ordinary program.
- Reach: every application, every hole table, every environment and path; the program performs
  only the application's operations and reads only keys with a carrier (`SigProgram`). Rows 111
  to 116, 282 and 288.
- Does not establish: anything of a program that performs a hole; any behaviour; that a hole
  table is lawful.
- Unlocks: R14, from R2's C3.

**`sketch_weakening`, with `sketch_more_holes`, `sketch_reads_its_holes` and
`Sketch.check_more_holes`.**

- Concept: `initial-algebras-folds`; property: the same congruence, and C3's monotone half
  `check_ext`.
- Question: registry claim `sketch-weakening` (role weakening), proposed; pointer
  `sketch_weakening`; consumer: declaring a hole, and composing two sketches.
- Reach: every application and every two hole tables. H2 has no premise on the program. H3 asks
  that the program is a Σ-program of the signature with the first hole table.
- Does not establish: an omission or a filling, which are the replacement law's; H2 from H3,
  which needs the open obligation 3 below.
- Unlocks: R14.

**`Sketch.hole_hasTy`, with `SigApp.withHoles_rowOf`.**

- Concept: `initial-algebras-folds`; property: the typing judgment at a `perform` node reads the
  row of its operation and nothing else of the signature.
- Question: registry claim `hole-rule` (role compatibility), proposed; pointer
  `Sketch.hole_hasTy`; consumer: the replacement law, for an omission (slice REPLACE).
- Reach: hole `k` of any hole table; a row made by `Row.hole`; closed columns that pass strict
  formation in normal form; every environment.
- Does not establish: a rule for a request that reads the environment; a run. A row that
  declares a template parameter has no such rule (a red control).
- Unlocks: R14.

## Open obligations

1. **Renumbering.** A sketch is pinned to the row count of its application. When the
   application gains a row before the hole table, every hole's position moves by one, and the
   stored program does not follow. A stale hole is not refused as such. It reads the row that
   now stands at its position. The checker then admits the sketch's program at another type, or
   the new row's request refuses the hole (two red controls). The consumer is an author who adds a host row while a
   sketch is open. Two ways serve that author.
   - With no new law: the new host row is appended after the hole table. H2
     (`sketch_more_holes`) keeps the sketch admitted at its type, and no position moves. The
     finished program then needs one renumbering, when the hole rows are dropped.
   - With a renumbering law: a map of positions renames the program's operations, and each
     operation keeps its row. The law rests on none of the four theorems as a premise. Each of
     the four holds for every application, so each holds again after the move. Its proof is a
     fusion of two folds (`hom_eq_cata_eff`), with the agreement at each operation that
     `check_alg_agreeOn` has for the identity map. `Eff` has no map on its operations today: a
     search of `src`, `tools` and `Test` found none.

   At the authoring surface the identity of a hole is its row's spelling, and the position is
   derived at each elaboration, as `Authoring.Row.call` reads `env.rows`. An authored sketch
   holds no stale position. The stored sketch does.
2. **A located refusal for a sketch with its hole table.** `Sketch.check` is the checker. A
   located refusal for a hole table is not in this slice. Three parts exist: `admitSig` at `app.withHoles holes` (three
   controls), raw formation by `Formation.checkInput` (one control), and `Ty.closed` for a
   declared column (one control). The consumer is the first tool that stores a sketch.
3. **A program that the checker admits is a Σ-program of its signature.** No theorem states it.
   With it, H2 follows from H3, and a tool can discharge H1's premise from a check. Its proof
   is one fold over the program's constructors.
4. **The notation.** The design note's two steps: a hole table as a field of `Module`, and a
   term elaborator that collects `?h`. Neither is implemented. The consumer is a battery or a
   scenario that writes many sketches in Lean.
5. **The request of a hole that runs.** It is a unit here. A request that carries the
   environment's values is derived from the traced environment (slice TRACE), when a run has a
   consumer.
6. **tsgo on a printed sketch.** No TypeScript ran. The study's section 9.8 keeps that question.
   The coordinator's probe answers its second question in part
   (`docs/research/2026-10-06-uniform-eliminators-landing-probe.md`). There tsgo 7 accepts
   `never` at every printed eliminator. It refuses a proper union at a generic call whose type
   arguments are inferred.

## Proposed texts (proposals only; the seat edits none of these files)

### The semantics registry (`tools/Tools/SemanticsRegistry.lean`)

Three claims, under the concept `initial-algebras-folds`:

```lean
    { id := "sketch-conservative", concept := "initial-algebras-folds", role := .compatibility
      title := "A program that performs no hole row is checked the same with any hole table appended after the application's rows, refusals included, at every environment and path"
      pointer := .witness `Effect4.Program.holes_conservative },
    { id := "sketch-weakening", concept := "initial-algebras-folds", role := .weakening
      title := "A program with holes that the checker admits stays admitted at its type with more holes declared, and the checker reads the rows of the holes that the program performs and no later row"
      pointer := .witness `Effect4.Program.sketch_weakening },
    { id := "hole-rule", concept := "initial-algebras-folds", role := .compatibility
      title := "A hole row with a unit request and closed, formed columns types its perform at those columns in normal form, in every environment, at any position of the hole table; no rule is added to HasTy"
      pointer := .witness `Effect4.Program.Sketch.hole_hasTy },
```

R14's `top` gains the three pointers, and its first open part leaves:

```lean
      top := [`Effect4.SliceView.lattice_minimal, `Effect4.Program.holes_conservative,
        `Effect4.Program.sketch_weakening, `Effect4.Program.Sketch.hole_hasTy]
```

One open part is new, and obligation 1 above gives its text: the renumbering of a sketch when
its application gains a row.

### The semantics document (`docs/core/semantics.md`, concept 7, required properties)

```text
- **A sketch is a conservative extension (`sketch-conservative`)**: a program that performs no
  hole row is checked the same with any hole table, refusals included
  (`holes_conservative` (`src/Effect4/Laws/Program/Sketch.lean`)). It is C3's reflection at a
  hole table. It says nothing of a program that performs a hole.
- **More holes keep a sketch (`sketch-weakening`)**: a sketch that the checker admits stays
  admitted at its type when more holes are declared, and the checker reads the rows of the
  holes that the sketch performs and no later row
  (`sketch_weakening` (`src/Effect4/Laws/Program/Sketch.lean`)).
- **The hole's rule (`hole-rule`)**: a hole has the type that its row declares, in every
  environment, for a row with a unit request and closed, formed columns
  (`Sketch.hole_hasTy` (`src/Effect4/Laws/Program/Sketch.lean`)). The typing judgment gains no
  rule.
```

### The dictionary (`docs/core/controlled-english.md`)

| Term | Meaning here | Tree anchor | Literature | Do not use | Qualifier |
| --- | --- | --- | --- | --- | --- |
| **sketch** (sketches) | A program with its hole table. With an empty hole table it is a program. The script of `proof_sketch` is a proof sketch. | `Sketch` (`src/Effect4/Program/Sketch.lean`) | an expression with holes (Omar, Voysey, Hilton and others, *Hazelnut*; read in `docs/research/2026-10-06-seat-GAP-study.md` §3) | "partial program", "incomplete program" | — |
| **hole** | An address of a program where no program is written yet. It is written as an operation at a hole row. Its stored name is its position in the hole table. | `Sketch.hole` (`src/Effect4/Program/Sketch.lean`) | empty hole (the same work, read in the same note) | "placeholder", "stub", "todo" | — |
| **hole row** | A host row with a unit request that declares a hole's type in three columns: the answer, the error and the requirement. | `Row.hole` (`src/Effect4/Program/Sketch.lean`) | an entry of a hole context (Omar, Voysey, Chugh and Hammer, *Live Functional Programming with Typed Holes*; read in the same note) | — | — |
| **hole table** | The hole rows of one sketch, in the order of declaration, appended after the application's row table. It only grows while the sketch is open. | `SigApp.withHoles` (`src/Effect4/Program/Sketch.lean`) | hole context (the same work) | "hole context" | — |
| **admitted modulo its holes** | The checker answers a type for the sketch's program at the application's typing signature extended by the hole table. It is the checker's answer, and not program admission. | `Sketch.check` (`src/Effect4/Program/Sketch.lean`); `holes_conservative` (`src/Effect4/Laws/Program/Sketch.lean`) | typing under a hole context (the same work) | "gap-admitted" | name the sketch |

Two more proposals for that file. The entry for "admission" has a list of qualifier words. Add
"sketch" and "sketches" to that list. The entry for "omit" waits for slice REPLACE, which lands
its law. This slice lands no anchor for it.

### The architecture document (`docs/ARCHITECTURE.md`, the source tree)

```text
| `src/Effect4/Program/Sketch.lean` | a sketch (decisions row 288): a program with its hole table. A hole is a host row with a unit request and three declared columns (`Row.hole`). The hole table stands after the application's rows (`SigApp.withHoles`), hole `k` is the operation at position `k` after them (`Sketch.hole`), and `Sketch.check` is the checker at the extended typing signature. The module adds no constructor, no rule of the typing judgment and no wire tag. It is not a Lean module (decisions rows 200 and 202) |
| `src/Effect4/Laws/Program/Sketch.lean` | the laws of a sketch, for R14. A hole table is an extension of the application's typing signature (`SigApp.withHoles_extends`). A program that performs no hole is checked the same with any hole table (`holes_conservative`). More holes keep a sketch admitted, and the checker reads no later row (`sketch_weakening`). A hole has its declared type in every environment (`Sketch.hole_hasTy`). The battery is `Test/Program/SketchControls.lean` |
```

### The state document and the system map

`docs/STATE.md`, in the paragraph "What the study found (row 288)", in place of its last
sentence:

```text
The first of them has landed (seat SKETCH): a sketch is a program with its hole table
(`src/Effect4/Program/Sketch.lean`), and its language is a conservative extension of the
program's (`src/Effect4/Laws/Program/Sketch.lean`). The replacement law is the next slice.
Nothing else of the study is a theorem of the tree yet.
```

`docs/core/system-map.md`, R14's status, after the sentence on `SliceView.lattice_minimal`:

```text
A second part is proved: the checker admits a sketch modulo its holes, and that language is a
conservative extension (`holes_conservative`, `sketch_weakening`, `Sketch.hole_hasTy`).
```

With the word in the dictionary, R14's title can read "a sketch checks and explains its types".

### One decisions row

| Question | Proposal | Evidence | Owner | Status |
| --- | --- | --- | --- | --- |
| How a sketch stores a hole, and what an edit keeps | (1) A sketch holds its program and its hole table, and the application's tables are a parameter of its check. (2) A hole's stored name is its position in an append-only hole table: declaring appends, filling leaves the row in place, and a hole is given another type by declaring a new hole. The row's spelling is the label that the printer prints and that an author calls. (3) A sketch is pinned to the row count of its application, and a renumbering is an open obligation. (4) A hole row's request is a unit while a sketch is checked. (5) `Sketch.check` is the checker, and a sketch's own admission waits for the first tool that stores one | `docs/research/2026-10-06-seat-SKETCH-design.md`; this receipt; `Test/Program/SketchControls.lean` | coordinator, under row 288 | proposed; the design was accepted in session on 2026-10-06 |

## The requirements R1 to R14

The slice serves R14 and no other requirement: three of R14's proposed claims become theorems.
It rests on R2's landed parts, C3 both ways and `SigApp.rows_append`, and it adds nothing to
R2's open parts. It reads R1's signature as a parameter and changes no admission. R3 is not
touched: no constructor of `Ty` is added. R4 to R13 are not touched. No machine, store,
session, codec, printer, reader or run changes. The LCNF lowering is not touched, and no host
row is answered. No requirement is closed by this slice.
