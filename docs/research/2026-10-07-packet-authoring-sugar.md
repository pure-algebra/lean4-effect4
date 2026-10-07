# 2026-10-07 packet: the authoring sugar

Status: a research note (history, not authority). It rules nothing, and it lands nothing. Base:
`0e9de44f`, branch `plan/open-parts`. It tests section 6 of the coordinator's examination
(`docs/research/2026-10-07-theorems-of-a-program.md`) against the tree, and it turns it into
slices. The first packet holds the application record and the claim record
(`docs/research/2026-10-07-packet-application-claims.md`).

## 1. The one thing to know first

**Five constructs compile as prototypes.** The to-do application written with them has
today's trees under authoring elaboration (`elaborateModule`). So no guard of the scenario
moves when a slice rewrites its source (appendix B gives the command and its result).

Three more facts.

- **One instrument does not serve the five.** The existing generator can write the functions
  of the atoms. A declared record, a declared failure and a declared block of rows are Lean
  commands. The conditional is one class and four rules of the `eff` macro.
- **The defect of the export names is wider than its report.** The test refuses every name
  that begins with `a`. It also accepts names that the imports of a printed module bind: `eq`,
  `get`, `Effect`. Section 3.6 gives the repair.
- **The program `add` stays refused after the repair, for a second reason.** The prelude
  exports an atom named `add`, and a printed module imports each atom by name.

## 2. What exists, and what is reused

### 2.1 What was read and run

| What | Evidence word |
| --- | --- |
| `src/Effect4/Program/Authoring.lean`; nine modules under `src/Effect4/Program/Authoring/` in full, and the two generated ones (`Lifts.lean`, `Rows.lean`) at their heads | reading |
| `tools/Effect4Gen/Rows.lean`, `Atoms.lean`, `PreludeAtoms.lean`, `CatalogueExe.lean` and `manifest.json` | reading |
| `src/Effect4/Codegen/PrintLeaf.lean`, `Print.lean`, `ClassTable.lean`, `Names.lean`; `src/Effect4/Api.lean` at `printModule` and `emitModule` | reading |
| `src/Effect4/Laws/Codegen/ReadLeaf.lean` at the laws of `Var.name`; `src/Effect4/Laws/Codegen/Admit.lean`; `src/Effect4/Laws/Api/ModuleReadable.lean` | reading |
| `harness/truth/module-imports.ts`; `ts/eff/read.ts` at `isBinderName` | reading |
| `Test/Dogfood/Scenario/Todo.lean`; `Test/Program/AuthoringContract.lean` at the conditional | reading |
| The prototypes `Sugar.lean` and `Names.lean`, and probe 1, each run by `lake env lean` in the worktree | tested |
| No TypeScript compiler ran. A statement about an import conflict is a reading of `module-imports.ts` | reading |

### 2.2 Where the examination's table is corrected

| # | The examination | The tree | Evidence |
| --- | --- | --- | --- |
| S1 | The same instrument can write functions for the atoms, a declared record and a declared failure | The generator reads a compiled table of the tree (`NativeOp.spelled`, `NativeAtom.row`). It serves the atoms. A record that an author declares stands in no such table: it needs a Lean command | reading; tested in the prototype |
| S2 | A tagged failure has three spellings | Two can be declared today: the pair and the record. A string literal alone has the type `string`, so no term has a tag's literal type outside `pair` and `tuple` | tested (`Sugar.lean`, the first evaluation) |
| S3 | The printer refuses an export name that begins with `a` | It does. It also accepts a name that the module's imports bind. On 20 names the repaired test differs at 7 | tested (`Names.lean`) |
| S4 | `Api.printModule` drops the reason | `Api.emitModule` keeps it, as an `EmissionRefusal`. The reason names the spelling and no cause | reading |
| S5 | A pure function is an atom's name as text | So is a comparison of two Booleans by `eq`, which the checker does not type. The first packet's draft found it | tested (the first packet, A.5) |

### 2.3 What is reused

| Need | Declaration and path |
| --- | --- |
| The scope reader and its names | `Src`, `TermSrc`, `Env`, `var`, `minted`, `app` (`src/Effect4/Program/Authoring.lean`) |
| The lifts of the constructors | the generated `src/Effect4/Program/Authoring/Lifts.lean` (`tools/Effect4Gen/Authoring.lean`) |
| The wrappers of the native rows | the generated `src/Effect4/Program/Authoring/Rows.lean` (`tools/Effect4Gen/Rows.lean`) |
| A generator that reads the atoms' table | `tools/Effect4Gen/PreludeAtoms.lean`, which reads `NativeAtom.row` |
| The atoms, their names and their arities | `NativeAtom`, `AtomRow` (`src/Effect4/Machine/Term.lean`); `NativeAtom.all` (`src/Effect4/Program/AtomInventory.lean`) |
| The block macro and its conveniences | `eff`, `expandDoElems`, `identToString`, `ifElse`, `bindName`, `selectOptionWith` (`src/Effect4/Program/Authoring/Sugar.lean`) |
| The scope laws of the conveniences | `ifElse_scoped`, `bindName_scoped` (`src/Effect4/Laws/Program/Authoring/Sugar.lean`) |
| The record builders | `record`, `field`, `recordSet` (`src/Effect4/Program/Authoring/Records.lean`) |
| A host row and its call | `Row.host`, `Row.call`, `RowDef` (`src/Effect4/Program/Authoring.lean`) |
| A block of rows and services | `Package`, `Package.install` (`src/Effect4/Program/Authoring.lean`, `Authoring/Services.lean`) |
| The spellings of an error payload | decisions row 120; `Classes.classTag?` (`src/Effect4/Codegen/Classes.lean`) |
| A printed binder and its reader | `Var.name` (`src/Effect4/Codegen/PrintLeaf.lean`); `Var.read` (`src/Effect4/Codegen/Read.lean`) |
| A decimal read from bytes | `decodeBytes` (`src/Effect4/Data/NatDecimal.lean`); `decodeBytes_repr` (`src/Effect4/Laws/Data/NatDecimal.lean`) |
| The names that a class may not take | `ClassTable.takenNames`, `effectNamespaces` (`src/Effect4/Codegen/ClassTable.lean`) |
| The module printer with its reason | `Api.emitModule` (`src/Effect4/Api.lean`); `emitModule` (`src/Effect4/Codegen/Checked.lean`) |

## 3. The definitions to add

Appendix A holds each prototype in Lean. This section says what each construct looks like, who
produces it and what it expands to.

### 3.1 Named functions for the atoms

**What it looks like.** `eq title (str "")` in place of `app "eq" [title, str ""]`.

**Who produces it.** The existing generator, as one more group. Its tool is a sibling of
`tools/Effect4Gen/PreludeAtoms.lean`: it reads `NativeAtom.all`, and each atom's name and
arity from `NativeAtom.row`. It writes one function for each atom. A variadic atom takes a
list. A second group writes each function's scope lemma, one application of `app_scoped`, as
`tools/Effect4Gen/Rows.lean` does for a row.

**Where the functions stand.** In a namespace of their own, `Authoring.Atom`. Of the 43 atoms,
seven carry a name that resolves at Lean's root: `not`, `or`, `and`, `ite`, `some`, `none` and
`get` (probe 5). In the namespace `Authoring` each would make that name ambiguous for every
file that opens it. An author opens the names that a file uses: `open Atom (eq pair)`.

**What it gives.** A wrong atom name is an error of Lean at the call. Today it is a refusal of
the checker at the build. A wrong count of arguments is an error of Lean too.

**What it leaves.** Seven atoms have a hand function in `Authoring` today (probe 5): the six
of `Authoring/Maps.lean`, and `tuple` of `Authoring/Tuples.lean`. The slice keeps them. A
later cleanup makes each an alias of its generated function.

### 3.2 A conditional of the program in a block

**The problem.** In an `eff` block `if c then a else b` expands to Lean's own `if`. That
selects one of two programs while the program is built. A test of the program is a term, and
Lean's `if` refuses a term.

**The repair is a choice by the type of the test.** A class `EffIf` has three instances.

| The test is | The block's conditional is |
| --- | --- |
| a term of the program (`TermSrc`) | the program's: `ifElse c a b` |
| a Boolean of Lean | the builder's: Lean's `if` |
| a decided proposition of Lean | the builder's: Lean's `if` |

The four rules of `expandDoElems` that hold `if` then expand to `effIf c a b`.

**No tree moves.** A block that tests a Boolean of Lean keeps its tree: the instance is Lean's
`if`. One guard of the prototype compares the two macros at both values. A block could not
test a term before. A census by a script found no conditional inside an
`eff do` block of the tree. The battery of the macro holds one in an `eff { }` block, with a
Boolean of Lean (`conditionalBranchProg`, `Test/Program/AuthoringContract.lean`).

**The scope law.** At a term the conditional is `ifElse`, so `ifElse_scoped` serves. The slice
owes no new law until a proof meets `effIf` itself.

### 3.3 A declared record

**What it looks like.**

```lean
eff_record Todo where id : .nat, title : .string, done : .bool
```

**What it declares.** Six declarations under `Todo`:

- `Todo.fields`, the field list, and `Todo.ty`, the type;
- `Todo.mk`, the constructor, with one argument for each field;
- `Todo.id`, `Todo.title` and `Todo.done`, the projections.

So an author writes the field list once. A missing argument of the constructor and a projection of no
field are errors of Lean at the call.

**Who produces it.** A Lean command: a `syntax` and a `macro_rules`. The existing generator
cannot: it writes a file from a table that its executable links, and an author's record is a
line of a battery.

**What the first slice leaves out.** An optional field; a value of the record for a script
(`recordVal`); a record update by name.

### 3.4 A declared tagged failure

**What it looks like.**

```lean
eff_failure NotFound where id : .nat
eff_failure SqlError message
```

**What it declares.** The declaration chooses the spelling of decisions row 120 from its
fields, so an author no longer chooses among three.

| Declared with | Spelling | Declarations |
| --- | --- | --- |
| fields | a record whose first field is `_tag` | `fields`, `ty`, `mk`, `is`, `raise` |
| the word `message` | the pair of the tag and a message | `ty`, `mk`, `is`, `raise` |

`NotFound.raise id` is `fail (NotFound.mk id)`. `NotFound.is e` is a handler's test,
`tagIs("NotFound", e)`.

**The third spelling stays out.** A failure with no field is the tag's literal. No term has
that type today: a string literal alone has the type `string`. The slice reports it, and it
adds no form.

**One trap, measured.** The word `message` of the command's syntax must be a keyword that is
not reserved. As a plain token it broke each binder named `message` in the same file.

**The declared type of a message failure is wider than a program's checked type.**
`EmptyTitle.ty` holds a message of type `string`. The checker gives `add` the literal of its
one message. The trees are equal, and the guards of the checked types stay as they are.

### 3.5 A declared block of host rows

**What it looks like.**

```lean
eff_rows TodoRepo error SqlError.ty cite "the to-do scenario" where
  insert(.string) : Todo.ty,
  all(.unit) : .list Todo.ty,
  setDone(.prod .nat .bool) : .option Todo.ty,
  delete(.nat) : .bool
```

**What it declares.** For each entry a row under `TodoRepo.row`, spelled `TodoRepo.insert`,
and a call under `TodoRepo`. It declares the list `TodoRepo.rows` in the written order. So a
module writes `rows := TodoRepo.rows`, and a program writes `TodoRepo.insert title`.

**It is a block of rows, and no service.** A service is a key and a carrier that a program
requires (`ServiceDef`). The to-do repository is four rows that the host answers. A block that
also declares a service key is a later form, over `Package`.

**The first packet's application holds the rows once.** With `Application`, no module lists
the rows again.

### 3.6 The export name's test

**The defect has two halves.**

1. **The test refuses too much.** `exportNameSafe` refuses a name whose first byte is `a`. A
   printed binder is `a` and a decimal. The TypeScript reader tests exactly that
   (`isBinderName`, `ts/eff/read.ts`). The Lean reader compares a name with `Var.name` of each
   position (`Var.read`).
2. **The test refuses too little.** A printed module has no import of its own. A lane writes
   the imports above it, and it imports each atom by name
   (`harness/truth/module-imports.ts`). So an export named `eq` meets an import named `eq`.
   No compiler ran for this packet: the conflict is a reading.

**The repair is one function that answers a reason.** `exportNameFault` answers why a name is
no export name, or nothing. The test is "no fault". Its reasons are six words.

| Reason | The name is |
| --- | --- |
| `notBinding` | no legal binding of the target |
| `binder` | a printed binder: `a` and the decimal of a position (`binderNamed`) |
| `reservedHead` | a reserved head of the printer |
| `layerName` | the name of a hoisted layer |
| `helper` | a helper of the prelude that a printed term calls |
| `imported` | a name that a module's imports bind: an atom, a namespace of `effect` |

**The binder test is exact, and the draft proves it**: `binderNamed s = true` exactly when `s`
is `Var.name i` for some `i` (`binderNamed_iff`, appendix A.6).

**No law of the tree reads the first byte of an export name.** The laws take
`exportNameSafe name = true` as a premise and never open it (`EnvelopeValid.safe`,
`emitModule_complete`). So the repair of the export name moves no proof.

**A row's spelling keeps today's rule.** `rowNamesSafe` refuses a spelling whose first byte is
`a`, and three proofs read that byte (`Var.name_ne`, `name_notin`, in
`src/Effect4/Laws/Codegen/ReadLeaf.lean`). A row spelled `a0.get` would print as a call on a
binder. The slice leaves it.

**The reason reaches the caller by a function, and the refusal's alphabet stays.**
`PrintRefusal.unsafeName` holds the spelling. A second field would move its generated codec
and the guards of three batteries. So `Api.printModule` keeps its type, and its docstring names
`Api.emitModule` and `exportNameFault` for the reason.

**What the repair does to the to-do application.** Measured on its names:

| Name | Today | After | Reason after |
| --- | --- | --- | --- |
| `add` | refused | refused | `imported`: the atom `add` |
| `list` | accepted | accepted | — |
| `complete` | accepted | accepted | — |
| `remove` | accepted | accepted | — |

So one module with the four exports under their own names still refuses `add`. Two ways are
open. A lane imports the atoms under one namespace, or the application names its exports
apart from its programs. The choice is the owner's or the coordinator's.

**What stays open.** Three names of the harness's import list stand in no list of Lean: the
adapters `Host`, `Sql` and `Kv`. The root of a row that a program performs is another such
name. The slice says where their list stands, or it reports them.

### 3.7 The to-do scenario after

Sections 1 and 2 of `Test/Dogfood/Scenario/Todo.lean` read as below. Each program elaborates
to today's tree (the prototype's guards).

```lean
eff_record Todo where id : .nat, title : .string, done : .bool
eff_failure NotFound where id : .nat
eff_failure SqlError message
eff_failure EmptyTitle message

eff_rows TodoRepo error SqlError.ty cite "the to-do scenario" where
  insert(.string) : Todo.ty,
  all(.unit) : .list Todo.ty,
  setDone(.prod .nat .bool) : .option Todo.ty,
  delete(.nat) : .bool

/-- `add(title)`: an empty title fails and asks the repository nothing. -/
def add (title : TermSrc) : Src NativeOp := eff do
  if eq title (str "") then
    EmptyTitle.raise (str "a title is required")
  else
    TodoRepo.insert title

/-- `list()`: every to-do. -/
def list : Src NativeOp := TodoRepo.all unit

/-- `complete(id)`: the to-do, marked done; a missing one fails with its id. -/
def complete (id : TermSrc) : Src NativeOp := eff do
  let updated ← TodoRepo.setDone (pair id (bool true))
  selectOptionWith updated (NotFound.raise id) fun todo => succeed todo

/-- `remove(id)`: a missing to-do fails with its id. -/
def remove (id : TermSrc) : Src NativeOp := eff do
  let removed ← TodoRepo.delete id
  if removed then succeed unit else NotFound.raise id
```

The two blocks with `if` are the text after slice IF. A scratch file cannot change the macro.
So the prototype compiles them under a copy of the macro with the four rules changed (`eff2`,
appendix A.2). Their trees are today's.

One construct is still a function call: the elimination of an option. A `match` of the
program in a block is a further form. No slice of this packet adds it.

## 4. The slices, in commit order

### 4.1 The table

| # | Slice | Size | Depends on | Existing tests that move |
| --- | --- | --- | --- | --- |
| 1 | NAMES: the export name's test and its reason | S | — | none found |
| 2 | ATOMS: the generated functions of the atoms | M | — | none |
| 3 | IF: the conditional of a block, by the type of its test | S | — | none found |
| 4 | DECLARE: a declared record and a declared failure | M | — | none |
| 5 | ROWS: a declared block of host rows | S | 4 | none |
| 6 | SCENARIO: the to-do scenario written with them | S | 2 to 5 | none: the trees are equal |

Slices 1 to 4 are independent of each other.

### 4.2 Slice 1, NAMES

- **Files.** Edited: `src/Effect4/Codegen/PrintLeaf.lean`: `binderNamed`, `importedNames`,
  `ExportFault`, `exportNameFault`, and `exportNameSafe` as "no fault". The list
  `effectNamespaces` moves there from `ClassTable.lean`, since `PrintLeaf.lean` stands below
  it. Edited: `src/Effect4/Api.lean`: the docstring of `printModule`. Edited:
  `Test/Dogfood/Scenario/Todo.lean`: its header's finding.
- **Size.** S: the draft is 101 lines with its controls and one law.
- **A new law needs a consumer.** `binderNamed_iff` has none in the law graph. Land it only
  with a registry claim, or keep the test's controls alone.
- **New battery lines**, in `Test/Codegen/PrintContract.lean`: one green line (`all` and
  `answer` are export names), and one red line for each of the two new reasons.
- **What to confirm by a narrow build.** The five guards that pin `a0`, `a1`,
  `Effect.succeed`, `L_0` and `export` stay green. A census by a pattern found `main` 76
  times and `program` 8 times beside the module printer, and no name of the new list.

### 4.3 Slice 2, ATOMS

- **Files.** New: `tools/Effect4Gen/AtomLifts.lean`. Edited: `tools/Effect4Gen/CatalogueExe.lean`,
  one entry. Edited: `tools/Effect4Gen/manifest.json`, two groups. New, generated:
  `src/Effect4/Program/Authoring/Atoms.lean` and `src/Effect4/Laws/Program/Authoring/Atoms.lean`.
  Edited: `src/Effect4.lean` and `src/Effect4/Laws.lean`, one import each. Edited: the
  Makefile's `DERIVED_OUT`, and `docs/GENERATED.md`, one row.
- **Size.** M: one tool of the size of `PreludeAtoms.lean`, and two generated files.
- **The lakefile does not change.** The generator's library takes each module under
  `Effect4Gen` by a glob.
- **New battery lines.** One reader: a generated function elaborates to the term of `app` at
  the atom's name. One control: the generated file names each atom of `NativeAtom.all`.
- **The gate that the change reaches.** `python3 scripts/generate.py --only` for the new group:
  the slice commits its output.

### 4.4 Slice 3, IF

- **Files.** Edited: `src/Effect4/Program/Authoring/Sugar.lean`: `EffIf`, its three instances,
  `effIf`, and the four `if` rules of `expandDoElems`.
- **Size.** S: the prototype's class is 22 lines, and four rules of the macro change.
- **New battery lines**, in `Test/Program/AuthoringContract.lean`. A block whose test is a
  term has the tree of `ifElse`. A block whose test is a Boolean of Lean keeps its tree.
- **What to confirm by a narrow build.** The two guards of `conditionalBranchProg` stay green.

### 4.5 Slice 4, DECLARE

- **Files.** New: `src/Effect4/Program/Authoring/Declare.lean`. Edited: `src/Effect4.lean`, one
  import. New: `Test/Program/AuthoringDeclare.lean`, and one import in `Test/All.lean`.
- **Size.** M: the prototype is 105 lines of two commands.
- **The module form.** The file is a module file, as `Sugar.lean` is. Its macro code stands in
  a `public meta section`. The prototype is a plain scratch file, so this packet compiles no
  such form.
- **New battery lines.** A declared record's type and constructor equal the hand-written ones.
  A declared failure's type equals the hand-written one, for each of the two spellings. One
  control of the keyword: a binder named `message` parses after the command.

### 4.6 Slice 5, ROWS

- **Files.** Edited: `Declare.lean` and its battery.
- **Size.** S: the prototype is 40 lines.
- **New battery lines.** The declared rows equal four hand-written rows, in order. A call of a
  declared row elaborates to `Row.call` of it.

### 4.7 Slice 6, SCENARIO

- **Files.** Edited: `Test/Dogfood/Scenario/Todo.lean`, sections 1 and 2.
- **Size.** S.
- **No guard changes.** Each guard of the file compares a built program, a type or a run. The
  trees are equal, so each stays as it is.

## 5. Risks, stop rules and open questions

### 5.1 Risks

| Risk | What limits it |
| --- | --- |
| A word of a command captures an identifier | Each word is a keyword that is not reserved. One control parses binders named `message`, `error` and `cite` |
| A generated name is hygienic, and no caller can write it | Each declared name is built from the declaration's own name, with no macro scope |
| An atom's function shadows a name of Lean | The functions stand in `Authoring.Atom`, and a file opens the ones that it uses |
| `EffIf` finds no instance | Lean then reports the class and the test's type. The test of a block is a term, a Boolean or a decided proposition |
| The macro code reaches an axiom above the ceiling | `identToString` exists for this (`Sugar.lean`). The prototype's helpers are within the ceiling. The axiom gate reads the landed file |
| The export name's repair meets a guard that pins a refused name | The census found none. A narrow build of the three batteries that name `unsafeName` confirms it |

### 5.2 Stop rules

1. Stop slice 1 if a law of the tree opens `exportNameSafe`. The read found none.
2. Stop slice 3 if a block of the tree changes its elaborated tree.
3. Stop slice 4 if the commands need a declaration outside the trust ceiling.
4. Stop slice 6 if one guard of `Todo.lean` changes.

### 5.3 Open questions

**Answered from the tree.**

| Question | Answer | Evidence |
| --- | --- | --- |
| Can the existing generator write a declared record? | No. It reads a table of the tree | `tools/Effect4Gen/Rows.lean`, `PreludeAtoms.lean` |
| Does the conditional's change move a tree? | None found | the census; the prototype's guard of a Boolean test |
| Does the narrowed test need a new proof? | No. One law is drafted, and nothing consumes it | `Names.lean` |
| Does the rewritten scenario keep its trees? | Yes, each of the four programs | `Sugar.lean`, 10 guards that compare trees |

**For the owner or the coordinator.**

1. **The name `add`.** A module cannot export it beside the prelude's atom. Recommendation:
   the lanes import the prelude's atoms under one namespace, when the application's module is
   built (the first packet's slice 13). Until then `exportNameFault` reports the reason.
2. **A failure with no field.** It needs a term of a tag's literal type. That is a question of
   the literal rule (DI-15, DI-55). Recommendation: leave it until a program needs one.
3. **The commands' names.** The prototype writes `eff_record`, `eff_failure` and `eff_rows`.
   A rename is local.

## What this does not establish

- No theorem of the tree, and no landed code. Each prototype compiles in a scratch file.
- That a printed module with an export named `eq` fails under tsgo. No compiler ran.
- That the commands compile in a module file with a `public meta section`.
- That the census of conditionals is whole. It is a script over indented lines.
- Anything about the row spellings that begin with `a`. The slice leaves them.

## Appendix A. The compiled prototypes

Each block is a part of a scratch file, unchanged. The scratch directory is temporary, so the
text stands here.

### A.1 The atoms' functions: a sample of the generated file

```lean
/-! ## Part 1. Named functions for the atoms: a sample of what a generated file would hold
(proposed: `src/Effect4/Program/Authoring/Atoms.lean`, generated from `NativeAtom.all`) -/

namespace Effect4.Program.Authoring.Atom

open Effect4.Program Effect4.Program.Authoring

/-- `eq` (the atom `NativeAtom.eq`). -/
def eq (x0 x1 : TermSrc) : TermSrc := app "eq" [x0, x1]
/-- `pair` (the atom `NativeAtom.pair`). -/
def pair (x0 x1 : TermSrc) : TermSrc := app "pair" [x0, x1]
/-- `not` (the atom `NativeAtom.boolNot`). -/
def not (x0 : TermSrc) : TermSrc := app "not" [x0]
/-- `and` (the atom `NativeAtom.boolAnd`). -/
def and (x0 x1 : TermSrc) : TermSrc := app "and" [x0, x1]
/-- `tagIs` (the atom `NativeAtom.tagIs`). -/
def tagIs (x0 x1 : TermSrc) : TermSrc := app "tagIs" [x0, x1]
/-- `strings` (the atom `NativeAtom.strings`, variadic). -/
def strings (xs : List TermSrc) : TermSrc := app "strings" xs

end Effect4.Program.Authoring.Atom
```

### A.2 The conditional (`src/Effect4/Program/Authoring/Sugar.lean`)

```lean
/-! ## Part 2. A conditional in an `eff` block, chosen by the type of its test
(proposed: `src/Effect4/Program/Authoring/Sugar.lean`) -/

namespace Effect4.Program.Authoring

open Effect4.Program

/-- How an `eff` block reads `if c then a else b`, by what `c` is. A term of the program is the
program's conditional. A Boolean or a decided proposition of Lean selects one of two programs
while the program is built. -/
class EffIf {α : Sort _} (c : α) (Op : Type) where
  pick : Src Op → Src Op → Src Op

instance (c : TermSrc) (Op : Type) : EffIf c Op := ⟨fun a b => ifElse c a b⟩
instance (c : Bool) (Op : Type) : EffIf c Op := ⟨fun a b => if c then a else b⟩
instance (c : Prop) [Decidable c] (Op : Type) : EffIf c Op := ⟨fun a b => if c then a else b⟩

/-- The conditional of an `eff` block. -/
def effIf {α : Sort _} (c : α) {Op : Type} [inst : EffIf c Op] (a b : Src Op) : Src Op :=
  inst.pick a b

end Effect4.Program.Authoring
```

The macro with its four rules changed, as a copy under a second keyword:

```lean
/-! ## Part 2b. The block macro with the four changed rules, under a second keyword
(the slice edits `expandDoElems` in place; a scratch file cannot, so the copy is `eff2`) -/

namespace Effect4.Program.Authoring

open Lean Parser Term

/-- The block macro of the prototype: `expandDoElems` with its four `if` rules expanding to
`effIf`. Every other rule is the tree's own. -/
scoped syntax (name := effDo2) "eff2 " doSeq : term

/-- `expandDoElems`, with the conditional chosen by the type of its test. -/
def expandDoElems2 : List (TSyntax `doElem) → MacroM (TSyntax `term)
  | [] => `(succeed unit)
  | [elem] =>
    match elem with
    | `(doElem| return $t:term) => `(succeed $t)
    | `(doElem| return) => `(succeed unit)
    | `(doElem| if $c:term then $t:doSeq else $e:doSeq) =>
      `(effIf $c (eff2 $t) (eff2 $e))
    | `(doElem| if $c:term then $t:doSeq) =>
      `(effIf $c (eff2 $t) (succeed unit))
    | `(doElem| $e:term) => `($e)
    | _ => Macro.throwErrorAt elem "unsupported final statement in eff block"
  | elem :: rest => do
    let restTerm ← expandDoElems2 rest
    match elem with
    | `(doElem| let $x:ident $[: $_:term]? ← $e:term) =>
      if x.getId == `_ then
        `(andThen $e $restTerm)
      else
        let s := identToString x
        `(bindName $(Syntax.mkStrLit s) $e (fun $x => $restTerm))
    | `(doElem| if $c:term then $t:doSeq else $e:doSeq) =>
      `(andThen (effIf $c (eff2 $t) (eff2 $e)) $restTerm)
    | `(doElem| if $c:term then $t:doSeq) =>
      `(andThen (effIf $c (eff2 $t) (succeed unit)) $restTerm)
    | `(doElem| return $t:term) =>
      `(andThen (succeed $t) $restTerm)
    | `(doElem| $e:term) =>
      `(andThen $e $restTerm)
    | _ => Macro.throwErrorAt elem "unsupported statement in eff block"

scoped macro_rules
  | `(eff2 $seq:doSeq) => expandDoElems2 (unnestElems (getDoSeqElems seq))

end Effect4.Program.Authoring
```

### A.3 A declared record and a declared failure (`src/Effect4/Program/Authoring/Declare.lean`, new)

```lean
/-! ## Part 3. A declared record and a declared tagged failure, as commands
(proposed: `src/Effect4/Program/Authoring/Declare.lean`) -/

namespace Effect4.Program.Authoring

/-- One field of a declaration: a name and a type of the language. -/
declare_syntax_cat effField
syntax ident " : " term : effField

/-- `eff_record Name where f₁ : t₁, …`: the record's fields, its type, its constructor and one
projection for each field. -/
syntax (name := effRecordDecl) "eff_record " ident " where " sepBy1(effField, ", ") : command

/-- `eff_failure Name where f₁ : t₁, …`: a tagged failure as a record whose first field is the
tag. It declares the fields, the type, the constructor, the test of a handler and `raise`.
`eff_failure Name message` is a tagged failure whose one field is its message: the pair of the
tag and the message (decisions row 120). The word `message` is no reserved keyword. -/
syntax (name := effFailureDecl) "eff_failure " ident " where " sepBy1(effField, ", ") : command
syntax (name := effMessageDecl) "eff_failure " ident &" message" : command

/-- The fields of a declaration, each as its name and its type. -/
def parseEffFields (fields : Array Lean.Syntax) :
    Lean.MacroM (Array (Lean.Ident × Lean.TSyntax `term)) :=
  fields.mapM fun f => match f with
    | `(effField| $x:ident : $t:term) => pure (x, t)
    | _ => Lean.Macro.throwUnsupported

/-- The type `TermSrc → … → result`, with one argument for each field. -/
def termArrows (count : Nat) (result : Lean.TSyntax `term) : Lean.MacroM (Lean.TSyntax `term) :=
  match count with
  | 0 => pure result
  | n + 1 => do
    let rest ← termArrows n result
    `(Effect4.Program.Authoring.TermSrc → $rest)

open Lean in
macro_rules
  | `(eff_record $name:ident where $fields,*) => do
    let parsed ← parseEffFields fields.getElems
    let n := name.getId
    let fieldsId := mkIdent (n ++ `fields)
    let tyId := mkIdent (n ++ `ty)
    let mkId := mkIdent (n ++ `mk)
    let entries ← parsed.mapM fun (x, t) =>
      `(($(Syntax.mkStrLit (identToString x)), false, ($t : Effect4.Program.Ty)))
    let args : TSyntaxArray `term := parsed.map fun (x, _) => ⟨x.raw⟩
    let present ← parsed.mapM fun (x, _) => `(($(Syntax.mkStrLit (identToString x)), $x))
    let mkTy ← termArrows parsed.size (← `(Effect4.Program.Authoring.TermSrc))
    let decls ← parsed.mapM fun (x, _) =>
      `(def $(mkIdent (n ++ x.getId)) (self : Effect4.Program.Authoring.TermSrc) :
            Effect4.Program.Authoring.TermSrc :=
          Effect4.Program.Authoring.field self $(Syntax.mkStrLit (identToString x)))
    let d1 ← `(def $fieldsId : List (String × Bool × Effect4.Program.Ty) := [$entries,*])
    let d2 ← `(def $tyId : Effect4.Program.Ty := Effect4.Program.Ty.record $fieldsId)
    let d3 ← `(def $mkId : $mkTy := fun $args* =>
        Effect4.Program.Authoring.record $fieldsId [$present,*])
    return mkNullNode (#[d1.raw, d2.raw, d3.raw] ++ decls.map (·.raw))
  | `(eff_failure $name:ident where $fields,*) => do
    let parsed ← parseEffFields fields.getElems
    let n := name.getId
    let tag := Syntax.mkStrLit (identToString name)
    let fieldsId := mkIdent (n ++ `fields)
    let tyId := mkIdent (n ++ `ty)
    let mkId := mkIdent (n ++ `mk)
    let isId := mkIdent (n ++ `is)
    let raiseId := mkIdent (n ++ `raise)
    let entries ← parsed.mapM fun (x, t) =>
      `(($(Syntax.mkStrLit (identToString x)), false, ($t : Effect4.Program.Ty)))
    let args : TSyntaxArray `term := parsed.map fun (x, _) => ⟨x.raw⟩
    let present ← parsed.mapM fun (x, _) => `(($(Syntax.mkStrLit (identToString x)), $x))
    let mkTy ← termArrows parsed.size (← `(Effect4.Program.Authoring.TermSrc))
    let raiseTy ← termArrows parsed.size (← `(Effect4.Program.Authoring.Src Op))
    let d1 ← `(def $fieldsId : List (String × Bool × Effect4.Program.Ty) :=
        ("_tag", false, Effect4.Program.Ty.lit $tag) :: [$entries,*])
    let d2 ← `(def $tyId : Effect4.Program.Ty := Effect4.Program.Ty.record $fieldsId)
    let d3 ← `(def $mkId : $mkTy := fun $args* =>
        Effect4.Program.Authoring.record $fieldsId
          (("_tag", Effect4.Program.Authoring.str $tag) :: [$present,*]))
    let d4 ← `(def $isId (failure : Effect4.Program.Authoring.TermSrc) :
          Effect4.Program.Authoring.TermSrc :=
        Effect4.Program.Authoring.app "tagIs" [Effect4.Program.Authoring.str $tag, failure])
    let d5 ← `(def $raiseId {Op : Type} : $raiseTy := fun $args* =>
        Effect4.Program.Authoring.fail ($mkId $args*))
    return mkNullNode #[d1.raw, d2.raw, d3.raw, d4.raw, d5.raw]
  | `(eff_failure $name:ident message) => do
    let n := name.getId
    let tag := Syntax.mkStrLit (identToString name)
    let tyId := mkIdent (n ++ `ty)
    let mkId := mkIdent (n ++ `mk)
    let isId := mkIdent (n ++ `is)
    let raiseId := mkIdent (n ++ `raise)
    let d1 ← `(def $tyId : Effect4.Program.Ty :=
        Effect4.Program.Ty.prod (Effect4.Program.Ty.lit $tag) Effect4.Program.Ty.string)
    let d2 ← `(def $mkId (text : Effect4.Program.Authoring.TermSrc) :
          Effect4.Program.Authoring.TermSrc :=
        Effect4.Program.Authoring.app "pair" [Effect4.Program.Authoring.str $tag, text])
    let d3 ← `(def $isId (failure : Effect4.Program.Authoring.TermSrc) :
          Effect4.Program.Authoring.TermSrc :=
        Effect4.Program.Authoring.app "tagIs" [Effect4.Program.Authoring.str $tag, failure])
    let d4 ← `(def $raiseId {Op : Type} (text : Effect4.Program.Authoring.TermSrc) :
          Effect4.Program.Authoring.Src Op :=
        Effect4.Program.Authoring.fail ($mkId text))
    return mkNullNode #[d1.raw, d2.raw, d3.raw, d4.raw]

end Effect4.Program.Authoring
```

### A.4 A declared block of rows (the same file)

```lean
/-! ## Part 3b. A declared block of host rows, as a command
(proposed: `src/Effect4/Program/Authoring/Declare.lean`) -/

namespace Effect4.Program.Authoring

/-- One row of a block: its name, its request type and its answer type. -/
declare_syntax_cat effRow
syntax ident "(" term ")" " : " term : effRow

/-- `eff_rows Name error E cite "…" where r₁(request₁) : answer₁, …`: one host row for each
entry, spelled `Name.rᵢ`, with the block's error column and citation. It declares each row
under `Name.row`, the list `Name.rows` in the written order, and one call of each row under
`Name`. The words `error` and `cite` are no reserved keywords. -/
syntax (name := effRowsDecl) "eff_rows " ident &" error " term:max &" cite " str " where "
  sepBy1(effRow, ", ") : command

open Lean in
macro_rules
  | `(eff_rows $name:ident error $err:term cite $cite:str where $rows,*) => do
    let n := name.getId
    let parsed ← rows.getElems.mapM fun r => match r with
      | `(effRow| $x:ident ($req:term) : $ans:term) => pure (x, req, ans)
      | _ => Macro.throwUnsupported
    let mut out : Array Syntax := #[]
    let mut rowIds : Array (TSyntax `term) := #[]
    for (x, req, ans) in parsed do
      let rowId := mkIdent (n ++ `row ++ x.getId)
      let callId := mkIdent (n ++ x.getId)
      let spelling := Syntax.mkStrLit (identToString name ++ "." ++ identToString x)
      rowIds := rowIds.push ⟨rowId.raw⟩
      out := out.push (← `(def $rowId : Effect4.Program.Authoring.RowDef :=
        Effect4.Program.Authoring.Row.host $spelling $req $ans $err $cite)).raw
      out := out.push (← `(def $callId (request : Effect4.Program.Authoring.TermSrc) :
          Effect4.Program.Authoring.Src Effect4.Program.NativeOp :=
        Effect4.Program.Authoring.Row.call $rowId request)).raw
    out := out.push (← `(def $(mkIdent (n ++ `rows)) : List Effect4.Program.Authoring.RowDef :=
      [$rowIds,*])).raw
    return mkNullNode out

end Effect4.Program.Authoring
```

### A.5 The to-do application with them, and the guards that compare the trees

```lean
/-! ## Part 4. The to-do application, written with them -/

namespace Sugared

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Program.Authoring.Atom (eq pair)

eff_record Todo where id : .nat, title : .string, done : .bool
eff_failure NotFound where id : .nat
eff_failure SqlError message
eff_failure EmptyTitle message

-- the declared types are the types of today's file
#guard Todo.ty = Test.Dogfood.Scenario.Todo.todoTy
#guard NotFound.ty = Test.Dogfood.Scenario.Todo.notFoundTy
#guard SqlError.ty = Test.Dogfood.Scenario.Todo.sqlErrTy

eff_rows TodoRepo error SqlError.ty cite "the to-do scenario" where
  insert(.string) : Todo.ty,
  all(.unit) : .list Todo.ty,
  setDone(.prod .nat .bool) : .option Todo.ty,
  delete(.nat) : .bool

-- the declared rows are the rows of today's file, in the same order
#guard TodoRepo.rows = [Test.Dogfood.Scenario.Todo.insert, Test.Dogfood.Scenario.Todo.all,
  Test.Dogfood.Scenario.Todo.setDone, Test.Dogfood.Scenario.Todo.delete]

/-- `add(title)`. The conditional's test is a term of the program, so it is the program's. -/
def add (title : TermSrc) : Src NativeOp :=
  effIf (eq title (str ""))
    (EmptyTitle.raise (str "a title is required"))
    (TodoRepo.insert title)

/-- `complete(id)`. -/
def complete (id : TermSrc) : Src NativeOp :=
  bindName "updated" (TodoRepo.setDone (pair id (bool true))) fun updated =>
    selectOptionWith updated (NotFound.raise id) fun todo => succeed todo

/-- `remove(id)`. -/
def remove (id : TermSrc) : Src NativeOp :=
  bindName "removed" (TodoRepo.delete id) fun removed =>
    effIf removed (succeed unit) (NotFound.raise id)

/-- A builder's conditional stays the builder's: its test is a Boolean of Lean. -/
def addOrList (adding : Bool) : Src NativeOp :=
  effIf adding (add (str "milk")) (TodoRepo.all unit)

def request (main : Src NativeOp) : Module NativeOp :=
  { rows := TodoRepo.rows, main }

open Test.Dogfood.Scenario.Todo in
-- each program elaborates to today's tree, so no guard of the scenario moves
#guard elaborateModule (request (add (str "milk"))) =
  elaborateModule (Test.Dogfood.Scenario.Todo.request (Test.Dogfood.Scenario.Todo.add (str "milk")))
#guard elaborateModule (request (remove (nat 1))) =
  elaborateModule (Test.Dogfood.Scenario.Todo.request (Test.Dogfood.Scenario.Todo.remove (nat 1)))
-- `complete` binds its payload under a minted name where today's binds it under "todo": the
-- trees are equal, because a tree holds levels and no name
#guard elaborateModule (request (complete (nat 1))) =
  elaborateModule (Test.Dogfood.Scenario.Todo.request (Test.Dogfood.Scenario.Todo.complete (nat 1)))
-- `list` is the call of the declared row
#guard elaborateModule (request (TodoRepo.all unit)) =
  elaborateModule (Test.Dogfood.Scenario.Todo.request Test.Dogfood.Scenario.Todo.list)
-- the builder's conditional selects a program
#guard elaborateModule (request (addOrList false)) = elaborateModule (request (TodoRepo.all unit))

/-- `complete(id)` in a block: the sequence is the block's, and the last line is the program's
elimination of an option. -/
def completeDo (id : TermSrc) : Src NativeOp := eff do
  let updated ← TodoRepo.setDone (pair id (bool true))
  selectOptionWith updated (NotFound.raise id) fun todo => succeed todo

/-- `remove(id)` in a block. The conditional is written through `effIf`: the block's own `if`
is the builder's until the macro's two rules change. -/
def removeDo (id : TermSrc) : Src NativeOp := eff do
  let removed ← TodoRepo.delete id
  effIf removed (succeed unit) (NotFound.raise id)

#guard elaborateModule (request (completeDo (nat 1))) = elaborateModule (request (complete (nat 1)))
#guard elaborateModule (request (removeDo (nat 1))) = elaborateModule (request (remove (nat 1)))

/-- `add(title)` in a block of the changed macro: the block's `if` at a term of the program. -/
def addIf (title : TermSrc) : Src NativeOp := eff2 do
  if eq title (str "") then
    EmptyTitle.raise (str "a title is required")
  else
    TodoRepo.insert title

/-- `remove(id)` in a block of the changed macro. -/
def removeIf (id : TermSrc) : Src NativeOp := eff2 do
  let removed ← TodoRepo.delete id
  if removed then succeed unit else NotFound.raise id

/-- A block of the changed macro whose test is a Boolean of Lean: the builder's conditional. -/
def branchIf (b : Bool) : Src NativeOp := eff2 do
  let removed ← TodoRepo.delete (nat 1)
  if b then succeed removed else NotFound.raise (nat 1)

/-- The same block under today's macro. -/
def branchToday (b : Bool) : Src NativeOp := eff do
  let removed ← TodoRepo.delete (nat 1)
  if b then succeed removed else NotFound.raise (nat 1)

-- the changed macro's conditional at a term is the program's: today's trees
#guard elaborateModule (request (addIf (str "milk"))) = elaborateModule (request (add (str "milk")))
#guard elaborateModule (request (removeIf (nat 1))) = elaborateModule (request (remove (nat 1)))
-- the changed macro's conditional at a Boolean of Lean is today's macro's: equal trees at both values
#guard [true, false].all fun b =>
  elaborateModule (request (branchIf b)) == elaborateModule (request (branchToday b))

-- measured: a string literal alone has the type `string`, and a pair keeps the literal's type
#eval (termTy (nativeSignature []) [] (.lit (.str "x")),
  termTy (nativeSignature []) [] (.app "pair" (termsOfList [.lit (.str "x"), .lit (.str "y")])))

-- measured: the export names that the module printer answers today
#eval ["get", "eq", "Effect", "pipe", "Host", "main", "add", "all", "list"].map fun n =>
  (n, exportNameSafe n)

end Sugared
```

### A.6 The export name's test (`src/Effect4/Codegen/PrintLeaf.lean`)

```lean
namespace Effect4.Program

open Effect4.Data.NatDecimal (decodeBytes)

/-- Whether a name is a printed binder: `a`, then the decimal spelling of a position, and
nothing else. It reads bytes, and it compares one string: no traversal of a `String`. -/
def binderNamed (s : String) : Bool :=
  match s.toByteArray.data.toList with
  | 97 :: rest => decide (s = Var.name (decodeBytes rest))
  | _ => false

/-- The names that the imports of a printed module bind, whatever its program: the `effect`
namespaces, the root export `pipe`, and each atom of the prelude. The prelude's helpers are
`termHelperNames` and the package adapters' roots, which the test reads beside this list. -/
def importedNames : List String :=
  Effect4.Codegen.effectNamespaces ++ ["pipe"] ++ NativeAtom.names

/-- Why a name is no export name, as a word. `none` for a name that the module may export. -/
inductive ExportFault
  /-- No legal binding of the target. -/
  | notBinding
  /-- A printed binder: the reader would read it as a variable. -/
  | binder
  /-- A reserved head of the printer. -/
  | reservedHead
  /-- The name of a hoisted layer. -/
  | layerName
  /-- A helper of the prelude that a printed term calls. -/
  | helper
  /-- A name that the module's imports bind. -/
  | imported
deriving DecidableEq, Repr

/-- **Why a name is no export name**, or `none`. The checks stand in the order of today's test. -/
def exportNameFault (name : String) : Option ExportFault :=
  if !Effect4.Codegen.Names.binderName name then some .notBinding
  else if binderNamed name then some .binder
  else if reserved.contains name then some .reservedHead
  else if (LayerTerm.readRefName name).isSome then some .layerName
  else if termHelperNames.contains name then some .helper
  else if importedNames.contains name then some .imported
  else none

/-- The proposed test: a name with no fault. -/
def exportNameSafe' (name : String) : Bool := (exportNameFault name).isNone

-- green: a name that begins with `a` and is no binder
#guard ["all", "answer", "a", "a01", "a1x", "list", "complete", "remove", "main"].all exportNameSafe'
-- red: the printed binders, each with its reason
#guard ["a0", "a1", "a12", "a100"].all fun name => exportNameFault name == some .binder
-- red: a name that the module's imports bind: an atom, a namespace of `effect`, `pipe`
#guard ["add", "eq", "get", "some", "Effect", "Data"].all fun name =>
  exportNameFault name == some .imported
#guard exportNameFault "pipe" == some .reservedHead
-- the other reasons, as today
#guard exportNameFault "Effect.succeed" == some .notBinding
#guard exportNameFault "export" == some .notBinding
#guard exportNameFault "L_0" == some .layerName
#guard exportNameFault "tupleAt" == some .helper
-- the proposed test refuses each name that today's test refuses for a reason that stands
#guard ["a0", "Effect.succeed", "L_0", "export", "tupleAt", "caseTagR"].all fun name =>
  !exportNameSafe name && !exportNameSafe' name
-- measured: the names where the two tests differ, on a list of 20 names
#eval ["main", "program", "handle", "y", "p", "id", "all", "answer", "add", "eq", "get", "some",
    "Effect", "Data", "Host", "Sql", "Kv", "list", "complete", "remove"].filterMap fun name =>
  if exportNameSafe name != exportNameSafe' name then
    some (name, exportNameSafe name, exportNameSafe' name) else none

/-- **The binder test is exact**: it holds of the printed binders and of no other name. -/
theorem binderNamed_iff (s : String) : binderNamed s = true ↔ ∃ i, s = Var.name i := by
  constructor
  · intro h
    unfold binderNamed at h
    split at h
    · exact ⟨_, of_decide_eq_true h⟩
    · exact absurd h Bool.false_ne_true
  · rintro ⟨i, rfl⟩
    have bytes : (Var.name i).toByteArray.data.toList = 97 :: (Nat.repr i).toByteArray.data.toList := by
      have ha : "a".toByteArray.data.toList = [97] := by decide
      rw [Var.name, String.toByteArray_append, ByteArray.data_append, Array.toList_append, ha]
      rfl
    unfold binderNamed
    rw [bytes]
    simp only [decodeBytes_repr, decide_true]

#print axioms binderNamed_iff
#print axioms exportNameFault

end Effect4.Program
```

## Appendix B. Commands and results

Each command ran in the worktree, through the slot script, as `lake env lean <file>`.

| File | Lines | Result |
| --- | --- | --- |
| `Sugar.lean` | 387 | exit 0; no error and no warning; the declared types and rows equal today's; 10 guards compare elaborated trees; a string literal alone has the type `string` |
| `Names.lean` | 101 | exit 0; the two tests differ at 7 of 20 names: `all` and `answer` become export names, and `eq`, `get`, `some`, `Effect` and `Data` stop being ones; `binderNamed_iff` is within `[propext, Quot.sound]` |
| `Probe1.lean` | 87 | the names and the arities of the atoms; today's test at seven names |
| `Probe5.lean` | 20 | 43 atoms; seven names resolve at Lean's root; seven are names of `Authoring` already |
