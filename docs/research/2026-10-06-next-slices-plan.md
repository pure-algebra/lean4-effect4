# 2026-10-06 the next slices, refined: a plan for review

Status: a research note (history, not authority). It rules nothing. The coordinator wrote it at
the owner's request, for the second reader's review before a slice starts. **Revised on
2026-10-06, after the two last seats landed**: seat PILOT (decisions row 298) and seat BOUNDS
(row 299). The owner then ratified the probe's recommendations (row 299, point 10), so slice
MATCH waits for no decision. No seat runs. Base: main at the commit that enters row 299.
**Slice ORDER landed the same day** (row 300). Section 5.1 says what it left. The coordinator's
review gives the rules that the next slices follow
(`docs/research/2026-10-06-slice-ORDER-review.md`). **Slice TABLE landed too** (row 302), with
its review (`docs/research/2026-10-06-slice-TABLE-review.md`). Section 5.2 says what it left.
Wave 1 is done. **The next hand-over is one chunk of four steps**, and
`docs/research/2026-10-06-chunk-2-brief.md` is its brief: QUERY, the probe of the TypeScript
printer, MATCH and CONVERT.

## 1. Question

Which slices come next, in which order, and what does each owe? What do the second reader's
reports change in the designs that we have?

## 2. The words of this note

- An **address table** holds one entry for each address of a program: the typing environment
  there, and the checker's answer there.
- An entry is **typed**, **refused** or **not reached**. It is not reached where a step on the
  way reads a sibling that the checker refuses.
- A **label** is data with a check: a rank or an order list, and a `Bool` function that reads it.
- The **frame of an edit** is the set of entries that an edit at an address cannot change.

Every other word is the dictionary's (`docs/core/controlled-english.md`): address, focus, focus
function, typing environment, omit, fill, union member, member rule, lifted rule, eliminator,
type slice, site.

## 3. What was read or run

| What | Evidence |
| --- | --- |
| The second reader's report on questions D2, D3, D5 and D6 of `docs/research/2026-10-06-probe-questions.md`, relayed by the owner in the session and not filed | reading |
| Lean 4.33.1 under `~/.elan/toolchains/leanprover--lean4---v4.33.1/src/lean`: `Lean/Elab/InfoTree/Types.lean`, `Lean/SubExpr.lean`, `Lean/Server/InfoUtils.lean`, `Lean/Language/Basic.lean`, `Lean/Meta/Transform.lean`, `Lean/Expr.lean`, `Lean/Server/Rpc/RequestHandling.lean`, `Lean/Widget/UserWidget.lean`, `Init/Data/List/Basic.lean` | reading, by search and by line |
| Batteries at the pinned revision `4488d40d`: `Batteries/Recycling/RBTree/Alter.lean`, and the README of that folder | reading |
| Decisions rows 281 to 297; the study of a gap with holes, sections 8 to 10; the receipts of the focus function and of seats UNION, FORM and CENSUS; the landing probe of the uniform eliminators | reading |
| Seat BOUNDS's receipt with its evidence folder; seat PILOT's design note, with the coordinator's landing note (`docs/research/2026-10-06-seat-PILOT-receipt.md`) | reading; both are merged |
| `docs/research/2026-10-06-graph-labels-probe.lean.txt`, with its output | tested: exit 0; two theorems at `[propext, Quot.sound]` |
| `docs/research/2026-10-06-address-table-probe.lean.txt` | tested: exit 0 with no output; 15 guards on five programs; no theorem |

Both probes ran through the Lean slot on main. Neither is a theorem of the tree.

## 4. Findings

### 4.1 The report, checked against the pinned sources

**Confirmed (read).** Each name stands where the report says, with the content that it gives.

- `InfoTree` has three constructors: `context`, `node` and `hole`. `TermInfo` holds the local
  context, the expected type and the expression. `TacticInfo` holds the goals and the
  metavariable contexts before and after. `InfoState.assignment` maps a hole to a tree.
- `SubExpr.Pos` is a `Nat` with four children for each node, and its four folds are `partial`.
- `SnapshotTree`, `SnapshotBundle.old?` and `SyntaxGuarded` are as the report says.
  `InfoTree.visitM` and `InfoTree.hoverableInfoAtM?` are `partial`.
- Batteries holds a path type with `zoom_fill'`, in a folder that its README calls deprecated.
- `transform` is `partial` and caches in a monad. The two evaluators of the RPC method and of
  the widget are private `unsafe` definitions of Lean core. The manifest holds no ProofWidgets.
- `Node.at_`, `Node.replaceAt`, `RefsWithin`, `Path.rank`, `Checker.check`,
  `ts/eff/json.gen.ts` and `ts/eff/wire.gen.ts` exist where the report names them.

**Corrected.**

| The report says | What the source says |
| --- | --- |
| The nearest thing to Lean's typed hole is `proof_goal` | A sketch's hole row is nearer: a host row with a declared type (`Row.hole` and `Sketch`, `src/Effect4/Program/Sketch.lean`; rows 288 and 291). `proof_goal` is the hole of a proof, and no hole of a program |
| `transform` caches by pointer equality | Its docstring says so. `ExprStructEq.beq` is `Expr.equal`, an equality by structure with a hash (`Lean/Expr.lean`). The conclusion stands: no pinned source has a pure generic form |
| Widget code stays under `tools/` because Lean's evaluators are `unsafe` | The trust rule binds the tree's own code, not Lean's. Two other reasons hold. A widget imports Lean's server modules. It also needs a JavaScript module, and a package needs the owner's yes |
| Form 1 of D5, as written, reduces under `decide` | As written it quantifies over every node, and it has no `Decidable` instance. As a check over the edge list it reduces (tested) |
| Form 3 reads `List.indexOf?` | The name is `List.idxOf?` in 4.33.1 |
| `WellFounded.fix` does not reduce in the kernel | Measured on one function by well-founded recursion on a number: `decide` and `rfl` fail, `decide +kernel` passes, and `simp` with the equation passes (tested). The proposition `WellFounded r` has no `Decidable` instance (tested) |
| `Path.rank : List Nat → Nat` | It takes a list of paths and a path: the rank of a site in the sorted list of sites |
| `ContextInfo` stores `env`, `mctx`, `fileMap` and `openDecls` | `CommandContextInfo` holds them, and `ContextInfo` extends it |

**Not checked:** the commit of ProofWidgets. No source of the tree holds it.

**On the orders:** the second reader agrees with the coordinator's probe
(`docs/research/2026-10-06-order-classes-probe.lean.txt`). Seat ORDER's brief stands as written.

### 4.2 Six findings that change what we build

1. **The address table is the first-order form of Lean's info tree.** Lean stores what its
   elaborator saw, by a side effect, and a request walks the stored tree. Our checker is a
   function, so the table is a function of the program. The probe states it from landed
   functions only. The generated path fold lists the addresses. `Node.envAt` answers the
   environment, and `Checker.check` answers the type or the refusal (tested). The program
   stores nothing more.
2. **Three slices stop waiting for the one pass.** The table is a specification. A tool, the
   TypeScript printer and a type slice can read it today, at the cost of the focus function. The linear
   pass becomes an implementation with one agreement theorem. It comes when a measure asks.
3. **Total marking has a specification at the addresses of a program.** The table's distinct
   refusals are the checker's refusals at every address of a program that it reaches. Take a
   generator body with two refused
   programs. `explain` answers one refusal, and the table holds both (tested). Where a later
   program reads a refused one, its entries are not reached (tested). Both halves of
   `marking-agrees` then follow from landed laws (not compiled). The entry at the root is the
   checker's answer. A typed program has a typed focus at every address (`hasTy_focusAt`).
4. **Reuse after an edit has a law here.** Lean reuses a result when the old syntax equals the
   new (`SyntaxGuarded`). We can reuse on a weaker test, with a proof: the edit keeps the
   focus's type. Each entry outside the focus is then unchanged (tested on one program). At the
   root that is `check_replace_focusAt`. The statement at every address is a proposed claim:
   the frame of an edit.
5. **A label is data with a check.** `decide`, `rfl` and the kernel read a rank and an order
   list alike (tested). One theorem says what the check means (`ranked_acyclic`, proved in
   scratch). The tree has such a label already: `RefsWithin` over `Path.rank`
   (`src/Effect4/Laws/Program/ReferenceExpansion.lean`). A `WellFounded` proposition is no
   label that a gate reads.
6. **Compute on demand needs no server and no package.** Four operations of the study's tool
   table have their function and their law in the tree today. They are the check, the
   omission, the filling and the context of a hole. A driver that reads one request
   and prints one answer is enough for a click. An editor view needs a JavaScript module, so it
   waits for the owner.

### 4.3 What the two landed seats change

- **Seat PILOT landed the first conversion** (row 298). A conversion is one line: `fiberTy` is
  `UnionRule.extend Member.fiber`. The extended rule keeps the member rule's own answer at a
  raw target, and it is the guarded rule elsewhere. The contract of a converted eliminator is
  stated once (`Eliminator.extend_laws`, the claim `union-rule-extend`).
- **Two rules need a first step.** `HasTy` states the list rule and the exit rule by shape.
  Their conversions state those rules through the function first, and that changes statements.
- **Seat BOUNDS's probe is merged, and the owner ratified its recommendations** (row 299). One
  function replaces the match of a template. A prelude atom is declared in the whole form,
  where tsgo computes the join itself. So an atom needs no printed type argument and no guard.
- **The checker and its prelude disagree at `cons` today** (the probe's finding). The scheme
  answers at a wide element with a union of two list types, and tsgo refuses the printed call.
  No program of the two corpora holds such a call. MATCH repairs it, so MATCH moves forward.
- **The typed print stays on two paths**: the guard's removal at an eliminator, and a row's
  type arguments at a binder term. Finding 2 lets it start early.

## 5. Proposals (not rulings): the slices

### 5.0 The order

```mermaid
flowchart TD
  ORDER
  TABLE --> QUERY
  TABLE --> PRINT
  TABLE --> COLUMN
  MATCH --> CONVERT
  PRINT --> UNGUARD
  CONVERT --> UNGUARD
  MATCH --> UNGUARD
  UNGUARD --> GAPLEAF
  TABLE --> PASS
  QUERY --> CLASSES
```

| Chunk | Slices | Why together |
| --- | --- | --- |
| 1, landed | ORDER, TABLE | Each adds modules and changes no statement. Their files are disjoint |
| 2 | QUERY; step 1 of PRINT; MATCH; CONVERT | One implementer works in one checkout, in a row. QUERY and the probe read the tree and rebuild nothing, so they come first. MATCH and CONVERT each rebuild the tree, so they come last and together |
| 3 | PRINT, steps 2 to 5; COLUMN | PRINT reads the probe's note and MATCH's guard at a binder term. COLUMN reads the table |
| 4 | UNGUARD | It needs PRINT, CONVERT and MATCH, and the owner has heard each widening |
| Later | PASS, CLASSES, GAPLEAF | Each has an entry condition (5.9 to 5.11) |

Two paths end at UNGUARD: TABLE, then PRINT; and MATCH, then CONVERT. MATCH comes before
CONVERT because it repairs a disagreement with tsgo, and a conversion repairs none. The
chunks replace the waves of the first version. The second model implements alone, so a
chunk is a row of steps and not a set of seats. One hand-back ends a chunk
(`docs/research/2026-10-06-chunk-2-brief.md`).

### 5.1 ORDER: the order of a lifted rule in Lean core's classes (landed, row 300)

The slice is landed. What it left for a later slice:

- **A carrier of answers states its order in core's classes** and takes `AnswerOrder.ofCore`.
  No slice writes the seven fields by hand again.
- **A join equation at a new carrier** is one application of `lift_union_eq_of`.
- **`lift_unique` and `lift_unique_pair` share their proof's shape**, 86 lines each. One lemma
  over the carrier is a candidate, when a third carrier comes.
- **A battery holds readers and controls only** (the review's rule).

### 5.2 TABLE: the address table and the list of refusals (landed, row 302)

The slice is landed. What it left for a later slice:

- **The table is a specification, and it is slow**: up to one check of the program for each
  entry. PASS answers the same table in one pass, and owes the agreement.
- **`mem_addresses_iff`, `refusals_head` and `refusals_nil_iff` are theorems.** The general
  law is `Node.mem_foldList_iff`: the path fold collects the yields of the addressed nodes
  and nothing else.
- **The slot table has its law** (`hasTy_extSlotEnv`). Its case for an operation's own term
  repeats one line of `bindTerm`, and MATCH gives both one function (row 302, point 5).
- **`table_replace_outside` is not stated.** It is the proposed claim `edit-frame`, for PASS.
  The battery tests it on one example with its red control.
- **Review questions 1 and 2 are open.** No slice looked for a counterexample to the frame
  of an edit. No law orders the refusals after the head.

The slice as it was planned:

- **Goal**: the address table as a library function, as the specification of every later pass.
- **New files**: `src/Effect4/Program/Typing/Table.lean` (a core module),
  `src/Effect4/Laws/Program/Typing/Table.lean`, `Test/Program/TableControls.lean`.
- **A first step.** `Node.foldList` and `PathYield` stand in the law graph
  (`src/Effect4/Laws/Program/PathFold.lean`), and a core module cannot import it. Write
  `Node.addresses` over the generated `foldMapAt` functions, or move the two definitions to a
  core module. Say which in the design note.
- **Definitions**, as the probe has them: `Node.addresses`, `Table.Entry`, `table` and
  `refusals`. Add `Sketch.table` over a sketch's signature, as `Sketch.focusAt` does.
- **A second part, for PRINT**: the environment of a term slot as a function, for the four
  slots that extend their node's environment. It is open items 2 and 3 of
  `docs/research/2026-10-06-seat-TRACE-receipt.md`.
- **Statements** (not compiled; the names are proposals):

```lean
-- not compiled
theorem mem_addresses_iff (n : Node Op) (a : List Nat) :
    a ∈ n.addresses ↔ (n.at_ a).isSome = true
theorem refusals_head (s : Signature Op) (env0 : TyEnv) (p : Eff Op) :
    (refusals s env0 p).head? = explain s env0 p
theorem refusals_nil_iff (s : Signature Op) (env0 : TyEnv) (p : Eff Op) :
    refusals s env0 p = [] ↔ (effTy s env0 p).isSome = true
-- the frame of an edit: a filling of the focus's type changes no entry outside the focus
theorem table_replace_outside {s : Signature Op} {env0 : TyEnv} {p p' q : Eff Op}
    {path a : List Nat} {f : Focus Op} (hf : focusAt s env0 p path = some f)
    (hq : effTy s f.env q = some f.ty)
    (hp : (Node.eff p).replaceAt path (.eff q) = some (.eff p')) (ha : ¬ path <+: a) :
    (Node.eff p').envAt s (.env env0) a = (Node.eff p).envAt s (.env env0) a ∧
      (focusAt s env0 p' a).map (·.ty) = (focusAt s env0 p a).map (·.ty)
```

- **Proof plan.** The first is the path fold's law (`foldList_subset_of_at`), with its converse
  to prove.
  The second and third read the root's entry and `hasTy_focusAt`. The fourth is the
  replacement law at each sub-program on the way to `a` (`NodeHasTy.replace_envAt`). It is
  read in both directions, since the old focus has the new one's type.
- **Controls**: the probe's 15 guards move to the control file.
- **Do not touch**: `Checker.check`; the functions of `src/Effect4/Program/Typing/Focus.lean`.

| Statement | Concept; claim | Reach | It does not establish | Consumer |
| --- | --- | --- | --- | --- |
| `mem_addresses_iff` | `initial-algebras-folds`; a step of `focus-function` | every node of the seven sorts | an order of the addresses | each statement below; QUERY |
| `refusals_head`, `refusals_nil_iff` | the same; `marking-agrees`, role compatibility; R14's open part becomes a claim | the addresses of a program | a refusal of a statement's, an action's or a layer's own rule, but through the program above it; a mark after a refused sibling that a rule reads; a repair | QUERY's refusals; the study's section 8.5 |
| `table_replace_outside` | the same; the proposed claim `edit-frame`, role substitution; R14 | a filling of the focus's type in the focus's environment; every address outside the focus | an edit that changes the focus's type; the entries inside the focus; behaviour | a tool that answers again after an edit; PASS |

### 5.3 QUERY: one driver that answers on demand

- **Goal**: one executable reads a request and prints an answer. Each operation is one library
  function, and each answer names the law that it stands on.
- **New files**: `tools/Drivers/Query.lean`, and a transcript fixture with its check. The
  `lean_exe` entry of `lakefile.toml` is the coordinator's: propose it in the receipt.
- **Input.** The program arrives as its canonical bytes (`decodeProgram`,
  `src/Effect4/Store/Domain/ProgramWire.lean`), at the empty application first. A search found
  no canonical codec of a sketch. The second step derives one, since this boundary reads it.
- **The operations, first version.** Each function is landed, or is TABLE's.

| Operation | Function | The law that the answer names |
| --- | --- | --- |
| check | `Sketch.check` | the checker decides; `holes_conservative` |
| addresses | `Node.addresses` | `mem_addresses_iff` |
| focus at an address | `Sketch.focusAt` | `focusAt_typed` |
| table, refusals | `Sketch.table`, `refusals` | `refusals_head`, `refusals_nil_iff` |
| omit at an address | `Sketch.omitAt`, with the hole row of the focus's type | `Sketch.check_omit_focusAt` |
| fill at an address | `Sketch.fillAt` | `Sketch.check_fill_focusAt` at the focus's type; a new check otherwise |

- **The protocol** is one JSON object for each request and each answer, with Lean's own `Json`
  under `tools/`. No server and no package. An MCP tool then maps to one operation.
- **Acceptance**: the transcript of the focus controls' example. Each answer equals the value
  that `Test/Program/FocusControls.lean` guards.
- **It does not establish**: any behaviour; a view; a stored session. It adds no theorem.
- **Later operations**: a type slice (COLUMN), a graph with its label (CLASSES) and the typed
  print (PRINT). The host session has the run's operations today.

### 5.4 PRINT: the printer writes the type arguments at a join

- **Goal**: at an eliminator whose term has more than one union member, the printed call
  carries its type arguments. Nothing else moves.
- **Step 1, a finite probe with tsgo 7.** List every printed form of the slot table of
  `docs/research/2026-10-06-seat-TRACE-receipt.md`, and each row call with a binder term. For
  each, run the form with the type arguments written at the join. The landing probe ran a few,
  and seat BOUNDS's probe ran `Ref.modify` with them (accepted).
- **Step 2, a second printer beside the first.** `printTyped` takes the typing environment
  where `print` takes its length. It gives each child its environment by `Node.childEnv`. A
  typed term printer asks `termTy` at each argument, so a term needs no address.
- **Step 3, the connector.** Let `NoJoin` say that no site of step 1's list needs a join. At
  an eliminator, its term has at most one union member. At a binder term, the interim guard
  of row 299 holds (5.6). Under `NoJoin` the two printers agree. While the guards stand, every
  admitted program has it.

```lean
-- not compiled; the names are proposals
theorem printTyped_eq_print (sig : Signature Op) (env : TyEnv) (e : Eff Op)
    (h : NoJoin sig env e) : printTyped sig env e = print sig env.length e
theorem check_noJoin (sig : Signature Op) (env : TyEnv) (e : Eff Op) (t : EffTy)
    (h : Checker.check sig env [] e = .ok t) : NoJoin sig env e   -- while the guards stand
```

- **Step 4, the reader.** A named map erases the type arguments of a join from printed syntax.
  The reader is today's reader after it. One law carries every read law over: the erased typed
  print is today's print.
- **Step 5**: the callers move to `printTyped`, and `print` stays as the form under `NoJoin`.
- **Controls**: the 73 modules of the truth lane and the 400 generated programs are unchanged
  byte for byte. Red: a join's type arguments with one member too few, refused by tsgo.
- **The type arguments are the lifted rule's answer.** By `Eliminator.adjoint` they are the
  least arguments at which the call checks. At a binder term they are the match's least
  bindings. State that as the printer's one fact for each site.
- **An atom prints no type argument.** Its prelude declaration computes the join (5.6).
- **Do not touch**: the template table's rows for other constructors; `Checker.check`.
- **Gates at the merge**: the wide gates with `check-tsdiag`, `check-corpus` and `check-ingest`.

| Statement | Concept; claim | Reach | It does not establish | Consumer |
| --- | --- | --- | --- | --- |
| the connector, the erasure law | `exact-codecs`; a step of the claim that `Effect4.Program.roundTrip_eq` serves | every program that the two printers print | that tsgo accepts a printed form: the lanes test that | UNGUARD; the removal of the binder term's guard |

### 5.5 CONVERT: the other eliminators, in the fiber rule's form

- **Goal**: each rule that reads a head is the extended rule of its member rule, as the fiber
  rule is (decisions row 298).
- **The form of one conversion**, as it landed:
  1. the by-shape function moves to `Member.<rule>`, and the rule becomes
     `UnionRule.extend Member.<rule>`, in one line;
  2. one section of `src/Effect4/Laws/Program/Eliminators.lean` holds its member facts: the
     instance of `Eliminator`, the one union member, the closed answer and the upper form;
  3. the rule's shape lemma goes, and each use moves the value up by `fits_subN` and the upper
     form: one line removed and one added;
  4. the contract is `Eliminator.extend_laws`, and no conversion proves it again.
- **The rules**: `Checker.listOf?`, `Checker.exitOf?`, `Decision.arms` at an option, and the
  cause rule. The list, exit, option and cause constructors answer at one union member, so
  `Eliminator.extend_liftOne` holds at each. The cause rule reads two heads and owes four
  member facts. A rule on an invariant handle is not converted.
- **A first step at two rules.** `HasTy` states the list rule and the exit rule by shape
  (`src/Effect4/Laws/Program/Typing/HasTy.lean`), with `listOf?_eq_some` and `exitOf?_eq_some`
  in the checker's bank. State those rules through the function first. That changes
  statements, so give the two statement lists.
- **Then the equalities**, as one slice: `Ty.sub t T` in place of `t = T` at the four Boolean
  tests, `restore`, the scope of `forkIn`, `setContext` and the interruptor.
- **Controls and gates**: the differential of the two corpora. Its producer is filed:
  `docs/research/2026-10-06-seat-PILOT-evidence/differential.lean.txt`. Pin the case policy
  again at each conversion, since the match on `Ty` moves to the member rule. A program that
  was admitted and is refused is a finding, and the owner hears of it first (row 294, point 5).
- **Placement**: concept `subtyping-algebra`; the claim `union-rule-extend`, one instance each;
  R14. Each conversion admits more programs: at `never`, and at one union member under a raw
  union. The coordinator reports each to the owner (row 285, point 3).

### 5.6 MATCH: the match of a template by bounds

The owner ratified the probe's recommendations (decisions row 299, point 10), and this slice
implements them. Its sources are `docs/research/2026-10-06-seat-BOUNDS-receipt.md` and the
evidence folder beside it.

- **Goal**: one function matches a template for atoms, rows and binder terms. It joins each
  parameter's lower bounds, and it reads a request up to its normal form.
- **The function** is the receipt's section 6.1, compiled in scratch
  (`scripts/Bounds.lean.txt` of the evidence folder). Its parts are `cands`, `solve` and
  `matchB`. `matchArgsB` reads an argument list, and `bindTermB` a binder term.
- **The definitions that change** (the receipt's section 11):
  - in `src/Effect4/Program/Ty.lean`: `Ty.infer` with its two siblings, `Ty.matchTemplate`,
    `Ty.matchTemplateArgs` and `Ty.templateAdmissible`;
  - in `src/Effect4/Program/NativeAtom.lean`: `Scheme.poly` and `Scheme.apply`, which lose the
    `join` flag;
  - in `src/Effect4/Program/Typing/Rules.lean`: `bindTerm` and `checkRow`;
  - in `src/Effect4/Machine/Term.lean`: the prelude strings.
- **The four ratified parts.**
  1. The match by bounds replaces the first-occurrence match and the `join` flag.
  2. A signature's admission refuses a template with a parameter under a nominal reference.
     No template of the tree has one.
  3. A prelude atom is declared in the whole form: a parameter is an argument's whole type,
     and the answer is read from it by index. The probe wrote it for six atoms: `getOrElse`,
     `ite`, `cons`, `append`, `get` and `mapFromEntries`. The cross form with its guard is the
     second choice, and the coordinator reports it if it is taken. The plain split is not
     used: it refuses calls that today's `append` accepts.
  4. The interim guards, by site. An atom has none, under the whole form. A row's request has
     none. A binder term keeps today's raw reading, with one guard. The term's type offers a
     greatest lower bound to each parameter that the cell does not fix. That guard goes with
     PRINT.
- **The statements** are the six of the receipt's section 10, each with its placement there:
  - S1: each argument is below its instance at the final bindings, in `Ty.subN`;
  - S2: a request below some instance has a match, and the match is the least one;
  - S3: where the present match answers, the match by bounds answers the same types;
  - S4: smaller arguments give smaller bindings;
  - S5: two requests with one normal form have one match;
  - S6: each template of the tree is in the reach of S2.
- Each compiles in scratch at `[propext, Quot.sound]`, within the premise. Three more are
  stated and not compiled. They are S3 at an argument list without its premise, S3 at a binder
  term's raw type, and each law under a nominal reference.
- **The claims.** `template-match-anchored` gives way to a claim of the complete match (S2).
  `checker-monotone` loses its clause on schemes and rows, and keeps the loop's.
- **The churn**, measured by the probe: 21 files and 530 lines name the present match or one
  of its laws. The anchored section of `src/Effect4/Laws/Program/Template.lean` holds 53 of
  its 99 declarations, and the complete match replaces it.
- **Controls**: the table of the receipt's section 6.1, as guards. Red: an invariant
  occurrence still refuses. The control of row 294, point 4, turns: `mapFromEntries` answers
  at a raw type and at its normal form alike.
- **It admits more programs**, by design: two candidates with no order now join. The probe
  found no moved type in 10284 applications of the two corpora. Name each moved row in the
  compatibility policy, and the coordinator reports it with the merge.
- **Gates at the merge**: the wide gates with `check-tsdiag`, `check-corpus`, `check-ingest`
  and `make check-target`. The citation query reads the prelude's declarations, and the probe
  emulated it: it did not run `check-target`.
- **A first commit that stands alone**: the declaration of `cons`. In the probe's model the
  cross form and the whole form each remove the disagreement of section 4.3. Today's match
  need not change for that (row 299, point 7). So the prelude can move before the match does.
- **It carries** the repair of the population filter (row 293, point 9), since both rebuild
  the tree.
- **Do not touch**: `Ty.join`, `Ty.normalize`, `Ty.sub`; the rules of `HasTy`.

| Statement | Concept; claim | Reach | It does not establish | Consumer |
| --- | --- | --- | --- | --- |
| S1 to S6 of the receipt | `subtyping-algebra`; `template-match-anchored`, restated as the complete match; a share of `checker-monotone`; R4 and R14 | a normal, admissible template with no nominal reference; a request of any raw form, read at its normal form; the order `Ty.subN` | a match under a union head or a nominal reference; membership of a value; a run; tsgo's inference | `rowTy_fits`, `syncRow_typed`; the removal of the raw answer; the gap's rule at a cell |

### 5.7 UNGUARD: the guards go, and the checker is monotone at its eliminators

- **Entry**: PRINT, CONVERT and MATCH are merged, and the owner has heard.
- **Three steps of one line each.** The binder term's guard goes, and the term is read at its
  normal form. The converted rules then answer the normal form: `UnionRule.extend` becomes
  `UnionRule.liftOne`. Then `UnionRule.liftOne` becomes `UnionRule.lift`.
- **The statement** is `checker-monotone`, in the corrected sentence of the study's section
  10.2, without its clause on schemes and rows (row 299).
- **Gates**: the conservativity script with the policy's names; the truth lane and the
  diagnostics lane on programs with a proper union, printed by `printTyped`.

### 5.8 COLUMN: type slices of the error and of the requirement

The study's brief stands (its section 9.7), with two changes. Its premise is row 290's: no
closed edge above an omitted address, or an error of `never` there. Its first step reads
TABLE's table, so it waits for no pass.

### 5.9 PASS: the linear pass, as a design probe

**Entry condition**: a measure. Run `table` on the largest programs of the two corpora first.
Three candidates, none compiled:

| Candidate | The idea | Cost |
| --- | --- | --- |
| M | The checker over a monad that records each node | The 65 arms and each proof that unfolds one (row 294, point 3). It marks at every sort |
| H | The node over holes. Check each child once. Omit each child to a hole row of its type, and ask the checker for the node over the holes | The checker does not change. The agreement is the omission's law (`Sketch.check_omit_focusAt`). It is exact where checked types are in normal form, so it follows UNGUARD |
| I | Keep the table. After an edit, check the focus again, and the entries that read a changed type | It needs `edit-frame`, and a stored table beside the sketch |

### 5.10 CLASSES: a label for each graph

**Entry condition**: QUERY has landed, and a view or a gate asks for a label.

- One small module: the two checks of the probe, `ranked_acyclic`, and a check that each node
  has one parent at most. No framework beyond what a consumer reads.
- **The labels.** The addresses of a program are a tree: the parent of an address drops its
  last index, and the rank is the length. The layer references have their rank already. The
  sites of a slice view form a tree, which the descent over a tree of sites reads (row 286,
  point 3). The order of `Node.addresses` is an order list for the table's own dependencies.
  That is a reading: an entry reads the entries above it and those of earlier siblings.
- **The first consumer** is QUERY: a graph's answer holds the nodes, the edges and the label.
  A view then picks a layout by the label, and a client runs the check again.
- The module graph and the proof plan get no label: Lean and Lake check both already.

### 5.11 GAPLEAF: the gap as a leaf of `Ty`

The study's brief stands (its section 9.7). It follows UNGUARD and TABLE. The coordinator tells
the owner before the append lands (row 288, point 5). Seat BOUNDS's receipt adds one fact: the
gap's rule at a cell is the function of the match by bounds.

### 5.12 The small repairs, each placed

| Repair | Lands with |
| --- | --- |
| The population filter reads a name as generated (rows 286 and 293) | MATCH |
| The five items of row 297, point 8 | COLUMN, or one short seat |
| The items of row 295, point 8, on the TypeScript lanes | PRINT |
| A generated step for the 54 arms and the 60 cases (the focus function's receipt, item 5) | PASS, if candidate M is taken |

### 5.13 What a lander needs beyond `AGENTS.md`

- Run every Lean, Lake and `make` command through `scratch/lean-slot.sh`. Run one `lake` in a
  worktree at a time.
- Write `-o ts/eff/node_modules -o harness/truth/node_modules` on every `make` call.
- Install nothing. A `bun` run outside `ts/eff` and `harness/truth` takes `--no-install`.
- Run tsgo by its path under `ts/eff/node_modules/.bin`.
- Send a design note first, one page, with each statement compiled in scratch.
- End with a receipt in the handoff form of `AGENTS.md`, and propose each registry text there.

The coordinator merges each head with the wide gates, in this order:

1. `lake build`, `make gen-fixtures` and `make corpus`;
2. `dune build` and `dune test --force engine`, each through `opam exec --switch=effect4`;
3. `make gen-truth` and `make check-truth`;
4. `make gen-semantics`, `make check-semantics`, `make check-cases`, `make check-docs` and
   `make check-language`;
5. `make gen-architecture` and `lake env lean Test/All.lean`;
6. `make check-conservativity` against the base, and `make check-tsdiag`.

## 6. Questions for the review

1. **TABLE.** Does `table_replace_outside` have a counterexample? Look where `Node.childEnv`
   reads something that is no sibling's type: the arms of `select`, and the cursor of `iterate`.
2. **TABLE.** After the head, is the order of `refusals` the checker's own order? The plan
   claims the head only.
3. **PRINT.** Which printed form has no place for a type argument? Give the full list for step 1.
4. **PRINT.** Is a table by address better than the second printer? It needs an address
   inside a term, which the tree does not have.
5. **QUERY.** A program's bytes do not name its row table. Which identity does a request carry?
6. **ORDER.** The brief's item 4 has two forms. Count the statements and the lines of each.
7. **PASS.** Does candidate H hold at a node whose rule reads a child's raw type?
8. **CLASSES.** Which graph gets its label first, and what reads it?
9. **MATCH.** The whole form changes what the citation query reads. Does `make check-target`
   read each atom at its parameter's template, as the probe's emulation does?
10. **CONVERT.** Which statements of `HasTy` change when the list rule and the exit rule are
    stated through the function?

## 7. What waits for the owner

1. **Nothing blocks chunk 2.** The owner ratified the probe's recommendations on
   2026-10-06 (row 299, point 10), and a conversion lands with a report (row 285, point 3).
2. **Rows 296 (point 5) and 297 (point 4)** stay open to overrule.
3. **Each widening of the admitted programs**: MATCH's, CONVERT's and UNGUARD's, each reported
   with its merge.
4. **The append of the gap's leaf**, before it lands.
5. **An editor view** needs a JavaScript package. The plan proposes none.
6. **The frozen contracts' pins**: their statement pins and their bare `#check` lines
   (rows 301 and 302). The coordinator touches neither before the owner decides.
7. **Whether the second model commits each stage on a branch of the checkout.** The brief of
   chunk 2 asks for it, so that the coordinator reviews stage by stage. Without it the
   receipt names the files of each stage.

The plan assumes that the coordinator merges each slice with the wide gates and writes the
records, as `AGENTS.md` says.

## 8. What this does not establish

- No theorem of the tree. Each statement of section 5 is not compiled, but for the two probes.
- The probes are finite: five programs, and one relation of four nodes.
- The cost of the table is not measured.
- Section 5.6 rests on a probe: each of its laws is a scratch file, and its counts are finite.
- Step 1 of PRINT is not run. The landing probe ran a few forms with written type arguments.
- The second reader's claims on a library that is no dependency are not checked.
