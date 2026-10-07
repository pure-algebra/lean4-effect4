# 2026-10-06 seat SKETCH receipt: slice TRACE, first half, the focus function

**The one thing to know before merging:** one statement of slice REPLACE changes, and it is a
step. `NodeHasTy.child_step` gains one conjunct. `NodeHasTy.replace`, the pointer of the claim
`typed-replacement`, keeps its statement and is now a corollary of `NodeHasTy.replace_envAt`.

Second: one answer of the focus function costs up to one check of the program. A caller that
asks at many addresses carries the environment down, or waits for the pass of the second half.

Status: a receipt (history, not authority). The slice is the first half of the study's "Slice
TRACE" (`docs/research/2026-10-06-seat-GAP-study.md`, section 9.7), under decisions row 292. Its
brief is `docs/research/2026-10-05-claude-lead/briefs/seat-trace-brief.md`, as amended. Its
design note is `docs/research/2026-10-06-seat-TRACE-design.md`. The dictionary's trace is the
machine's list of run events, so this receipt says "the focus function" and never "the trace".

## Base and head

Branch `seat/sketch`, in the worktree `/Users/pooks/Dev/lean4-effect4-t3b`. The slice starts at
`15531103`, the head of slice REPLACE. The branch's base is `ea0f584a`: I merged nothing from
main. The head is the commit that adds this receipt.

| Commit | What |
| --- | --- |
| `f522f1c1` | the design note, with its two scratch probes |
| `524fd0cc` | the core module: the step, its fold, `focusAt`; `Sketch.focusAt` |
| `a34425e8` | the statements as nine planned goals, each placed |
| `91cf14c6` | each goal proved in place; the step lemma's conjunct |
| `a3bd195c` | the battery and its root import |
| the head | this receipt |

## Changed files

| File | Change |
| --- | --- |
| `src/Effect4/Program/Typing/Focus.lean` | new, a Lean module (row 200): `NodeEnv`, `Node.childEnv`, `Node.envAt`, `Focus`, `focusAt` |
| `src/Effect4/Program/Sketch.lean` | one import; `Sketch.focusAt`; one paragraph of the head |
| `src/Effect4.lean` | one import, directly after `import Effect4.Program.Typing.Agreement` |
| `src/Effect4/Laws/Program/Typing/Replace.lean` | one import; `NodeTy.env`; `effTy_map_of_hasTy`; the conjunct of `NodeHasTy.child_step`; `NodeHasTy.replace_envAt`; `NodeHasTy.replace` as its corollary; the head |
| `src/Effect4/Laws/Program/Typing/Focus.lean` | new: seven theorems on `focusAt` |
| `src/Effect4/Laws/Program/Sketch.lean` | one import; three theorems; the head's table and placement |
| `src/Effect4/Laws.lean` | one import, directly after `import Effect4.Laws.Program.Typing.Check` |
| `Test/Program/FocusControls.lean` | new: the controls |
| `Test/All.lean` | one import, directly after `import Test.Program.BlameContract` |
| `docs/research/2026-10-06-seat-TRACE-design.md`, and three probe files beside it | new |
| `docs/research/2026-10-06-seat-TRACE-receipt.md` | new: this receipt |

The slice changes no line of `Checker.check`, of `explain`, of a refusal, of `HasTy` or of
`Node.replaceAt`. No proof looks inside `Record.fieldType`, `Record.setType` or
`Formation.HeadFormed`.

## What the slice decided

1. **Three shapes of environment** (`NodeEnv`). `HasTy`, `EffsHasTy` and `ActionHasTy` read an
   environment. `StmtsHasTy` reads the loop flag too. The two layer judgments read nothing.
2. **The step has one case for each arm of `Node.child`**, and one more for the statements after
   a `bindYield`: 54 arms. Eleven read a type first. Eight ask `effTy` for an earlier sibling
   program's type, and three ask `termTy` for the type of a term of the node.
3. **The step reads the node's environment by projection**, and it matches the node and the
   index alone. So its matcher has the shape of `Node.child`'s, and each environment fact of the
   step lemma is `rfl` or one lemma.
4. **`Node.envAt` and `focusAt` are two functions.** The first answers at every sort of node,
   and where the node has no type. The second adds the checker's type at a program.
5. **`NodeHasTy.child_step` is strengthened in place**, and no second step lemma is written.
   The 60 cases keep their text. The 58 with a child gain one component: `rfl` in 47, and one
   lemma in 11. One induction then proves `NodeHasTy.replace_envAt`.
6. **The two edits of a sketch are stated again at the computed focus**, beside the two
   statements of slice REPLACE, which do not change.

## Commands and results

Each Lean, Lake and `make` command ran from the worktree's root, through
`/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`. `SCRATCH` is the seat's scratch folder.
`FLAGS` is `-o build -o ts/eff/node_modules -o harness/truth/node_modules`.

| # | Command | Result |
| --- | --- | --- |
| 1 | `lake env lean -M6144 SCRATCH/focus_probe1.lean` | exit 0: the definitions, six idioms of the environment fact, the values of the controls |
| 2 | `lake env lean -M6144 SCRATCH/focus_probe2.lean` | exit 0, at the first run: eleven theorems print axioms within `[propext, Quot.sound]` |
| 3 | `lake build Effect4.Program.Typing.Focus Effect4.Program.Sketch Effect4`, two runs | the last: `Build completed successfully (201 jobs).`, exit 0 |
| 4 | `lake build Effect4.Laws.Program.Typing.Focus Effect4.Laws.Program.Sketch`, at the goals | `Build completed successfully (285 jobs).`, exit 0 |
| 5 | the same command, at the proofs | `Build completed successfully (285 jobs).`, exit 0 |
| 6 | `lake build Test.Program.FocusControls` | `Build completed successfully (288 jobs).`, exit 0 |
| 7 | `lake build`, at `a3bd195c` | `Build completed successfully (1045 jobs).`, exit 0 |
| 8 | `lake env lean -M6144 SCRATCH/status-trace.lean` | exit 0: the axioms, the plan status and the census below |
| 9 | `make FLAGS gen-fixtures` | `PASS generate: requested producers ran in dependency order`, exit 0; no file changed |
| 10 | `make FLAGS check-cases` | `conform cases: PASS, exit 0; .lake/conform/cases.json`, exit 0 |
| 11 | `make FLAGS check-docs` | `PASS check-docs: every path, link, citation and make target in 76 documents resolves`, exit 0 |
| 12 | `make FLAGS check-proof-style` | exit 0 |
| 13 | `python3 scripts/check-language.py --show`, on the design note and on this receipt | no finding |

Commands 7 to 12 ran at `a3bd195c`, the head before this receipt. The first run of command 3
failed on my own text: inside `namespace NodeEnv` a pattern variable named `env` is read as the
constructor. The report of command 10 names no site in `Node.childEnv`, and the policy needs no
row for it.

Not run: `check-gen`, `check-slow`, `check-corpus`, `check-target`, `check-truth`, the
conservativity script, `gen-semantics`, `gen-architecture`. No TypeScript ran and no OCaml ran.

## Axiom output

The gate lines of command 7:

```text
info: Test/All.lean:290:0: Effect4 library-root gate: 181 API/utility modules, 325 Laws-only modules; every library source is reachable; Effect4 never reaches Laws
info: Test/All.lean:290:0: Effect4 module and axiom gate: checked 795 modules and 91904 declarations; phases (ms): sources and closure 33, library roots 509, declarations 5604, resolution 1091, axioms 22997, exemptions 436; semantic/test axioms are [propext,
 Quot.sound]; exact implementation boundary (17 module(s), 23 declaration(s)) additionally allows Classical.choice
info: Test/All.lean:290:0: Effect4 goal gate: 28 planned goal(s), each a theorem whose body is `sorry` outside the Effect4 root; 12 declaration(s) rest on goals; no other declaration reaches sorryAx
```

No planned goal of the slice is open: the goal gate counts what it counted at the slice's
start. Command 8, for each theorem that the slice adds or changes:

| Theorem | Axioms | Plan status |
| --- | --- | --- |
| `effTy_map_of_hasTy` | `[propext, Quot.sound]` | proved |
| `NodeHasTy.child_step` | `[propext, Quot.sound]` | proved |
| `NodeHasTy.replace_envAt` | `[propext, Quot.sound]` | proved |
| `NodeHasTy.replace` | `[propext, Quot.sound]` | proved |
| `focusAt_eq_some` | `[propext, Quot.sound]` | proved |
| `focusAt_nil` | `[propext, Quot.sound]` | proved |
| `focusAt_typed` | `[propext, Quot.sound]` | proved |
| `hasTy_focusAt` | `[propext, Quot.sound]` | proved |
| `hasTy_replace_focusAt` | `[propext, Quot.sound]` | proved |
| `check_focusAt` | `[propext, Quot.sound]` | proved |
| `check_replace_focusAt` | `[propext, Quot.sound]` | proved |
| `Sketch.check_focusAt` | `[propext, Quot.sound]` | proved |
| `Sketch.check_fill_focusAt` | `[propext, Quot.sound]` | proved |
| `Sketch.check_omit_focusAt` | `[propext, Quot.sound]` | proved |

`#plan_status` ends with `next goals: 0`. `#semantics_census` lists every theorem of the three
law modules under `initial-algebras-folds`, with none untagged.

## Evidence

- **Proved**: twelve new theorems, and two changed ones (`NodeHasTy.child_step`, its statement;
  `NodeHasTy.replace`, its proof). The axiom gate read them in command 7.
- **Proved**: three theorems of the battery. Two take a conclusion from the law at a focus that
  reads its environment: `fill_a_reading_focus` and `omit_a_reading_focus`.
- **Tested**: the battery's 46 `#guard` lines. Each is a finite check on named programs.
- **Reading**: the table of term slots, and the cost bounds, in the section on the printer.
- Bounded evidence: every control is one program. No evidence is host-only.

## The statements as compiled

```lean
inductive NodeEnv where                       -- src/Effect4/Program/Typing/Focus.lean
  | env (env : TyEnv)
  | body (env : TyEnv) (inLoop : Bool)
  | closed
def Node.childEnv (s : Signature Op) (ctx : NodeEnv) : Node Op → Nat → Option NodeEnv
def Node.envAt (s : Signature Op) : NodeEnv → Node Op → List Nat → Option NodeEnv
structure Focus (Op : Type) where
  program : Eff Op
  env : TyEnv
  ty : EffTy
def focusAt (s : Signature Op) (env0 : TyEnv) (p : Eff Op) (path : List Nat) : Option (Focus Op)
def Sketch.focusAt (s : Sketch) (app : SigApp) (path : List Nat) : Option (Focus NativeOp)

theorem NodeHasTy.child_step {s : Signature Op} {n c : Node Op} {τ : NodeTy Op} {i : Nat}
    (hn : NodeHasTy s n τ) (hc : n.child i = some c)
    (hlead : ∃ rest q, c.at_ rest = some (.eff q)) :
    ∃ τc, NodeHasTy s c τc ∧ n.childEnv s τ.env i = some τc.env ∧
      ∀ {s' : Signature Op} {c' n' : Node Op}, SigExtends s s' → NodeHasTy s' c' τc →
        n.setChild i c' = some n' → NodeHasTy s' n' τ

theorem NodeHasTy.replace_envAt {s : Signature Op} (path : List Nat) {n : Node Op}
    {τ : NodeTy Op} {q : Eff Op} (hn : NodeHasTy s n τ) (hat : n.at_ path = some (.eff q)) :
    ∃ (env : TyEnv) (t : EffTy), n.envAt s τ.env path = some (.env env) ∧ HasTy s env q t ∧
      ∀ {s' : Signature Op} {q' : Eff Op} {n' : Node Op}, SigExtends s s' → HasTy s' env q' t →
        n.replaceAt path (.eff q') = some n' → NodeHasTy s' n' τ

theorem focusAt_eq_some {s : Signature Op} {env0 : TyEnv} {p : Eff Op} {path : List Nat}
    {f : Focus Op} :
    focusAt s env0 p path = some f ↔
      (Node.eff p).at_ path = some (.eff f.program) ∧
        (Node.eff p).envAt s (.env env0) path = some (.env f.env) ∧
        effTy s f.env f.program = some f.ty

theorem focusAt_nil (s : Signature Op) (env0 : TyEnv) (p : Eff Op) :
    focusAt s env0 p [] = (effTy s env0 p).map fun t => ⟨p, env0, t⟩

theorem focusAt_typed {s : Signature Op} {env0 : TyEnv} {p : Eff Op} {path : List Nat}
    {f : Focus Op} (hf : focusAt s env0 p path = some f) :
    (Node.eff p).at_ path = some (.eff f.program) ∧ HasTy s f.env f.program f.ty

theorem hasTy_focusAt {s : Signature Op} {env0 : TyEnv} {p q : Eff Op} {T : EffTy}
    {path : List Nat} (hp : HasTy s env0 p T) (hat : (Node.eff p).at_ path = some (.eff q)) :
    ∃ (env : TyEnv) (t : EffTy), focusAt s env0 p path = some ⟨q, env, t⟩

theorem hasTy_replace_focusAt {s : Signature Op} {env0 : TyEnv} {p : Eff Op} {T : EffTy}
    {path : List Nat} {f : Focus Op} (hp : HasTy s env0 p T)
    (hf : focusAt s env0 p path = some f) {s' : Signature Op} {q' p' : Eff Op}
    (hext : SigExtends s s') (hq' : HasTy s' f.env q' f.ty)
    (hrep : (Node.eff p).replaceAt path (.eff q') = some (.eff p')) : HasTy s' env0 p' T

theorem check_focusAt {s : Signature Op} {env0 : TyEnv} {p0 : List Nat} {p q : Eff Op}
    {T : EffTy} {path : List Nat} (hp : Checker.check s env0 p0 p = .ok T)
    (hat : (Node.eff p).at_ path = some (.eff q)) :
    ∃ (env : TyEnv) (t : EffTy), focusAt s env0 p path = some ⟨q, env, t⟩

theorem check_replace_focusAt {s : Signature Op} {env0 : TyEnv} {p0 : List Nat} {p : Eff Op}
    {T : EffTy} {path : List Nat} {f : Focus Op} (hp : Checker.check s env0 p0 p = .ok T)
    (hf : focusAt s env0 p path = some f) {s' : Signature Op} {q' : Eff Op} {pq : List Nat}
    (hext : SigExtends s s') (hq' : Checker.check s' f.env pq q' = .ok f.ty) :
    ∃ p', (Node.eff p).replaceAt path (.eff q') = some (.eff p') ∧
      ∀ p1, Checker.check s' env0 p1 p' = .ok T

theorem Sketch.check_focusAt (s : Sketch) (app : SigApp) {T : EffTy} {path : List Nat}
    {q : NativeEff} (hs : s.check app = .ok T)
    (hat : (Node.eff s.program).at_ path = some (.eff q)) :
    ∃ (env : TyEnv) (t : EffTy), s.focusAt app path = some ⟨q, env, t⟩

theorem Sketch.check_fill_focusAt (s : Sketch) (app : SigApp) {T : EffTy} {path : List Nat}
    {f : Focus NativeOp} (hs : s.check app = .ok T) (hf : s.focusAt app path = some f)
    (more : RowTable) {q' : NativeEff} {pq : List Nat}
    (hq' : Checker.check (app.withHoles (s.holes ++ more)).signature f.env pq q' = .ok f.ty) :
    ∃ s', Sketch.fillAt { s with holes := s.holes ++ more } path q' = some s' ∧
      s'.check app = .ok T

theorem Sketch.check_omit_focusAt (s : Sketch) (app : SigApp) {T : EffTy} {path : List Nat}
    {f : Focus NativeOp} (hs : s.check app = .ok T) (hf : s.focusAt app path = some f)
    (name : String) (hans : f.ty.answer.closed = true) (herr : f.ty.error.closed = true)
    (hansN : f.ty.answer.normalize = f.ty.answer) (herrN : f.ty.error.normalize = f.ty.error)
    (formed : Formation.Formed (Formation.instantiatedSites
      (Row.hole name f.ty.answer f.ty.error f.ty.requires.elems).normalizeTypes [])) :
    ∃ s', s.omitAt app path (Row.hole name f.ty.answer f.ty.error f.ty.requires.elems) = some s' ∧
      s'.check app = .ok T
```

`NodeHasTy.replace` and the other nine statements of slice REPLACE stand as merged.

## Landed theorems and their placement

All twelve carry `@[semantics "initial-algebras-folds" (requirement := R14)]`.

**`NodeHasTy.replace_envAt`, with the step lemma's conjunct and `effTy_map_of_hasTy`.**

- Concept: `initial-algebras-folds`; property: the typing judgment follows the program's
  constructors, so its rules invert at one child, and along a path.
- Question: the registry's open part `focus-function`, proposed here as a claim (role
  inversion); pointer `NodeHasTy.replace_envAt`.
- Reach, under rows 288 and 292:
  - the six judgments, at every typing signature of every operation alphabet;
  - a program as the focus, at every address;
  - every extension of the typing signature;
  - the environment as `Node.envAt` answers it, from the environment of the node at the root.
- Does not establish:
  - an environment after a sibling that the checker refuses;
  - any behaviour;
  - a focus of a smaller type, or of a type that is equal only after normalization;
  - a term as the focus.
- Unlocks: R14. It makes the replacement law usable by a function's caller.

**The seven theorems on `focusAt`.**

- Concept and question: the same claim, stated at a program and at the checker.
- Reach: `focusAt_typed` and `focusAt_eq_some` hold for every program, typed or not. The two
  answers (`hasTy_focusAt`, `check_focusAt`) and the two laws (`hasTy_replace_focusAt`,
  `check_replace_focusAt`) start from a typed program.
- Does not establish: a bound on the cost; the environment of a term slot that extends its
  node's environment.
- Consumers: the three theorems on a sketch; a reader of a term's type at a node.

**`Sketch.check_focusAt`, `Sketch.check_fill_focusAt`, `Sketch.check_omit_focusAt`.**

- Concept and question: consumers of `focus-function` on a sketch; their own consumer is a
  tool's fill and omit at an address.
- Reach: a sketch that the checker admits, and the focus that `Sketch.focusAt` answers. The
  omission's premises are on the answered type, so a tool decides each.
- Does not establish:
  - an omission at a type that is equal only after normalization (slice REPLACE's limit);
  - an omission with the row that declares the answer alone (slice COLUMN);
  - any behaviour.

## What the printer reads at an eliminator

This section is the input of the next slice. It is a reading of `Checker.check` and of `argTy`,
with two tested controls. The term whose type an eliminator reads is called its term here.

**The read.** The TypeScript printer stands at a node and prints an eliminator. It reads three
things, and it needs no type of the node itself:

1. the environment of the node: `Node.envAt`, or `Node.childEnv` step by step on its way down;
2. the environment of the term's slot: the node's own, or one of four extensions (the table);
3. the type of the eliminator's term: `termTy` there. `Ty.members` lists the members that the
   type arguments of the join are written from.

**Tested.** Under `length`, the environment at the node is one variable of two members: a list
of numbers and a list of strings. `termTy` answers both. With two fiber types under a join
the checker refuses the node as `notFiber`, and `focusAt` answers none there. `Node.envAt`
still answers, and the term has its two fiber types. So the printer's read does not depend on
the conversion of the eliminator (`Test/Program/FocusControls.lean`).

**Where an eliminator's term stands.**

| Node | The term | The rule reads |
| --- | --- | --- |
| `awaitFiber fiber mode` | `fiber` | `fiberTy` |
| `select s d a0 a1` | `s` | `Decision.arms` |
| the actions `runIn`, `interrupt`, `interruptScoped` | `target` | `fiberTy` |
| the actions `interruptAll`, `awaitAll`, `awaitAllFailFast` | `targets` | `Checker.listOf?`, then `fiberTy` |
| the action `closeScope scope exit` | `exit` | `Checker.exitOf?` |
| a term `field`, `recordSet`, `tupleAt` | its target | `Record.fieldType`, `Record.setType`, `Tuple.typeAt` |
| a term `fold accTy list init body` | `list` | `Checker.listOf?` |
| an application of an atom | each argument | the atom's scheme (`Signature.atomOf`) |

Each term of the first five rows is typed at its node's environment. A term of the last three
rows stands inside another term, and it is typed at that term's environment. Under the body of
a `fold` that environment has two more variables, the accumulator and the element.

**The four slots that extend their node's environment.** Every other term slot of a program, of
a statement and of a fiber action is typed at the node's environment.

| Slot | Its environment | From the step function |
| --- | --- | --- |
| the test of `catchIf test body handler` | the node's, and the body's error | the environment of child 1, the handler |
| the test and the result of `iterate` | the node's, and the cursor | the environment of child 0, the body |
| the step of `iterate` | the node's, the cursor, and the body's answer | child 0's environment, and `effTy` of the body there |
| an operation's own term (`Signature.termOf`) | the node's, and the parameter's instance | not from the step function: the row check computes the instance (`bindTerm`) |

**The cost of one answer.** One call of `Node.envAt` costs at most one check of the program.
The reason: a step reads at most one sibling or one term of its node, and it then goes into
another child. So the sub-programs that one call checks are disjoint, and each node is checked
at most once. `focusAt` adds the check of the focus, which is disjoint from them.

**The cost of a walk over every eliminator**, for a program of `n` nodes with `E` eliminators:

- **By one call for each eliminator, from the root**: at most `E` checks of the program. The
  reason: the calls share nothing, and each repeats the checks before its address.
- **By one walk down that carries the environment**, with one call of `Node.childEnv` at each
  edge: at most `2 · L · n` node checks. A read-first position is a child that a later child's
  step reads. Three examples: the first program of a `bind`, a handled body, the program of a
  `bindYield`. `L` is the largest number of read-first positions on the way from the root to
  one node. The reason: a step into a later child checks the read-first child again, and
  `matchCause` has two such steps.
  - A statement list, or a chain of `bind` on the right, has `L = 1` when no head holds a
    read-first position. The walk is then linear.
  - A chain of `bind` on the left has `L` near its depth, and the walk is quadratic.

**The linear form, not built.** It is one pass in the checker's order. At a node it gives each
child its environment, takes the child's type back, and records both at the child's address.
Each node is then checked once. Per node the pass needs two things:

- the environment of each child from the types before it. `Node.childEnv` has that table. The
  pass would reuse its 54 arms, with the eleven reads taken from the types that the pass has
  computed already. So the step would be split in two. One part is a table that takes the
  read type as an argument. The other is the call of `effTy` or `termTy` that
  `Node.childEnv` makes today;
- the node's own type from its children's types. Only the checker's arms have that.

So the linear form is the checker with a record at each node. It is the same pass as total
marking, which visits every node too. It is the first way of REPLACE's receipt, a checker over
a monad. The step function stays as its specification. The pass's record at an address
should be `focusAt`'s answer there. No theorem states that agreement. Its proof would read
`NodeHasTy.replace_envAt` and the uniqueness of a type (`hasTy_unique`).

## Open obligations

1. **One pass that answers every address.** The focus function is exact and slow for a caller
   that asks everywhere. The linear form above belongs with total marking, in one design.
2. **The environment of an operation's own term.** The fourth row of the slot table needs the
   parameter's instance, which the row check computes and does not return. Its consumer is the
   TypeScript printer at an eliminator inside such a term.
3. **A slot table as a function.** The table above is prose. A function from a node and a slot
   to the slot's environment would let the printer ask one question. It waits for the printer.
4. **The sort of the answered environment.** From a program's root, `Node.envAt` answers the
   shape of the node's own sort. No theorem states it, and no caller needs it today: `focusAt`
   reads the shape, and `hasTy_focusAt` proves the answer on a typed program.
5. **A generated step.** The 54 arms and the 60 cases follow the rules of `HasTy` mechanically.
   A constructor appended to the program family now adds one arm and one case for each of its
   node children. A command that reads the six judgments could emit both.
6. **Total marking**, the second half. Not taken, as REPLACE's receipt says.
7. **The normal form of a checked type.** Unchanged from REPLACE's receipt: an omission asks
   for an answer and an error in normal form, and the function does not change that.

## Proposed texts (proposals only; the seat edits none of these files)

### The semantics registry (`tools/Tools/SemanticsRegistry.lean`)

One claim, under the concept `initial-algebras-folds`:

```lean
    { id := "focus-function", concept := "initial-algebras-folds", role := .inversion
      title := "The typing rules invert along a path, as a function: at an address of a program in a typed node, the fold of the step function answers the environment of the focus, the checker answers its type there, and the replacement law holds at that pair with no existential; the step has one case for each arm of Node.child, and Checker.check does not change"
      pointer := .witness `Effect4.Program.NodeHasTy.replace_envAt },
```

R14's `top` gains `Effect4.Program.NodeHasTy.replace_envAt`, and the open part `focus-function`
leaves. The open part `marking-agrees` gains one clause, before "the second half of slice
TRACE":

```text
one pass that answers every address is the same traversal: it checks each node once and records the environment and the type at each address, where the focus function costs up to one check of the program for each answer; the step function stays as its specification (docs/research/2026-10-06-seat-TRACE-receipt.md, the section on the printer);
```

### The semantics document (`docs/core/semantics.md`, concept 7, required properties)

```text
- **The focus function (`focus-function`)**: at an address of a program in a typed node, a
  function answers the environment of the focus, and the checker answers its type there
  (`Node.envAt`, `focusAt` (`src/Effect4/Program/Typing/Focus.lean`)). The replacement law
  holds at that pair with no existential (`NodeHasTy.replace_envAt`
  (`src/Effect4/Laws/Program/Typing/Replace.lean`); `check_replace_focusAt`
  (`src/Effect4/Laws/Program/Typing/Focus.lean`)). The step has one case for each arm of
  `Node.child`. It answers nothing after a sibling that the checker refuses, and one answer
  costs up to one check of the program.
```

### The dictionary (`docs/core/controlled-english.md`)

The entry "focus" keeps its meaning and its literature. Its anchor becomes the structure, as
the coordinator asked:

```text
`Focus`, `focusAt` (`src/Effect4/Program/Typing/Focus.lean`); `hasTy_replace` (`src/Effect4/Laws/Program/Typing/Replace.lean`)
```

Two new entries. The fifth column of each is "—".

| Term | Meaning here | Tree anchor | Literature | Do not use | Qualifier |
| --- | --- | --- | --- | --- | --- |
| **focus function** | The function that answers the focus at an address of a program: the sub-program, its environment and its type. It runs the checker on sub-programs and stores nothing. | `focusAt` (`src/Effect4/Program/Typing/Focus.lean`); `NodeHasTy.replace_envAt` (`src/Effect4/Laws/Program/Typing/Replace.lean`) | — | — | — |
| **typing environment** (typing environments) | The types of the variables that a node of a program can read, in binding order. A statement reads the loop flag with it, and a layer reads none. | `TyEnv` (`src/Effect4/Program/Typing/Rules.lean`); `NodeEnv` (`src/Effect4/Program/Typing/Focus.lean`) | typing context (standard) | — | — |

The entry "trace" needs no change. One sentence could be added to it, if the coordinator wants
the boundary stated there:

```text
The focus function is not a trace: it stores nothing.
```

### The architecture document (`docs/ARCHITECTURE.md`, the source tree)

```text
| `src/Effect4/Program/Typing/Focus.lean` | the focus at an address, for R14 (decisions row 292): the sub-program, its typing environment and its type. `NodeEnv` is what a node's typing judgment reads from above, in three shapes. `Node.childEnv` is the step, with one case for each arm of the generated `Node.child`, and `Node.envAt` is its fold along a path. `focusAt` adds the checker's type at a program. It changes no line of the checker and stores nothing |
| `src/Effect4/Laws/Program/Typing/Focus.lean` | the laws of `focusAt`, for R14: its answer is the sub-program at the address, typed there (`focusAt_typed`); on a typed program it answers at every address of a program (`hasTy_focusAt`, `check_focusAt`); the replacement law holds at its answer with no existential (`hasTy_replace_focusAt`, `check_replace_focusAt`). The battery is `Test/Program/FocusControls.lean` |
```

The row of `src/Effect4/Laws/Program/Typing/Replace.lean` gains one sentence:

```text
The step lemma also says that the step function answers the child's environment, and `NodeHasTy.replace_envAt` folds it: the pointer of the registry claim `focus-function`, with `NodeHasTy.replace` as its corollary.
```

The row of `src/Effect4/Program/Sketch.lean` gains "`Sketch.focusAt` is the focus at an address
of a sketch." The row of `src/Effect4/Laws/Program/Sketch.lean` gains one sentence:

```text
The two edits are stated again at the focus that `Sketch.focusAt` answers (`Sketch.check_fill_focusAt`, `Sketch.check_omit_focusAt`), so a tool has every premise in hand.
```

### The state document and the system map

`docs/STATE.md`, after the sentence on slice REPLACE in "What the study found (row 288)":

```text
The focus function has landed too (the first half of slice TRACE, row 292): `focusAt` answers
the sub-program at an address, its typing environment and its type
(`src/Effect4/Program/Typing/Focus.lean`), and the replacement law holds at its answer with no
existential. One answer costs up to one check of the program. One pass that answers every
address waits for total marking.
```

`docs/core/system-map.md`, R14's status, after the sentence on the replacement law:

```text
Its focus is computed: a step function with one case for each arm of `Node.child` answers the
focus's environment, and the law holds at that answer (`NodeHasTy.replace_envAt`, the claim
`focus-function`).
```

### Decisions rows

No new row is needed. Row 292, point 2, has its first half landed: the cite is this receipt.

## The requirements R1 to R14

The slice serves R14 and no other requirement. The open part `focus-function` becomes a
theorem, and the two edits of a sketch hold at a computed focus. It reads R1's `effTy_sound` and
`effTy_complete` and changes no admission of a program. It rests on R2's landed parts through
the replacement law, and it adds nothing to R2's open parts. R3 is not touched: no constructor
of `Ty` is added. R4 to R13 are not touched. No machine, store, session, codec, printer, reader
or run changes. The LCNF lowering is not touched, and no host row is answered. No requirement is
closed by this slice.
