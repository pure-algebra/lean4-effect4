# 2026-10-06 seat SKETCH receipt: slice REPLACE, the replacement law

**The one thing to know before merging:** the law is proved, and its environment and type of
the focus are existential. A tool cannot use it at a focus that reads its environment until a
function names that pair. The first half of slice TRACE is that function, and it follows on
this branch.

Status: a receipt (history, not authority). The slice is the study's section 9.7, "Slice
REPLACE" (`docs/research/2026-10-06-seat-GAP-study.md`), under decisions rows 282 and 288. It
follows slice SKETCH on the same branch (`docs/research/2026-10-06-seat-SKETCH-receipt.md`).

## Base and head

Branch `seat/sketch`, in the worktree `/Users/pooks/Dev/lean4-effect4-t3b`. The slice starts at
`aaacafd2`, the head of slice SKETCH, whose base is `ea0f584a`. The head is the commit that adds
this receipt.

| Commit | What |
| --- | --- |
| `b67d0bba` | the statements as ten planned goals, each placed; the judgment of a node; the two edits of a sketch |
| `8d6a8157` | each goal proved in place, with six steps; each step names the claim and its consumer |
| `c45af63a` | the battery and its root import |
| `fcfe1a9c` | one more control: an omission that is refused |
| the head | this receipt |

## Changed files

| File | Change |
| --- | --- |
| `src/Effect4/Laws/Program/Typing/Replace.lean` | new: `NodeTy`, `NodeHasTy`, and thirteen theorems |
| `src/Effect4/Program/Sketch.lean` | `Sketch.fillAt` and `Sketch.omitAt`; one section and one table row of the head comment |
| `src/Effect4/Laws/Program/Sketch.lean` | one import; three theorems; the head's table and placement |
| `src/Effect4/Laws.lean` | one import, directly after `import Effect4.Laws.Program.Sketch` |
| `Test/Program/ReplaceControls.lean` | new: the controls |
| `Test/All.lean` | one import, directly after `import Test.Program.SketchControls` |
| `docs/research/2026-10-06-seat-REPLACE-receipt.md` | new: this receipt |

The slice changes no rule of `HasTy`, no line of the checker and no line of `Node.replaceAt`.
No proof looks inside `Record.fieldType`, `Record.setType` or `Formation.HeadFormed`: the law's
cases read each rule's premises as hypotheses.

## What the slice decided

1. **One judgment over nodes, and no mutual induction.** `NodeHasTy s n τ` holds the six typing
   judgments by the node's sort, and it adds no rule. A statement has no judgment of its own, so
   a statement is typed with the statements after it. The law is then one induction on the path.
2. **One step, with one case for each arm of the generated `Node.child`.** `Node.child` has 53
   arms, and `NodeHasTy.child_step` has 60 cases, because a statement list and a layer spine have
   several rules. Each case is one rule applied again, as each line of `hasTy_ext` is.
3. **Two dead ends.** The empty list after a `return` and the empty tail of a one-layer spine
   have no typed replacement. The step asks that its child leads to a program, and no path to a
   program crosses a dead end.
4. **Two edits of a sketch in the core module.** `Sketch.fillAt` and `Sketch.omitAt` are
   functions over `Node.replaceAt`. `omit` is a keyword of Lean, so the function carries the
   address in its name. The coordinator accepted both in session.

## Commands and results

Each Lean, Lake and `make` command ran from the worktree's root, through
`/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`. `SCRATCH` is the seat's scratch folder.
`FLAGS` is `-o build -o ts/eff/node_modules -o harness/truth/node_modules`.

| # | Command | Result |
| --- | --- | --- |
| 1 | `lake env lean -M6144 SCRATCH/replace_probe.lean`, six runs | the last: exit 0; every theorem prints axioms within `[propext, Quot.sound]` |
| 2 | `lake env lean -M6144 SCRATCH/canon.lean` | exit 0: a checked node's answer that is not in normal form |
| 3 | `lake build Effect4.Laws.Program.Sketch Effect4`, at the goals | `Build completed successfully (397 jobs).`, exit 0 |
| 4 | `lake build Effect4.Laws.Program.Sketch`, at the proofs | `Build completed successfully (283 jobs).`, exit 0 |
| 5 | `lake env lean -M6144 Test/Program/ReplaceControls.lean` | exit 0, no message |
| 6 | `lake build Test.Program.ReplaceControls Effect4` | `Build completed successfully (399 jobs).`, exit 0 |
| 7 | `lake env lean -M6144 SCRATCH/normalform.lean` | exit 0: `mapFromEntries` refuses the normal form of a type that it admits raw |
| 8 | `lake build Test.Program.ReplaceControls`, with the last control | `Build completed successfully (285 jobs).`, exit 0 |
| 9 | `lake build`, at the head's sources | `Build completed successfully (1042 jobs).`, exit 0 |
| 10 | `make FLAGS gen-fixtures` | `PASS generate: requested producers ran in dependency order`, exit 0; no file changed |
| 11 | `make FLAGS check-cases` | `conform cases: PASS, exit 0; .lake/conform/cases.json`, exit 0 |
| 12 | `make FLAGS check-docs` | `PASS check-docs: every path, link, citation and make target in 76 documents resolves`, exit 0 |
| 13 | `make FLAGS check-proof-style` | exit 0 |
| 14 | `lake env lean -M6144 SCRATCH/status-replace.lean` | exit 0: the axioms, the plan status and the census below |
| 15 | `python3 scripts/check-language.py --show` on this receipt | no finding |

Commands 10 to 13 ran twice. The results above are the run after commit `c45af63a`. At the
head, `gen-fixtures` passed again with no file changed. For the other three `make` ran no
recipe there: each marker is newer than its inputs, and the last control changes none of them.

The first five runs of command 1 failed on my own text. Each failure taught one fact:

- `scoped` and `omit` are keywords of Lean;
- an alternative of `cases` takes no named argument;
- an alternative of `cases` binds no name for an explicit field that the index fixes.

Not run: `check-gen`, `check-slow`, `check-corpus`, `check-target`, `check-truth`, the
conservativity script, `gen-semantics`, `gen-architecture`. No TypeScript ran and no OCaml ran.

## Axiom output

The gate lines of command 9:

```text
info: Test/All.lean:289:0: Effect4 library-root gate: 180 API/utility modules, 324 Laws-only modules; every library source is reachable; Effect4 never reaches Laws
info: Test/All.lean:289:0: Effect4 module and axiom gate: checked 792 modules and 91756 declarations; phases (ms): sources and closure 113, library roots 884, declarations 5961, resolution 1229, axioms 17513, exemptions 400; semantic/test axioms are [propext,
 Quot.sound]; exact implementation boundary (17 module(s), 23 declaration(s)) additionally allows Classical.choice
info: Test/All.lean:289:0: Effect4 goal gate: 28 planned goal(s), each a theorem whose body is `sorry` outside the Effect4 root; 12 declaration(s) rest on goals; no other declaration reaches sorryAx
```

No planned goal of the slice is open: the goal gate counts what it counted at the slice's
start. Command 14, for each theorem of the slice:

| Theorem | Axioms | Plan status |
| --- | --- | --- |
| `Node.at_stmts_nil` | `[propext]` | proved |
| `Node.at_layers_nil` | `[propext]` | proved |
| `layersHasTy_cons` | `[propext, Quot.sound]` | proved |
| `NodeHasTy.child_step` | `[propext, Quot.sound]` | proved |
| `NodeHasTy.replace` | `[propext, Quot.sound]` | proved |
| `hasTy_replace` | `[propext, Quot.sound]` | proved |
| `stmtsHasTy_replace` | `[propext, Quot.sound]` | proved |
| `effsHasTy_replace` | `[propext, Quot.sound]` | proved |
| `actionHasTy_replace` | `[propext, Quot.sound]` | proved |
| `layerHasTy_replace` | `[propext, Quot.sound]` | proved |
| `layersHasTy_replace` | `[propext, Quot.sound]` | proved |
| `Node.replaceAt_eff` | `[propext]` | proved |
| `check_replace` | `[propext, Quot.sound]` | proved |
| `Sketch.fillAt_of_replaceAt` | `[propext]` | proved |
| `Sketch.check_fill` | `[propext, Quot.sound]` | proved |
| `Sketch.check_omit` | `[propext, Quot.sound]` | proved |

`#plan_status` ends with `next goals: 0`. `#semantics_census` lists every theorem of
`Effect4.Laws.Program.Typing.Replace` under `initial-algebras-folds`, with none untagged.

## Evidence

- **Proved**: the thirteen theorems of `src/Effect4/Laws/Program/Typing/Replace.lean` and the
  three new theorems of `src/Effect4/Laws/Program/Sketch.lean`. The axiom gate read them in
  command 9.
- **Proved**: four theorems of the battery. Two take a conclusion from the law and not from an
  evaluation: `omit_first_child` and `fill_the_hole`.
- **Tested**: the battery's 35 `#guard` lines. Each is a finite check on named programs.
- **Tested**: the two scratch probes of commands 2 and 7. Their facts are controls of the
  battery now.
- **Reading**: the three sentences below on which rules read a raw type.
- Bounded evidence: every control is one program. No evidence is host-only.

## The statements as compiled

```lean
inductive NodeHasTy (s : Signature Op) : Node Op → NodeTy Op → Prop   -- the six judgments

theorem NodeHasTy.child_step {s : Signature Op} {n c : Node Op} {τ : NodeTy Op} {i : Nat}
    (hn : NodeHasTy s n τ) (hc : n.child i = some c)
    (hlead : ∃ rest q, c.at_ rest = some (.eff q)) :
    ∃ τc, NodeHasTy s c τc ∧
      ∀ {s' : Signature Op} {c' n' : Node Op}, SigExtends s s' → NodeHasTy s' c' τc →
        n.setChild i c' = some n' → NodeHasTy s' n' τ

theorem NodeHasTy.replace {s : Signature Op} (path : List Nat) {n : Node Op} {τ : NodeTy Op}
    {q : Eff Op} (hn : NodeHasTy s n τ) (hat : n.at_ path = some (.eff q)) :
    ∃ (env : TyEnv) (t : EffTy), HasTy s env q t ∧
      ∀ {s' : Signature Op} {q' : Eff Op} {n' : Node Op}, SigExtends s s' → HasTy s' env q' t →
        n.replaceAt path (.eff q') = some n' → NodeHasTy s' n' τ

theorem hasTy_replace {s : Signature Op} {env0 : TyEnv} {p q : Eff Op} {T : EffTy}
    {path : List Nat} (hp : HasTy s env0 p T) (hat : (Node.eff p).at_ path = some (.eff q)) :
    ∃ (env : TyEnv) (t : EffTy), HasTy s env q t ∧
      ∀ {s' : Signature Op} {q' p' : Eff Op}, SigExtends s s' → HasTy s' env q' t →
        (Node.eff p).replaceAt path (.eff q') = some (.eff p') → HasTy s' env0 p' T

theorem check_replace {s : Signature Op} {env0 : TyEnv} {p0 : List Nat} {p q : Eff Op}
    {T : EffTy} {path : List Nat}
    (hp : Checker.check s env0 p0 p = .ok T) (hat : (Node.eff p).at_ path = some (.eff q)) :
    ∃ (env : TyEnv) (t : EffTy), (∀ pq, Checker.check s env pq q = .ok t) ∧
      ∀ {s' : Signature Op} {q' : Eff Op} {pq : List Nat}, SigExtends s s' →
        Checker.check s' env pq q' = .ok t →
        ∃ p', (Node.eff p).replaceAt path (.eff q') = some (.eff p') ∧
          ∀ p1, Checker.check s' env0 p1 p' = .ok T

theorem Sketch.check_fill (s : Sketch) (app : SigApp) {T : EffTy} {path : List Nat}
    {q : NativeEff} (hs : s.check app = .ok T)
    (hat : (Node.eff s.program).at_ path = some (.eff q)) :
    ∃ (env : TyEnv) (t : EffTy),
      (∀ pq, Checker.check (app.withHoles s.holes).signature env pq q = .ok t) ∧
      ∀ (more : RowTable) {q' : NativeEff} {pq : List Nat},
        Checker.check (app.withHoles (s.holes ++ more)).signature env pq q' = .ok t →
        ∃ s', Sketch.fillAt { s with holes := s.holes ++ more } path q' = some s' ∧
          s'.check app = .ok T

theorem Sketch.check_omit (s : Sketch) (app : SigApp) {T : EffTy} {path : List Nat}
    {q : NativeEff} (hs : s.check app = .ok T)
    (hat : (Node.eff s.program).at_ path = some (.eff q)) :
    ∃ (env : TyEnv) (t : EffTy),
      (∀ pq, Checker.check (app.withHoles s.holes).signature env pq q = .ok t) ∧
      ∀ (name : String), t.answer.closed = true → t.error.closed = true →
        t.answer.normalize = t.answer → t.error.normalize = t.error →
        Formation.Formed (Formation.instantiatedSites
          (Row.hole name t.answer t.error t.requires.elems).normalizeTypes []) →
        ∃ s', s.omitAt app path (Row.hole name t.answer t.error t.requires.elems) = some s' ∧
          s'.check app = .ok T
```

The five siblings of `hasTy_replace` have its form, one for each other judgment:
`stmtsHasTy_replace`, `effsHasTy_replace`, `actionHasTy_replace`, `layerHasTy_replace`,
`layersHasTy_replace`.

## Landed theorems and their placement

All sixteen carry `@[semantics "initial-algebras-folds" (requirement := R14)]`.

**`NodeHasTy.replace`, with its six instances, `NodeHasTy.child_step`, `check_replace` and the
four small steps.**

- Concept: `initial-algebras-folds`; property: the typing judgment follows the program's
  constructors, so it is a congruence at one address.
- Question: registry claim `typed-replacement` (role substitution), proposed; pointer
  `NodeHasTy.replace`; consumers: `Sketch.check_fill`, `Sketch.check_omit`, and the first half
  of slice TRACE.
- Reach, under rows 282 and 288:
  - the six judgments, at every typing signature of every operation alphabet;
  - a program as the focus, at every address;
  - every extension of the typing signature;
  - the focus's type kept exactly.
- Does not establish:
  - any behaviour;
  - a focus of a smaller type, or of a type that is equal only after normalization;
  - a term as the focus;
  - a program with a layer reference;
  - a function that computes the focus's environment and type.
- Unlocks: R14. It restates the plan's `focus-decomposes` and `focus-composes` as one claim.

**`Sketch.check_fill` and `Sketch.check_omit`, with `Sketch.fillAt_of_replaceAt`.**

- Concept: the same; property: the same congruence, at the two edits of a sketch.
- Question: consumers of `typed-replacement`; their own consumer is a tool's fill and omit.
- Reach: a sketch that the checker admits, and an address of a program in it. A filling has the
  focus's type exactly, and it may declare more holes. An omission asks four things of the
  focus's type, and the next section lists them.
- Does not establish:
  - a filling or an omission at a type that is equal only after normalization;
  - an omission with the row that declares the answer alone (slice COLUMN);
  - any behaviour.
- Unlocks: R14.

## The premises of an omission, and the question on normal form

`Sketch.check_omit` states four premises on the focus's type `t`, as the coordinator asked to
see them:

1. `t.answer.closed = true` and `t.error.closed = true`: the hole row has no template parameter.
2. `t.answer.normalize = t.answer` and `t.error.normalize = t.error`: the columns are in normal
   form.
3. `Formation.Formed (Formation.instantiatedSites (Row.hole name …).normalizeTypes [])`: the row
   check's own formation, on the three columns.
4. The row declares the requirement as `t.requires.elems`, the requirement's own key list. It is
   no premise: `Row.normalize_of_ascending` gives it.

The coordinator asked one question on premise 2. Is it needed only because some rules read a
raw type? The law would then hold up to the normal form once every rule reads the normal form.
**It is not: one more kind of rule fails, and I name it.**

- **Reading.** A rule that reads a raw head or an equality is one cause: `fiberTy`,
  `Checker.listOf?`, `Checker.exitOf?`, and the tests `t = .bool`. Candidate N repairs it.
- **Tested.** An atom's scheme is the second cause, and candidate N does not repair it.
  `mapFromEntries` has the scheme `[list (prod string (var 0))] → map string (var 0)`
  (`src/Effect4/Program/NativeAtom.lean`). Command 7 gives the atom two types for one argument.
  At the raw type `list (prod string (union nat string))` it answers
  `Readonly<Record<string, number | string>>`. At that type's normal form, a list of a union of
  two pairs, it is refused. So a program whose focus has such a raw answer is admitted, and its
  omission is refused at the term (`Test/Program/ReplaceControls.lean`, the last red control).
- **Reading.** The cause is how a scheme infers. A parameter binds at its first occurrence, in
  the raw type of the argument. At the raw type the parameter binds the union. At the normal
  form it binds `number` at the first pair, and the second pair does not match.
- **Reading.** It is the cause of the study's section 9.6 (b) again: inference by first
  occurrence. There one parameter stood at two places. Here it stands at one place, and the
  normal form of the argument shows that place twice, once for each member. A row does not have
  this fault at its request, because `checkRow` matches the request in normal form on both
  sides. The repair is the same: a parameter that binds by join over a union's members.
- So the corrected sentence of `checker-monotone` needs one more condition. I propose its text
  below. I know no third kind of rule (reading).

What a later slice can drop: after candidate N and after the repair of inference, premise 2 can
weaken to "up to the normal form". Neither alone is enough. A law that says so is not stated
here.

## Open obligations

1. **A function for the focus's environment and type.** The law says that they exist. A tool
   needs to compute them, and a proof must say that the computed pair is the law's. The link
   needs one fact for each rule: which environment the rule gives its child. `child_step` holds
   those facts in its 60 cases. The coordinator assigned the function to this seat, as the first
   half of slice TRACE (row 292):
   - a step function with one case for each arm of `Node.child`;
   - its fold `focusAt` along a path;
   - the law with no existential.

   It follows on this branch, with its own receipt. Until then the law is usable where the
   focus's type holds in every environment. Two proved controls show it: a hole, and a program
   that reads no variable.
2. **The two ways to a trace, and what each costs.** The study's section 9.4 said that one
   generic transformer of the checker's algebra gives the trace. That is wrong. A field of the
   algebra is a pure function of its children. A wrapper cannot see the environment that the
   field passes.
   - **A checker over a monad.** The checker's algebra has 65 fields, and each is written again
     over a monad with a local environment. A trace and a marking checker are then two
     interpretations, each with its agreement by `foldM_natural_eff`
     (`src/Effect4/Program/Fold.lean`). The cost is every proof that unfolds an arm of
     `Checker.check`:
     - the 73 inversion lemmas of `src/Effect4/Laws/Program/Typing/CheckInversion.lean`;
     - the 13 theorems of `src/Effect4/Laws/Program/Typing/CheckSound.lean`;
     - the 10 weakening theorems of `src/Effect4/Program/Typing.lean`;
     - the 65 fields of `check_alg_agreeOn` (`src/Effect4/Laws/Program/Signature.lean`);
     - the derivation by `fold_of` (`src/Effect4/Laws/Program/Folds/Checker.lean`).

     `grep -rl 'Checker\.check' src Test --include='*.lean'` answers 39 files: 20 under `src`
     and 19 under `Test`. Five of them are this seat's.
   - **A step function beside the checker.** It has 53 arms, and `child_step` gains one
     conjunct in each of its 60 cases. No proof that reads `Checker.check` changes. A constructor
     appended to the program family adds one arm and one case for each node child. It adds one
     line to `hasTy_ext` in the same way. Row 292 chose this way.
3. **Total marking**, the second half of slice TRACE. I do not take it now. It is a second
   checker with a recovery value at each refusal, and its natural form is the checker over a
   monad of point 2. It deserves its own design after the first half.
4. **The checker's types are not in normal form.** A node's answer is its term's raw type. So an
   omission is conditional, and `mapFromEntries` shows a refused omission. Two repairs are open,
   and each changes which programs the checker admits (reading). One normalizes a node's answer
   where the checker gives it. The other repairs inference, as section 9.6 (b) proposes. Neither
   is in this slice.
5. **A generated step.** The 60 cases follow the rules of `HasTy` mechanically. A command that
   reads the six inductive judgments could emit them. Its consumer is the next constructor
   appended to the program family. Today the cases are written by hand, as `hasTy_ext` is.
6. **A term as the focus.** `Node.child` addresses no term. The printer's first need is the type
   of a scrutinee term. The first half of slice TRACE answers it through the environment at the
   node and `termTy`.
7. **The row that declares the answer alone.** `Sketch.omitAt` takes any row. No law here states
   that form. It is slice COLUMN's `column-graduality`.

## Proposed texts (proposals only; the seat edits none of these files)

### The semantics registry (`tools/Tools/SemanticsRegistry.lean`)

One claim, under the concept `initial-algebras-folds`:

```lean
    { id := "typed-replacement", concept := "initial-algebras-folds", role := .substitution
      title := "A typed node splits at an address of a program into an environment and a type of the focus, and every program of that type in that environment, under every extension of the typing signature, stands in the focus's place with the node keeping its type; one statement over the six typing judgments, with no rule added"
      pointer := .witness `Effect4.Program.NodeHasTy.replace },
```

R14's `top` gains `Effect4.Program.NodeHasTy.replace`, and the open part `typed-replacement`
leaves. Two open parts change.

- Under `column-graduality`, in place of "with three declared columns an omission keeps the
  whole type at every address, by typed-replacement":

```text
with three declared columns an omission keeps the whole type where the focus's columns are closed, formed and in normal form (Sketch.check_omit); elsewhere the hole row is read in normal form, and an omission can change the type of the whole or be refused (the controls on a pair and on mapFromEntries, Test/Program/ReplaceControls.lean); a filling has no such premise
```

- Under `checker-monotone`, after "that binds one parameter at two covariant places", add:

```text
, and with no scheme that binds a parameter at the first member of a union (mapFromEntries refuses the normal form of an argument that it admits raw)
```

The open part `focus-function and marking-agrees` holds two claims, and row 292 splits the
slice. I propose two parts in its place. The second keeps the present text on marking.

```text
focus-function (proposed claim; initial-algebras-folds): a function answers the environment and the type of the focus at an address, and the replacement law holds at its answer with no existential (NodeHasTy.replace states the pair as existential); a step function with one case for each arm of Node.child, and its fold along a path; Checker.check does not change; the first half of slice TRACE (decisions row 292), with seat SKETCH
```

```text
marking-agrees (proposed claim; initial-algebras-folds): a checker that marks each local failure answers on every program, its first mark is the located refusal of explain, it has no mark exactly where the program is admitted, and a marked program is admitted modulo its holes when each mark is read as a hole; not compiled; the second half of slice TRACE
```

### The semantics document (`docs/core/semantics.md`, concept 7, required properties)

```text
- **The replacement law (`typed-replacement`)**: a typed node splits at an address of a program
  into an environment and a type of the focus, and every program of that type in that
  environment stands in the focus's place, under every extension of the typing signature
  (`NodeHasTy.replace` (`src/Effect4/Laws/Program/Typing/Replace.lean`)). Its six instances are
  the six typing judgments. It is the law of filling and of omitting in a sketch
  (`Sketch.check_fill`, `Sketch.check_omit` (`src/Effect4/Laws/Program/Sketch.lean`)). The
  focus's type is kept exactly: the law says nothing at a type that is equal only after
  normalization, and nothing of behaviour. The environment and the type are existential.
```

### The dictionary (`docs/core/controlled-english.md`)

| Term | Meaning here | Tree anchor | Literature | Do not use | Qualifier |
| --- | --- | --- | --- | --- | --- |
| **omit** (omits, omitted, omission, omissions) | To replace the sub-program at a site by a hole. A sketch omits by a new hole, declared at the end of its hole table. A type slice omits each site that it does not keep. | `Sketch.omitAt` (`src/Effect4/Program/Sketch.lean`); `Sketch.check_omit` (`src/Effect4/Laws/Program/Sketch.lean`); `omitted` (`src/Effect4/Laws/Slice/Lattice.lean`) | to omit a sub-term (Carroll, Madhavapeddy and Omar 2026, p. 9; read in `docs/research/2026-10-06-seat-GAP-study.md` §3) | "fold" (it is the catamorphism), "cut" (it is the registry's) | — |
| **fill** (fills, filled, filling, fillings) | To put a program at an address of a sketch, in a hole's place or in any sub-program's. The hole table does not shrink: a filled hole's row stays. | `Sketch.fillAt` (`src/Effect4/Program/Sketch.lean`); `Sketch.check_fill` (`src/Effect4/Laws/Program/Sketch.lean`) | hole filling (Omar, Voysey, Chugh and Hammer, *Live Functional Programming with Typed Holes*; read in the same note, §4.6) | "complete" for this: completeness is against a judgment | — |
| **address** (addresses) | A path of child indices from the root of a program to one of its nodes. It names a site. A term has no address. | `Node.at_` (`src/Effect4/Program/Refs.lean`) | a path in a tree (Huet, *The Zipper*; read in the same note, §4.3) | "location", "position" for this | — |
| **focus** | The sub-program at an address, with the environment and the type that the rest of the program gives it. | `hasTy_replace` (`src/Effect4/Laws/Program/Typing/Replace.lean`) | the focus of a typed decomposition (Carroll, Madhavapeddy and Omar 2026, Theorem 5.2; read in the head of `Replace.lean`) | — | — |

The dictionary has the word "omitted" already, in the entries "site" and "mask" of seat
LATTICE. The entry above gives the verb one meaning for both uses. The head of
`src/Effect4/Laws/Slice/Lattice.lean` says the same: to omit is to replace a sub-program by a
hole.

The entries "declarable" and "fillable" get no anchor in this slice, and no theorem here uses
either word. They wait for their slice.

### The architecture document (`docs/ARCHITECTURE.md`, the source tree)

```text
| `src/Effect4/Laws/Program/Typing/Replace.lean` | the replacement law of the typing judgment, for R14: a typed node splits at an address of a program into an environment and a type of the focus, and a program of that type stands in its place under every extension of the typing signature (`NodeHasTy.replace`; `hasTy_replace` and its five siblings; `check_replace` at the checker). `NodeHasTy` holds the six judgments by the node's sort and adds no rule. The step `NodeHasTy.child_step` has one case for each arm of the generated `Node.child`. The battery is `Test/Program/ReplaceControls.lean` |
```

The row of `src/Effect4/Program/Sketch.lean` gains one sentence:

```text
The two edits of a sketch are `Sketch.fillAt` and `Sketch.omitAt`, over `Node.replaceAt`.
```

The row of `src/Effect4/Laws/Program/Sketch.lean` gains one sentence:

```text
A filling of the focus's type keeps the sketch's type (`Sketch.check_fill`), and so does an omission whose hole row declares that type exactly (`Sketch.check_omit`).
```

### The state document and the system map

`docs/STATE.md`, in the paragraph "What the study found (row 288)", after the sentence on the
sketch:

```text
The replacement law has landed too (slice REPLACE): a program of the focus's type stands in the
focus's place, over the six typing judgments, with no rule added
(`src/Effect4/Laws/Program/Typing/Replace.lean`). An omission with three columns keeps the type
where the focus's columns are closed, formed and in normal form. The law's environment and type
are existential, and the first half of slice TRACE makes them a function.
```

`docs/core/system-map.md`, R14's status, after the sentence on a sketch:

```text
A third part is proved: a typed program splits at an address, and a program of the focus's
type stands in the focus's place (`NodeHasTy.replace`, the claim `typed-replacement`). It is
the law of the two edits of a sketch (`Sketch.check_fill`, `Sketch.check_omit`). Its
environment and type of the focus are existential.
```

### Decisions rows

Row 288, point 3: the coordinator amends it at this slice's merge, in these words of the
session. The law that states them is `Sketch.check_omit`.

```text
an omission with three columns keeps the whole type where the focus's columns are closed, formed and in normal form, with the requirement as its own key list; a filling has no such premise
```

One proposal, for row 285 or for a new row. The conversions of candidate N are not enough for
an omission at a type out of normal form. Inference by first occurrence is a second cause, at
an atom's scheme. The evidence is the control on `mapFromEntries`.

## The requirements R1 to R14

The slice serves R14 and no other requirement: one more proposed claim becomes a theorem, and
two edits of a sketch gain their law. It rests on R2's landed parts, `SigExtends` and `hasTy_ext`
with its siblings, and it adds nothing to R2's open parts. It reads R1's `check_sound` and
`check_complete` and changes no admission of a program. R3 is not touched: no constructor of `Ty`
is added. R4 to R13 are not touched. No machine, store, session, codec, printer, reader or run
changes. The LCNF lowering is not touched, and no host row is answered. No requirement is closed
by this slice.
