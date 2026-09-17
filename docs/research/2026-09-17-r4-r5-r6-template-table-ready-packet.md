# Ready packet: the template table, the generic reader, the host reader (R4, R5, R6)

2026-09-17. Owner's direction of the day: `gen` stays, the alphabet is settled, the line is R4,
R5, R6, and the generic reader is what is wanted most. Design authority:
`docs/research/2026-09-16-printer-reader-positions-design.md` §3, §10, §14. This packet fixes the
declarations, the order, the gates, and one decision the owner owes (DI-91). Nothing here is implemented
except the probe of §2.

## 0. What is being replaced, measured

`src/Effect4/Codegen/Print.lean` is 728 lines, `src/Effect4/Codegen/Read.lean` 3,504, and
`ts/eff/read.ts` is a hand port of the second. Every printing clause but the leaf printers has one
shape: print each child at the depth its binder row gives, then plug the results into a fixed
`TypeScript.Expr` skeleton. `Read.lean`'s bulk is that shape inverted and proved once per
constructor (`read_print`, `read_exact_all` with its sixty-odd numbered cases). The skeleton as
data turns both directions into one function each and the two laws into one induction each.

Until R5, no loop is read: `iterate` prints and both readers refuse it, 45 of the 410 corpus
programs are out of the printed corpus directory and with it out of the reader lane, the
diagnostics lane and the OCaml differential (`Test/Codegen/ReadContract.lean`, `holdsLoop`;
`tools/Tools/Corpus.lean`'s header).

## 1. The target, for now

The design's `print` lands in R2's `Tree`. R1 to R3 are not in the tree (the `Doc` draft is at
`~/Dev/lean4-doc`). R4's own acceptance test is "beside the old printer with a guard on every
corpus program", and the old printer lands in `TypeScript.Expr`, so R4 and R5 are built over
`TypeScript.Expr` now. When R2 lands, the template's carrier changes and the table does not.

## 2. The calculus (`src/Effect4/Codegen/Template.lean`, new)

Probed against the pinned `TypeScript.Expr` (`docs/research/2026-09-17-template-probe.lean`,
checked with `lake env lean`; it is the module's first cut): with the formers `hole`,
`binderRef`, `ident`, `call`, `arrow`, `lambda`, `cond`,

- `inst (n : Nat) (σ : Subst) : Tpl → Option Expr` prints a template at depth `n`
  (`binderRef k` is `Var.name (n + k)`);
- `matchT (n : Nat) : Tpl → Expr → Option Subst` reads one, collecting holes left to right and
  checking binder names against the depth;
- `match_inst : inst n σ t = some e → matchT n t e = along σ (holes t)`, by one mutual
  induction on templates, compiles at `[propext, Quot.sound]` with explicit `simp only` sets.

The module extends the probe with what the printer's clauses use and nothing more:

- formers `str`, `int`, `bool`, `object` (fields in order), `arr`, `method`, `generic`,
  `arrowBlock` with the three statement formers the image uses (`letInit` with an annotation,
  `assign`, `ret`, `exprStmt`);
- sorted holes. A captured argument is one of `expr`, `exprs` (the variadic `raceAll` and
  `mergeAll`), `str` (`caseTag`'s tag), `int` (`yieldNow`'s priority), so `Subst` is
  `List (Nat × Arg)` over that sum. There is no `type` hole: under DI-91 the readable loop
  carries no annotation, and the annotated one is outside `readable`;
- the second engine lemma, **proved in the probe (2026-09-17, evening)**: for a template whose
  holes are distinct, `inst_of_match : matchT n t e = some σ → (holes t).Nodup → inst n σ t =
  some e`, at `[propext, Quot.sound]`. It is `read_exact`'s engine as `match_inst` is
  `read_print`'s. The proof's shape, for the module: state it with a context on both sides
  (`inst n (pre ++ σ ++ post) t`, with the template's holes fresh for `keys pre`), so every
  compound case is re-association; it needs `match_keys` (what a match collects is keyed by the
  holes, left to right) and one fact about `lookup` past a block that does not hold the key.
  One trap: `beq_self_eq_true` in a `simp only` set brings `Classical.choice` and breaks the
  axiom ceiling; use `decide_eq_true rfl` for `(i == i) = true`. A table row's template must
  therefore have distinct holes: one more generated per-row guard (`decide`).

## 3. The table (`src/Effect4/Codegen/Templates.lean`, new)

One row per (constructor, classifier), the shape `tools/Effect4Gen/binders.json` already has
(`whenArg`/`whenHead` for `select`'s three decisions; `closed` for a layer's body). A row is:
the constructor, the classifier, the template, and per constructor field its sort and the binder
slots it sees. Families: `Eff`, `ActionTerm`, `LayerTerm`, `CauseTerm`. The classifiers the
printer has today: `catchIf` on `test = true` (`Effect.catch` against `Effect.catchIf`),
`provideLayer` on `isLocal`, `select` on the decision, `awaitFiber` on the mode, `fork` on
`daemon`, `interruptAll` on the interruptor, `CauseTerm.interrupt` on the same.

Guards, generated, per row: the binder columns equal `binders.json`'s (the design's §14: generation
is not a theorem, the per-row guard is); the rigid heads of the table are exactly
`Print.heads`, so `reserved` is read off the table and `Head` retires with R5.

Leaf sorts keep their hand printers and readers, because they are not skeletons: `Term`, `Lit`,
`ServiceKey`, `ForkOptions`, and the row call of `perform` (`printRow` and the four `readRow*`,
whose inverse is the signature's `spell`, law `LawfulSpelling`). `Stmts` under `gen` stays
hand-written in the first cut and becomes a second table over `TypeScript.Stmt` when it is the
largest thing left.

## 4. Order, each step gated and committed before the next

1. **R4.1** `Template.lean`: the calculus of §2 with `match_inst` and the converse (both proved in
   the probe for the seven first formers; the module extends them to the rest). Gate: builds
   under the axiom ceiling; `make check`.
2. **R4.2** `Templates.lean`: the table with its per-row guards. Gate: the guards; `make check`
   (the conformance policy names any new default arm).
3. **R4.3** `printT`, the fold over the table. Guard first: `printT = print` on the 400, the wire
   corpus and `Forms.all`'s examples. Then law 10 as a theorem, one `rfl`-sized case per row.
   Then `print := printT` and the hand clauses go. Gate: no golden byte moves; `make check`,
   `check-truth`, `check-tsdiag`, `check-ocaml`.
4. **R5.1** `readT`: first matching row, holes read by sort at their depth. Guard: `readT =
   readEff` on every corpus image. `InImage` and pairwise disjointness of the table decided once
   (`decide`), the `Effect.suspend` group (`suspend`, `select … .bool`, `iterate`) justified by
   `print_not_cond`'s generalisation, not by a tie-break.
5. **R5.2** the laws through the two engine lemmas: `read_print` (law 11), `read_exact` with no
   `readable` premise, as today (law 12). `readable` keeps its name and is guarded by a Boolean
   equality against today's definition on the corpus before it is redefined.
6. **R5.3** `iterate` is read (the unannotated form, DI-91). `holdsLoop` in `ReadContract` turns back into the
   plain guard; `tools/Tools/Corpus.lean` writes loops again; `generated/corpus-index.tsv` and
   `generated/tsdiag-agreement.tsv` regain the 45 rows. `Read.lean` is `readable`, the leaf
   readers and the table.
7. **R6** the table exported as a document (`ts/eff/templates.gen.ts`, written by the generator
   the way `wire.gen.ts` is); `ts/eff/read.ts`'s clauses replaced by one matcher over it. Gate:
   `check-ts-reader` byte-identical on every oracle, loops included; DI-88's LCNF-to-TypeScript
   reader backend is cancelled, as the design says.

## 5. The decision that was owed (DI-91): ruled and landed 2026-09-17

**D1′, how the reader obtains `iterate`'s cursor type.** Scouted
(`docs/research/2026-09-17-scout-bidirectional-types-and-iterate-ergonomics.md` §2 to §4); the
claims below marked compiled were re-run by the coordinator.

The rule in force is B19 (`docs/research/2026-09-16-implementation-review-log.md`, 10:05): types
meet source by projection only; `ofTy : Ty → Option TypeRef` is the view map and nothing reads a
`TypeRef` back, "never a section". The reason is that `ofTy` is not injective. Compiled:
`ofTy nat = ofTy int = ofTy (handle "number")`, and `ofTy (union nat int) = ofTy nat`. Compiled
too: `effTy` does not respect that kernel (the counting loop types at cursor `nat` and is refused
at cursor `handle "number"`), so a reader that canonizes and a round trip "up to the kernel" would
change which programs type. No `readTy` with `readTy (ofTy t) = some t` exists; the first cut of
this packet recommended that law and it is withdrawn.

**Ruled by the owner, (d′): make the annotation optional** (landed with DI-92's fix). `Eff.iterate (cursorTy : Option Ty)`.
`none` means the cursor's type is `termTy env initial`; it prints as the unannotated
`let aN = initial`, which is the image the loop had before `37ff9b21` and both readers read; it
reads back. `some t` is the widened cursor; it prints `let aN: T` and is not readable, the status
`select … .option` has today. B19 stays literally whole. The `type` hole sort of §2 goes away
and step R5.3 no longer waits on a ruling. The generator already writes exactly the synthesized
type, so all 45 loop rows return. The annotation has no runtime meaning (every compile and
meaning site binds it as `_`), so the loop proofs do not move. Cost: the field, one `let` in
`effTy` and in the blame, one premise in each of `HasTy`, `Inversion`, `Sound`, the printer's and
`readable`'s `iterate` clauses, the OCaml translation arm; the rest regenerated; tag 28's layout
changes (one day old, no retained vector, the compat policy names it).

Fallback, (a): a chosen representative `readTy` with `ofTy (readTy r) = some r` on the image and
`readable` asking `readTy (ofTy c) = some c`. Additive behind (d′) for `some c`; a section, so it
needs a written amendment to B19 for that one clause. The other routes (a typed reader, a
`TypeRef` in `Eff`, the quotient round trip, a subtype field) are priced in the scout's table and
are dearer or unsound.

Ruled with it: a unit-result loop does NOT print as the bare `Effect.whileLoop`; the loop keeps
its one printed shape and nothing just retired is refurbished. Still open: the loop sugar as
authoring-only definitions (`iterateWith` with minted binders and the result
defaulting to the cursor, `whileLoop`, `forever`, `countTo`). rc.112 has no `Effect.iterate` and
no `Effect.loop`, so there is no idiomatic head to print; `forEach` and `reduce` wait on one atom,
`uncons`. Found on the way and filed as DI-92: `admitProgram`'s `int` ban does not see a `Ty`
inside the program tree (compiled: a program with `Ty.int` as a cursor annotation is admitted).

## 5b. The reader as an authored `Eff` program (the owner's question; scouted 2026-09-17)

Scout note: `docs/research/2026-09-17-scout-reader-as-eff-program.md`, eight compiled probes; the
coordinator re-ran probes 1 and 2 and got the note's results. The coordinator's first assessment
was wrong on two points and the owner was right: the authoring layer is a Lean-hosted builder, so
a Lean function over the table authors the reader.

- **It works today with no language addition.** One layer of the reader, folded out of a table by
  a Lean function with the existing sugar (`selectTag`, `ifElse`, `app "eq"`, `fst`, `snd`), is in
  `Straight`, its meaning equals a Lean `matchLayer` on hits and misses, the machine agrees at
  `run_eq_meaning`'s budget, and it prints through this repository's printer using prelude names
  that already exist. A 38-row layer is 46 KB on the wire.
- **List atoms are not needed**: a cons list as tagged pairs is taken apart by `select … (.tag
  "cons")` with `fst` and `snd`. The real gap is elsewhere: the generated `Image` of a type is
  `Val.ctor index args`, and no atom or decision can see a `Val.ctor`. So the input is encoded as
  tagged pairs (free), or two atoms land (`ctorIndex`, `ctorArg`; about the `isSome`/`getOrElse`
  cascade, raw programs only).
- **The recursion stays outside.** Authoring-time unrolling grows by the table's total arity per
  level (measured; tens of megabytes at depth 3 for the real table). A worklist under `iterate`
  runs and does not type. The layer as a program under the generic fold is the shape.
- **Two limits.** `Ty` has no recursive type, so a general reader is a raw program with no typed
  module; and `run_eq_meaning` and the loop agreement are stated at the empty environment, so
  they do not cover a program with a free node variable (a closed program per node does type and
  emit).
- **It is circular until R5**: the authored reader is built from `select … (.tag _)`, which
  `readable` refuses until the generic reader lands. So it cannot precede R5.
- **Verdict, accepted:** R6 as §4 step 7 says (export the table, one matcher in TypeScript: one
  new artefact against three). The reader as a program follows R5.2 as a worked demonstration of
  a compiler written in the language, in three small slices (the real table folded into a `Src`
  with per-row guards; one compile theorem against `matchLayer`, so the laws stay on `matchT`;
  the closed variant printed and run on the host). Steps 1 to 5 do not wait for it.

## 6. What this does not do

No `Doc`, no `Tree`, no spans (R1 to R3); no change to the alphabet; no change to what prints
(every golden byte identical through step 3); nothing pushed.
