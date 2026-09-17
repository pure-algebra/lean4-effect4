# Ready packet: the template table, the generic reader, the host reader (R4, R5, R6)

2026-09-17. Owner's direction of the day: `gen` stays, the alphabet is settled, the line is R4,
R5, R6, and the generic reader is what is wanted most. Design authority:
`docs/research/2026-09-16-printer-reader-positions-design.md` §3, §10, §14. This packet fixes the
declarations, the order, the gates, and one decision the owner owes. Nothing here is implemented
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
  `mergeAll`), `type` (`iterate`'s annotation), `str` (`caseTag`'s tag), `int` (`yieldNow`'s
  priority), so `Subst` is `List (Nat × Arg)` over that sum;
- the second engine lemma, owed and not yet probed: for a template whose holes are distinct,
  `matchT n t e = some σ → inst n σ t = some e`. It is `read_exact`'s engine as `match_inst`
  is `read_print`'s.

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

1. **R4.1** `Template.lean`: the calculus of §2 with `match_inst` and the converse. Gate: builds
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
6. **R5.3** `iterate` is read (needs D1 below). `holdsLoop` in `ReadContract` turns back into the
   plain guard; `tools/Tools/Corpus.lean` writes loops again; `generated/corpus-index.tsv` and
   `generated/tsdiag-agreement.tsv` regain the 45 rows. `Read.lean` is `readable`, the leaf
   readers and the table.
7. **R6** the table exported as a document (`ts/eff/templates.gen.ts`, written by the generator
   the way `wire.gen.ts` is); `ts/eff/read.ts`'s clauses replaced by one matcher over it. Gate:
   `check-ts-reader` byte-identical on every oracle, loops included; DI-88's LCNF-to-TypeScript
   reader backend is cancelled, as the design says.

## 5. The decision the owner owes

**D1, how `iterate`'s annotation is read.** The printed loop carries `let aN: T = initial`, a
`TypeRef`. B19 rules out a `TypeRef → Ty` inverse for the surface's type comparisons. The reader
still has to produce a `Ty`. Three ways:

- (a) a section on the canonical image: `readTy : TypeRef → Option Ty` with `readTy (ofTy t) =
  some t` for normal `t`, used by the reader alone; `readable (iterate c …)` then asks that `c`
  is normal. B19 stays the rule for comparisons, which still never invert.
- (b) a typed reader: the reader is handed a typing environment and recomputes the cursor type
  from `initial`. Loses loops whose annotation is wider than the initial's type, which is the
  reason `iterate` has an annotation at all.
- (c) the annotation kept as syntax in `Eff` (`iterate` holds a `TypeRef`). Pulls the target's
  syntax into the core alphabet.

Recommended: (a). It is a function on the image only, its law is one equation, and it is the
smallest change that reads every printed loop.

## 6. What this does not do

No `Doc`, no `Tree`, no spans (R1 to R3); no change to the alphabet; no change to what prints
(every golden byte identical through step 3); nothing pushed.
