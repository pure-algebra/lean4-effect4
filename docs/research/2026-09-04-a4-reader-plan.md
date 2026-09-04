# A4 — the reader of the printer's image, with its two theorems (plan for the agent)

Date: 2026-09-04. Parent: `docs/research/2026-09-04-ast-relation-plan.md` §5.2. Lane A4 of
the AST relation. The printer is `Effect4/Syntax/Print.lean` (read it first, all of it: the
reader is its inverse constructor by constructor); the syntax is `Effect4/Syntax/Eff.lean`;
the typing is `Effect4/Syntax/Typing.lean`; the fragment is
`.lake/packages/typescript/TypeScript/Syntax.lean` (`Expr`, `Stmt`).

## Deliverables (two new files; nothing else is touched)

1. `Effect4/Syntax/Read.lean` — `ReadRefusal`, `Var.read`, `readTerm`/`readTerms`,
   `readCause`, `readForkOptions`, the mutual `readEff`/`readStmts`/`readEffs`/…, the
   predicates `LawfulSpelling` and `Readable`, and the theorems `read_print` and
   `read_exact`. Library `Effect4` picks the module up by glob; the import into
   `Effect4.lean` is the coordinator's.
2. `Effect4Test/Syntax/ReadContract.lean` — `#guard` pins, in the idiom of
   `Effect4Test/Syntax/PrintContract.lean` (read it): one round trip per constructor of
   `Eff` (all 24 rows of `arms`), per statement form, per `awaitFiber` mode, per fork shape,
   plus one refusal pin per `ReadRefusal` constructor. The import into `Effect4Test.lean` is
   the coordinator's.

## Facts checked on this toolchain (2026-09-04), so the design is fixed

* `Var.name i = "a" ++ toString i`; `String` equality is choice-free; `Var.name` is
  injective by `String.append_right_inj` and `Nat.repr_inj` (both in core; `toString i`
  unfolds to `Nat.repr i` — `simp [Var.name] at h` then `Nat.repr_inj`). The gate forbids
  `String.toList`, `String.foldl`, `String.toNat?` (they reach `Classical.choice`), so
  **the reader never decodes digits**: it recovers a binder by comparing against the names
  it expects.
* `TypeScript.Expr` and `TypeScript.Stmt` have no `DecidableEq` (nested inductives). Never
  compare expressions; compare `String`s, `Bool`s, `Int`s. Pins compare `Eff` values and
  `Except ReadRefusal (Eff Op)` values.
* Nested structural recursion over `Expr`/`Stmt` (through `List Expr`, `List Stmt`,
  `List (String × Expr)`) works on this toolchain with `termination_by structural`; if a
  clause resists, use well-founded recursion on `sizeOf` — the theorems use the equation
  lemmas and `readEff.induct`, not the recursor.

## The reader

```lean
namespace Effect4.Syntax
variable {Op : Type}

inductive ReadRefusal
  | unknownHead (name : String)        -- a call whose head is neither a combinator nor a row
  | unknownIdent (name : String)       -- an identifier that is no binder, no reserved name, no value row
  | arity (head : String)              -- a combinator or row called with the wrong argument list
  | binder (expected : String)         -- a lambda/const/step parameter that is not the binder due
  | shape (what : String)              -- any other form the printer never emits (`what` names it)
  | negative (value : Int)             -- a negative integer literal
  | unsupportedStmt                    -- a statement form the printer never emits
deriving DecidableEq, Repr
```

* `Var.read (n : Nat) (s : String) : Option Nat` by recursion on `n`: `Var.read 0 _ = none`;
  `Var.read (n+1) s = if Var.name n = s then some n else Var.read n s`. Lemmas
  `Var.read_name : i < n → Var.read n (Var.name i) = some i` (induction on `n`, injectivity
  for the `≠` step) and `Var.read_exact : Var.read n s = some i → s = Var.name i`.
* `reserved : List String` — every fixed head the printer emits: `Effect.succeed`,
  `Effect.fail`, `Effect.failCause`, `Effect.sync`, `Effect.suspend`, `Effect.flatMap`,
  `Effect.gen`, `Effect.catchCause`, `Effect.matchCauseEffect`, `Effect.onExit`,
  `Effect.exit`, `Effect.uninterruptible`, `Effect.interruptible`, `Effect.whileLoop`,
  `Effect.yieldNowWith`, `Fiber.join`, `Fiber.await`, `Effect.forkChild`,
  `Effect.forkDetach`, `Effect.forkIn`, `Effect.forkScoped`, `Fiber.runIn`,
  `Fiber.interrupt`, `Fiber.interruptAll`, `Fiber.interruptAllAs`, `Fiber.awaitAll`,
  `Effect.raceAll`, `Effect.context`, `Effect.fiberId`, `Scope.close`, `Effect.scoped`,
  `Effect.acquireRelease`, `Cause.fail`, `Cause.die`, `Cause.interrupt`, `Cause.combine`,
  `undefined`.
* Terms. `readTerm (n : Nat) : TypeScript.Expr → Except ReadRefusal Term`:
  `.ident s` → `.var i` when `Var.read n s = some i`, else `.lit .unit` when `s = "undefined"`,
  else `unknownIdent s`; `.int k` → `.lit (.nat k.toNat)` when `0 ≤ k`, else `negative k`;
  `.bool b` → `.lit (.bool b)`; `.str s` → `.lit (.str s)`; `.call (.ident atom) args` →
  `.app atom (readTerms args)` (atoms are not checked against `reserved` in term position —
  the printer never puts a combinator in term position); anything else → `shape "term"`.
  `readTerms : List Expr → Except ReadRefusal Terms`.
* Causes. `readCause`: `Cause.fail [t]`, `Cause.die [t]`, `Cause.interrupt []`,
  `Cause.interrupt [t]`, `Cause.combine [l, r]`; else `shape "cause"`.
* Fork options. `readForkOptions`: exactly
  `.object [("startImmediately", .bool b), ("uninterruptible", u)]` with `u` one of
  `.bool true` (`.uninterruptible`), `.bool false` (`.interruptible`), `.str "inherit"`
  (`.inherit`); else `shape "forkOptions"`.
* Rows. The reader takes `spell : String → Option Op` as a parameter (the inverse of
  `(sig.rowOf op).spelling`; not a `Signature` field, so nothing existing changes). A row
  head `s` with `spell s = some op`, `row := sig.rowOf op`, answers `.perform op r` when
  `row.kind ≠ .async` and `.callback op r` when `row.kind = .async`, where:
  `.ident s` requires `row.shape = .value` and gives `r = .lit .unit`;
  `.call (.ident s) args` requires `row.shape = .call`, and then: if `row.request = Ty.unit`,
  `args` must be exactly `row.trailing.map .ident` (check with an `idents? : List Expr →
  Option (List String)` and `List String` equality) and `r = .lit .unit`; otherwise `args`
  must be `request :: row.trailing.map .ident` and `r = readTerm n request`. Any mismatch
  is `arity s`.
* Effects. `readEff (sig : Signature Op) (spell : String → Option Op) (n : Nat) :
  TypeScript.Expr → Except ReadRefusal (Eff Op)`, in the order of the §5.1 table, matching
  exactly what `print` emits (`Effect4/Syntax/Print.lean` lines 110–184), including binder
  checks: every `.lambda [x] body` and `.arrowBlock [y] …` parameter must equal the
  `Var.name` the printer used at that position (`n`, `n + 1`, `n, n + 1` for
  `acquireRelease`); a mismatch is `binder expected`. Order of the `.ident s` arm: reserved
  first (`Effect.fiberId` → `.withFiber .getId`; `undefined` → `.yieldError (.lit .unit)`),
  then a binder (`Var.read n s = some i` → `.yieldError (.var i)`), then a value row
  (`spell s`), else `unknownIdent s`. Order of the `.call (.ident s) args` arm: the
  combinators of `reserved`, then a row (`spell s`), then `.yieldError (.app s
  (readTerms args))`. `.int`/`.bool`/`.str` → `.yieldError (.lit …)`. `Effect.suspend [.arrow
  none (.cond t a b)]` → `.branch`; `Effect.suspend [.arrowBlock [] [.letInit x i, .ret
  (.call (.ident "Effect.whileLoop") [.object [("while", .arrow none t), ("body", .arrow none
  b), ("step", .arrowBlock [y] [.assign x' s])]])]]` with `x = x' = Var.name n`, `y = Var.name
  (n + 1)` → `.whileLoop`; `Effect.suspend [.arrow none b]` otherwise → `.suspend`.
  `Effect.gen [.generator stmts]` → `.gen (readStmts n stmts)`: `constYield x v` (`x =
  Var.name n`, rest at `n + 1`), `yieldDiscard v`, `ret v` (a term), `ifElse t a b`,
  `whileTrue none body`, `breakTo none`; every other statement → `unsupportedStmt`.
  `Effect.raceAll [.arr items]` → `.withFiber (.raceAll (readEffs n items))`. `Effect.forkChild
  [p, o]` / `Effect.forkDetach [p, o]` → `.fork` with `daemon := false/true` from the head
  and the mask from `readForkOptions o`. The rest are one-to-one with the table.

## The predicates

```lean
/-- `spell` inverts the signature's spellings, and no spelling collides with a binder
name or a reserved name. -/
def LawfulSpelling (sig : Signature Op) (spell : String → Option Op) : Prop :=
  (∀ op, spell (sig.rowOf op).spelling = some op) ∧
  (∀ s op, spell s = some op → (sig.rowOf op).spelling = s) ∧
  (∀ op i, (sig.rowOf op).spelling ≠ Var.name i) ∧
  (∀ op, (sig.rowOf op).spelling ∉ reserved)

/-- What the printer loses and the reader cannot recover, as a decidable predicate over
the program: every variable is in scope at `n` (`.var i` with `i < n`, binders counted as
the printer counts them); a `perform` is on a row whose kind is not `.async` and a
`callback` on an `.async` row; the request of a value row, and of a call row with a
`unit` request, is exactly `.lit .unit`; a `.yieldError (.app atom _)` has `spell atom =
none` and `atom ∉ reserved`; a `.yieldError (.var i)` has `i < n`. -/
def Readable (sig : Signature Op) (spell : String → Option Op) (n : Nat) : Eff Op → Bool
```

(`Readable` is mutual with `readableStmts`, `readableEffs`, `readableAction`, following the
binder counts of `print`/`printStmts` exactly; scoping of terms uses a `Term.scoped n :
Term → Bool`.)

## The theorems (at `propext`/`Quot.sound`; check with `#print axioms`)

```lean
theorem read_print (sig : Signature Op) (spell : String → Option Op) (n : Nat) (e : Eff Op)
    (x : TypeScript.Expr) (hlaw : LawfulSpelling sig spell) (hr : Readable sig spell n e = true)
    (hp : print sig n e = .ok x) : readEff sig spell n x = .ok e

theorem read_exact (sig : Signature Op) (spell : String → Option Op) (n : Nat)
    (x : TypeScript.Expr) (e : Eff Op) (hlaw : LawfulSpelling sig spell)
    (h : readEff sig spell n x = .ok e) : print sig n e = .ok x
```

`read_print` by the mutual structural induction on `Eff`/`Stmts`/`Effs`/`ActionTerm`
(state the four mutual statements and prove them in one `mutual` block, or one theorem over
the family via `Eff.rec` with four motives), case by case: unfold `print` on the constructor,
obtain `x`, unfold `readEff` on that shape, use `Var.read_name` for the binders and the
`Readable` conjuncts for the rows. `read_exact` by `readEff.induct` (the functional
induction principle Lean generates), case by case: each accepting arm prints back its input
(`Var.read_exact` for binders; `LawfulSpelling` for rows; `Int.ofNat k.toNat = k` under
`0 ≤ k`; `idents?` exactness for trailing names). Term-level lemmas first:
`readTerm_printTerm : Term.scoped n t = true → readTerm n (printTerm t) = .ok t` and
`readTerm_exact : readTerm n x = .ok t → printTerm t = x`, and the same for causes and fork
options.

## The pins (`Effect4Test/Syntax/ReadContract.lean`)

The battery's alphabet is `PrintContract`'s (copy `rowOf`, `updateRow`, `sig`) plus
`spell : String → Option (Fin 3)` inverting the three spellings, and a fourth-row variant
where `Ref.update`'s trailing `incr` is read back. One pin per constructor:
`(print sig n e).bind (readEff sig spell n) = .ok e` — inline the program in the `#guard`,
never behind a `def` over rendered text (the axiom gate audits `Effect4Test.*` `def`s; a
`def` holding an `Eff` value is fine, a `def` folding a `String` is not). Refusal pins: one
per `ReadRefusal` constructor on a hand-built `Expr`. Also pin that `LawfulSpelling sig spell`
holds by `decide` where decidable, or state it as a theorem with a short proof.

## Rules

Use PowerShell (the Bash tool is disabled). Do not commit and do not `git add`. Do not edit
any file other than the two deliverables and scratch files under the scratchpad
(`C:\Users\kokok\AppData\Local\Temp\claude\C--Users-kokok-Dev-lean4-effect4\7d8163ed-c306-41e3-a4d8-7f8ba475fb79\scratchpad`);
in particular not `Effect4.lean`, `Effect4Test.lean`, `Effect4Test/Audit/AxiomGate.lean`,
`Effect4/Syntax/Print.lean`, `Typing.lean`, `Eff.lean`, `Native.lean`, `Compile.lean`. Run
`lake build` only for the targets `Effect4.Syntax.Read` and `Effect4Test.Syntax.ReadContract`,
one invocation at a time; another agent is building its own module in the same tree, so if a
build fails with `0xC0000409` under load, rerun it once. No `sorry`, `partial`, `unsafe`,
`native_decide`, `axiom`, `extern`, `implemented_by`, and no declaration reaching
`Classical.choice` (check every theorem and def with `#print axioms` in a scratch file via
`lake env lean`). If a proof cannot be closed, leave the theorem *stated* with the exact
place it is stuck described in the report — never a `sorry` in the file; put the stuck
statement in a comment block and say so. Report: what was built, the `#print axioms`
receipts, the pin count, and anything the printer does that the design above did not
foresee (a shape two constructors share, a binder the printer reuses), with file and line.
