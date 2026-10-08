# 2026-10-08 UNGUARD: what the checker admits when the two guards go

Status: a research note for the owner's hearing of decisions row 325, point 5, and for Codex's
review. Nothing in it is landed. The plan is `docs/research/2026-10-07-typed-print-design.md`.

## In one paragraph

Two interim guards refuse a program where TypeScript cannot infer a type argument by itself. That
is a call where one type parameter receives two types with no order between them, such as
`number` and `string`. The match by bounds answers their union, and the typed print (slice P2a,
row 325) can write that union on the call. UNGUARD removes the guards: `Bounds.matchTerm` becomes
`Bounds.matchB` (`src/Effect4/Program/Bounds.lean`). No admitted program changes its type or its
printed bytes. Only refusals become admissions.

## What does not move

- **Every program admitted today.** Where the guarded match answers, the match by bounds answers
  the same bindings (`matchB_of_matchTerm`, `src/Effect4/Laws/Program/Template.lean`). With no
  join, the typed print is the print (`printTyped_eq_print`,
  `src/Effect4/Laws/Codegen/PrintTyped.lean`).
- **The native atoms** (`get`, `take`, `cons`, …). They have no guard: the prelude declaration
  takes an argument's whole type, and tsgo computes the join there (row 299, point 10).
- **The native rows.** A cell or the whole request fixes each parameter, so the guard refuses
  nothing there (row 315, point 2; the corpus lane measured no move).
- **The two corpora.** The probe found no application that the guard refuses and none whose type
  moves (row 299, point 2).
- **The eliminators** (`optionCase`, `caseTag`, the fiber and scope rules). They are slice P2b,
  with a hearing of their own.

## The widenings

### W1. A host row's request offers a parameter two unordered types

The rows are an application's host rows whose request holds a type parameter (template rows).

- **Example** (tested, `firstRow`, `Test/Program/BoundsControls.lean`). The row is
  `L.first<A>(xs: List<A>): Option<A>`. One branch builds a list of numbers, and the other a list
  of strings, so the argument's type is `List<number> | List<string>`.
- **Today**: refused, `requestNotSubtype` (`checkRow`, `src/Effect4/Program/Typing/Rules.lean`).
- **After**: admitted at `A = number | string`, with the answer `Option<number | string>`. The
  call prints as `L.first<number | string>(xs)`.
- **The same parameter at two places** falls under W1 too. A row `L.same<A>(x: A, y: A): A` called
  with `1` and `"a"` binds `A` to `number | string` (tested at the template:
  `matchB [] (.prod (.var 0) (.var 0)) (.prod .nat .string)`, the same battery).

### W2. An operation's own term answers two unordered types

Two of the eight `Ref` rows with a binder term widen: `Ref.modify` and `Ref.modifySome`. Their
reply parameter `B` is the one parameter that the cell does not fix. The six update forms answer
the cell's own type, so nothing moves there.

- **Example** (tested, `twoPairs`, `Test/Program/BoundsControls.lean`). The program is
  `Ref.modify(cell, s => s > 0 ? [1, s] : ["negative", s])` on a cell of numbers. The step's type
  is `[number, number] | [string, number]`.
- **Today**: refused, `resultNotSubtype` (`bindTerm`, the same file). tsgo refuses the call with
  no type argument too: it picks one candidate
  (`docs/research/2026-10-07-chunk-2-review-evidence/binder_joined.ts.txt`, tsgo
  7.0.0-dev.20260629.1).
- **After**: admitted at `B = number | string`. The call prints as
  `Ref.modify<number, number | string>(a0, …)`, the form that `Test/Codegen/PrintTyped.lean`
  already prints.
- **A spelling anomaly goes.** Today the pair of a union `[number | string, number]` passes, and
  its normal form, the two pairs, is refused. One type is admitted in one spelling and refused in
  the other (the battery's "raw reading" lines). After UNGUARD both spellings are admitted.

### Not a widening: the address table

The slot table (`Node.extSlotEnv`, `src/Effect4/Program/Typing/Table.lean`) and the call instance
(`rowBindings`, `src/Effect4/Program/Typing/Call.lean`) read the same guarded match. They move with
the checker, so the table keeps agreeing with it (`annotate_eq_table`).

## The questions for the owner

1. **W1: admit a host row's call at a join?** Recommended: admit. The match by bounds is sound,
   least and complete (`Bounds.matchB_complete`, the claim `template-match-complete`). tsgo
   accepts the call with the type argument (`docs/research/2026-10-06-print-probe.md`). The
   refusal comes only from the printer, which now writes the argument. The alternative keeps
   refusing at host rows: the author writes an explicit annotation instead.
2. **W2: admit `Ref.modify` and `Ref.modifySome` at a join?** Recommended: admit, for the same
   reasons, and because it removes the spelling anomaly.
3. **The order of a host row's type arguments.** It is a boundary fact (row 325, point 2). The
   printed call lists the arguments in the order of the row's template variables, `.var 0`
   first, so the host's declaration must declare its parameters in that order. Recommended:
   state the rule in `docs/core/host-boundary.md`, and check it against the generated host
   declaration.
4. **The order of the landing.** Today's reader refuses type arguments on a call whose
   operation declares none (`installTypeArgs`, `src/Effect4/Codegen/Read.lean`;
   `E4-CHECK-CE-013`). A widened program would print and not read back. Recommended: land P3,
   the reader's erasure of a join's type arguments, first, then UNGUARD, in one landing.

## What UNGUARD changes in the tree

- **Code.** `matchTerm` becomes `matchB` at four sites: `checkRow`, `bindTerm`, `Node.extSlotEnv`
  and `rowBindings`. `rowBindingsB` replaces `rowBindings`. The guard and its laws go.
- **Laws.** The row check's laws restate through `matchB` (`rowTy_intro`,
  `checkRow_request_iff` and their siblings). `typeArgsAt_none` stops holding, so the connector
  `printTyped_eq_print` keeps its statement under `NoJoin` only.
- **Controls.** The red lines of `Test/Program/BoundsControls.lean` turn green: `firstRow` at two
  lists, `twoPairs`, and the raw reading.
- **Gates by reach.** The truth lane runs one printed join for each widening under tsgo 7, the
  target lane runs, and the corpus lane checks that no row moves.
- **Claims.** The removal unblocks the proposed claim `checker-monotone`, whose statement is false
  while the guards stand (row 306).

## What this note does not establish

- That tsgo accepts each printed join in its context. The probe wrote the forms by hand. The
  lanes test the printed ones after UNGUARD.
- Anything at an eliminator over a union (P2b).
- That no application uses the widened forms. The corpora do not, and the dogfood apps were not
  measured.
