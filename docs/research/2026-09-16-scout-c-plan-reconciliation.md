# Scout C: the printer/reader redesign against the foundational plan and the proof obligations

Written 2026-09-16 night against `refactor/phase1-phase3` at `7556ddef`, read-only: no `lake`, no
`make`, no edit outside this file. Everything below was read in the tree, in the layout package at
`/Users/pooks/Dev/lean4-doc` (`b864325`), or in the tracked receipts.

Evidence words, used exactly. **proved**: a Lean theorem whose statement I read in the tree, whose
green status is stamped by a commit or by `docs/STATE.md`. **tested**: a `#guard` or a lane that
exists in the tree. **stamped**: recorded in a tracked receipt (a committed TSV, a commit message,
`docs/STATE.md`). **reproduced**: I re-ran it here; I re-ran nothing, so this word appears nowhere
below. **assumed**: my inference with no receipt, marked as such.

The owner's instruction this note answers: "I also want us to look forward and not forget the prior
proof obligations we had planned for previously... lets not be silly and make more work for
ourselves... we had the foundational language implementation plan still to get through."

## 0. The answer in six sentences

The redesign and the foundational plan do not compete: the redesign lives entirely on the **surface**
obligations (O2 to O8, O15, O17) and touches none of the **semantic** ones (O9 to O14, O16), so it
can run beside M2 and M3 rather than in front of them. It cancels real planned work: DI-88's
LCNF-to-TypeScript backend for the canonical reader (a whole packet), the `reconstructible` half of
Commit F (about 65 lines of a second hand-written fold), and the printer's and reader's place in the
"new constructor cost" list. It does not cancel the `Eff` series, S1's wire tags, the `Ty` series,
the machine invariant, or the loop laws, and nothing in it substitutes for them. The template table
should land **after** `select` and `iterate`, not before, because the table must cover the final
alphabet anyway and its acceptance is a corpus-wide byte agreement that a moving alphabet would
invalidate twice; the argument that put the binder table first does not transfer, because that was
a one-commit promotion of an existing eleven-row definition and this is a rewrite of a 704-line
printer and a 3531-line reader. One real hazard is already in `docs/STATE.md`: its "Next, in order"
list uses the name "S1" for two different things (line 36 the `Doc` carrier, line 40 the wire tags),
which is the two-lists problem in miniature. The agent unlock (S9a) is three stages away and the
shortest path to it is R1, R2, R3 plus one tooling driver, which is also the shortest path to the
owner's stated night goal.

## 1. Q1. Stage by stage: served, replaced, delayed

First, the naming. The redesign numbers its stages S0 to S11
(`docs/research/2026-09-16-printer-reader-positions-design.md:300-324`) and the plan numbers its
packets S0 to S9 (`docs/research/2026-09-16-foundational-language-implementation-plan.md:655-784`).
They collide, and `docs/STATE.md` already reads ambiguously: line 36 ends "Next: S1, the `Doc`
carrier", line 40 says "then S1, then the `Eff` series", meaning the wire tags. Throughout this note
the redesign's stages are **R0 to R11** and the plan's keep their S names. Renaming them in the
design note is a one-line edit and it is the cheapest half of Q6.

Column meanings. "Plan" is the item in the ratified M1/M2/M3 (`docs/STATE.md:22-30`) or the packet in
plan §5. "Obligations" are rows of `docs/research/2026-09-16-strict-proof-obligations.md:13-29`.
"OCaml" says whether the stage regenerates the OCaml face: the LCNF image is cut from the roots
`Effect4.Api.run` and `Effect4.Api.replay` plus the machine entries (`ocaml/gen/api_gen.ml:1-2`,
`ocaml/engine/api_engine.ml:1-2`), so the printer and the reader are **not** in it; `ocaml/eff/eff_types.ml`
is cut from the `Eff` inductive by the `eff` group (`Makefile:151-152`).

| R | What it is | Plan items touched | Obligations | Verdict | OCaml | Reason |
| --- | --- | --- | --- | --- | --- | --- |
| R0 | the agreement lane, landed `7556ddef` | plan S0 (evidence); §3.9 "Target type relation" | O17 | serves | no | O17 says host typing is evidence, never a theorem; this is the first executed form of that evidence, stamped in `generated/tsdiag-agreement.tsv` (135 typed-clean, 181 refused-agree, 0 typed-errors). |
| R1 | the `Doc` package | none: the plan has no layout item | none directly | orthogonal, prerequisite | no | `Doc` is a new carrier, not a change to any planned object. Drafted already at `/Users/pooks/Dev/lean4-doc` (`Doc/Core.lean:81` initiality, `Doc/Measure.lean:41` the monoid, `Doc/Layout.lean:94,99` the two policies, `:147,150` spans and locate, `Doc/Laws.lean:110-115` the house policy's state-independence, zero `sorry`, 14 `#guard`s). |
| R2 | `Tree`, the render algebra, the span check | §3.9's "rendering remains at the existing target text boundary"; B18/B19's structural carrier | O2, O17 | serves | no | The carrier `TypeRef` and `ofTy` (`Codegen/Types.lean`) are already the projection B19 ruled; R2 gives their text a position without a second renderer. |
| R3 | blame to code by span containment | DI-86 (landed `353b7960`); plan §4 "located diagnostics with an erasure theorem" | none new; extends O17 | serves | no | `Api.explain` answers a path (`src/Effect4/Api.lean:112`), `codesOf` answers codes (`src/Effect4/Codegen/Diagnostics.lean:87`); R3 is the join, which is what an agent and an editor need. |
| R4 | the template table, `print` as the fold | §3.9 "add no second raw printer"; O8's binder-annotation half | O8, O15 | replaces | no | The binder columns come from `tools/Effect4Gen/binders.json`, so the printer's `n + 1` (13 sites, `Codegen/Print.lean`) stops being a copy of `Node.binders`. This is B17's route finished on the printer. |
| R5 | the generic reader | §3.9 "the canonical reader retains `read_exact`"; DI-88's first clause | O5, O7, O15 | replaces the proofs, keeps the statements | no | Laws 11 and 12 replace `read_print` (`Codegen/Read.lean:1750`) and `read_exact` (`:2908`) by one induction over the table. The statements must not move: see §4. |
| R6 | the host reader from the exported table | DI-88 (`docs/DESIGN-ISSUES.md:162`), register B12 | O17 | replaces a whole packet | no, but `check-ts-reader` and the ingest lanes | B12 sized the alternative as an LCNF-to-TypeScript backend plus a driver; R6 exports the table instead and the engines shrink to one normalizer per parser, which is DI-37's independence. |
| R7 | the schema printer on the same mechanism | none by name; `Codegen/Schema.lean` (536 lines) is the hand-written `documentExpr` | none named | serves the schema plane | no; `check-schema-codec`, `check-schema-ts` | The plan never assigned an owner to the schema printer. R7 gives it the printer's mechanism and one table. |
| R8 | the Effect module surface through the `tsgo` checker | DI-89 row generation (M2, `docs/DESIGN-ISSUES.md:163`) | O16 | serves, and supplies DI-89's mechanism | no | DI-89 asks for "a bounded declaration reader into `Ty`" over the pinned package; R8 is that reader, taken from the compiler we already depend on rather than written again. |
| R9 | the tooling protocol, the CLI, the MCP toolkit | plan S9's "general authoring API" is different work; this is its face | none | orthogonal | no | Nothing in the plan owns the agent face. Today there is no MCP server and no CLI in the tree (`tools/`, `ts/` have none). |
| R10 | the containment tree over the same `Doc` | none; the layout specification's §3.4 | none | orthogonal, cheap | no | One more `Doc`-valued fold over `Eff` sharing `blame`'s path annotations. It is the second consumer that justifies R1. |
| R11 | diff and incremental rendering | none | none | delays nothing; defer | no | The lenses exist (`NodeLenses.lean`); the differ is small. It should wait for an edit operation on the authoring surface, as the design says. |

Two stages in the plan are **delayed** by the redesign if the redesign is taken in full: DI-88's
ingest packet (M2's tail) loses its LCNF backend clause and gains R6, and plan S9b/S9c's "printed
back by recognition" (`docs/STATE.md:39`) gains the table as its mechanism. Nothing else in M1, M2 or
M3 is delayed by anything in R0 to R11, because no stage above changes `Eff`, `Ty`, the machine, the
wire or the reference.

## 2. Q2. Planned work that becomes unnecessary, quantified

**1. Commit F, `readable = scopedAt ∧ reconstructible`** (`docs/STATE.md:37`,
`docs/UNIVERSAL-ALGEBRA-REFACTOR.md:251-263,312-318`). Half of it is already done and half of it is
about to be redone.

- `scopedAt` is generated from `binders.json` and landed at `75a6c2b4` (`src/Effect4/Program/Scoped.lean`,
  300 lines, generated), so the binder half needs no work: what is owed is the theorem
  `readable → scopedAt`, which `docs/STATE.md:37` already names as the fallback.
- `reconstructible` as written would be a second hand fold with nine overrides
  (`docs/UNIVERSAL-ALGEBRA-REFACTOR.md:253-263`) over the same 27 constructors the template table is
  about to own. R5 turns exactly those overrides into side conditions of table rows.
- Measured: the `readable` family is `Codegen/Read.lean:779-888`, about 110 lines; the refactor note
  claims −65. My verdict: take the theorem `readable → scopedAt` (cheap, no definition moves, and it
  is the premise the hoisting proofs already want), and **do not write `reconstructible`**. Saving:
  one day of work that R5 would rewrite, at the cost of zero.

**2. `print` and `read` in the new-constructor cost list** (`docs/STATE.md:40`). With the table, a
constructor costs one template row instead of a `print` arm, a `readHead` arm, a `readable` arm and
the arms in four proofs. Measured on `branch`, the constructor `select` replaces: the packet counts
71 lines in 18 files of which `Read.lean` is 5 and `Print.lean` 1 to 2
(`docs/research/2026-09-16-select-and-iterate-ready-packet.md:7`), plus the arms in `read_print`
(`Read.lean:1750`, 190 lines to `:1940`), `read_exact_all` (`:2308-2908`, 600 lines), `print_readable`
(`:3350-3531`, 181 lines) and `readable_weaken` (`:3285-3350`, 65 lines). Per constructor the
printer and reader cost is **about 60 to 100 lines including the proof arms**. That is the saving,
per constructor, and it is real but small next to the 6 to 10 days R4 and R5 cost
(`docs/research/2026-09-16-ts-ast-algebra-precedents.md:1386-1401`). The large number is the one-off:
the reader's proof block `Read.lean:1750-3531` is 1781 lines and laws 11, 12 and 14 replace most of
it.

**3. The forms' per-row guards.** Nineteen `#guard`s in `src/Effect4/Program/Authoring/Forms.lean:92-...`,
each checking that one form's elaboration equals `Template.expand` on the table's example arguments
(landed `2bed2204`). Under R4 `Forms.all` becomes rows of the same table (design §3, line 81), so the
per-example guard becomes an instance of the generated law 10 (`unTmpl (tmpl c args) = some (c, args)`,
one `rfl` per row). This is **not** a deletion of 19 guards for nothing: it replaces nineteen
example-sized tests with a universal statement per row. Count the change as neutral in lines and
positive in strength.

**4. DI-88's "canonical reader generated from `Read.lean`"** (`docs/DESIGN-ISSUES.md:162`, register
B12). This is the single largest saving. The ruled route is an LCNF-to-TypeScript backend over
`Read.lean`'s closure, sized in B12 against the OCaml precedent (a 209-line driver plus the `Lcnf`
library, which is `src/OCaml5/Lcnf/*` today). R6 replaces it with the exported table plus a generic
matcher. What retires either way: `ts/eff/read.ts` (1566 lines). What retires only under R6: the
backend itself, which is a packet nobody has started. The two engines shrink under both routes
(`ts/eff/ingest/ck.ts` 1077, `ts/eff/ingest/oxc.ts` 952). **Recommendation: amend DI-88's second
clause to name the exported table rather than the LCNF backend, and keep the rest of the row as
ruled.**

**5. The profile module deletion.** Already done at `670f76ab` (`src/Effect4/Codegen/Profile.lean`,
−210 lines; −261 across the commit; seven axiom exemptions gone per `docs/STATE.md:12`). The redesign
does not touch it. Listed here only to close the candidate.

**What does not become unnecessary, and should not be claimed as a saving:** `readable` itself
(design §3, line 86 says it "stays as the domain restriction and shrinks"), the reader's refusal
alphabet, `LawfulSpelling`, the corpus and its goldens, and the round-trip statements. See §4.

## 3. Q3. What must not be delayed, and the order

Five things must keep moving whatever the redesign does, because nothing in R0 to R11 produces them
and every one of them is on the critical path of the ratified plan.

1. **The `Eff` series** (DI-79, `docs/DESIGN-ISSUES.md:153`): `Decision`, `select`, `iterate`, and
   the retirements of `branch`, `whileLoop`, `callback`, `yieldError`. The packet is drop-in
   (`docs/research/2026-09-16-select-and-iterate-ready-packet.md`), its step 0 is done (`0cb8b6a9`,
   `6b770453`, `ff0c042b`), and it is the only item that reduces the alphabet. Delaying it delays
   S1, S4, O13 and O14 together.
2. **S1, stable wire tags.** `branch`'s retirement shifts every later tag
   (`src/Effect4/Program/Wire.lean:14-18`: tags are declaration positions), and the retired `choose`
   held 23 while `provideLayer` now holds 23, so retirement cannot be defined by ordinal today.
   Nothing in the redesign touches the wire, so S1 is free to run in parallel with R1 and R2.
3. **The `Ty` series and M2's semantic repairs** (DI-80, DI-81, DI-87): `scopeExit`, `fiberId`,
   `refSet` answering unit, unit spelling, full-key service identity. These are the machine plane and
   the redesign never reaches them. They also carry the only compatibility re-pin in M2.
4. **Straight and loop safety (S8a, S8a-L) and the invariant under them (O9, D5).** The obligations
   note's §6 step 1 says D5's statement can be written today against the current machine with no
   dependency, and B16 asks for it before S8a-L adds a second fragment theorem. The redesign gives
   no reason to move it and no help with it.
5. **Observation and clocks (S7).** Half landed tonight (`243b785f`, `7ab964ec`: the test clock as
   the decision tape, `runSequential`, `runDilated`); the second half is `denote` and `Straight` as
   `EffAlgebra` instances plus the virtual-time agreement (`docs/STATE.md:38`).
6. **DI-90, the `Effects` package.** Restated by the owner tonight: see §7.1.

### The template table before or after `select`

**After.** The reasoning, stated against the two orders:

- The order ruling of this morning (`docs/research/2026-09-16-algebraic-reading-assessment-and-order-ruling.md:35`)
  put the binder table before `select` and was explicit that this is a **cost** argument, not a
  necessity. Its cost case rested on the table being a promotion of an existing private eleven-row
  definition (`childLevel`, then at `Laws/Codegen/HoistingReadable.lean:45`), verified against green
  proofs in one commit with zero behaviour change. The template table has none of those properties:
  it is a rewrite of `Codegen/Print.lean` (704 lines) and `Codegen/Read.lean` (3531 lines), its own
  author sizes it at three to five days each with "this is the big one" attached
  (`docs/research/2026-09-16-ts-ast-algebra-precedents.md:1386,1394`), and its acceptance is a
  corpus-wide `#guard` agreement plus byte-identical goldens. The argument does not transfer.
- The table must cover the final alphabet in any case. Landing it first means writing rows for
  `branch` (which retires in S4), then adding rows for `select` and `iterate`, then deleting
  `branch`'s row, and re-running the corpus agreement after each. Landing it second means one pass
  over a settled alphabet.
- The saving the other order buys is the 60 to 100 lines per constructor of §2 item 2, twice. That
  is the price of the delay, and it is worth paying once.
- The saving is also mostly in R5, not R4: R4 alone (print as a fold beside the old printer) removes
  no reader arm and no proof arm. So "the table first" would have to mean R4 **and** R5 first, which
  is the full 6 to 10 days in front of the one packet that reduces the alphabet.

The exception that proves the rule: R1, R2 and R3 touch neither the alphabet nor the printer's
clauses (R2 keeps `TypeScript.Expr` with a total map into `Tree`), so they are free to land first,
and R3 is the owner's stated goal for the night.

### The order

1. R1, the `Doc` package (drafted, `b864325`), as a path require, its six laws, goldens unmoved.
2. R2, `Tree` and the positioned render, the fusion lemma, the span check against `tsgo`.
3. R3, blame to code by span containment, on R0's lane.
4. The `Eff` series, steps 1 to 5 of the packet, each step regenerating the OCaml face and running
   `make check-ocaml` (`Makefile:352-356`).
5. S1's tag rule, then `branch`'s retirement and B18's deletion list.
6. R4 and R5 against the settled alphabet; `Forms.all` becomes rows in the same move.
7. R6, then M2's semantic repairs, with DI-89's rows taken through R8.
8. M3: S8a, S8a-L, S8b, S7's second half, the `Effects` retirement, S9b and S9c; R7, R9, R10 as
   their schema and agent faces.

D5's and D6's statements (the typed-state invariant, the observation carrier) can be written at any
point from now; they start no build of their own, as the order ruling records
(`...order-ruling.md:76`).

## 4. Q4. The obligations and the definitions to freeze

**Touched by the redesign.** O2 (types agree by projection: the template table's type holes consume
`ofTy`, so R2 and R4 are the first consumers of B19's ruling in the renderer), O5 (module
reconstruction: R5 re-proves it), O7 (adequacy: R4 re-proves it), O8 (checked emission: R4 owns the
binder annotation, which B19 says comes from `ofTy` at the certificate's `TyEnv`), O15 (forms), O17
(target typing as external evidence: R0 landed it, R3 sharpens it). Of the definitions to freeze,
the redesign touches D2 (types as syntax, landed) and D3 (one typed certificate, landed `9eb223b`),
and it consumes D4 (the source envelope, whose import clause landed at `9c4dffc4`).

**Untouched.** O9 to O14 and O16; D5, D6, D7, D8, D9. This is the clean line: the redesign is the
surface, the plan's remaining M2 and M3 are the machine. It is why they compose, and it is also why
the redesign cannot be read as progress on the semantic obligations.

**Does anything weaken a proved statement? Three checks.**

1. **The DI-86 laws moved beside their definitions** (`582ca7ed`: 399 lines left
   `src/Effect4/Laws/Program/Typing/Blame.lean` and `src/Effect4/Program/Typing/Blame.lean` grew to
   776). The statement `explain_none_iff` is unchanged and `Api.check` is total by it
   (`src/Effect4/Api.lean:125,436`). Nothing weakens. But the plan says twice that theorem
   derivations live in Laws and the runtime stays independent of Laws (plan §3.9, "Keep theorem
   derivations in Laws and the runtime independent of Laws"; §4, "The public package contains
   check/domain evidence only"). The letter holds (no `import Effect4.Laws` in the runtime) and the
   spirit is bent. The proofs concern the checker's own definitions, not Laws-only meanings, and the
   reason is good: the application root must not reach `Effect4.Laws`. **Amend the plan's wording
   rather than leave a landed commit reading as a violation.**
2. **Replacing `read_print` with the generic theorem.** Safe only if the premises do not move. Today
   `read_print` is stated on `LawfulSpelling sig spell`, `readable sig spell n e = true` and
   `print sig n e = .ok x` (`Codegen/Read.lean:1750-1752`), and `ModuleEmission.readModule`,
   `readModule_printModule_readable` and `Api.printModule_roundTrip` all carry `readable` as a
   premise (O5's status line). The design's law 11 is stated on the same domain, but the design also
   says the templates' disjointness is true only "on the image" and that the image must be
   characterised (§4, and `...ts-ast-algebra-precedents.md:1429-1434` item 2). If law 11 ends up
   stated on "the image of `print`" instead of on `readable`, every theorem above changes domain
   silently. **The guard to demand: `readable` keeps its name and its domain, and any new definition
   of it is accompanied by a Boolean equality against today's, proved by `cases` per constructor.**
   The same guard applies to Commit F, which is why §2 item 1 recommends the theorem and not the
   redefinition.
3. **`readable` shrinking** (design §3, line 86). "Shrinks" must mean fewer lines, never fewer
   programs. With the equality of check 2 in hand this is safe; without it, O5 and O7 quietly change
   what they promise.

Two statements the redesign **adds** that the plan does not have and should: the renderer's
injectivity on the image, and `Fmt` functional (design §4, §9 item 14). They are the first
statements in the estate that say the printed text determines the program, which is what a host
reader's correctness ultimately rests on.

## 5. Q5. The agent unlock, and the shortest path from HEAD

S9a is "scoped construction" in the plan (§5 S9a) and "the authoring layer" in the language note
(`docs/research/2026-09-16-language-after-the-rulings.md:353-368`): named binders, a derived-forms
library, and located refusals, so that "an agent writes a program in a day instead of a day and a
half of index arithmetic, and every refusal it gets is actionable".

What is already true at HEAD, stamped: named authoring over the binder table (`0cb8b6a9`, 48
generated lifts, `src/Effect4/Program/Authoring/Lifts.lean`); the derived forms as combinators
(`2bed2204`, nineteen forms with their guards); the native rows as wrappers (`f2d3299a`) and async
rows authoring as the reader reads them (`7ab964ec`); the located refusal by path and reason
(`353b7960`); the one call from a named source to a certificate, `Api.author`
(`582ca7ed`, `src/Effect4/Api.lean:491`). Of S9a's three parts, two exist and the third, "located
refusals", exists as a **path**, not as a span or a host code.

So the redesign does advance the unlock, and it advances exactly the part that is missing. The
shortest path from `7556ddef` to "an agent authors a program by name, gets a located refusal with a
TypeScript code and a span, and sees the containment tree with paths":

1. **R1** (`Doc`), already drafted at `/Users/pooks/Dev/lean4-doc` `b864325` with no `sorry`: land it
   as a path require and prove the six laws. Spans and `locate` are already written
   (`Doc/Layout.lean:132-152`).
2. **R2** far enough to annotate the existing renderer's output with `Eff` paths. The full `Tree`
   is not needed for a span: a `Doc Path` over the existing `TypeScript.Expr` render gives
   `path → (start, end)` and the fusion lemma keeps the goldens.
3. **R3**: join `Api.explain`'s path (`Api.lean:112`) to the span from (2) and to `codesOf`
   (`Codegen/Diagnostics.lean:87`) on R0's lane, and report agree/contained/disagree per program.
4. **R10** for the containment tree: one more `Doc`-valued fold over `Eff` with the same path
   annotations. The design calls it a day's work and it shares everything with (2).
5. One driver in `Tools` that answers `author`, `check`, `explain` and `tree` over stdin or a file,
   so the agent has a face that is not a Lean import. The generated MCP toolkit (R9) is the shaped
   version of this; the driver is the one-day version.

Steps 1 to 4 are the redesign's own first half and step 5 is small. Nothing on this path needs the
`Eff` series, S1, the template table or any M2 repair, which is the strongest argument for doing R1
to R3 first.

## 6. Q6. The replacement for `docs/STATE.md`'s "Next, in order"

Written to be pasted in place of `docs/STATE.md:34-40`, with the redesign renumbered R so the list
has one meaning per name.

> ## Next, in order
>
> One list. The redesign's stages are **R0 to R11** (`docs/research/2026-09-16-printer-reader-positions-design.md`
> §10, renumbered from S so they do not collide with the plan's S0 to S9); the plan's packets keep
> their S names. R0 landed at `7556ddef`.
>
> 1. **R1, the `Doc` package.** Drafted at `~/Dev/lean4-doc` (`b864325`): `Doc` with its fold and
>    initiality, the product `Measure`, the house and elastic policies, the stream, `spans`,
>    `locate`, fourteen guards, no `sorry`. Land it as a path require, prove the six laws of the
>    design's §9, keep every golden byte-identical.
> 2. **R2, `Tree` and the positioned render.** The render algebra into `Doc Path`, the fusion lemma
>    against `Render.expr`, and the span check against `tsgo` for every corpus program. The house
>    fragment keeps running beside it until the goldens match.
> 3. **R3, blame to code by span containment.** `Api.explain`'s path, R2's spans and
>    `Codegen/Diagnostics.lean`'s `codesOf` joined on R0's lane: agree, contained, disagree per
>    program. This is the owner's night ask and the missing third of the S9a unlock.
> 4. **The `Eff` series** (DI-79; packet `2026-09-16-select-and-iterate-ready-packet.md`). Step 0 is
>    done (`0cb8b6a9`, `6b770453`, `ff0c042b`). Then `Decision` and `select`; the loop interface cut
>    to `loopEnter`/`loopResume`, `iterate`, the `whileLoop` rewrite. A new constructor costs one row
>    in `binders.json` plus the hand-written owners (`effTy`, `compileEff`, `denote`, `print`,
>    `read`, `Straight`); `print` and `read` leave that list at R4 and R5, not before. Every step
>    regenerates the OCaml face (`make gen`, then `make check-ocaml`).
> 5. **S1, stable wire tags**, then `branch`'s retirement and B18's deletion list.
> 6. **R4 and R5, the template table and the generic reader**, against the settled alphabet.
>    `readable` keeps its name and its domain, with a Boolean equality against today's definition as
>    the guard; `Read.lean` comes down to `readable` and the table; `Forms.all` becomes rows of the
>    same table and its nineteen example guards become generated `rfl`s. `readable → scopedAt` is
>    proved here; `reconstructible` is not written (the table owns those rows).
> 7. **R6, the host reader from the exported table**, replacing `ts/eff/read.ts` (1566 lines) and
>    DI-88's LCNF-to-TypeScript backend clause.
> 8. **M2, the semantic repairs**: the `Ty` series (`scopeExit`, `fiberId`), `refSet` answers unit,
>    unit spelling and the type-oracle gap, full-key service identity, the one keyed route with the
>    facade deletions and the session generated into the OCaml engine (S6), layers (S5), B18's
>    strings off the wire, DI-89's package rows **through R8** (the Effect module surface read from
>    the pinned package by the `tsgo` checker) rather than a second declaration reader, then the
>    ingest packet.
> 9. **M3, the proofs and the rest**: D5's and D6's statements first (they start no build and B16
>    wants the invariant before a second fragment theorem), then S8a and S8a-L, S7's second half,
>    S9b and S9c, S8b, and the `Effects` retirement as restated by the owner (§7.1 of the scout note:
>    retire the dependency, keep the free monad's core in-tree under its own names, or state the
>    first-order replacement as its own packet).
> 10. **R7, R9, R10** as the schema and agent faces: the schema printer on the same mechanism, the
>     tooling protocol with the generated CLI and MCP toolkit, the containment tree.
>
> Deferred with a reason: R11 (diff and incremental) until the authoring surface has an edit
> operation; the two-dimensional layout algebras until R1 has its second consumer; the `eff { ... }`
> macro until `select` exists, so it is written once.

## 7. The owner's two additions

### 7.1 Retiring `Effects` rather than adopting it

DI-90 as ruled (`docs/DESIGN-ISSUES.md:164`) says "bring the consumed algebra core in-tree under the
same names and drop the pin, in M3 with the proofs; the proof chain does not change. No rewrite of
the free monad." The owner now says "I already want to retire Effects", keeping first-order `Eff`
and the generated algebras. Those are two different moves and the difference is expensive.

**What `src/` actually consumes.** Six files import the package
(`grep '^import Effects'`): `src/Effect4/Laws/Program/Denote.lean` (`Effects.Algebra.Laws`),
`src/Effect4/Laws/Program/Sched.lean` (`Effects.Algebra.Sum`), `src/Effect4/Machine/Context.lean`
(`Effects.Algebra.Program`), `src/Effect4/Schema/EffectfulField.lean` (`Effects.Algebra.Laws`,
`Effects.Flow.Block`), and two `Test/Machine/Runtime/*` files (`Effects.Algebra.Program`,
`Effects.Flow.Block`, `Effects.Trace`). Sixteen files mention `Effects.` at all; the heaviest are
`Laws/Program/DenoteR.lean` (49), `Laws/Program/Denote.lean` (30), `Laws/Program/Intro.lean` (19),
`Laws/Program/Sched.lean` (15), `Machine/Context.lean` (12). The names used, counted: `Program.pure`
68, `interpret` 23, `Program.bind` 23, `Program` 14, `Program.vis` 11, `Program.inl` 9,
`Signature.*` 6, `Program.perform` 4, `Handler` 5.

**Where the free monad actually sits.** `StoreSig` is one line
(`src/Effect4/Laws/Program/Denote.lean:41`), `denote : NativeEff → List Val → Effects.Program StoreSig ExitV`
is at `:66`, and `meaning e env s = (Effects.interpret storeHandler (denote e env)).run s` at `:135`.
The straight fragment's meaning, `run_eq_meaning`, `Intro`, `Sched` and the simulation modules are
all stated over that carrier. `Machine/Context.lean:102-108` is the one **runtime** consumer: the
service-access signature and `UsesOnly` over `Effects.Program`.

**The two costs.**

- *Retire the dependency, keep the carrier.* Copy `Effects/Algebra/Signature.lean` (45 lines),
  `Algebra/Program.lean` (70), `Algebra/Handler.lean` (57) and `Algebra/Laws.lean` (127) in-tree
  under the same names: **299 lines**, plus `Algebra/Sum.lean` (374) if `Sched.lean` keeps the
  signature sum and `Flow/Block.lean` (273) for `Schema/EffectfulField.lean`. Upper bound **946
  lines** of the package's 10,763. Zero proof edits, because the names do not move; one axiom-audit
  pass; the pin and the `effects` require go (`lakefile.toml:120-124`). This is DI-90 as ruled and it
  is a day.
- *Retire the free monad.* `Effects.Program` is an inductive whose `vis` carries a **Lean function**
  as its continuation (`.lake/packages/effects/Effects/Algebra/Program.lean:34-38`), which is
  precisely what makes `denote (bind a b) env` compositional. A genuinely first-order carrier cannot
  hold that continuation; the honest first-order replacement of `denote`'s target is a concrete
  monad (a `StateT Stores` with an exit), which deletes `interpret` and with it the claim that the
  meaning is interpreter-independent, the claim U11's scheduler-as-handler research is built on. The
  edit surface is about 144 `Effects.` sites across ten Laws modules plus the two runtime consumers,
  and every meaning equation and simulation lemma in `Denote`, `DenoteR`, `Intro`, `Means`, `Sched`
  and `Simulation/*` is restated. This is a packet, not a cleanup, and the plan already forbids it in
  M3 ("No rewrite of the free monad").

**How to restate DI-90 and the M3 items.** Amend the ruling text to: "Retire the dependency. Copy
the four algebra modules (`Signature`, `Program`, `Handler`, `Laws`) and, only if their consumers
survive the S7 and S3c work, `Sum` and `Flow/Block`, in-tree under the same names; drop the pin and
the require; re-run the axiom audit. The free monad stays the denotation's carrier and `Eff` stays
first-order: the two are different objects and the language's claim that a program is data is about
`Eff`, not about the meaning's carrier. Making `denote`'s carrier concrete is a separate packet with
its own reason, and it costs the interpreter-independence of the meaning." M3's line in
`docs/STATE.md:30` then reads "the `Effects` dependency retired (DI-90)" rather than "the `Effects`
package in-tree", and the one real prerequisite is that `Schema/EffectfulField.lean`'s use of
`Flow/Block` is decided first, because it is the only consumer that would drag 273 further lines in.

### 7.2 The schema plane, ranked, and whether M2 should move it earlier

The schema plane in the tree: `src/Effect4/Schema/*` is 9203 lines in thirteen modules, the largest
being `Annotations.lean` (2329), `Representation.lean` (2111), `Check.lean` (1827) and
`EffectfulField.lean` (982); `src/Effect4/Codegen/Schema.lean` (536) is the hand-written printer of
those documents; the lanes are `check-schema-codec` in `check-host` and `check-schema-ts`,
`check-schema-pins`, `check-schema-host` in `check-full` (`Makefile:235-236,392-406`).

Ranked by how much each item advances the schema and interop plane rather than the machine:

| Rank | Item | Plane | Why |
| --- | --- | --- | --- |
| 1 | R8, the Effect module surface through `tsgo` | schema and interop | It is the mechanism DI-89's row generation needs, and the same extraction feeds the class APIs and the package rows. Nothing else in the plan produces it. |
| 2 | R7, the schema printer as rows of the template table | schema | Retires the 536-line hand printer, and makes the grammar document itself emittable as `tsSyntax.gen.ts`. |
| 3 | R6, the host reader from the table | interop | One view of foreign and printed code, which is DI-88's stated purpose. |
| 4 | DI-89 package rows (M2) | schema and interop | Ruled already; its cost drops to almost nothing once R8 exists. |
| 5 | R2 and R4, `Tree` and the templates | interop | The carrier both printers share; `ofTy` is already the projection. |
| 6 | S3c full service identity (M2) | both | The requirement column is a schema-shaped object (`R` as full keys, O16) and the nominal declaration is a printed class. |
| 7 | B18's strings off the wire (S1) | both | `Row.typeArgs` and handle names carry structure instead of text; the schema plane stops parsing strings. |
| 8 | The `Ty` series, `refSet` unit, unit spelling, layers, the keyed route | machine | No schema content; they move the wire and the reference. |
| 9 | S8a, S8a-L, S8b, the invariant | machine | Pure semantics. |

**Should M2 move the schema and interop items earlier? Yes, with one condition.** The machine half of
M2 (the `Ty` series, `refSet`, unit spelling, layers, the keyed route) is the half that moves the
stored alphabet, forces a compatibility re-pin and regenerates the OCaml face. The schema and interop
half (DI-89 rows through R8, R6, R7, B18's structural carrier at the boundary) touches none of those.
So they are not competing for the same lane, and the owner's stated purpose (agent-first, Effect TS
interop) is served by the second half. The condition: **DI-89's rows must not land before S1's tag
rule if a row's shape is stored**, because a generated row is data on the wire. If the generated rows
are produced as source-level data checked by the drift gate and not re-pinned bytes, that condition is
empty and the schema half can start immediately after R3.

**The OCaml face, since the table asks for it.** The LCNF image is cut from `Effect4.Api.run` and
`Effect4.Api.replay` plus the machine entries (`ocaml/gen/api_gen.ml:1-2` names the exact roots), so
the printer and the reader are not in it (there is no `print` in `ocaml/gen/api_gen.ml`). What
regenerates the OCaml face: any change to the `Eff` inductive (the `eff` and `wire` groups, and
`ocaml/eff/eff_types.ml`, 626 lines), any change in the closure of `run`/`replay` (the `lcnf` group,
`ocaml/gen/api_gen.ml`, 16314 lines, and `ocaml/engine/api_engine.ml`), and the keyed session when S6
generates it into the engine. What must not break it: the `Eff` series (steps 3 and 5 of the packet
say `make check-ocaml` after the compile and reference arms), the `Ty` series, S3's value boundaries,
S5's layers and S6's session. Every stage R0 to R11 is OCaml-neutral, which is another reason they
can run beside the machine work rather than in front of it.

### 7.3 The design note's §12, added while this scout was running

`docs/research/2026-09-16-printer-reader-positions-design.md:370-412` landed after my first read and
records the owner's late-night direction. Three of its bullets bear on this reconciliation.

- **"A full Eff-typed effectful compilation API: schema → effectful AST, compile f(ast) → schema or
  TypeScript module."** Stated there as a compile that produces a *plan*, an `Eff CompileOp` whose
  rows are the effects a compile needs, typed by `TypedProgram` and replayable from a tape. Against
  the plan and the obligations this is **new work, not planned work**: it adds a second `Op` family
  and a row table, which is DI-89's contract (rows with a typing lemma and a behaviour law, an
  unregistered head refusing by name, `docs/DESIGN-ISSUES.md:163`) applied to the toolchain rather
  than to an Effect package. It should be scheduled as a row family under DI-89's rules, not as a
  stage of the redesign, and its one new theorem (the effectful compile agrees with the pure
  template fold where the effects answer as the tables say) belongs beside law 10 in R4.
- **"Retire Effects."** §12 states it as the free monad going, not only the package. My §7.1 is the
  costed answer: the dependency goes for 299 to 946 copied lines with no proof edits; the *carrier*
  going is about 144 call sites in ten Laws modules plus `Machine/Context.lean` and
  `Schema/EffectfulField.lean`, and it deletes `interpret`, which is what makes the meaning
  interpreter-independent and what U11's scheduler-as-handler research stands on. Decide which of the
  two DI-90 now means before anything is cut.
- **"One coordinate system: `paths e` indexes every projection, and every projection commutes with
  `Node.child`."** This is the sharpest obligation in §12 and it is stateable today: `Node.child`
  and `Node.setChild` are generated (`NodeLenses.lean`), `foldMapAt_*` is the path fold, and
  `Api.blame` already answers a path. It belongs in the obligations note as a new row beside O15,
  because it is the statement that keeps spans, the containment tree, a diagram and an MCP tool from
  each inventing coordinates.

## 8. The three things to decide first

1. **Order: R1 to R3 now, the `Eff` series next, the template table after S1.** The one decision that
   changes the next two weeks. It costs 60 to 100 lines twice (the printer and reader arms of
   `select` and `iterate`, written by hand and then turned into rows) and it buys a settled alphabet
   before a 6 to 10 day printer and reader rewrite, plus the owner's night goal (a refusal with a
   code and a span) inside the first three stages. The alternative, the table first, is defensible
   only if the owner wants the printed surface frozen before the alphabet changes again, and nothing
   in the plan says that.
2. **DI-90's restatement.** "Retire the dependency" and "retire the free monad" are different
   packets: 299 to 946 lines with zero proof edits, against about 144 call sites in ten Laws modules
   plus two runtime modules and the loss of the meaning's interpreter-independence. Decide which one
   the word "retire" means, so M3's line and the `Effects` row say the same thing.
3. **The `readable` guard, before R5 starts.** `readable` is a premise of `read_print`,
   `read_exact`, `print_readable`, `ModuleEmission.readModule` and `Api.printModule_roundTrip`. Rule
   now that any new definition of it, whether from Commit F or from the template table, ships with a
   Boolean equality against today's, proved per constructor; otherwise the round-trip theorems change
   what they promise without anyone editing their statements. The same ruling retires
   `reconstructible` as a thing anyone writes by hand.
