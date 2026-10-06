# 2026-10-06 brief for seat FORM: formation refuses a type variable outside a template

Status: a brief (history, not authority). One page. Base: the head that the dispatch message
names. It is stage 0a of the plan of the study of a gap with holes: a repair of the present
checker, and groundwork of R14 (decisions rows 282 and 288, point 6 a).

## The slice

Formation has no rule at a type variable. So a program's annotation can hold `Ty.var`, and the
checker then gives the program a type that is not closed. Two programs of one node show it
(the study's section 9.6 (a), compiled in scratch): `succeed` of an empty record whose optional
field is declared at `var 7` is admitted at `{ readonly a?: T7 }`, and
`Deferred.make<T5, number>()` is admitted at `Deferred<never, number>`.

**The repair: a type variable is formed in a template only.** One clause of
`Formation.HeadFormed` says it, with one refusal reason. Then state and prove that a formed
program that the checker admits has closed types. The gap needs that invariant: a gap is then
the only open leaf of a sketch's type.

## Read first

1. `AGENTS.md`, in full.
2. The study, sections 9.6 (a), 6.6 and the brief of slice FORM in 9.7
   (`docs/research/2026-10-06-seat-GAP-study.md`), with its probe
   `docs/research/2026-10-06-seat-GAP-probe_var.lean.txt`.
3. `src/Effect4/Program/Formation.lean`: `HeadFormed`, `Formed`, `programSites`,
   `argumentAnnotations`, and how a template's sites differ from a program's.
4. Where a proof reads `HeadFormed`: `src/Effect4/Laws/Program/Template.lean`,
   `src/Effect4/Laws/Api/Formation.lean`, and the contract battery
   `Test/Program/FormationContract.lean`.
5. `Ty.closed` and `Ty.instantiate` (`src/Effect4/Program/Ty.lean`), and the claim
   `raw-formation` in `tools/Tools/SemanticsRegistry.lean`.

## The assignment

1. **A design note first, half a page** (`docs/research/2026-10-06-seat-FORM-design.md`):
   - the clause, and how formation knows that a site is a template's (a row's columns, a
     scheme) and not a program's annotation;
   - the refusal reason, and every generated file and case policy that an appended reason
     moves. List them before you edit. The coordinator pins a case policy at the merge;
   - the statement of `check_closed` as Lean elaborates it, with each premise it needs: a
     closed environment, well-scoped rows and schemes, closed service carriers. The study's
     statement is not compiled.
   Send the note's path and the statements, and go on.
2. **The clause**, with its reason. An operation's type arguments are annotation sites, so the
   same clause refuses the second program.
3. **`check_closed`**, stated as a planned goal, placed, and proved in place. If a type
   operation does not keep closed types closed, stop at that operation, state the missing fact
   as its own planned goal, and name it first in the receipt.
4. **Controls.** Red: the two programs of one node are refused at formation, each with the new
   reason. Green: a row whose columns hold a parameter is still formed; each program of the
   truth lane and of the batteries is still formed (the build shows it).
5. **A count.** Search the tree for a program that holds `Ty.var` in an annotation: the
   batteries, the fixtures, the generators. Report each, and whether its verdict moves.

**Not in this slice:** `Ty.instantiate` and its rule at an unbound parameter; the rows; a gap;
the atoms that bind one parameter at two places (the study's 9.6 (b)).

## Placement

| Statement | Concept; claim | Reach | It does not establish | Consumer |
| --- | --- | --- | --- | --- |
| the clause | `subtyping-algebra`; `raw-formation`, role decidability | every annotation of a program | closed types of the checker | `check_closed` |
| `check_closed` | `subtyping-algebra`; the proposed claim `checked-types-closed`, role inversion; R1, R3 and R14 | a closed environment; a signature with well-scoped rows and schemes, and closed service carriers | a closed type of a sketch with a gap; anything of a run | `ofSchema_schema`'s premise, `ofTy`, the codec; stage 6 of the study's plan |

## The files, and the rules

- **Edited:** `src/Effect4/Program/Formation.lean`; the law files that read `HeadFormed`; the
  generated refusal alphabet, by its generator. **New:** one law file for `check_closed`
  (for example `src/Effect4/Laws/Program/Typing/Closed.lean`) and one battery
  (`Test/Program/FormationClosed.lean`).
- **Root anchors:** in `src/Effect4/Laws.lean`, directly after
  `import Effect4.Laws.Api.Formation`; in `Test/All.lean`, directly after
  `import Test.Program.FormationContract`.
- Tag each new theorem `@[semantics "subtyping-algebra" (requirement := R14)]`.
- **It narrows the admitted programs.** That is ratified (row 288). Name every verdict that
  moves. Do not pin a case policy and do not edit the compatibility policy: give the lines of
  each refusal in the receipt.
- Do not edit `docs/core/decisions.md`, `docs/STATE.md`, `lakefile.toml`,
  `generated/semantics.md`, `docs/core/semantics.md` or `tools/Tools/SemanticsRegistry.lean`.
  Propose their text in the receipt.
- No `partial`, `unsafe`, `native_decide`, `axiom`, `extern` or `implemented_by`. No
  `simp_all`, `first` or `try`. A hand `simp` is `simp only [...]`. Every warning is an error.
- The shell's rules are in the dispatch message.

## Acceptance, and the receipt

Each landed statement is a theorem at `[propext, Quot.sound]`, or a planned goal that the
receipt names first with its missing fact. The controls pass. Run narrow builds after each
step. Run the default `lake build` once at the end, with the gate lines, then
`make gen-fixtures`, `make check-cases` (give its lines if it refuses) and `make check-docs`.
Not run, and listed so: `check-gen`, `check-slow`, `check-corpus`, `check-target`,
`check-truth`, the conservativity script, `gen-semantics`.

The receipt is `docs/research/2026-10-06-seat-FORM-receipt.md`, in the handoff form of
`AGENTS.md`: the one thing to know before merging; base, head and commits; changed files;
commands with results; the statements as compiled, with axioms and plan status; each verdict
that moved; the proposed registry text. One paragraph accounts for R1 to R14. Your last message
gives the head, the receipt's path and its first item.
