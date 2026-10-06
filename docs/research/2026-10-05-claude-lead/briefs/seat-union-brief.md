# 2026-10-06 brief for seat UNION: one combinator for a rule that reads a union member by member

Status: a brief (history, not authority). One page. Base: the head that the dispatch message
names. It is a groundwork slice of R14 (decisions rows 282 and 285). The owner ordered it on
2026-10-06, as the first step of candidate N, the uniform eliminators.

## The slice

Two rules of the checker read a union member by member today: the field read and the field
write (`Record.fieldType` and `Record.setType`, `src/Effect4/Program/Record.lean`). Each applies
a member rule to every member of the target's normal form and joins the answers. At `never`
there is no member, so the rule answers `never`. The other eliminators read a type by its
shape and refuse a union: `fiberTy` (`src/Effect4/Program/Typing/Rules.lean`), `Decision.arms`
at `.option` (`src/Effect4/Program/Decision.lean`), and more. Candidate N converts them, one
family per later slice.

**This slice names the pattern once, proves its laws once, and writes the two record rules
through it. It changes no rule, no admitted program and no existing statement.** Each later
conversion is then an instance that owes its member rule's facts and nothing else. The gap's
lifted eliminators are the same instances (seat GAP's study, section 5.3).

## Read first

1. `AGENTS.md`, in full.
2. `src/Effect4/Program/Record.lean`, and `Ty.members`, `Ty.join`, `Ty.normalize` and `Ty.sub`
   in `src/Effect4/Program/Ty.lean`.
3. The four proofs that carry soundness from the member rule today: `fieldType` and `setType`
   in `src/Effect4/Laws/Program/Typed.lean`; `record_fieldType_fits` and `record_setType_fits`
   in `src/Effect4/Laws/Program/Typed/RecordOperations.lean`. Each is four lines over
   `has_members` or `fits_members`, the normal form's law and `joinResults`.
4. The laws of members under the order: `sub_iff_members`, `members_join`, `member_sub_self`,
   `Normal.members` (`src/Effect4/Laws/Program/TypeAlgebra.lean`, `Ty.lean`).
5. The by-shape rules, to know the consumers: `fiberTy`, `Decision.arms`, `Record.tagArms`.
6. Seat GAP's study, section 5.3 and the brief of slice UNIFORM in 9.7
   (`/Users/pooks/Dev/lean4-effect4-t3b/docs/research/2026-10-06-seat-GAP-study.md`).

## The assignment

1. **A short design note first** (`docs/research/2026-10-06-seat-UNION-design.md`): the
   combinator as Lean elaborates it. Decide these, each with its reason, then send the path and
   the statements and go on.
   - The answer's carrier. The field read answers one type. A fiber or an exit answers a pair,
     a value type and an error type. A decision answers the types that its arms bind. Say what
     the carrier must give (a join and a least element), with no Mathlib.
   - The homes: a core module that `Record.lean` imports, and one law module.
   - The premise on a member rule that makes the lifted rule monotone in `Ty.sub`.
   - Lean's own tools, as a design input: can a command or an attribute declare an instance and
     its soundness theorem from a member rule and its member lemma? Implement it only if this
     slice's two instances already pay for it. Otherwise file the note for the conversions.
2. **The combinator**, with `fieldType` and `setType` written through it. Each stays equal to
   its present definition, by `rfl` or by a proved equation. `Record.joinResults` keeps its name.
3. **The laws, once.** State each as a planned goal, placed, and prove it in place.
   - *Total at `never`*: the lifted rule answers the carrier's least element.
   - *One member*: on a normal type that is one member, the lifted rule is the member rule, up
     to the join with the least element. `fieldType_normal` and `setType_normal` follow from it
     (`src/Effect4/Laws/Program/Typing/TermIntro.lean`), with their statements unchanged.
   - *Normal form*: two types with one normal form have one answer.
   - *Monotone*: under the premise of the note, a smaller target is admitted where a larger one
     is, at a smaller answer.
   - *Soundness transfer*: for a membership relation that reads the normal form, the members and
     a join, and for a value operation: a member rule that is sound at each member lifts to a
     sound rule. The tree has two such relations, `Has` and `Fits w`. Prove the four theorems
     of item 3 of the reading list from it, with their statements unchanged.
4. **Controls** in a battery (`Test/Program/UnionRule.lean`): the lifted rule at `never`; at a
   union of two records; at a union with one member that refuses. Red controls: a member rule
   that is not monotone, whose lifted rule is not; and `fiberTy` at a union of two fiber types,
   which refuses today. The second records the present behaviour for the conversion that
   changes it.

**Not in this slice:** the conversion of any by-shape rule; any change of `HasTy`, of `check`,
of a refusal or of the prelude; an atom's template inference; a gap.

## Placement

| Statement | Concept; requirement | Reach | It does not establish | Consumer |
| --- | --- | --- | --- | --- |
| The five laws | `subtyping-algebra`; R14, the proposed claim `union-rule-lift` | every member rule into a carrier with a join and a least element; `Ty.sub`, `Ty.normalize`, `Ty.members`; `Has` and `Fits w` | that any other rule reads a union this way; `checker-monotone`; that tsgo agrees; an invariant position | each conversion slice of candidate N; the gap's lifted eliminators (stage 6 of the study) |

## The files, and the rules

- **New:** one core module (for example `src/Effect4/Program/UnionRule.lean`), one law module
  (`src/Effect4/Laws/Program/UnionRule.lean`) and the battery. A new core module opens with
  `module`, `public import` and `@[expose] public section` (decisions row 200).
- **Edited:** `src/Effect4/Program/Record.lean`, and the three law files of the reading list.
- **Root anchors:** in `src/Effect4/Laws.lean`, directly before
  `import Effect4.Laws.Program.TypeAlgebra`; in `Test/All.lean`, directly after
  `import Test.Program.RecordOperations`. The core module is reached through `Record.lean`.
- Tag each new theorem `@[semantics "subtyping-algebra" (requirement := R14)]`.
- **No existing statement changes.** Show it: list `#check` of each theorem that names
  `fieldType`, `setType` or `joinResults`, at the base and at the head, and compare the lists.
- **No term and no type moves.** `make gen-fixtures` leaves `git status` empty.
- Do not edit `docs/core/decisions.md`, `docs/STATE.md`, `lakefile.toml`,
  `generated/semantics.md`, `docs/core/semantics.md` or `tools/Tools/SemanticsRegistry.lean`.
  Propose their text in the receipt: the claim's row and title, and the required property.
- No `partial`, `unsafe`, `native_decide`, `axiom`, `extern` or `implemented_by`. No
  `simp_all`, `first` or `try`. A hand `simp` is `simp only [...]`. Every warning is an error.
  No planned goal stays open at the hand-back unless the receipt names its missing fact first.
- The shell's rules are in the dispatch message.

## Acceptance, and the receipt

Each landed statement is a theorem at `[propext, Quot.sound]`. The controls pass, each red one
red for its stated reason. Run narrow builds after each step. Run the default `lake build` once
at the end, with the gate lines, then `make gen-fixtures`, `make check-cases` and
`make check-docs`. Not run, and listed so: `check-gen`, `check-slow`, `check-corpus`,
`check-target`, `check-truth`, the conservativity script, `gen-semantics`.

The receipt is `docs/research/2026-10-06-seat-UNION-receipt.md`, in the handoff form of
`AGENTS.md`: the one thing to know before merging; base, head and commits; changed files;
commands with results; the statements as compiled, with axioms and plan status; **what an
instance owes**, as a list that a conversion's brief can copy; the proposed registry text. One
paragraph accounts for R1 to R14. Your last message gives the head, the receipt's path and its
first item.
