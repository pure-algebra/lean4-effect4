# 2026-10-06 brief for seat PILOT: the fiber rule as a lifted rule, under the guard

Status: a brief (history, not authority). One page. Base: the head that the dispatch message
names. It holds seat UNION's combinator (decisions row 293). This is the pilot conversion of
candidate N (rows 285 and 292). **It fixes the form of every later conversion**, so its design
note and its receipt are read as a pattern.

## The slice

`fiberTy` answers the value type and the error type of a fiber handle's type
(`src/Effect4/Program/Typing/Rules.lean`). It reads the head of the raw type. So it refuses
`never`, and it refuses a type whose normal form is one fiber type under a raw union. Seven
sites of `Checker.check` ask it, and the judgment states each fiber rule through it
(`src/Effect4/Laws/Program/Typing/HasTy.lean`).

After this slice `fiberTy` is the guarded lifted rule of its member rule. It answers at
`never` and at one union member of the normal form. It keeps today's refusal at a proper
union (row 292: tsgo 7 refuses the printed call there until the printer writes the type
arguments).

**Read first:** `AGENTS.md`; seat UNION's receipt, sections 7, 8 and 9
(`docs/research/2026-10-06-seat-UNION-receipt.md`); the coordinator's probe, finding 2
(`docs/research/2026-10-06-uniform-eliminators-landing-probe.md`); the two modules
`src/Effect4/Program/UnionRule.lean` and `src/Effect4/Laws/Program/UnionRule.lean`.

## The assignment

1. **A design note first, one page** (`docs/research/2026-10-06-seat-PILOT-design.md`), with
   each statement compiled in scratch. Send its path, and go on.
2. **The guard**, one definition beside `UnionRule.lift`: the lifted rule where the target's
   normal form has at most one union member, and a refusal elsewhere (the receipt's
   `liftOne`). Its head comment says why it exists and what removes it. Its laws stand in the
   law module: it implies the lifted rule's answer; it is the lifted rule at one union member
   or none; it reads the normal form.
3. **The contract of a guarded eliminator, stated once.** For every `Eliminator rule C`, prove
   what the guarded rule gives. No later conversion proves these again.
   - It answers the least answer at `never`.
   - Its answer `a` has the target below `C a`, in `Ty.subN`, and `a` is the least such.
   - Where the member rule answers at a raw type, the guarded rule answers there too, with an
     answer equal up to the order. Find the exact member premise that this needs.
   - It refuses a target with two union members in its normal form.
4. **The rule.** The by-shape function stays, as the member rule, under a new name. The
   default is one namespace for every member rule of the checker: `Member.fiber`. `fiberTy`
   becomes the guarded lifted rule of it, one line. The name `fiberTy` stays where the
   judgment, the inversions and the checker name it. Say whether a statement of
   `HasTy.lean`, of `Typing/CheckInversion.lean` or of `Checker.lean` changes its text: the
   default build is the evidence.
5. **The instance.** `fiberTy_eliminator` and `subN_fiberOf_iff` move from the battery
   (`Test/Program/UnionRule.lean`) into one law module that each later conversion extends:
   `src/Effect4/Laws/Program/Eliminators.lean`, one section for each converted rule.
6. **The shape lemma.** `fiberTy_eq_some` (`src/Effect4/Laws/Program/Typed/Membership.lean`)
   is false of the new rule. Its replacement is the upper form of step 3. Each of its 13 uses
   in `src/Effect4/Laws/Program/Typed/Denotation.lean` moves the value up by `fits_subN`.
   Count the lines that each use costs.
7. **The differential.** The old rule did not read the normal form, so an answer can change
   its spelling. Compare the verdict and the type of each program before and after, up to the
   normal form: the 400 programs of the generated corpus (`generated/corpus-index.tsv`, by
   `make corpus`) and the 73 of the truth lane. **A program that was admitted and is now
   refused is a finding: stop and report it.** List each row that moves, by name.
   - **One mechanism is known.** An atom's scheme infers on the raw type of its argument. So
     the checker refuses the normal form of a type that it admits raw: `mapFromEntries` is
     admitted at `list (prod string (union nat string))` and refused at a list of the union of
     the two pairs (seat SKETCH, compiled). A converted rule answers a normal form, so a value
     type that holds a product over a union reaches a later atom as a union of products.
   - Compile one closed program that today's checker admits and the converted rule refuses
     by that mechanism, or say why none exists. Put it in the design note. Do not change the
     rule to avoid it: the cause is the match of a template, which seat BOUNDS probes.
   - Say in the receipt whether a conversion must wait for the match by bounds.
8. **Controls**, in the battery. `never` is answered with two `never`. One fiber type under a
   raw union with `never` is answered. Two fiber types with no order are refused with
   `notFiber`. A sketch joins a handle that a hole declares at `never`, and `Sketch.check`
   admits it (`src/Effect4/Program/Sketch.lean`). Each red control is red for its stated
   reason.
9. **A cut, as its own commit.** Five theorems lost their last use in `src` with seat UNION
   (its receipt, section 2). Cut them, with their four lines of
   `Test/Program/RecordOperations.lean`.

**Not in this slice:** another rule's conversion; the printer; the removal of the guard; a
theorem that the whole checker is monotone.

## Placement of the obligations

- Concept `subtyping-algebra`; the required property is "a rule that reads a union member by
  member" (`docs/core/semantics.md`, section 2.6). Tag each theorem
  `@[semantics "subtyping-algebra" (requirement := R14)]`.
- The contract of step 3 is a new question. Propose its registry claim in the receipt, with
  one pointer: a statement over every `Eliminator`. The upper form at the fiber rule is a
  step of the claim `denote-typed` (R3), and its consumer is `Typed/Denotation.lean`.
- Reach: the guarded rule of a member rule with the three facts of `Eliminator`; the order
  `Ty.subN`. Decisions rows 285, 292 and 293.
- It does not establish: `checker-monotone` (false under the guard at a proper union); that
  every admitted program stays admitted (the differential is a finite check); anything that
  tsgo accepts.
- It unlocks: the other conversions as instances, and a hole at `never` under an eliminator.

## The rules

- Three seats edit near you: seat SKETCH (the replacement law over `HasTy`), seat FORM
  (`Formation.HeadFormed`) and seat LANES (the TypeScript lanes). Read none of their branches.
- Seat FORM's law file is not in your base. It holds one lemma that reads the rule by cases:
  a closed handle type has a closed value type and a closed error type. Compile its
  replacement in scratch, from `lift_closed_pair`, and give it in the receipt.
- Root anchors. In `src/Effect4/Laws.lean`: directly after
  `import Effect4.Laws.Program.UnionRule`. In `Test/All.lean`: directly after
  `import Test.Program.UnionRule`.
- Do not edit `docs/core/decisions.md`, `docs/STATE.md`, `lakefile.toml`,
  `generated/semantics.md`, `docs/core/semantics.md`, `docs/core/controlled-english.md` or
  `tools/Tools/SemanticsRegistry.lean`. Propose their text in the receipt.
- No `partial`, `unsafe`, `native_decide`, `axiom`, `extern` or `implemented_by`. No
  `simp_all`, `first` or `try`. A hand `simp` is `simp only [...]`. Every warning is an error.
  State each theorem as a planned goal, placed, and prove it in place.
- The dictionary's words: union member, member rule, lifted rule, eliminator.
- The shell's rules are in the dispatch message.

## Acceptance, and the receipt

Each landed statement is a theorem at `[propext, Quot.sound]`. Run narrow builds after each
step. Before the hand-back run the default `lake build` once, with the gate lines, then
`make gen-fixtures`, `make corpus`, `make check-cases` and `make check-docs`. Not run, and
listed so: `check-gen`, `check-slow`, `check-target`, `check-truth`, `gen-semantics`,
`gen-architecture`, `dune`.

The receipt is `docs/research/2026-10-06-seat-PILOT-receipt.md`, in the handoff form of
`AGENTS.md`. Its first item is the one thing to know before merging. It also gives:

- **the measured churn**: files, lines, and the cost of one use site;
- **the differential's rows**, by name, for the compatibility policy;
- **the form of the next conversion's brief**, half a page: what an instance writes, in which
  file, in which order;
- the proposed registry and dictionary texts, and one paragraph that accounts for R1 to R14.

Your last message gives the head, the receipt's path and its first item.
