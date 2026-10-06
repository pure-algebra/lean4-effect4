# 2026-10-06 brief for seat BOUNDS: a probe of the match by bounds

Status: a brief (history, not authority). One page. Base: the head that the dispatch message
names. It is a research probe for stage 0b of the plan of the study of a gap with holes. The
owner approved its direction and its paper on 2026-10-06 (decisions row 292, points 4 and 5).
**The seat edits no tracked source.** It works in scratch and files notes.

## The question

An operation's template binds a type parameter at its first occurrence
(`Ty.infer`, `Ty.matchTemplate`, `Ty.matchTemplateArgs`, `Scheme.apply`). So the verdict of
`getOrElse(o, d)`, of `ite(c, a, b)` and of a list append depends on the order of the
arguments, and two candidates with no order between them are refused. The proposed rule goes
by polarity (`docs/research/2026-10-06-repeated-parameter-by-polarity.md`, finding 4):

1. a parameter with an invariant occurrence is fixed by it, and each covariant candidate is
   below it;
2. a parameter with covariant occurrences only is the join of its candidates, and `never` with
   no candidate;
3. the instance is then checked as today.

**Is that rule a replacement of the present match: sound, least, complete with no anchored
premise, and equal to the present match wherever that one succeeds? Measure it, and prove what
scratch allows.**

## Read first

1. `AGENTS.md`, in full.
2. The note above, and the paper it reads: Dolan and Mycroft, POPL 2017
   (`vendor/papers/gradual-holes/dolan-mycroft-mlsub-popl17.pdf` in the coordinator's checkout;
   13 pages). Read it in full, and take each statement from its page.
3. The present match and its laws: `Ty.infer`, `Ty.instantiate`, `Ty.matchTemplate` and
   `Ty.sub` (`src/Effect4/Program/Ty.lean`); `checkRow` and `bindTerm`
   (`src/Effect4/Program/Typing/Rules.lean`); `Scheme.apply` and the atoms' templates
   (`src/Effect4/Program/NativeAtom.lean`); `matchTemplate_complete_anchored`, `Ty.anchored`,
   `Ty.bottomFree` and the laws around them (`src/Effect4/Laws/Program/Template.lean`); the
   property `template-match-anchored` (`docs/core/semantics.md`, section 2.6), with the
   counterexample that bounds it.
4. Seat GAP's study, sections 5.5 and 9.6 (b), with its model `gap_types.py`
   (`docs/research/2026-10-06-seat-GAP-study.md`). Seat CENSUS's receipt, sections 6.3 and 7,
   with its scripts (`docs/research/2026-10-06-seat-CENSUS-receipt.md` and its evidence folder).

## The assignment

1. **The function, in scratch**, against the tree: the variance of each occurrence of a
   parameter in a template, the candidates, the solution, the instance. Say which positions of
   `Ty` are covariant and which are invariant, from `Ty.sub`'s own cases. Say whether any is
   contravariant: the note assumes none.
2. **A differential census.** Run both matches on every template application of the two
   corpora: the atoms and the rows. Reuse seat CENSUS's scripts where they serve. Report:
   - each application where both succeed with different instances, up to the normal form;
   - each application that the present match admits and the new one refuses: a finding;
   - the applications that only the new one admits, by operation.
3. **The laws, in scratch**, each compiled or marked as not compiled:
   - sound: the instance is an instance of the template, and each argument is below it;
   - least: every instance that the arguments fit is above the match's;
   - complete: a request below some instance has a match. Find the exact premise. Say whether
     the anchored premise goes, and whether the premise on `never` stays
     (`Ty.bottomFree`, and the counterexample of the present theorem);
   - conservative: it equals the present match where that one succeeds, up to the normal form.
4. **The binder term's parameter.** `Ref.modify`'s result parameter first occurs in the
   result of the row's binder term, and the checker binds it from the term's raw type. Say what
   the rule by bounds gives there.
5. **The gap's rule at a cell.** The study's exact rule collects a lower and an upper bound
   from each member (its section 5.5). Compare it with your function when a gap is read as a
   parameter. Say whether one function serves both, with your evidence.
6. **The target.** In a scratch copy of the truth lane's prelude, write the signatures of
   `getOrElse`, `ite` and the list append by polarity: one TypeScript parameter for each
   covariant occurrence, and their union in the answer. Run tsgo 7 on the forms that it refuses
   today (`docs/research/2026-10-06-uniform-eliminators-tsgo-probe.ts.txt`: `O6`, `T1`, `L7`),
   and on the 73 generated modules of the truth lane against the changed copy. Report each
   module whose verdict or declared type moves. Edit nothing in the tree.

## The rules

- **A research seat.** Edit no tracked source and no generated file. Commit only files under
  `docs/research` on your branch: the receipt, and each scratch file as text beside it
  (`.lean.txt`, `.ts.txt`, `.py.txt`, with its output).
- Label each result with its evidence word: compiled, tested, reproduced, read, or assumed.
  Report a compiling finite probe as a finite probe.
- No install and no download. tsgo 7 only, the pinned compiler. `tsc` is never run.
- The shell's rules are in the dispatch message.

## The receipt

`docs/research/2026-10-06-seat-BOUNDS-receipt.md`, in the research note's form of
`docs/core/controlled-english.md` section 6.3: the question; what was read or run; the findings
with their evidence; proposals; what this does not establish. It ends with:

- **a verdict**: replace the match, replace it under a named premise, or do not;
- **the statements** that an implementation slice would owe, each with its placement: concept
  `subtyping-algebra`, the claims `template-match-anchored` and the proposed `checker-monotone`,
  R3 and R14, its reach, what it does not establish, and its consumer;
- **the churn**: which definitions and which law files the replacement touches, and which
  generated files move (the prelude's atoms, `generated/row-citations.tsv`).

Your last message gives the head, the receipt's path, the verdict and the three counts of the
census.
