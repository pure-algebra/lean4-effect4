# 2026-10-06 brief for seat CENSUS: the probes of the type slicing plan

Status: a brief (history, not authority). Base: the head that the dispatch message names. The
owner asked for these probes on 2026-10-06 (decisions row 281, point 4): "go ahead with your
recommendations and run the probes". It is research. It proves nothing and edits no tracked
source.

## What it is for

The plan `docs/research/2026-10-06-type-slicing-plan.md` reads the paper "Bidirectional Type
Slicing" (`vendor/papers/program-graphs/bidirectional-type-slicing-2607.12197v1.pdf`) and
maps it to our checker. Everything in it rests on one property, graduality: fold away a part
of a program, and the rest still checks, at a type with less information. The plan says by
reading that our checker has the property in part. **Your slice measures it.** Its numbers
decide how far candidate A reaches, what candidate N would change, and what candidate G must
repair (the plan's section 4.3).

## Read first

1. `AGENTS.md`, in full.
2. The plan, in full, and the paper's pages 5 to 12 and 18 to 23.
3. `src/Effect4/Program/Checker.lean` (`check`, its mutual block, `rowCheck`),
   `src/Effect4/Program/Typing/Rules.lean` (`EffTy`, `termTy`, `argTy`, `catchIfError`,
   `fiberTy`), `src/Effect4/Program/Record.lean`, `src/Effect4/Program/Tuple.lean`,
   `src/Effect4/Program/Decision.lean`, `src/Effect4/Program/NativeAtom.lean` (how a scheme
   applies), `src/Effect4/Program/Refs.lean` (`replaceAt`, the path orders) and
   `src/Effect4/Program/Node.lean`.
4. The focus brief's section 2, for the environment that each child inherits
   (`docs/research/2026-10-05-codex-foundation-packet/implementation-audit/capability-design-2026-10-06/next-slices/focus/brief.md`).

## The probes

Each is a finite test in a scratch Lean file, run on the checker of the tree. File each
script as text beside the receipt. Label each result: tested, reproduced, or read only.

1. **The graduality census.** For each admitted program of the generated corpus
   (`Test.Program.Gen`, the 400 programs of `make corpus`) and of the truth lane
   (`harness/truth/Truth.lean`, its `corpus`), and for each single effect address of it:
   - **Fold A**: replace the node by a program with the node's own answer type, the error
     `never` and no requirement. One form is `succeed` of a fresh variable, at an
     environment that gains that variable, with the rest weakened. Say which form you use.
   - **Fold N**: replace the node by a program of type `never` in all three columns.
   - Run `check` on each folded program. Record: admitted or refused, with the refusal's
     rule and path; and for an admitted one, each column against the full program's column
     (equal, smaller, larger or unrelated, by `Ty.sub` and by the requirement's inclusion).
   - Then do the same for each term address, under fold N alone, where the corpus has a
     closed term of type `never` to put there. If none exists, say so: it is a finding.
   Report one table by rule: the parent's constructor and the child's index, the count of
   folds, the count refused, and the counts by column outcome. List each rule that breaks
   graduality with one smallest program for it.
2. **The eliminator census**, by reading, then checked by a guard each: for every
   eliminator of `termTy`, `argTy` and `check`, does it distribute over a union's members,
   and what does it answer at `never`? One table. It is the list that candidate N would make
   uniform.
3. **The analysing rules**, by reading: each place where the checker compares a type with an
   expected one, the source of the expectation (a row's declaration, a declared field, an
   annotation, a fixed type) and the refusal that it gives. It is the list that analysis
   slices and a marking checker need.
4. **The lattice, on two examples of the paper.** Write the plan's generic interface in
   scratch (a mask, a monotone check, a valid mask, the one-step descent). Render as programs
   of ours the four incomparable minimal slices of the paper's page 18 and the meet that
   breaks the Galois connection on its page 23. Enumerate every mask by brute force. Report
   the minimal masks that our checker gives, and each difference from the paper's answer
   with its cause.
5. **Candidate A at work.** On every program of the two corpora with a non-empty error
   column or requirement: for each member of the error union and each required service, the
   minimal mask by the one-step descent under fold A, where the mask stays in A's domain
   (the plan's section 4.3: no address whose error flows into a value). Report the sizes
   (kept nodes against all nodes), the programs where the descent leaves A's domain, and
   three worked examples as highlighted program text. Check the completion law on each
   minimal mask by a finite test: replace each folded region by two other admitted
   sub-programs of the same answer type, and test that the queried member stays.

Stop rule: probes 1 to 3 are the floor. If probe 4 or 5 does not fit your time, hand back
with its design and the first numbers.

## What each probe tests

| Probe | The proposed claim that it tests (the plan's section 6) | A refutation looks like |
| --- | --- | --- |
| 1, fold A | `column-graduality` | a refused fold, or a larger column, at an address of A's domain |
| 1, fold N | `checker-monotone` | a refused fold: each one names an eliminator or an invariant position |
| 2 | the reach of candidate N | an eliminator that cannot distribute |
| 3 | `expected-type-slice`, the `marking-` rows | an analysing rule whose answer reads the refused premise |
| 4 | `slice-lattice-minimal` | a descent that ends at a mask that is not minimal |
| 5 | `slice-completion` | a completion that loses the queried member |

None of these is proved by a probe. A compiling finite probe is reported as a finite probe.

## The files, and the rules

- You edit no tracked source. Your scratch files live in the scratch folder that the
  dispatch names. You commit only notes and filed texts under `docs/research/`, each with
  `git add -f`: the receipt, and each probe's script and output as `.txt`.
- No planned goal, no theorem in the tree, no change of a battery.
- No install and no download. A paper that is not under `vendor/papers/` is not read: name
  it without a locator, and mark it "not read".
- The shell's rules are in the dispatch message.

## The receipt

`docs/research/2026-10-06-seat-CENSUS-receipt.md`, in the handoff form of `AGENTS.md`: the
one thing to know first; base, head and commits; the commands with results; then one section
for each probe with its table, its smallest counterexamples and its evidence label. End
with three lists: what the numbers say for candidate A, for candidate N and for candidate G;
each sentence of the plan that the numbers correct, quoted with its correction; and the
probes that you would run next. Your last message gives the head, the receipt's path and
its first item.
