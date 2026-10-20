# Response to the review of "Schema as the carrier"

Status: response, 2026-10-19, by the note's author. The review is `README.md` beside this file,
at HEAD `b0b962ff8`. The verdict, rework before implementation, is accepted. The note is reworked
at `docs/research/2026-10-19-schema-as-the-carrier.md`, and nothing is dispatched.

## 1. The one thing to know

Every blocker reproduces. Two admitted programs compute naturals past the host's safe bound
and no codec writes them, so P1 as a totality claim was false. An interrupted exit inside a
success value still refuses after the outer strip. The raw defect mapping collides. The note now
states the observation as total by refusal and complete against codec admission, with a
recursive type-directed normaliser. It puts the numeric bound where it belongs, the profile
judgment of §9.1 item 2. The probe gained the review's five controls, a comparator with expected
classes, reciprocal decoding and a failing control. Its count is 26 executed agreements, 1 after
one fiber renaming, 4 differences, and 9 refusals, 7 of them on both faces.

## 2. Each finding

| Finding | Reproduced | Taken up as |
| --- | --- | --- |
| 1, P1 is false | yes: `overNat` and `overInt` are admitted, finish, and refuse (`probe/out/lean.txt`) | P1 restated as a located refusal, complete against `isCodecValue`; the totality claim is withdrawn; note §5 |
| 2, Lean encodes 2^53, Effect rejects it | yes: `exactBound` encodes in Lean; the generated natural Schema rejects it; the prelude's arithmetic refuses it earlier, "outside the integer profile" | finding 8.7 and move J: one bound, `safeBound`, on both wires, under M2 |
| 3, nested annotations | yes: `nestedInterrupt` is refused after the outer strip | D2, the recursive normaliser, a fold over the type; the codec's laws keep their statements |
| 4, defect collisions | yes, by reading: `Defect.ofError (.tag n) = .user n` is the normal form, and the raw mapping is injective only on it; rc.112's decoder drops extra fields; `missingService` has no key | R5 with two options; move G reworked; finding 8.9 |
| 5, named types and generic calls | yes, by reading: `ty_app` refuses, `SchemaCode.ofTy` takes no declarations, `CallInstance` holds a call's concrete types | D1 expands `b.app.types`; move E uses the checked instance; the first landing is terminal output (R8) |
| 6, the counts | yes: 25 literal, 1 renamed, 4 differ, 5 generation refusals | the counts restated in §8; `compare.ts` with `expected.tsv`, reciprocal decoding and a non-zero exit; one altered line fails it |
| 7, the census is not branch coverage | yes | the census named a structural inventory; execution witnesses counted by the comparator; move I reworked; the string-keyed map representative named |
| 8, OCaml unverified | yes | §6 reworded: rule coverage and gated differentials, the stage law planned; move A owes a fresh native comparison |
| 9, the public shape and the text | yes: `JSON.stringify(-0)` is `0`; `NatJson` holds naturals only | D1 has three cases, terminal, refused and live; the text profile is the integers within the bound; `number` and negative zero are named as out of this landing (R9) |

## 3. One thing the controls added

On the Effect face, the three oversize sums are refused before any Schema sees them: the
prelude's arithmetic dies with "outside the integer profile" (`harness/truth/prelude-atoms.gen.ts`).
Lean's machine computes the exact natural, and its nat wire writes 2^53. So the two faces
refuse the same programs for different reasons, and the sum 2^53 is refused by one face only.
That is the profile judgment's gap, not the observation's, and the note inherits M2 rather than
deciding it.

## 4. What is not conceded

Nothing in substance. Two framings are kept with the review's corrections. The codec remains the
owner of admitted terminal data, as the review says. And the constructor census stays, as an
inventory that the comparator's execution classes complement, not as the acceptance condition.

## 5. The decisions now open

R1 to R9 in the note's §10, with the evidence in §12. The two that unblock the rest are R5, the
defect domain, and R7, the numeric bound. The order of the moves follows the review's dependency
chart. J and G come first, then H and D, then A with C. The native comparison follows, then B,
E, F and I.

## 6. Evidence

- `probe/Faces.lean`, 40 cases, the review's five controls among them; `probe/out/lean.txt`,
  `probe/out/bun.txt`, `probe/out/census.txt`, `probe/out/types.tsv`.
- `probe/compare.ts` and `probe/expected.tsv`: classes `equal` 26, `renamed` 1, `differ` 4,
  `refusedBoth` 7, `refusedEffect` 1, `refusedLean` 1; exit 0; with one altered line, exit 1.
- The review's own probes, reproduced on my side with the same answers
  (`evidence/schema-carrier-review.lean`, `evidence/schema-carrier-review.ts`).
