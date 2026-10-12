# Checked public numeric inputs

The OCaml engine now checks public numeric replies and natural literals before constructing their represented values.
Exact multiplication support lands in the existing numeric library.
The multiplication compiler row and generated warning repair remain pending.

## Placement

Concept: translation-simulation, R8, through item 12's R-T2 and R-T8 obligations.
Consumer: the public OCaml engine and its program converter, plus the planned `Profile.scale` compiler row.
The natural observation uses the existing bound of `2^53 - 1`.
The float observation uses the existing unsigned bit carrier's representability bound.
These finite target checks establish no general Lean-to-OCaml simulation.
The foreign host and raw generated constructors remain trusted boundaries.

## Change

`E4_clock.mul` uses exact Zarith multiplication.
The existing `to_profile_nat` supplies checked observation afterward.
The multiplication controls retain exact products above both the JavaScript bound and the machine-integer bound.

`E4_engine.answer_async_success` refuses negative and oversized natural values before constructing a decision.
`answer_async_float` checks the complete IEEE-754 bits before conversion to the existing integer carrier.
It accepts representable patterns and refuses the remaining patterns without truncation.
`Make` refuses hosts whose integer size differs from 63 bits.

`E4_program.of_lit` applies the same natural check.
The source and byte-loading routes already consume this converter.
The engine's public decision type stays abstract.
The raw `INSTANCE` value constructors remain outside this checked public interface.
There is no source float literal constructor in the current literal alphabet.

## Verification

Base: `40db61ad1`.
`IngressEvidence.json` records every changed source path, its hash, and the generated engine files used by this run.
The tool reports OCaml 5.1.1, dune 3.24.2, and arm64.

```sh
opam exec --switch=effect4 -- dune runtest clock --force
opam exec --switch=effect4 -- dune exec engine/test/test_engine.exe
git diff --check
```

The clock tests pass, including exact multiplication and refusal beyond the profile.
The engine tests pass on both Fast and Ref, with 182 checks and zero failures.
The new cases include negative replies, oversized replies, source literals, and encoded literals.
They accept zero and the largest permitted natural reply.
They accept float patterns for zero, 1.5, and the carrier's largest bit pattern.
They refuse 2.0, negative zero, negative one, infinity, and NaN.
The tests reach the new public constructors directly.

The compiler first rejects two ambiguous documentation comments; the repaired interfaces compile.
An initial broad test attempt starts before the implementation patch applies and is stopped.
It supplies no acceptance evidence.
The retained logs come from the final narrow commands above.
No Lean source changes in this slice, so no Lean axiom gate is added.

## Remaining work

The adjacent machine slice checks `Profile.scale` and the exact Lean multiplication control with the whole laws library.
The next target slice adds its OCaml compiler row, restores warning 8, and regenerates the reached outputs.
The current finite ingress tests use the recorded generated engine files without regeneration.
The reached behavior comparisons still run at the planned sweep.
Propose the R-T8 boundary repair and R-T2 retained-atom choice in the coordinator's register after their remaining checks.
