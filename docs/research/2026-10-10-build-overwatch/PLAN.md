# Narrow-build review plan

Review commit: `294c89cdee0fd5874c01df45fb2654c5a480b2cd`.
Previous reviewed commit: `4867cf2b2c41502460949c60143cc9ed0d97b4ab`.

Keep the primary checkout and its active work unchanged.
Reuse the attached review worktree.

## Finishing criteria

1. Compare the new build prerequisites with the files each tool reads.
2. Exercise a fresh check and a changed dependency without running a full build.
3. Compile the extracted goal command and its direct consumers from pinned source.
4. Run the existing goal, placement and closure controls against those compiled modules.
5. Review the proposed facts cache against the existing walk contracts.
6. Record new findings, unchanged findings and the limits of the checks.

## Scope

These checks concern build freshness and proof-report tooling.
They add no semantic theorem and change no registry claim.
The cache remains a proposal.
Finite controls do not establish whole-library agreement or a runtime performance claim.
