# Timeout contract decision evidence

The existing retry statement rejects a second attempt after an applied success or a nonretryable host failure.
The pinned runtime permits both when the attempt yields before its exit reaches the race observer.

## Evidence

Proof role: counterexample control.
Evidence status: checked finite host probe.
Scope: rc.112 `Effect.raceFirst`, `Effect.retry`, and the documented custom scheduler interface.

`RaceFirstYield.ts` applies one host reply, forces the attempt to yield, completes the timer, and drains scheduled tasks.
The timer is a callback controlled by the probe.
The retry has three retries and retries only the string `Timeout`.
The probe omits exponential delays and uses no physical clock.

`RaceFirstYield.output.json` records two attempts after both an applied success and an applied `BadRequest` failure.
The two controls omit the forced yield and record one attempt.
The compiler is tsgo `7.0.0-dev.20260629.1`.

The pin checks `Scheduler.shouldYield` before evaluating the resumed success or failure in `internal/effect.ts`.
The pin selects the winner through entrant exit observers in `raceAllFirst`, in that same source file.
These checks distinguish reply application from the attempt's observed exit.

## Proposed owner choices

The source-aligned contract permits another attempt only after the timeout form returns a declared typed failure.
A timer winner supplies the declared `Timeout` failure even when the host already applied another result.
An attempt winner supplies that attempt's exit.

The stronger contract makes host success application prevent a retry, even when the attempt yields before finishing.
The stronger contract also prevents a timeout retry after an applied nonretryable host failure.
It requires a scheduling or winner-selection rule stronger than the pinned runtime's exit observers.

Recommendation: select the source-aligned contract and observe each timeout-form outcome with its attempt identity.
Do not infer that outcome from the host call's receipt, application, or retirement.

## Proposed observation schema

Keep the existing host-call observations.
Add a record for each completed timeout form: attempt identity, selected entrant identity, and returned exit.
Name the two entrant roles `attempt` and `timer` in that record.

For every attempt after the first, require the preceding timeout form's returned exit to be a declared typed failure.
Require the next attempt identity to follow that completed form's attempt identity.
Keep the four-attempt bound as a separate clause.
Keep interrupted or incomplete forms outside the completed-outcome premise.

This note proposes the observation and predicate.
It changes no statement, representation, budget, or timeout behaviour.
