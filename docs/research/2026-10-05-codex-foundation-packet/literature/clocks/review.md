# Clock contract references

Evidence status: standards and API sources checked; finite Effect probes retained separately.
Proof role: design input and proposed obligation.
Scope: unit migration and the clock profile before timed APIs.

## Sources and their authority

[High Resolution Time Level 2](https://www.w3.org/TR/2019/REC-hr-time-2-20191121/) is a W3C Recommendation dated 21 November 2019.
Section 6 requires a monotonic clock for the relevant same-origin measurements.
System clock changes must not produce negative elapsed differences there.
Resolution remains a separate question in section 7.1.

[High Resolution Time Level 3, 1 September 2026](https://www.w3.org/TR/2026/WD-hr-time-3-20260901/) is a Working Draft.
Section 2.1 separates adjustable wall time from elapsed-time measurement.
Section 2.2 distinguishes durations from moments and disallows comparisons across unrelated clocks.
This draft helps state the domain model; it is not a ratified replacement for Level 2.

[POSIX clock_gettime, Issue 8](https://pubs.opengroup.org/onlinepubs/9799919799/functions/clock_gettime.html) belongs to IEEE Std 1003.1-2024.
Clock resolution is implementation-defined.
The monotonic clock has a fixed, unspecified origin and cannot be set through clock_settime.
Changing real time must not change expiration of a relative interval already blocked on the old time.
This supplies a useful timer contract; it does not make Effect4 a POSIX implementation.

[Node v26.10.0 process documentation](https://nodejs.org/docs/v26.10.0/api/process.html) specifies `process.hrtime.bigint` as nanoseconds represented by a BigInt.
Its arbitrary origin is unrelated to time of day.
The document specifies Node's API; the finite probes run on Bun 1.4.2.
It does not establish Bun conformance or physical nanosecond resolution.

## Recommendation

Accept exact internal nanoseconds as a representation choice.
Keep wall moments, monotonic moments, and durations distinct in the contract.
A chosen logical test profile can derive both readings from one counter with a shared origin.
That profile does not cover arbitrary live host wall clocks.

Choose the compatibility boundary before changing `ClockMillis`, `Native.sleep`, session commands, or persisted journals.
Keep every existing millisecond input's meaning through exact conversion.
Define a distinct target `bigint` image before admitting public nanosecond results.
Avoid promising that a finer integer unit changes the host's timer resolution.

Proposed obligation: `clock_unit_compatibility`.
Concept: `translation-simulation`, serving R10 and M7 under decisions row 83.
Proposed placement: the clock-profile registry claim selected by that ruling.
Consumer: timer and session migration before new timed APIs.
Premises: named origins, fixed input version, exact millisecond conversion, and a target numeric representation with a named profile-support judgment.
Observation: legacy replies and deadlines after projecting nanoseconds back to their declared unit.
Exclusions: physical accuracy, unrelated origin comparison, live wall monotonicity, and arbitrary host-clock agreement.
Immediate prerequisite: freeze the profile and journal/wire conversion policy.

The process-local backwards-wall-clock probe supplies a negative case.
Its unchanged-clock run supplies the positive control.
Neither establishes a theorem about all executions.

## Receipt

[download-manifest.json](download-manifest.json) retains exact URLs, timestamps, sizes, and SHA256 hashes for four successful downloads.
The first sandbox DNS failure remains in `manifest.json`; the successful authorized download supersedes that attempt.
The source extraction uses Python's HTML parser and changes no application or system setting.
