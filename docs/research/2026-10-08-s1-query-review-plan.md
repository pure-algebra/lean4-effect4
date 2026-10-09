# S1 query review controls

Base: `979be0ad`.
The review compares S1a and S1b with `8785c6f9`.
Claude owns the ongoing splice work in the primary checkout.

## Claim and scope

`Tools.Query.answer` promises a law name only after deciding that law's premises.
Its focus answer now uses `Sketch.focusAt`, including a whole definition block at the root.
The control compares that answer with the premise of `focusAt_typed`.
The concept is `initial-algebras-folds`, requirement R14.
The existing consumers are the query's focus operation and the sketch's focus laws.
No new semantic theorem is proposed or proved.

A plain program supplies the positive control.
An admitted definition block supplies the challenged root answer.
An invalid address supplies the refusal control.
A slot after a definition invocation checks the remaining global-signature reader.
The slot check records an extension gap; the S1 plan does not expressly include that operation.
Root replacement by another block records the existing theorem's stated limit.

The checks are finite evaluations of the public query and library functions.
They establish no runtime, host, schedule, or full-module agreement.
The review changes only research files.
