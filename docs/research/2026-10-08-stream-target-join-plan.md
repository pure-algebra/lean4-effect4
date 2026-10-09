# Array pull target join: module slice

Base: `7beadadc863b382a32c33014174256d94276c197`.

`arrayPull` joins two effects through a Boolean selection.
The ordinary target printer wraps that selection in `Effect.suspend`.
The target compiler chooses one success type and refuses the other branch.

Replace this join with one success containing the pure `ite` term.
Its two values are valid tagged pairs in either branch.
`ite` retains the condition and selected value without adding an effect or stored representation.

Keep `arrayBatch`, `arrayStep`, and their existing laws unchanged.
Use the existing machine controls for repeated pulls, empty input, independent opens, and outer binders.
Retain old and candidate emissions and pinned tsgo results before changing the module.

The separate two-item tuple distribution failure belongs to the shared helper and target type projection.
Keep that failure visible; this slice does not change its caller or printer.
The frozen Ref header refusal also remains.

Done means: narrow builds pass, the actual candidate pull compiles under pinned tsgo, and finite machine and target observations agree.
No new theorem is proposed.
