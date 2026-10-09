# Shared target packet failure retention

Base: `d45ee275540b96958518b9ac6b9b9ef5a320ff11`.
The coordinator authorizes a repair to `harness/ts_packet.py` and focused controls.
The shared dependency commits already belong to the integration branch.
Only the unique repair commits need integration.

## Contract

A helper discovery failure currently escapes before the packet's retention handler starts.
Move all temporary packet preparation into that handler's scope.
Retain every available named input exactly and record the original failure.
An early failure must not manufacture missing caller inputs or claim successful compilation.
Successful retention remains strict about every required input.
Occupied evidence directories and wrong installed versions remain refused.

## Scope and completion

Edit only the shared Python packet helper, its focused Python controls, and dedicated research notes.
Keep generated helpers, callers, package versions, TypeScript settings, and Lean declarations unchanged.
Use the real installed Bun runtime and pinned tsgo 7 compiler.
Check early helper failure, compiler refusal, partial preparation, strict success, and existing output/version refusals.
Run the Python controls, strict language checks, and the explicit-path whitespace check.
Commit the unique repair paths without a sweep or push.
