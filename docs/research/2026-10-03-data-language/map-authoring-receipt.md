# Map authoring receipt

The ordinary `Effect4.Api` import now includes the six string-map authoring functions.
These functions resolve names and reconstruct ordinary native atom applications.
They add no stored program representation or typing rule.

Base: `a595fd36` on `codex/data-language-wave`.
Files: `Program/Authoring/Maps.lean`, `Api.lean`, `Test/Api/MapAuthoring.lean`, `Test/All.lean` and the README example description.
The Test root includes the earlier map value, typing and raw-handle fixtures.

`LEAN_NUM_THREADS=3 lake build Effect4.Program.Authoring.Maps` passes.
`LEAN_NUM_THREADS=3 lake build Test.Api.MapAuthoring` passes; Lake reports 127 jobs.
The finite guards check normalized result typing, execution, optional presence, immutable update, key order and entry reconstruction.
The generated TypeScript print call also succeeds for the lookup example.
No new theorem or axiom premise is introduced.
These controls establish no general target execution or host-session property.

The map lookup fixture compares normalized types.
The checker retains the constructed union with the empty map's bottom value type before normalization.
This follows the distinction between raw type formation and canonical form.
