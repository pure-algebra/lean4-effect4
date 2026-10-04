# Public record authoring example

## Result

`Effect4.Api` now imports the existing generated composition builders.
An application can compose the new record builders through its ordinary API import.
Before this change, the example failed because `Authoring.bind` was not exposed by that import.

Base: `9746e85c` on `codex/data-language-wave`.
The commit containing this receipt supplies the resulting head.

## Changes and checks

`Test/Api/RecordAuthoring.lean` checks the README example through `Effect4.Api` alone.
It checks the optional answer type, an absent nickname, an updated required nickname and the unchanged original record.
The accepted examples also produce TypeScript syntax.
`Test/All.lean` imports the fixture.
`README.md` describes these operations and keeps the separate JSON and Schema codec work explicit.

`LEAN_NUM_THREADS=3 lake build Test.Api.RecordAuthoring` passes with 125 jobs.
The new README section passes the strict controlled-English check.
`git diff --check` passes.

These are finite application checks.
This slice adds no theorem or trust exemption.
It claims neither general target execution agreement nor JSON codec support.
