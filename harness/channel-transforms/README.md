# Channel transformation packet

Run `python3 harness/channel-transforms/run.py --install <node_modules> --out <empty-directory>`.
The install holds Effect 4.0.1 and tsgo 7.0.0-dev.20260629.1.

The producer checks whole modules through `Api.Author.build` and emits them.
The existing reader refuses their handle request headers with `ReadRefusal.shape "definition"`.
The producer checks that exact refusal and records every unreadable header in the manifest.
This packet establishes no read-back result.
It compares finite machine observations with fixed numeric answers.
The runner typechecks those exact files and executes them with Effect 4.0.1.
The receipt retains inputs, commands, hashes, compiler diagnostics, and observed answers.

The cases cover whole-batch maps, completion maps, composition, retained state, and both Stream consumers.
The wrong batch control retains a sum of 10 instead of the mapped sum of 30.
The wrong completion callback leaves 42 instead of 43.

The profile uses explicit Chunk/End values and list-valued batches.
It assumes nonempty source and mapped batches.
It establishes no native Done-cause correspondence, asynchronous progress, or whole-stream target simulation.
The source pin is `vendor/effect-4.0.1/src/Channel.ts`.
The declarations cite `map`, `mapEffectSequential`, `mapDoneEffect`, and `transformPull` there.

The numeric producer explicitly ascribes both values of its boolean branch.
Without those ascriptions, the existing printer fails tsgo with `TS2375` on the differing answer variants.
Decisions row 218 assigns that repair to the shared `ifCase` printer.
The retained branch-refusal packet keeps the unannotated source, emitted declarations and compiler diagnostics.
