# Review of the parent recommendations

Reviewed snapshot: `recommendations-reviewed.md`, SHA256 `049665f968f6b4749d859a6b1e8cf68d59e96ab6ee3281f096d4c3368bcf8940`.
This is a source-based design review, not proof or implementation acceptance.

The central design is consistent with the source: one stored program, existing admission, distinct runtime projections and explicit proof applicability.
No new program IR or generic category framework is required.

Three clarifications keep the first slice precise:

1. Checked inspection has a route domain, not the synchronous `Looped` domain. Routing uses host operations and `catchIf`. The revised brief supports its effect routes alongside nested iterate. Only the rewrite remains restricted to `Looped`.
2. The first focus reports inferred local types and named parent constraints. It does not infer a unique expected `EffTy`. A branch contributes to a join; a loop step is below its cursor type. A wider cursor can admit several different step types.
3. Schema/profile selection is not a necessary input to the generic checker-owned focus. The exact program and signature, address and root-derived context determine it. A target explanation can add a named profile as a separate consumer. Do not make a new schema declaration a prerequisite for inspecting existing programs.

Two implementation boundaries also matter:

- The Routing repair follows decisions row 218's `ifCase` choice. An annotation on the printed arrow was explicitly rejected. The focus provides branch facts but does not itself close the printer, reader or target-typing obligations.
- `Api.Built` imports `Api`; a new companion importing Built cannot be imported back into `Api.lean`. Follow existing `Api.Author` placement at the `Effect4` root.

The runtime explanation remains correctly separate in the parent packet. Its source/capture/world premises are not supplied merely by this lexical focus.
No additional correction to that boundary is proposed here.
