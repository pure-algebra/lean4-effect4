# The cut list, amended after review

Status: implementation proposal, not a report of removals.
Base: `774ddc3d784c0e0a04bd0d1e0bf6556c630074b2`.
The [review](codex-review.md) checks every row of [cuts-v1.md](cuts-v1.md).
The [survey](cuts-survey.md) retains its original evidence.
This list supplies the corrected scope, owner, and acceptance for each cut.

K0 runs beside semantic contract work.
Rows that need generated store rules land with their stated store slice.
Cleanup does not block the checking seam.
Never delete a proved owner before its replacement has a consumer and its connecting laws.

## The eighteen cuts

| Cut | Original target | Amended implementation | Owner | Acceptance |
| --- | --- | --- | --- | --- |
| K-01 | `Store.putOr` | Delete the unused wrapper. Keep the used `putRootOr`. | K0 | Search callers and build the affected store module and direct dependents. |
| K-02 | `Cascade.CascadingStore` | Delete the module, `Api` import and export, and both affected `SchemaGenerationContract` sections. Keep `Word.Layered` and `LocalFirst`. | K0 | No remaining caller or root import. Build API and the affected contract fixture. |
| K-03 | `Api.Author.buildIn` citation | Cite `Api.Author.build` in the `Module.types` docstring. | K0 | Check the declaration exists at the cited path. No code build follows a comment-only edit. |
| K-04 | Hash-injective `address_inj` | Replace its consumer with Lean `address_inj_resident`. Keep both own-address lookup premises and equal addresses. Update `NodeContract`, `ProgramContent` documentation, the Node header, and `E4-CAS-CE-006`. | K0, with coordinator-owned register text proposed in its receipt | The resident theorem needs neither global `Addressed` nor hash injectivity. Move the actual test reader, then narrow build and `#axiom_audit`. |
| K-05 | `Pin.holds_of_injective` | Delete the unused theorem and correct the header. Keep `holds_or_collision`. | K0 | Search actual consumers, build the touched law module, and audit it. |
| K-06 | `putNode_fresh_closed`, `verify_sound'` | Delete the unused aliases. | K0 | Search callers and build the touched law modules. |
| K-07 | `wf_closed` | Move the `WordContract` reader before deletion. Narrow G6 in `e4_cas.mli` to an empty start, or instantiate `wfFrom_apply` with the actual faithful closed prefix. The selected general contract uses the latter premises. | K0 | Keep `Word.wfFrom earlier w = true`, `Word.Faithful earlier`, and `Closed (Word.toStore earlier)`. `wf_apply` alone covers an empty start. |
| K-08 | Flat `Ty_` mirror rows | Repair `ocamlMatchArms` for standalone `function` and qualified constructor names. Then change keys to `Ty.t` and prefixes to `Ty.`. | K0 | Run M's current generated-file controls. Keep the two type-block census rows explicitly unresolved until the replacement reader supports them. Do not delete the gap from the census. |
| K-09 | `E4_nat` | Delete the obsolete module and only its N test cases. Replace remaining `max_nat` references with `max_int` where they test bounded big-endian host values. | K0 | Keep the unrelated big-endian tests. Update comments and dune ownership, then run affected math tests. |
| K-10 | `E4_log.Vec` | Move callers to `Lcnf_array` and remove the alias. | K0 | Build engine callers and run their existing behavioral tests. |
| K-11 | Duplicate `to_list` bodies | Keep `Lcnf_array.to_list` as the single owner. Use the temporary-array path only within host capacity, with the existing fold/reverse path beyond that bound. | K0 | Compare list values, integer and float allocations, and small/large sizes. Exercise the fallback using a test-injectable capacity threshold. Report allocated words, not a general speed claim. |
| K-12 | `bench_array.ml` | Delete it and its dune stanza entries. Keep `bench_frame.ml`. | K0 | `bench_frame` still measures the real writer. Check dune builds without the deleted executable. |
| K-13 | Hand engine `File.lean:N` citations | Replace line citations with declaration names and current paths. | K0 | Search remaining hand-written citations. Do not rewrite generated headers by hand or quote an unmeasured count. |
| K-14 | Three decode-refusal mappings | Generate one mapping from the Lean owner and use it in ordinary reads, import, and recovery. Report `Unknown_tag` explicitly. | ST1a producer, ST2 callers | Double-fault and recovery cases agree with the declared refusal order. No second mapping remains. |
| K-15 | Sealed-segment `Bad_pack` | Return a recovery fault value. Do not re-raise through `Store_error` or truncate committed/sealed content. | ST2 | A malformed sealed segment returns the named fault and leaves the evidence available. Active uncommitted-tail recovery remains distinct. |
| K-16 | WAL header | Fix its moved path and false `E4_log` consumer claim. Keep `E4_wal` for the run persistence consumer. | K0 | Check the named current declarations and intended consumer. |
| K-17 | Pre-move Store paths | Resolve each cited declaration to its current `Store/Carrier` or `Store/Domain` owner. Regenerate generated references through their producer. | K0 | Check names as well as paths. A blind prefix rewrite does not suffice. |
| K-18 | Array/list gap in `ocaml/gen/NOTES.md` | Delete the obsolete gap and correct the earlier Array-to-list description. | K0 | The note matches `Lcnf_array` and the generator's current mapping. |

## Source owners and limits

`Store.putOr` and `Store.putRootOr` live in `src/Effect4/Store/Domain/Store.lean`.
`wfFrom_apply` and `wf_apply` live in `src/Effect4/Store/Domain/Word.lean`.
Their test reader lives in `Test/Store/WordContract.lean`.
The general native closure claim lives in `ocaml/engine/cas/e4_cas.mli`.

`ocamlMatchArms` and its identifier reader live in `tools/Conform/Manifest/Readers.lean`.
The mirror rows live in `tools/Conform/Effect4/mirrors.json`.
`review-probes/SeamsMirrorControls.lean` demonstrates both parser defects against current generated files.

The vector owners are `ocaml/lcnf/lcnf_array.ml` and `ocaml/engine/e4_trace.ml`.
`review-probes/host-probes.log` records finite allocation measurements by carrier and size.
The temporary array reduces allocation for the measured large integer cases.
The measurements do not establish an improvement for every size or float carrier.
A flat-array capacity limit must not narrow the vector operation's domain silently.

`E4_cas`, `E4_wal`, `E4_checkpoint`, and `E4_chunk` remain for the named persistence consumers.
Keep `Registry` and `Pin` in the root-kind alignment work.
Removing unused Cascade does not authorize deleting `Word.Layered` or `LocalFirst`.
A later tier replacement needs its first real consumer and connector laws before caller migration and deletion.

`Tools.Session.Snapshot` moves only after the new replayed document serves its callers.
Delete it in the corresponding caller migration, not as an isolated early cut.
The [implementation plan](README.md) owns that sequence.

K0 receipts name changed paths, exact checks, and evidence limits.
The coordinator applies proposed register edits at the assigned anchors.
This document changes no production file and commits no removal.
