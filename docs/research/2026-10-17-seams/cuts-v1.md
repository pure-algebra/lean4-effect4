# The cut list, ruled (2026-10-17)

Status: plan (history, not authority). The survey is `cuts-survey.md` beside this note, checked
against `774ddc3d7`. Slice K0 of `README.md` §9 lands every row ruled "now"; the other rows land
with the slice that replaces them, named in the survey.

## Cut now (slice K0)

| Area | Cut | Change |
| --- | --- | --- |
| Lean core | `Store.putOr` | delete; its docstring's claim of three users is false |
| Lean core | `Cascade.CascadingStore`, its `export` in `src/Effect4/Api.lean`, its test section | delete; `Word.Layered` and `LocalFirst` stay the proved two-tier owner until the tiered store of `README.md` §7 |
| Lean core | the `Api.Author.buildIn` citation in `Module.types`'s docstring | cite `Api.Author.build` |
| Lean laws | `address_inj`, whose premise is an injective SHA-256 | replace with the Lean theorem `address_inj_resident` (decisions row 411 (1): a statement Lean proves in a few lines is a theorem, not a declared fact); drop its `example`; fix the module doc and `E4-CAS-CE-006`'s text |
| Lean laws | `Pin.holds_of_injective` | delete; `holds_or_collision` stays |
| Lean laws | the aliases `putNode_fresh_closed` and `verify_sound'` | delete |
| Lean laws | `wf_closed`, a weaker `wf_apply` | delete; `e4_cas.mli` cites `wf_apply` |
| tools | `tools/Conform/Effect4/mirrors.json` rows on the flat `Ty_` shape | re-key to `Ty.t` and `Ty.`; drop the two type-block rows |
| OCaml engine | `E4_nat` and `test_math.ml`'s N cases | delete; comments say `max_int` |
| OCaml engine | `E4_log.Vec` | callers name `Lcnf_array` |
| OCaml engine | `E4_trace.to_list` beside `Lcnf_array.to_list` | the faster body moves into `Lcnf_array.to_list`; words allocated compared before and after |
| OCaml engine | `ocaml/engine/bench/bench_array.ml` | delete; D-3 is settled |
| OCaml engine | Lean `File.lean:N` citations in hand engine headers (about 360) | cite declarations by name and path |
| OCaml store | the decode-refusal mapping written three times in `e4_cas.ml` | one function; recovery reports `Unknown_tag` |
| OCaml store | `Bad_pack` raised by recovery inside a sealed segment | a value of the recovery result |
| OCaml store | `e4_wal.mli`'s stale path and its false "feeds `E4_log`" | fix the header; the module stays for run nodes |
| OCaml store | pre-move `src/Effect4/Store/*.lean` paths in about 40 files | rewrite to `Store/Carrier/*` and `Store/Domain/*` |
| docs | the `ocaml/gen/NOTES.md` row on `Array` as a list | delete |

## Ruled on the survey's unsure rows

| Row | Ruling | Reason |
| --- | --- | --- |
| `CascadingStore` | cut now | no generated or TypeScript use (grep of `ts/`, `ocaml/`); one test; the proved owner stays |
| `address_inj`'s replacement | a Lean theorem | decisions row 411 (1) |
| `wf_closed` | cut now | one citation to move |
| `bench_frame.ml` | keep | its second part measures the real writer |
| `Tools.Session.Snapshot` | cut with S1 | `Doc`'s replay-proved cache replaces it |
| `E4_trace.to_list` | cut now, measured | words allocated are deterministic here; CPU time is not |

## Kept on purpose

`E4_cas`, `E4_wal`, `E4_checkpoint`, `E4_chunk` and OCaml's root kinds `Registry` and `Pin` have no
consumer outside their tests today. They stay: the action cache, the document history and the run
nodes of `README.md` §5.4 are their consumers.
