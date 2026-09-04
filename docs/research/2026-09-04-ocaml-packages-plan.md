# OCaml packages for the avatar, the daemon and the codegen: stop hand-rolling

Status: 2026-09-04, plan. The user's ruling: use the ecosystem, Jane Street's first. The
reification pins OCaml 5.1.1 and js_of_ocaml 5.7.1 because those are the modelled runtimes;
libraries above them change nothing the model is about, so they are free to use.

## 1. The switch

`opam switch effect4`, `ocaml-base-compiler.5.1.1`, js_of_ocaml pinned at 5.7.1 (the modelled
effects backend; 5.8/6.x change it). Installed set, first cut:

| Package | Why |
| --- | --- |
| `base`, `core`, `core_unix`, `stdio` | the standard library the avatar and daemon should have been written against: `Map`/`Set`/`Deque`/`Hashtbl` with comparators, `Or_error`, `Command` for CLIs |
| `ppx_jane` (= `ppx_sexp_conv`, `ppx_compare`, `ppx_hash`, `ppx_fields_conv`, `ppx_variants_conv`, `ppx_enumerate`, `ppx_let`, `ppx_here`, …) | `[@@deriving sexp, compare, equal, hash, fields, variants]` on every generated carrier: serialisation, equality and hashing for free; **`Fields.iter`/`Fields.fold` is the mechanical field-by-field walk the RunFiber ↔ avatar relation needs**; `Variants.to_rank` gives constructor order for the ports' diff |
| `ppx_expect`, `ppx_inline_test`, `expect_test_helpers_core` | expect tests are inline golden tests: every witness, corpus row list and daemon reply becomes an `[%expect]` block that `dune runtest` checks and `dune promote` updates; replaces compare.py and the ad-hoc row files |
| `sexplib`, `bin_prot` | the daemon's wire: sexps for humans and the JSON-lines schema, bin_prot for the fast path; both derived from the same carriers, nothing hand-copied |
| `fieldslib`, `variantslib` | the runtime side of the ppx above, used directly by the relation checker |
| `ppxlib` | Jane Street's ppx framework and the OCaml AST as a library: parse and typecheck Lean-generated OCaml (`Ppxlib.Parse`, `Pprintast`, and `compiler-libs` `Typemod` behind it) so `OCaml5.Ml.Check` has a real oracle, and `Ast_builder` if generation ever moves to the OCaml side |
| `js_of_ocaml-compiler` 5.7.1, `js_of_ocaml`, `js_of_ocaml-ppx` | the modelled backend, installed rather than vendored; `Js_of_ocaml.Js` bindings and the `[%js]` ppx for the daemon's JavaScript face and the Promise bridge (P6 hand-declared externals) |
| `eio`, `eio_main` | the community's effects-based structured concurrency: `Switch` is a scope, `Promise` is a Deferred, `Fiber.fork`/`first`/`any` are fork and race; a reference implementation to compare the avatar's semantics against, and the daemon's server loop (native only: no jsoo backend) |
| `picos`, `picos_std`, `picos_io` | the effects-based scheduler *interface* (one-shot continuations, triggers, computations with cancellation, `Ivar`): the substrate the avatar's park/resume/interrupt could sit on instead of raw `Effect.Deep`, keeping the rc.112 scheduling policy in the avatar's own dispatcher |
| `yojson` | already there; the JSON-lines schema until bin_prot/sexp take over |
| `ocamlformat` | canonical formatting so "byte-identical to the generated module" is a formatting-invariant comparison |

Second cut, when wanted: `bonsai` + `virtual_dom` + `async_js` (Jane Street's web UI on jsoo: an
Effect program explorer that shows a run's fibers, dispatcher, observers and rows live, driven
by the daemon's `step`/`explain`), `incremental`, `core_bench`, `ocaml-lsp` for the daemon's
editor face.

## 2. How each lane uses it

- **W1, the port.** Carriers get `[@@deriving sexp, compare, equal, fields, variants]` from
  the generator; the relation to Deep is a `Fields.fold` over `run_fiber`; witnesses and corpus
  expectations become `%expect` tests; `Core.Map`/`Deque` replace the hand-rolled tables and
  buckets (the dispatcher's FIFO buckets are a `Map` keyed by priority of `Deque`s).
- **W2, the daemon.** `Command` for the CLI, `Eio` for the native server loop, sexp/bin_prot
  wire derived from the carriers, `Js_of_ocaml` for the node face; every reply type derives
  its schema.
- **W3, the codegen API.** `OCaml5.Ml.Check` gains an executable oracle: the rendered module is
  parsed with `ppxlib`/`compiler-libs` and typechecked, diagnostics fed back; `ocamlformat` is
  the canonical printer the Lean renderer is compared against, so layout choices stop mattering.
- **The Lean side** is unchanged: it renders the same OCaml text, now with deriving attributes
  (`Ml.Syntax` already has attributes) and against Base's names.

## 3. Rules

Pin versions in a `dune-project`/`.opam` file under the avatar; the switch is reproducible from
it. The 4.14.2 switch and the vendored jsoo build in `effect4_of_ocaml/_build` stay untouched
for the old receipts. Nothing modelled changes: `Effect.Deep` is still what Picos/Eio bottom out
in, and the Lean machine is still OCaml 5.1.1's runtime.

## 4. Ruling: representability first (user, 2026-09-04)

Everything we write in OCaml, data structures, streaming, web API, type modelling, has to be
**directly representable, functionally, in the Lean model**. That is the selection rule for
packages and for style, above convenience:

1. **Syntax.** Every construct used has a spelling in `OCaml5.Ml.Syntax` and renders from it;
   `OCaml5.Ml.Check` carries a **profile** (an allowlist of constructs and of library modules
   with their signatures as data) and rejects code outside it. Generated and hand-written OCaml
   both pass the checker before they are built.
2. **Semantics.** Every library construct whose behaviour we claim has a Lean carrier with laws:
   `Base.Map`/`Set` as finite maps with the lemmas we use; `Deque` as the dispatcher bucket
   carrier; `Sexp` as `Ml.Sexp` with a total round trip; `Eio.Switch`/`Promise`/`Fiber` and
   `Picos` computations against the OCaml5 machine (they bottom out in `Effect.Deep`, which is
   already modelled); streaming as explicit pull/push carriers matching `Effect4/Channel`'s
   shapes; the web face as a service alphabet at the host boundary, modelled the way TRACE-DAG
   treats the host, never as semantics. What has no carrier is a refusal row, not a dependency.
3. **Types both ways.** `OCaml5.Ml.Reflect` maps Lean structures/inductives to OCaml types *and*
   OCaml library types (as description data extracted from `.mli`/`cmi` through ppxlib) back to
   Lean descriptions, so a library's types can be talked about in Lean before its values are
   used.
4. **No magic.** No `Obj`, no `Marshal`, no polymorphic comparison on abstract types, no
   functors beyond what `Ml.Syntax` spells; ppx-generated code is admitted only as the plain
   OCaml it expands to (`ppx_jane`'s derivers expand to first-order functions over the carrier;
   the profile lists them with the laws we rely on: `compare` total order, `sexp_of`/`of_sexp`
   round trip, `Fields.fold` visiting every field once in declaration order).

The consequence for the port: prefer Base/Core structures with obvious Lean counterparts,
write the daemon and the streaming layer as plain functions over derived carriers, and treat
every package as a modelling obligation before it is a convenience.
