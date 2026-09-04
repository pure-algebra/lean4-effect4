# Building `effect4d` with dune

`effect4d` is built by dune since 2026-09-04, from the workspace `ocaml/`
(`dune-project`, `dune-workspace`, `dune` there; `avatar/dune` and `server/dune` below it).
One `dune build` produces the three hosts from one module list. `build-server.sh` and
`tests/run-tests.sh` are the earlier shell build and stay for reference; nothing runs them.

## 1. One command, on either machine

```
ocaml/server/tools/dune-build.sh     # build: avatar + daemon, all three hosts
ocaml/server/tools/dune-test.sh      # build, then every test on every host reachable
```

Both enter the `effect4` opam switch (`opam env --switch=effect4`: OCaml 5.1.1, dune 3.24.2,
js_of_ocaml 5.7.1) and build into `ocaml/_build`. Plain `dune build` from anywhere
under `ocaml` does the same once the switch is active.

| artefact | dune's name | the README's name (a copy) | run it |
| --- | --- | --- | --- |
| bytecode | `_build/default/server/effect4d.bc` | `effect4d.byte` | `ocamlrun effect4d.byte` |
| native | `_build/default/server/effect4d.exe` | `effect4d.native` | `./effect4d.native` |
| js_of_ocaml `--enable effects` | `_build/default/server/effect4d_js.bc.js` | `effect4d.js` | `node effect4d.js`, `require("./effect4d.js")` |
| the library test | `_build/default/server/tests/lib_test.{bc,exe}` | | `dune build @server/runtest` |

Useful targets: `dune build avatar` (the avatar alone), `dune build server/effect4d.exe`,
`dune build @server/runtest` (builds and runs `tests/lib_test.ml` on both hosts).

- **macOS (the Mac, node on the PATH)**: the two scripts as above. `dune-test.sh` runs
  `tests/node_module_demo.mjs` and `tests/test_client.py` with `node`.
- **Windows (this machine)**: the same two scripts from WSL Ubuntu:
  `wsl -e bash /mnt/c/Users/kokok/Dev/lean4-effect4/ocaml/server/tools/dune-test.sh`.
  Node is not installed in WSL; the scripts find the Windows `node.exe` through interop
  (it is on WSL's PATH via the mise shims) and convert every path they hand it with
  `wslpath -w`. From PowerShell, the js host is `node <windows path>\_build\default\server\effect4d.js`
  fed on stdin — the node transport takes no flags. `W2_NODE=/path/to/node.exe` names the
  node when it is not on the PATH; `W2_HOSTS=bytecode,native` restricts the test client.

The avatar's own `avatar/build-dune.sh` still works: it passes `--root avatar` and builds
into its own directory. A bare `dune build` inside `avatar/` now resolves to the
`ocaml` root (that is what `dune-workspace` there does) and builds the avatar's
default alias into `ocaml/_build`. The root `dune` file's `(dirs avatar server gen)` is
what the workspace builds; `link/`, `eff/` and `probes/` are outside it, and their scripts
pass `--root .`, which is what keeps them their own roots.

## 2. What changed from `build-server.sh`

| before (`build-server.sh`) | now (`server/dune`) |
| --- | --- |
| copies `avatar/*.ml` into a build dir, reads the module list off `build-avatar.sh`'s `modules=` line | `(libraries effect4-avatar)`: the avatar's own library, compiled once by its own project and linked (§4) |
| one `ocamlc`/`ocamlopt` command each, `-I +unix unix.cma` | library `effect4d_lib` + executable `effect4d` `(modes byte exe) (libraries effect4d_lib unix)` |
| `ocamlc -no-check-prims` then `js_of_ocaml compile --enable effects --target-env=nodejs server_runtime.js` | executable `effect4d_js` `(modes js)` with `(js_of_ocaml (flags (--enable effects --target-env=nodejs)) (javascript_files server_runtime.js))`; dune's separate compilation builds the runtime, the stdlib and every library once per config (`_build/default/.js/effects=cps/`), so the effects setting reaches every unit |
| five python generators run by the script, including `corpus_data.ml` | `corpus_data.ml` is the avatar's own dune rule; the other four are rules in `server/dune` (§3) |
| `W2_AVATAR_REV=<rev>`: build the avatar half from a git revision, with a fallback to HEAD when the tree does not compile | gone. `workshop/` is git-ignored since Prod cleanup 4 (`.gitignore:7`), so no revision carries the avatar; the daemon is built against the working tree, and a tree that does not compile is a build error |
| default OCaml warnings, non-fatal | dune's dev warning set, non-fatal: `(flags (:standard -warn-error -a))` for the daemon, `-w -a` for the avatar copy as `avatar/dune` has it |
| `generator`/`regenerate` header rows name `build-server.sh` | they name `ocaml/server/dune` and `tools/dune-build.sh` |

Three daemon sources changed with the build:

- `e4d_snapshot.ml` and `effect4_daemon.ml` (`reachable`) follow the avatar's F2 checkpoint
  (`b133c99`) and the in-flight port: `pending.remaining` is the list of targets not yet
  visited (was a count; the snapshot now reports the list and `failFast`, `reachable` the
  count and the list), `answer` has `Aexits` and `Aprogram` (a closure: named, not shown),
  `RaceStarted` carries an entrant count and `RaceSkipped` is retired, a race reports its
  `programsPending`, and a completed Deferred holds a program rather than a `completion`
  value. The daemon had not been compiled against the avatar since `b60fe28`.
- `effect4_daemon.ml`'s replay scan compared event lists with polymorphic `=`; an
  `Aprogram` answer inside a `ResumedWith` event makes that raise `Invalid_argument
  "compare: functional value"` and killed the session (the first fiber program's `why`).
  The scan now compares rendered events, and any exception the handlers let escape is an
  `internal-error` reply rather than the end of the session (README §1).
- `tests/test_client.py` reads the goldens and the mask table from `server/generated/traces/`
  when `generated/traces/` is absent (`W2_TRACES` overrides), takes `W2_NODE`/`W2_JSOO` for
  the node host, and finds `ocamlrun` on the PATH when `OCAML5_BIN` is unset.

## 3. The generated modules

All four are `(rule ...)` stanzas in `server/dune`; python3 is required (WSL has
`/usr/bin/python3`; the Mac has its own). They regenerate on `dune build` when an input
changes — with two exceptions noted below. Nothing under `server/generated/` is generated
*by* the build: it holds vendored inputs (§3.1).

| module | generator | inputs |
| --- | --- | --- |
| `e4d_masks_data.ml` | `echo`/`cat` in the rule (no python) | `generated/traces/masks.tsv` (vendored), `../avatar/corpus/known-divergences.tsv` |
| `e4d_families_data.ml` | `tools/gen_families.py <fixture files>` | `generated/harness-trace/{fibers-fixture.stub,ref-fixture,deferred-fixture,scope-fixture,layer-fixture}.ts` (vendored) |
| `e4d_armmap.ml` | `tools/gen_armmap.py <lean dir> <avatar modules>` | the fourteen hand-written avatar modules, and `<repo>/src/Effect4/Machine/*.lean` |
| `e4d_pins.ml` | `tools/gen_pins.py --avatar … --server … --tools … --inputs … --lean …` | the same avatar modules, `programs.txt`, every daemon source and `dune`, the generators, the vendored inputs, the Lean modules; `%{ocaml_version}`, `node --version`, `js_of_ocaml --version` |

The two exceptions: the Lean modules live at `<repo>/src/Effect4/Machine/` — outside the
dune workspace, which dune cannot declare a dependency on — so the arm-map and pins rules
depend on `(universe)` instead. They re-run on every build (about a second) and read the
Lean files through `%{workspace_root}/../../../src/Effect4/Machine`; downstream
compilation re-runs only when their output changes. Citations resolve against all sixteen
Machine modules (`Effect4/Deep/*.lean` moved there in Prod cleanup 3), `Fibers.lean` first;
paths in the answers read `src/Effect4/Machine/….lean`.

The three `..` are not decoration. `%{workspace_root}` expands to the *build context* root
as the action sees it — from `_build/default/server` that is `./..`, i.e.
`<repo>/ocaml/_build/default` — so climbing out of it takes `_build/default` → `_build` →
`ocaml` → `<repo>`. The count encodes two facts: the workspace root is one directory below
the repo root, and a build context is two below the workspace root. When the estate moved
out of `workshop/OCaml5/` on 2026-09-04 the path was left one `..` short of the repo root
and both rules died with `FileNotFoundError: './../../src/Effect4/Machine'`; that is the
symptom to look for if either root moves again.

When the avatar's module list changes (`avatar/dune`, the library's `(modules ...)`), the
avatar deps of the arm-map and pins rules in `server/dune` must follow. A removed module
fails the build loudly; an added one is silently absent from the arm map until listed.
Nothing else has to follow: the daemon links the library rather than a copy of its modules
(§4), so the library's own `(modules ...)` is the only module list.

### 3.1 The vendored inputs (`server/generated/`)

`generated/traces/` (the mask table with the rc.112 pin, and the 25 goldens of `ref`,
`deferred`, `scope`, `layer`) and `harness/trace/*fixture*.ts` left main with the Flow route
in `75002d7` ("Prod cleanup 1"); they live on branch `archive/flow-route` at `606918e`.
`tools/vendor-archived-inputs.sh` copies exactly those 31 files, byte for byte, from that
revision into `server/generated/{traces,harness-trace}/` and records each blob in
`server/generated/archived-from.tsv`. The daemon's `masks`, `families` and `pins` answers
and the test client's `rows-vs-golden` checks read these copies; the header `input` rows
label them `ocaml/server/generated/…`.

## 4. The avatar is linked, not copied

`effect4d_lib` says `(libraries effect4-avatar)`. The avatar's library carries
`(public_name effect4-avatar)` (`avatar/dune`; the package is `avatar/effect4-avatar.opam`,
named by `avatar/dune-project`), and a public name is what makes a library visible outside
the dune project that defines it — `avatar/` is its own project, `server/` is in the root
project. Dune compiles the fifteen avatar modules once, into `_build/default/avatar/`, and
both the avatar's own executables and the daemon link that. The avatar's sources are read,
never written.

Until 2026-09-04 the library was private, so `(libraries effect4_avatar)` failed with
"Library effect4_avatar not found" and `server/dune` compiled the same fifteen modules a
second time from `copy_files#` copies, as a library `effect4_avatar_copy` — what
`build-server.sh` did with `cp`. Three edits retired that: `(public_name effect4-avatar)`
in `avatar/dune`, the `copy_files#` and `effect4_avatar_copy` stanzas deleted, and
`effect4d_lib`'s `(libraries effect4_avatar_copy)` → `(libraries effect4-avatar)`.

Measured after the change, on this machine (WSL Ubuntu, the `effect4` switch):
`dune build avatar server gen` from `ocaml/` exits 0; `ls _build/default/server/*.ml` shows
the sixteen daemon modules and no `deep_*.ml`, i.e. no avatar module is compiled under
`server/` any more; `tools/dune-test.sh` is unchanged at 14,677 checks, 0 failures; and the
arm map still resolves 62 `exact` / 48 `byLine` / 8 `unresolved` (§6).

## 5. What was exercised, and what was not

Exercised on this machine (WSL for the OCaml hosts, Windows node for the js host):

- `--version`, `--schema` and `--once '{"request":"run","source":"fixture","family":"ref","program":"makeGet"}'`
  on native and bytecode; the same three requests on stdin of the js host; the answers
  agree across the three hosts field for field except `host` (R1, `hosts-agree`).
- `dune build @server/runtest`: `tests/lib_test.ml` on bytecode and native (12 checks each).
- `tests/node_module_demo.mjs` with `node.exe` through WSL interop (12 checks): the module
  exports, `runProgram`, a forking/racing fiber program under a JS caller, `explain`,
  `step`, determinism across calls.
- `tests/test_client.py` on `bytecode,native,jsoo` in one invocation — every request type
  on the 25 vendored goldens, the committed avatar faces of `fiber` and `extra`, 20 corpus
  programs, the §0 properties, TCP on native, the batch session on node; the counts are in
  §6.

Not exercised, and why:

- `--tcp` on the bytecode host (the test client drives TCP on native only; same code).
- `W2_AVATAR_REV` builds from a git revision: no longer possible (§2).
- The estate's own gate (`avatar/compare.py` against `generated/traces`,
  `scripts/check-trace-host.sh`): the goldens are archived; the test client's own
  comparison against the vendored copies stands in.
- `why` against an rc.112 reference produced by `avatar/corpus_rc112.mjs`: needs the
  effect node_modules; the test client plants its own divergence instead.
- `--once`/`--version`/`--schema` flags on the js host: the node transport has none; the
  requests go on stdin (README §1), and that is what was run.

## 6. Results of the last run on this machine

2026-09-04, Windows 11, WSL Ubuntu, the `effect4` switch (OCaml 5.1.1, dune 3.24.2,
js_of_ocaml 5.7.1), Windows node v22.23.2 through interop — re-run unchanged after the
estate moved from `workshop/OCaml5/` to `ocaml/` and after §4's copy block was retired.
`wsl -e bash ocaml/server/tools/dune-test.sh`, 11 seconds end to end after a warm build:

```
=== the library surface, bytecode            PASS: 0 failures   (12 checks)
=== the library surface, native              PASS: 0 failures   (12 checks)
=== the js_of_ocaml build, required as a node module (node.exe)
                                             PASS: 0 failures   (12 checks)
=== the protocol, hosts: bytecode,native,jsoo
=== host bytecode (interactive)              60 programs, 1.2s
=== host native (interactive)                60 programs, 0.4s
=== host jsoo (interactive)                  60 programs, 2.2s
checks: 14677                                hosts-agree 60, tcp-ok 1, tcp-rows 1,
                                             batch-answers-every-request 1, batch-state-is-reset 1
PASS
```

14,677 is the count the daemon's own commit (`b60fe28`) reported for the shell build: the
same 60 programs on the same three hosts. The one-shot answers to `version`, `schema` and
the `ref.makeGet` run, taken separately on each host, agree field for field except `host`.

The count is worth reading, not just seeing pass. `tests/test_client.py` locates the
committed avatar faces by walking up from its own file, and the move left that walk one
directory too high: `corpus_faces` then found no directory, returned `[]`, and the suite
**passed** on 45 programs and 6,449 checks. The first run after the move reported exactly
that; the fix (`OCAML`/`REPO`/`AVATAR` at the head of the file) restored 60 and 14,677.
A silent drop in `checks:` is the signature of a face directory that has moved.

The arm map resolved against `src/Effect4/Machine/*.lean` (all sixteen modules) carries
62 `exact`, 48 `byLine` (unverified) and 8 `unresolved` citation tokens; README §7.8's
16/12/4 counted the avatar of `b60fe28` against `Effect4/Deep/*.lean` and is superseded by
what `explain` and `version` report.
