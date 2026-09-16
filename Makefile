# The one entry point. `make help` lists the targets.
#
# Four kinds of target:
#   build*   Lake builds; the axiom audit runs inside `lake build Test`.
#   corpus   the printed corpus, a build artifact under .lake/corpus that three checks
#            read (the TypeScript reader, the ingest smoke, the OCaml engine differential).
#   gen-*    the generated files, one rule per group, in the dependency order the
#            producers need. A rule fires when its generator, its inputs, or the
#            compiled core it reads changed; its marker is .lake/gen/<group>.
#   check-*  the checks. `check` is the tier that runs after every change;
#            `check-host` adds the outside oracles (the real Effect runtime, the
#            TypeScript compiler, the OCaml engine); `check-full` is everything.
#            A check that names its inputs is a marker rule too (.lake/check/<name>)
#            and is skipped while nothing it reads has changed; `make -B <target>`
#            or `make clean-check` forces it. CI starts from a fresh clone, so it
#            has no markers and runs everything.
#
# Staleness is judged by GNU make from file times: a rule's prerequisites are the
# generator's or checker's sources plus the Lake trace of the compiled root it reads
# (Lake rewrites a module's .trace whenever that module or anything it imports
# changes). Drift of a committed generated file is `make check-gen`: regenerate the
# stale groups, then `git diff --exit-code` over every generated path.
#
# One Lean process at a time (.NOTPARALLEL), and one `make` at a time: the scripts no
# longer take a lock file, this file is the lane. Checks that need no Lean can be run
# in parallel from a second shell; a parallel lane is a later step.
#
# The scripts under scripts/ are the checks and producers that are programs in their
# own right; a step that is one to five commands is written here, not wrapped.

SHELL := /bin/bash
LAKE ?= lake
BUN ?= bun
PY ?= python3
OPAM_SWITCH ?= effect4
OCAML ?= opam exec --switch=$(OPAM_SWITCH) --
GEN := .lake/gen
CHK := .lake/check
export LEAN_NUM_THREADS ?= 3
.DEFAULT_GOAL := help
.NOTPARALLEL:

# Lake's trace of the whole core (src/Effect4.lean imports every core module) and of
# the proof graph. A change anywhere beneath either rewrites the file.
CORE := .lake/build/lib/lean/Effect4.trace
LAWS := .lake/build/lib/lean/Effect4/Laws.trace
TRACE := .lake/build/lib/lean/Effect4
LEAN_SOURCES := $(shell find src Test -name '*.lean')
TS_EFF_SOURCES := $(wildcard ts/eff/*.ts ts/eff/test/*.ts ts/eff/ingest/*.ts ts/eff/ingest/test/*.ts) ts/eff/package.json ts/eff/bun.lock ts/eff/tsconfig.json
VENDOR_SOURCES := $(wildcard vendor/effect-4.0.0-rc.112/src/*.ts vendor/effect-4.0.0-rc.112/src/internal/*.ts)

# ---------------------------------------------------------------------------- build

.PHONY: build build-tools
build: ## lake build: the core, the proof graph, the batteries and the axiom audit
	$(LAKE) build

build-tools: build ## the generator and checker roots (Tools, OCaml5, Conform, Effect4Gen)
	$(LAKE) build Tools OCaml5 Conform Effect4Gen

# ---------------------------------------------------------------------------- gen
#
# The order below is the producers' dependency order: derived writes Lean modules the
# rest import; eff cuts the OCaml files and the engine structure that reads them; ts cuts
# the TypeScript tables the ingest README renders. Each marker depends on the previous
# one, so a regenerated upstream group re-cuts everything downstream of it.

DERIVED_SOURCES := $(wildcard tools/Effect4Gen/*.lean tools/Effect4Gen/guards/*.lean) tools/Effect4Gen/manifest.json tools/Effect4Gen/binders.json
DERIVED_TRACES := $(addprefix $(TRACE)/,Store/Canonical.trace Program/Native.trace Store/RowCanonical.trace \
  Store/Pin.trace Store/Node.trace Api/Frontier.trace Program/Eff.trace Program/Ty.trace Program/Refs.trace \
  Program/Authoring.trace)
DERIVED_OUT := src/Effect4/Store/Derived/Json.lean src/Effect4/Store/Derived/Schema.lean \
  src/Effect4/Program/Derived.lean src/Effect4/Store/PinDerived.lean src/Effect4/Api/Derived.lean \
  src/Effect4/Program/Fold.lean src/Effect4/Program/Binders.lean src/Effect4/Program/Authoring/Lifts.lean

$(GEN)/derived: $(DERIVED_SOURCES) $(DERIVED_TRACES) | build
	$(PY) scripts/generate.py --only derived
	@mkdir -p $(GEN) && touch $@

$(GEN)/specs: $(GEN)/derived tools/Conform/Cli/EmitSpecs.lean tools/Conform/Effect4/specs.json $(TRACE)/Program/Typing.trace
	$(PY) scripts/generate.py --only specs
	@mkdir -p $(GEN) && touch $@

EFF_SOURCES := src/OCaml5/Tools/EffGen.lean $(wildcard src/OCaml5/Eff/*.lean) \
  scripts/generate-engine-structure.py scripts/lib/program_structure.py ocaml/engine/api_engine.ml
$(GEN)/eff: $(GEN)/specs $(EFF_SOURCES) $(CORE)
	$(PY) scripts/generate.py --only eff
	@mkdir -p $(GEN) && touch $@

$(GEN)/wire: $(GEN)/eff src/OCaml5/Tools/EffWire.lean $(CORE)
	$(PY) scripts/generate.py --only wire
	@mkdir -p $(GEN) && touch $@

$(GEN)/cas: $(GEN)/wire src/OCaml5/Tools/CasGoldens.lean $(CORE)
	$(PY) scripts/generate.py --only cas
	@mkdir -p $(GEN) && touch $@

TS_SOURCES := $(wildcard tools/Tools/*.lean) src/Effect4/Codegen/Print.lean lakefile.toml \
  vendor/effect-4.0.0-rc.112/src/unstable/sql/SqlClient.ts vendor/effect-4.0.0-rc.112/src/unstable/sql/Statement.ts \
  vendor/effect-4.0.0-rc.112/src/unstable/persistence/KeyValueStore.ts
$(GEN)/ts: $(GEN)/cas $(TS_SOURCES) $(CORE)
	$(PY) scripts/generate.py --only ts
	@mkdir -p $(GEN) && touch $@

$(GEN)/readme: $(GEN)/ts ts/eff/ingest/render-readme.ts ts/eff/profile.gen.ts ts/eff/forms.gen.ts ts/eff/taxonomy.gen.ts
	$(PY) scripts/generate.py --only readme
	@mkdir -p $(GEN) && touch $@

# The four LCNF outputs (each header carries its own regenerating command).
LCNF_SOURCES := src/OCaml5/Tools/LcnfGen.lean $(wildcard src/OCaml5/Lcnf/*.lean) \
  ocaml/engine/externs.txt ocaml/engine/tools/api_engine_prelude.ml
$(GEN)/lcnf: $(GEN)/readme $(LCNF_SOURCES) $(CORE)
	$(PY) scripts/generate.py --only lcnf
	@mkdir -p $(GEN) && touch $@

# The truth harness: Lean writes the corpus from the committed tapes, then the real
# runtime prints the modules, re-records the tapes and writes the result. Both are
# deterministic given the pinned host; the comparison against a fresh run is check-truth.
TRUTH_SOURCES := harness/truth/Truth.lean harness/truth/prelude.ts harness/truth/run-truth.ts \
  $(wildcard harness/truth/tapes/*.jsonl) ts/eff/package.json ts/eff/bun.lock
$(GEN)/truth: $(GEN)/lcnf $(TRUTH_SOURCES) $(CORE) $(LAWS)
	$(LAKE) env lean -M4096 --run harness/truth/Truth.lean harness/truth/corpus.json --tapes harness/truth/tapes
	$(BUN) run harness/truth/run-truth.ts --manifest harness/truth/corpus.json --out harness/truth --timeout 300 --tape-out harness/truth/tapes
	@mkdir -p $(GEN) && touch $@

$(GEN)/host-protocol: $(GEN)/truth tools/Tools/HostProtocol.lean $(TRACE)/Api/HostSession.trace
	$(LAKE) build Effect4.Api.HostSession
	$(LAKE) env lean -M4096 --run tools/Tools/HostProtocol.lean harness/truth/session
	@mkdir -p $(GEN) && touch $@

SCHEMA_TS_DIR := harness/schema-generation
$(GEN)/schema-ts: $(GEN)/host-protocol $(wildcard $(SCHEMA_TS_DIR)/Emit*.lean) $(TRACE)/Codegen/Schema.trace
	$(LAKE) env lean -M4096 $(SCHEMA_TS_DIR)/EmitFixture.lean > $(SCHEMA_TS_DIR)/Person.generated.ts
	$(LAKE) env lean -M4096 $(SCHEMA_TS_DIR)/EmitCoverageFixture.lean > $(SCHEMA_TS_DIR)/AllRepresentations.generated.ts
	$(LAKE) env lean -M4096 $(SCHEMA_TS_DIR)/EmitMultiFixture.lean > $(SCHEMA_TS_DIR)/TwoRoots.generated.ts
	@mkdir -p $(GEN) && touch $@

# The runtime behaviour census is cut from the vendored rc.112 sources; its producer
# prints the table.
generated/effect-runtime-census.tsv: scripts/generate-effect-runtime-census.sh $(VENDOR_SOURCES)
	bash scripts/generate-effect-runtime-census.sh > $@
$(GEN)/census: $(GEN)/schema-ts generated/effect-runtime-census.tsv
	@mkdir -p $(GEN) && touch $@

# The groups generate.py can regenerate into a temporary directory (no host runtime).
HERMETIC_GROUPS := derived specs eff wire cas ts readme
GEN_GROUPS := $(HERMETIC_GROUPS) lcnf truth host-protocol schema-ts census

.PHONY: gen gen-hermetic $(addprefix gen-,$(GEN_GROUPS)) clean-gen
gen: $(addprefix $(GEN)/,$(GEN_GROUPS)) ## regenerate every stale generated group, in order
gen-hermetic: $(addprefix $(GEN)/,$(HERMETIC_GROUPS)) ## the Lean-only groups (no host runtime)
# one group: make gen-eff, make gen-truth, ...
$(addprefix gen-,$(GEN_GROUPS)): gen-%: $(GEN)/%
clean-gen: ## forget the generation markers (the next `make gen` re-cuts everything)
	rm -rf $(GEN)

# Every committed path a generator writes. The drift check diffs exactly these.
GENERATED_PATHS := $(DERIVED_OUT) src/Effect4/Laws/Program/Typing/Specs.lean \
  ocaml/eff ocaml/goldens/eff ocaml/engine/cas/goldens ocaml/engine/e4_program_layout.ml \
  ocaml/engine/e4_program_layout.json \
  ocaml/gen/api_gen.ml ocaml/gen/fibers_gen.ml ocaml/gen/machine_gen.ml ocaml/engine/api_engine.ml \
  ts/eff/eff.gen.ts ts/eff/json.gen.ts ts/eff/profile.gen.ts ts/eff/taxonomy.gen.ts ts/eff/forms.gen.ts \
  ts/eff/wire.gen.ts ts/eff/packages.gen.ts ts/eff/ingest/README.md \
  harness/truth/corpus.json harness/truth/generated harness/truth/result.json harness/truth/result.md \
  harness/truth/tapes harness/truth/session/protocol.gen.ts harness/truth/session/tape.schema.json \
  $(SCHEMA_TS_DIR)/Person.generated.ts $(SCHEMA_TS_DIR)/AllRepresentations.generated.ts $(SCHEMA_TS_DIR)/TwoRoots.generated.ts \
  generated/effect-runtime-census.tsv generated/corpus-index.tsv

# ---------------------------------------------------------------------------- corpus
#
# The printed corpus: 400 programs of Lean's seeded generator (Test/Program/Gen.lean) and
# the wire corpus, printed by tools/Tools/Corpus.lean as TypeScript beside the JSON and
# the canonical bytes of the program Lean's own reader kept, with Lean's typing verdict
# per program in index.tsv. A build artifact, not committed. It is re-cut when Lake's
# trace of Tools.Corpus changes, which Lake rewrites when the generator, the printer, the
# wire or the tool itself changes; the `lake build` that refreshes the trace is a no-op
# otherwise. The OCaml engine differential reads the directory through E4_LEAN_CORPUS.
# The index (one row per program: name, wellTyped, readable, chars) is also installed as
# generated/corpus-index.tsv, the committed expected file that names every program whose
# verdict a change moved (DI-60); check-gen holds it.

CORPUS := .lake/corpus
CORPUS_TRACE := .lake/build/lib/lean/Tools/Corpus.trace
export E4_LEAN_CORPUS := $(abspath $(CORPUS))
export EFFECT4_CORPUS := $(abspath $(CORPUS))

$(CORPUS_TRACE): $(LEAN_SOURCES) $(wildcard tools/Tools/*.lean) | build
	$(LAKE) build Tools.Corpus

$(CORPUS)/index.tsv: $(CORPUS_TRACE)
	rm -rf $(CORPUS) && mkdir -p $(CORPUS)
	$(LAKE) env lean -M4096 --run tools/Tools/Corpus.lean $(CORPUS) 400 4
	{ printf '# GENERATED by make corpus (tools/Tools/Corpus.lean over Test/Program/Gen.lean and the wire corpus); do not edit\n# name\twellTyped\treadable\tchars\n'; cat $(CORPUS)/index.tsv; } > generated/corpus-index.tsv

.PHONY: corpus
corpus: $(CORPUS)/index.tsv ## the printed corpus under .lake/corpus (Lean's 400 programs and the wire corpus)

# The pinned TypeScript install the reader, the ingest and the truth harness run on.
ts/eff/node_modules: ts/eff/package.json ts/eff/bun.lock
	cd ts/eff && $(BUN) install --frozen-lockfile
	@touch $@

# The truth harness and the schema codec resolve Effect and the compiler through
# harness/truth/node_modules, a link to that install (never a second install: the truth
# runner refuses a link that selects a different one).
harness/truth/node_modules: | ts/eff/node_modules
	ln -s ../../ts/eff/node_modules $@

.PHONY: doctor
doctor: ## the tools and installs every tier needs, with their versions
	@printf 'lean       %s\n' "$$(lean --version 2>&1 | head -1)"
	@printf 'lake       %s\n' "$$(lake --version 2>&1 | head -1)"
	@printf 'python3    %s\n' "$$(python3 --version 2>&1)"
	@printf 'bun        %s\n' "$$(bun --version 2>&1 || echo missing)"
	@printf 'node       %s\n' "$$(node --version 2>&1 || echo missing)"
	@printf 'opam       %s\n' "$$(opam --version 2>&1 || echo missing)"
	@printf 'dune       %s\n' "$$($(OCAML) dune --version 2>&1 || echo 'missing (the OCaml lane needs the effect4 switch)')"
	@printf 'ts/eff     %s\n' "$$(test -d ts/eff/node_modules/effect && echo 'installed (effect, @effect/sql-sqlite-bun, oxc-parser)' || echo 'missing: bun install --frozen-lockfile --cwd ts/eff')"
	@printf 'truth link %s\n' "$$(test -e harness/truth/node_modules && echo 'present' || echo 'missing: make harness/truth/node_modules')"
	@printf 'schema-host %s\n' "$$(test -d harness/schema-host/node_modules/effect && echo 'installed (typescript 7.0.2, tsgo)' || echo 'missing: npm ci --prefix harness/schema-host (check-schema-ts, check-schema-host)')"

# ---------------------------------------------------------------------------- checks

CHECKS := roots citations cases native ts-reader truth target schema-codec ocaml ingest ingest-smoke \
  host-protocol census schema-ts schema-pins schema-host compat tools corpus
.PHONY: check check-host check-full check-gen check-gen-full clean-check FORCE $(addprefix check-,$(CHECKS))
FORCE:

check: build check-roots check-gen check-cases check-native check-ts-reader ## after every change
check-host: check check-citations check-truth check-corpus check-target check-schema-codec check-ocaml check-ingest-smoke ## per slice: the outside oracles and the citation scans
check-full: check-host check-tools check-gen-full check-ingest check-host-protocol check-census check-schema-ts check-schema-pins check-schema-host ## everything

# Drift: regenerate the stale Lean-only groups, then refuse any change to a committed
# generated file. `check-gen-full` re-cuts every group, the host-cut ones included,
# without trusting file times.
define refuse_drift
	git diff --exit-code --stat -- $(GENERATED_PATHS)
	@untracked="$$(git status --porcelain -- $(GENERATED_PATHS) | grep '^??' || true)"; \
	  if [ -n "$$untracked" ]; then echo "FAIL check-gen: untracked generated files:"; echo "$$untracked"; exit 1; fi
endef

check-gen: gen-hermetic $(CORPUS)/index.tsv ## regenerate the stale Lean-only groups and the corpus index; refuse a changed committed file
	$(refuse_drift)
	@echo 'PASS check-gen: every Lean-only generated file is what its generator emits'

check-gen-full: ## regenerate every group from scratch (host runtime included) and refuse a changed committed file
	$(MAKE) -B gen
	$(refuse_drift)
	@echo 'PASS check-gen: every generated file is what its generator emits'

# one check: make check-roots, make check-truth, ...
$(addprefix check-,$(CHECKS)): check-%: $(CHK)/%
clean-check: ## forget the check markers (the next `make check` runs every check)
	rm -rf $(CHK)

# A fresh elaboration of Test/All.lean sees a new orphan source file even when Lake's
# roots are cached; the compiled import graph and the source inventory are AxiomGate's.
# The audit itself already runs inside `lake build` (Test.All re-elaborates whenever a
# module it imports changed), so the fresh elaboration is keyed on the source inventory:
# it re-runs when a file is added, removed or renamed, not on every edit.
$(CHK)/inventory: FORCE
	@mkdir -p $(CHK); printf '%s\n' $(sort $(LEAN_SOURCES)) > $@.new; \
	  if cmp -s $@.new $@; then rm -f $@.new; else mv $@.new $@; fi
$(CHK)/roots: $(CHK)/inventory lakefile.toml lean-toolchain | build
	$(LAKE) env lean Test/All.lean
	@echo 'PASS library-roots: fresh module, root-closure and axiom audit'
	@mkdir -p $(CHK) && touch $@

CONFORM_SOURCES := $(shell find tools/Conform -name '*.lean' -o -name '*.json') scripts/check-conform.py scripts/lib/conform_report.py
$(CHK)/cases: $(CORE) $(CONFORM_SOURCES)
	$(PY) scripts/check-conform.py cases
	@mkdir -p $(CHK) && touch $@

$(CHK)/native: $(CORE) $(CONFORM_SOURCES)
	$(PY) scripts/check-conform.py native
	@mkdir -p $(CHK) && touch $@

# The two citation scans read every text file of the nine trees both scripts name, with
# `vendor`, `node_modules`, `_copy`, `research`, `_build` and `.lake` pruned as the scripts
# prune them; the marker names those files, so the scans run when one of them changes and
# not otherwise. Every cited path exists; no line-numbered citation into a mutable document.
CITATION_TREES := src Test tools ocaml ts docs scripts harness generated
CITATION_SOURCES := $(shell find $(CITATION_TREES) \( -type d \( -name vendor -o -name node_modules -o -name _copy -o -name research -o -name _build -o -name .lake \) -prune \) -o -type f -print)
$(CHK)/citations: scripts/check-source-citations.py scripts/check-internal-citations.sh scripts/source-citations-allowed.txt $(CITATION_SOURCES)
	$(PY) scripts/check-source-citations.py
	bash scripts/check-internal-citations.sh
	@mkdir -p $(CHK) && touch $@

# The TypeScript reader against Lean's reader: every `.ts` of the corpus and of the truth
# lane's exported modules must read back to the JSON Lean's own reader kept (`--oracle`),
# then the package's type check and its pinned cases.
TRUTH_GENERATED := harness/truth/corpus.json harness/truth/result.json harness/truth/result.md $(wildcard harness/truth/generated/*.ts)
$(CHK)/ts-reader: $(CORPUS)/index.tsv ts/eff/node_modules $(TS_EFF_SOURCES) $(TRUTH_GENERATED) harness/truth/prelude.ts
	cd ts/eff && $(BUN) run check.ts $(abspath $(CORPUS)) $(abspath harness/truth/generated) --oracle $(abspath $(CORPUS))
	cd ts/eff && $(BUN) run typecheck
	cd ts/eff && $(BUN) test
	@mkdir -p $(CHK) && touch $@

$(CHK)/truth: $(CORE) $(LAWS) $(TRUTH_SOURCES) $(TRUTH_GENERATED) $(wildcard harness/truth/session/*.ts) scripts/check-truth.py | harness/truth/node_modules
	$(PY) scripts/check-truth.py
	@mkdir -p $(CHK) && touch $@

# The corpus lane: every program of the generated corpus (Test/Program/Gen.lean, 400 at
# depth 4) printed and type-checked, the admitted ones run on rc.112, its rc.112 exit,
# schedule and sync exit compared with the machine's and its inferred tsc type with Lean's,
# one row per program in harness/truth/corpus-results.tsv (the committed expected file;
# `make gen-corpus-results` promotes a fresh run; harness/truth/corpus-known-differences.md
# registers each disagreement by program, dimension and outcome). The work directory is
# harness/truth/corpus-check (ignored), beside the prelude and session sources the modules
# import; everything the lane reads is a prerequisite.
CORPUS_LANE := scripts/check-corpus.py scripts/lib/truth_host.py tools/target/corpus.ts tools/target/oracle.ts tools/target/profile.ts \
  harness/truth/corpus-results.tsv harness/truth/corpus-known-differences.md Test/fixtures/target/selection.json \
  harness/truth/tsconfig.json harness/truth/prelude-inventory.ts $(wildcard harness/truth/session/*.ts) \
  ts/eff/profile.gen.ts ts/eff/eff.gen.ts ts/eff/packages.gen.ts ts/eff/tsconfig.json
$(CHK)/corpus: $(CORE) $(LAWS) .lake/build/lib/lean/Test/Program/Gen.trace $(TRUTH_SOURCES) $(CORPUS_LANE) ts/eff/node_modules | build harness/truth/node_modules
	$(PY) scripts/check-corpus.py
	@mkdir -p $(CHK) && touch $@

.PHONY: gen-corpus-results
gen-corpus-results: | build harness/truth/node_modules ## promote a fresh corpus run to harness/truth/corpus-results.tsv
	$(PY) scripts/check-corpus.py --promote

# T0: the printed programs' answer, error and requirement types against the pinned
# TypeScript compiler (tools/target). The oracle reads the truth modules and their
# prelude, the generated TypeScript tables, the package's compiler config and install,
# and the toolchain file; each is a prerequisite so a change to any of them re-runs it.
$(CHK)/target: $(TRUTH_GENERATED) harness/truth/prelude.ts Test/fixtures/target/selection.json $(wildcard tools/target/*.ts tools/target/*.json) \
  ts/eff/profile.gen.ts ts/eff/eff.gen.ts ts/eff/packages.gen.ts ts/eff/tsconfig.json ts/eff/node_modules lean-toolchain
	$(BUN) test tools/target
	$(BUN) tools/target/cli.ts --repo .
	@mkdir -p $(CHK) && touch $@

# The schema codec: Lean's `Ty.encode` results for the contract's cases, compared with
# rc.112's `Schema.toCodecJson` on the host; nothing committed.
$(CHK)/schema-codec: $(CORE) $(wildcard harness/truth/schema-codec/*) | build harness/truth/node_modules
	@tmp="$$(mktemp -d "$${TMPDIR:-/tmp}/effect4-schema-codec.XXXXXX")"; \
	  $(LAKE) env lean -M4096 --run harness/truth/schema-codec/Emit.lean "$$tmp/values.ts" && \
	  node harness/truth/node_modules/typescript/bin/tsc --project harness/truth/schema-codec/tsconfig.json && \
	  $(BUN) harness/truth/schema-codec/check.ts "$$tmp/values.ts"; \
	  status=$$?; rm -rf "$$tmp"; exit $$status
	@mkdir -p $(CHK) && touch $@

# The OCaml lane (the effect4 opam switch; local only until the runner has one): the eff
# library's goldens and wire tests, the LCNF route's smoke, the engine's own tests and the
# three-engine differential (which reads the printed corpus), and the engine seam check.
OCAML_SOURCES := $(shell find ocaml -type f -not -path '*/_build/*')
$(CHK)/ocaml: $(CORPUS)/index.tsv $(OCAML_SOURCES)
	cd ocaml && $(OCAML) dune build && $(OCAML) dune test eff gen
	cd ocaml && $(OCAML) dune test engine
	$(OCAML) bash ocaml/engine/tools/gen-check.sh
	@mkdir -p $(CHK) && touch $@

# The ingest smoke: the printed corpus through the foreign recognizer's printed contract.
# The census over the constructed foreign corpus is check-ingest (nightly).
$(CHK)/ingest-smoke: $(CORPUS)/index.tsv ts/eff/node_modules $(TS_EFF_SOURCES)
	$(BUN) ts/eff/ingest/check-corpus.ts printed $(abspath $(CORPUS))
	@mkdir -p $(CHK) && touch $@

$(CHK)/ingest: $(CORPUS)/index.tsv ts/eff/node_modules $(TS_EFF_SOURCES) tools/Tools/ForeignCorpus.lean tools/Tools/Styles.lean $(OCAML_SOURCES) scripts/check-ingest.sh
	bash scripts/check-ingest.sh
	@mkdir -p $(CHK) && touch $@

$(CHK)/host-protocol: $(CORE) $(wildcard harness/truth/session/*.ts harness/truth/session/*.lean harness/truth/session/*.json) tools/Tools/HostProtocol.lean scripts/check-host-protocol.py
	$(PY) scripts/check-host-protocol.py
	@mkdir -p $(CHK) && touch $@

$(CHK)/census: $(VENDOR_SOURCES) generated/effect-runtime-census.tsv Test/Audit/RuntimeCoverage.lean scripts/check-effect-runtime-census.sh scripts/generate-effect-runtime-census.sh
	bash scripts/check-effect-runtime-census.sh
	@mkdir -p $(CHK) && touch $@

SCHEMA_SOURCES := $(shell find src/Effect4/Schema -name '*.lean') src/Effect4/Codegen/Schema.lean
$(CHK)/schema-ts: $(SCHEMA_SOURCES) $(wildcard $(SCHEMA_TS_DIR)/*) scripts/check-schema-typescript-generation.sh
	bash scripts/check-schema-typescript-generation.sh
	@mkdir -p $(CHK) && touch $@

# The rest of the Schema slice, on its inputs (ledger decision 3): the rc.112 tag pins
# are a textual extraction from the vendored SchemaRepresentation.ts; the host
# harnesses run the pinned Schema host (EFFECT4_EFFECT_NODE_MODULES, harness/schema-host).
SCHEMA_PIN := vendor/effect-4.0.0-rc.112/src/SchemaRepresentation.ts
$(CHK)/schema-pins: $(SCHEMA_PIN) src/Effect4/Schema/Representation.lean scripts/check-schema-census.sh
	bash scripts/check-schema-census.sh $(SCHEMA_PIN)
	@mkdir -p $(CHK) && touch $@

$(CHK)/schema-host: $(SCHEMA_SOURCES) $(shell find harness/schema-annotations harness/schema-effectful-field -type f -not -path '*/node_modules/*') scripts/check-schema-annotations.sh scripts/check-schema-effectful-field.sh | build
	bash scripts/check-schema-annotations.sh
	bash scripts/check-schema-effectful-field.sh
	@mkdir -p $(CHK) && touch $@

# The compatibility snapshot: reflect the working tree in a checkout outside the
# repository and compare its constructor shapes with the promoted baseline. Joins
# `check` once the baseline is re-promoted at the freeze commit (the current one
# predates the removal of `choose`).
COMPAT_BASELINE ?= Test/fixtures/baseline/66ee4657-supplement-v1/snapshot.json
$(CHK)/compat: $(CORE) scripts/check-compatibility.py scripts/lib/compatibility.py tools/Compatibility/Extract.lean $(COMPAT_BASELINE)
	@work="$$(mktemp -d "$${TMPDIR:-/tmp}/effect4-compat.XXXXXX")/tree"; \
	  $(PY) scripts/check-compatibility.py prepare --work "$$work" --working-tree && \
	  $(PY) scripts/check-compatibility.py reflect --work "$$work" && \
	  $(PY) scripts/check-compatibility.py compare --baseline $(COMPAT_BASELINE) --candidate "$$work/snapshot.json"; \
	  status=$$?; rm -rf "$$(dirname "$$work")"; exit $$status
	@mkdir -p $(CHK) && touch $@

SELFTEST_SOURCES := $(wildcard scripts/test-*.sh scripts/test-*.py scripts/check-*.sh scripts/check-*.py scripts/lib/*) Test/Audit/AxiomGate.lean \
  $(shell find Test/fixtures/trust-gate Test/fixtures/internal-citations -type f)
$(CHK)/tools: $(SELFTEST_SOURCES) | build
	bash scripts/test-trust-gate.sh
	bash scripts/test-internal-citations-gate.sh
	$(PY) scripts/test-source-citations.py
	$(PY) scripts/test-conform-report.py
	$(PY) scripts/test-program-structure.py
	$(PY) scripts/test-compatibility.py
	$(PY) scripts/test-corpus-check.py
	@mkdir -p $(CHK) && touch $@

# ---------------------------------------------------------------------------- help

.PHONY: help clean
help: ## this list
	@awk 'BEGIN {FS = ":.*## "} /^[a-zA-Z0-9_-]+:.*## / {printf "  %-18s %s\n", $$1, $$2}' $(MAKEFILE_LIST)
	@echo
	@echo '  check-<name>       one check: roots, cases, native, ts-reader, truth, target, schema-codec,'
	@echo '                     ocaml, ingest, ingest-smoke, host-protocol, census, schema-ts, corpus,'
	@echo '                     schema-pins, schema-host, compat, tools'
	@echo '                     (each skipped while its inputs are unchanged; -B forces)'
	@echo '  gen-<group>        one generated group: derived, specs, eff, wire, cas, ts, readme, lcnf,'
	@echo '                     truth, host-protocol, schema-ts, census'

clean: ## lake clean (drops the build, the generation and check markers)
	$(LAKE) clean
