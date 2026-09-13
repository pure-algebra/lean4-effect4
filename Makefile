# The one entry point. `make help` lists the targets.
#
# Three kinds of target:
#   build*   Lake builds; the axiom audit runs inside `lake build Test`.
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
# One Lean process at a time (.NOTPARALLEL). Checks that need no Lean can be run
# in parallel from a second shell; a parallel lane is a later step.

SHELL := /bin/bash
LAKE ?= lake
BUN ?= bun
PY ?= python3
GEN := .lake/gen
CHK := .lake/check
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

DERIVED_SOURCES := $(wildcard tools/Effect4Gen/*.lean tools/Effect4Gen/guards/*.lean) tools/Effect4Gen/manifest.json
DERIVED_TRACES := $(addprefix $(TRACE)/,Store/Canonical.trace Program/Native.trace Store/RowCanonical.trace \
  Store/Pin.trace Store/Node.trace Api/Frontier.trace Program/Eff.trace Program/Ty.trace)
DERIVED_OUT := src/Effect4/Store/Derived/Json.lean src/Effect4/Store/Derived/Schema.lean \
  src/Effect4/Program/Derived.lean src/Effect4/Store/PinDerived.lean src/Effect4/Api/Derived.lean \
  src/Effect4/Program/Fold.lean

$(GEN)/derived: $(DERIVED_SOURCES) $(DERIVED_TRACES) | build
	bash scripts/generate.sh --only derived
	@mkdir -p $(GEN) && touch $@

$(GEN)/specs: $(GEN)/derived tools/Conform/Cli/EmitSpecs.lean tools/Conform/Effect4/specs.json $(TRACE)/Program/Typing.trace
	bash scripts/generate.sh --only specs
	@mkdir -p $(GEN) && touch $@

EFF_SOURCES := src/OCaml5/Tools/EffGen.lean $(wildcard src/OCaml5/Eff/*.lean) \
  scripts/generate-engine-structure.py scripts/lib/program_structure.py ocaml/engine/api_engine.ml
$(GEN)/eff: $(GEN)/specs $(EFF_SOURCES) $(CORE)
	bash scripts/generate.sh --only eff
	@mkdir -p $(GEN) && touch $@

$(GEN)/wire: $(GEN)/eff src/OCaml5/Tools/EffWire.lean $(CORE)
	bash scripts/generate.sh --only wire
	@mkdir -p $(GEN) && touch $@

$(GEN)/cas: $(GEN)/wire src/OCaml5/Tools/CasGoldens.lean $(CORE)
	bash scripts/generate.sh --only cas
	@mkdir -p $(GEN) && touch $@

TS_SOURCES := $(wildcard tools/Tools/*.lean) scripts/generate-ts-eff.sh src/Effect4/Codegen/Print.lean lakefile.toml \
  vendor/effect-4.0.0-rc.112/src/unstable/sql/SqlClient.ts vendor/effect-4.0.0-rc.112/src/unstable/sql/Statement.ts \
  vendor/effect-4.0.0-rc.112/src/unstable/persistence/KeyValueStore.ts
$(GEN)/ts: $(GEN)/cas $(TS_SOURCES) $(CORE)
	bash scripts/generate.sh --only ts
	@mkdir -p $(GEN) && touch $@

$(GEN)/readme: $(GEN)/ts ts/eff/ingest/render-readme.ts ts/eff/profile.gen.ts ts/eff/forms.gen.ts ts/eff/taxonomy.gen.ts
	bash scripts/generate.sh --only readme
	@mkdir -p $(GEN) && touch $@

# The four LCNF outputs (each header carries its own regenerating command).
LCNF_SOURCES := src/OCaml5/Tools/LcnfGen.lean $(wildcard src/OCaml5/Lcnf/*.lean) \
  ocaml/engine/externs.txt ocaml/engine/tools/api_engine_prelude.ml
$(GEN)/lcnf: $(GEN)/readme $(LCNF_SOURCES) $(CORE)
	bash scripts/generate.sh --only lcnf
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

$(GEN)/host-protocol: $(GEN)/truth tools/Tools/HostProtocol.lean scripts/generate-host-protocol.sh $(TRACE)/Api/HostSession.trace
	bash scripts/generate-host-protocol.sh
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
  generated/effect-runtime-census.tsv

# ---------------------------------------------------------------------------- checks

CHECKS := roots cases native ts-reader truth target schema-codec ocaml ingest ingest-smoke \
  host-protocol census streams schema-ts compat tools
.PHONY: check check-host check-full check-gen check-gen-full check-citations clean-check $(addprefix check-,$(CHECKS))

check: build check-roots check-gen check-cases check-native check-citations check-ts-reader ## after every change
check-host: check check-truth check-target check-schema-codec check-ocaml check-ingest-smoke ## per slice: the outside oracles
check-full: check-host check-gen-full check-ingest check-host-protocol check-census check-streams check-schema-ts ## everything

# Drift: regenerate the stale Lean-only groups, then refuse any change to a committed
# generated file. `check-gen-full` re-cuts every group, the host-cut ones included,
# without trusting file times.
define refuse_drift
	git diff --exit-code --stat -- $(GENERATED_PATHS)
	@untracked="$$(git status --porcelain -- $(GENERATED_PATHS) | grep '^??' || true)"; \
	  if [ -n "$$untracked" ]; then echo "FAIL check-gen: untracked generated files:"; echo "$$untracked"; exit 1; fi
endef

check-gen: gen-hermetic ## regenerate the stale Lean-only groups and refuse a changed committed file
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

$(CHK)/roots: $(LEAN_SOURCES) lakefile.toml lean-toolchain scripts/check-library-roots.sh | build
	bash scripts/check-library-roots.sh
	@mkdir -p $(CHK) && touch $@

CONFORM_SOURCES := $(shell find tools/Conform -name '*.lean' -o -name '*.json') scripts/check-conform.sh scripts/check-conform.py
$(CHK)/cases: $(CORE) $(CONFORM_SOURCES)
	bash scripts/check-conform.sh cases
	@mkdir -p $(CHK) && touch $@

$(CHK)/native: $(CORE) $(CONFORM_SOURCES)
	bash scripts/check-conform.sh native
	@mkdir -p $(CHK) && touch $@

check-citations: ## every cited path exists; no line-numbered citation into a mutable document
	$(PY) scripts/check-source-citations.py
	bash scripts/check-internal-citations.sh

TRUTH_GENERATED := harness/truth/corpus.json harness/truth/result.json harness/truth/result.md $(wildcard harness/truth/generated/*.ts)
$(CHK)/ts-reader: $(CORE) $(TS_EFF_SOURCES) tools/Tools/Corpus.lean $(TRUTH_GENERATED) harness/truth/prelude.ts scripts/check-ts-eff-corpus.sh
	bash scripts/check-ts-eff-corpus.sh
	@mkdir -p $(CHK) && touch $@

$(CHK)/truth: $(CORE) $(LAWS) $(TRUTH_SOURCES) $(TRUTH_GENERATED) $(wildcard harness/truth/session/*.ts) scripts/check-truth.py scripts/check-truth.sh
	bash scripts/check-truth.sh
	@mkdir -p $(CHK) && touch $@

$(CHK)/target: $(TRUTH_GENERATED) Test/fixtures/target/selection.json $(wildcard tools/target/*.ts) ts/eff/profile.gen.ts scripts/check-target.py
	$(PY) scripts/check-target.py
	@mkdir -p $(CHK) && touch $@

$(CHK)/schema-codec: $(CORE) $(wildcard harness/truth/schema-codec/*) scripts/check-schema-codec.sh
	bash scripts/check-schema-codec.sh
	@mkdir -p $(CHK) && touch $@

OCAML_SOURCES := $(shell find ocaml -type f -not -path '*/_build/*' -not -name '*.cut-from')
$(CHK)/ocaml: $(OCAML_SOURCES) scripts/check-ocaml.sh
	bash scripts/check-ocaml.sh dune-tests
	bash scripts/check-ocaml.sh engine-tests
	bash scripts/check-ocaml.sh gen-check
	@mkdir -p $(CHK) && touch $@

$(CHK)/ingest-smoke: $(CORE) $(TS_EFF_SOURCES) tools/Tools/Corpus.lean scripts/check-ingest.sh
	bash scripts/check-ingest.sh --smoke
	@mkdir -p $(CHK) && touch $@

$(CHK)/ingest: $(CORE) $(TS_EFF_SOURCES) tools/Tools/Corpus.lean tools/Tools/ForeignCorpus.lean tools/Tools/Styles.lean $(OCAML_SOURCES) scripts/check-ingest.sh
	bash scripts/check-ingest.sh
	@mkdir -p $(CHK) && touch $@

$(CHK)/host-protocol: $(CORE) $(wildcard harness/truth/session/*.ts harness/truth/session/*.lean harness/truth/session/*.json) tools/Tools/HostProtocol.lean scripts/check-host-protocol.py
	$(PY) scripts/check-host-protocol.py
	@mkdir -p $(CHK) && touch $@

$(CHK)/census: $(VENDOR_SOURCES) generated/effect-runtime-census.tsv Test/Audit/RuntimeCoverage.lean scripts/check-effect-runtime-census.sh scripts/generate-effect-runtime-census.sh
	bash scripts/check-effect-runtime-census.sh
	@mkdir -p $(CHK) && touch $@

$(CHK)/streams: $(VENDOR_SOURCES) $(shell find harness/streams -type f -not -path '*/node_modules/*') scripts/check-streams.sh
	bash scripts/check-streams.sh
	@mkdir -p $(CHK) && touch $@

$(CHK)/schema-ts: $(shell find src/Effect4/Schema -name '*.lean') src/Effect4/Codegen/Schema.lean $(wildcard $(SCHEMA_TS_DIR)/*) scripts/check-schema-typescript-generation.sh
	bash scripts/check-schema-typescript-generation.sh
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

SELFTEST_SOURCES := $(wildcard scripts/test-*.sh scripts/test-*.py scripts/lib/*) Test/Audit/AxiomGate.lean $(shell find Test/fixtures/trust-gate Test/fixtures/internal-citations -type f)
$(CHK)/tools: $(SELFTEST_SOURCES) | build
	bash scripts/test-trust-gate.sh
	bash scripts/test-internal-citations-gate.sh
	$(PY) scripts/test-source-citations.py
	$(PY) scripts/test-conform-report.py
	$(PY) scripts/test-program-structure.py
	$(PY) scripts/test-compatibility.py
	@mkdir -p $(CHK) && touch $@

# ---------------------------------------------------------------------------- help

.PHONY: help clean
help: ## this list
	@awk 'BEGIN {FS = ":.*## "} /^[a-zA-Z0-9_-]+:.*## / {printf "  %-18s %s\n", $$1, $$2}' $(MAKEFILE_LIST)
	@echo
	@echo '  check-<name>       one check: roots, cases, native, ts-reader, truth, target, schema-codec,'
	@echo '                     ocaml, ingest, ingest-smoke, host-protocol, census, streams, schema-ts,'
	@echo '                     compat, tools (each skipped while its inputs are unchanged; -B forces)'
	@echo '  gen-<group>        one generated group: derived, specs, eff, wire, cas, ts, readme, lcnf,'
	@echo '                     truth, host-protocol, schema-ts, census'

clean: ## lake clean (drops the build, the generation and check markers)
	$(LAKE) clean
