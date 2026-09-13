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
#
# Staleness of a generated group is judged by GNU make from file times: a rule's
# prerequisites are the generator's sources plus the Lake trace of the compiled
# root it reads (Lake rewrites a module's .trace whenever that module or anything
# it imports changes). `make check-gen` does not trust file times: it regenerates
# every group and refuses if a committed file changed (`git diff --exit-code`).
#
# One Lean process at a time (.NOTPARALLEL). Checks that need no Lean can be run
# in parallel from a second shell; a parallel lane is a later step.

SHELL := /bin/bash
LAKE ?= lake
BUN ?= bun
PY ?= python3
GEN := .lake/gen
.DEFAULT_GOAL := help
.NOTPARALLEL:

# Lake's trace of the whole core (src/Effect4.lean imports every core module) and of
# the proof graph. A change anywhere beneath either rewrites the file.
CORE := .lake/build/lib/lean/Effect4.trace
LAWS := .lake/build/lib/lean/Effect4/Laws.trace
TRACE := .lake/build/lib/lean/Effect4

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
	bash scripts/generate.sh --only derived --force
	@mkdir -p $(GEN) && touch $@

$(GEN)/specs: $(GEN)/derived tools/Conform/Cli/EmitSpecs.lean tools/Conform/Effect4/specs.json $(TRACE)/Program/Typing.trace
	bash scripts/generate.sh --only specs --force
	@mkdir -p $(GEN) && touch $@

EFF_SOURCES := src/OCaml5/Tools/EffGen.lean $(wildcard src/OCaml5/Eff/*.lean) \
  scripts/generate-engine-structure.py scripts/lib/program_structure.py ocaml/engine/api_engine.ml
$(GEN)/eff: $(GEN)/specs $(EFF_SOURCES) $(CORE)
	bash scripts/generate.sh --only eff --force
	@mkdir -p $(GEN) && touch $@

$(GEN)/wire: $(GEN)/eff src/OCaml5/Tools/EffWire.lean $(CORE)
	bash scripts/generate.sh --only wire --force
	@mkdir -p $(GEN) && touch $@

$(GEN)/cas: $(GEN)/wire src/OCaml5/Tools/CasGoldens.lean $(CORE)
	bash scripts/generate.sh --only cas --force
	@mkdir -p $(GEN) && touch $@

TS_SOURCES := $(wildcard tools/Tools/*.lean) scripts/generate-ts-eff.sh src/Effect4/Codegen/Print.lean lakefile.toml \
  vendor/effect-4.0.0-rc.112/src/unstable/sql/SqlClient.ts vendor/effect-4.0.0-rc.112/src/unstable/sql/Statement.ts \
  vendor/effect-4.0.0-rc.112/src/unstable/persistence/KeyValueStore.ts
$(GEN)/ts: $(GEN)/cas $(TS_SOURCES) $(CORE)
	bash scripts/generate.sh --only ts --force
	@mkdir -p $(GEN) && touch $@

$(GEN)/readme: $(GEN)/ts ts/eff/ingest/render-readme.ts ts/eff/profile.gen.ts ts/eff/forms.gen.ts ts/eff/taxonomy.gen.ts
	bash scripts/generate.sh --only readme --force
	@mkdir -p $(GEN) && touch $@

LCNF_SOURCES := src/OCaml5/Tools/LcnfGen.lean $(wildcard src/OCaml5/Lcnf/*.lean) \
  ocaml/engine/externs.txt ocaml/engine/tools/api_engine_prelude.ml
$(GEN)/lcnf: $(GEN)/readme $(LCNF_SOURCES) $(CORE)
	bash scripts/generate.sh --only lcnf --force
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
# prints the table, and the data-stamps script (which insists on the Lean lane lock)
# writes the provenance record that the label check still reads.
CENSUS_SOURCES := scripts/generate-effect-runtime-census.sh scripts/generate-data-stamps.py \
  $(wildcard vendor/effect-4.0.0-rc.112/src/*.ts vendor/effect-4.0.0-rc.112/src/internal/*.ts)
$(GEN)/census: $(GEN)/schema-ts $(CENSUS_SOURCES)
	bash scripts/generate-effect-runtime-census.sh > generated/effect-runtime-census.tsv
	mkdir -p .lake/LANE.lock && $(PY) scripts/generate-data-stamps.py census; status=$$?; rmdir .lake/LANE.lock; exit $$status
	@mkdir -p $(GEN) && touch $@

# The groups generate.py regenerates into a temporary directory for its byte comparison.
HERMETIC_GROUPS := derived specs eff wire cas ts readme
GEN_GROUPS := $(HERMETIC_GROUPS) lcnf truth host-protocol schema-ts census

.PHONY: gen gen-hermetic $(addprefix gen-,$(GEN_GROUPS)) clean-gen
gen: $(addprefix $(GEN)/,$(GEN_GROUPS)) ## regenerate every stale generated group, in order
gen-hermetic: $(addprefix $(GEN)/,$(HERMETIC_GROUPS)) ## the Lean-only groups (no host runtime)
$(addprefix gen-,$(GEN_GROUPS)): gen-%: $(GEN)/% ## one group: make gen-eff, make gen-truth, ...
clean-gen: ## forget the generation markers (the next `make gen` re-cuts everything)
	rm -rf $(GEN)

# Every committed path a generator writes. The drift check diffs exactly these.
GENERATED_PATHS := $(DERIVED_OUT) src/Effect4/Laws/Program/Typing/Specs.lean \
  ocaml/eff ocaml/goldens/eff ocaml/engine/cas/goldens ocaml/engine/e4_program_layout.ml \
  ocaml/engine/e4_program_layout.json ocaml/engine/e4_program_layout.json.cut-from \
  ocaml/gen/api_gen.ml ocaml/engine/api_engine.ml \
  ts/eff/eff.gen.ts ts/eff/json.gen.ts ts/eff/profile.gen.ts ts/eff/taxonomy.gen.ts ts/eff/forms.gen.ts \
  ts/eff/wire.gen.ts ts/eff/packages.gen.ts ts/eff/ingest/README.md \
  harness/truth/corpus.json harness/truth/corpus.json.cut-from harness/truth/generated harness/truth/result.json \
  harness/truth/result.json.cut-from harness/truth/result.md harness/truth/tapes \
  harness/truth/session/protocol.gen.ts harness/truth/session/tape.schema.json harness/truth/session/tape.schema.json.cut-from \
  $(SCHEMA_TS_DIR)/Person.generated.ts $(SCHEMA_TS_DIR)/AllRepresentations.generated.ts $(SCHEMA_TS_DIR)/TwoRoots.generated.ts \
  generated/effect-runtime-census.tsv generated/effect-runtime-census.tsv.cut-from

# ---------------------------------------------------------------------------- checks

.PHONY: check check-host check-full check-gen check-gen-hermetic check-roots check-cases check-native \
  check-citations check-ts-reader check-truth check-target check-schema-codec check-ocaml check-ingest \
  check-ingest-smoke check-host-protocol check-census check-streams check-schema-ts check-compat check-tools sweep

check: build check-roots check-gen-hermetic check-cases check-native check-citations check-ts-reader ## after every change
check-host: check check-truth check-target check-schema-codec check-ocaml check-ingest-smoke ## per slice: the outside oracles
check-full: check-host check-ingest check-host-protocol check-census check-streams check-schema-ts ## everything

# Drift: regenerate without trusting file times, then refuse any change to a committed file.
# The hermetic form covers the Lean-only groups; the full form adds the host-cut groups.
check-gen-hermetic: ## regenerate the Lean-only groups and refuse a changed committed file
	$(MAKE) -B gen-hermetic
	git diff --exit-code --stat -- $(GENERATED_PATHS)
	@untracked="$$(git status --porcelain -- $(GENERATED_PATHS) | grep '^??' || true)"; \
	  if [ -n "$$untracked" ]; then echo "FAIL check-gen: untracked generated files:"; echo "$$untracked"; exit 1; fi
	@echo 'PASS check-gen: every Lean-only generated file is what its generator emits'

check-gen: ## regenerate every group (host runtime included) and refuse a changed committed file
	$(MAKE) -B gen
	git diff --exit-code --stat -- $(GENERATED_PATHS)
	@untracked="$$(git status --porcelain -- $(GENERATED_PATHS) | grep '^??' || true)"; \
	  if [ -n "$$untracked" ]; then echo "FAIL check-gen: untracked generated files:"; echo "$$untracked"; exit 1; fi
	@echo 'PASS check-gen: every generated file is what its generator emits'

check-roots: ## every module reachable from a root; proofs separate; the axiom ceiling
	bash scripts/check-library-roots.sh

check-cases: ## no catch-all match arm on a core type without a declared cover
	bash scripts/check-conform.sh cases

check-native: ## the compiler's memory layout of every core type is covered and coherent
	bash scripts/check-conform.sh native

check-citations: ## every cited path exists; no line-numbered citation into a mutable document
	$(PY) scripts/check-source-citations.py
	bash scripts/check-internal-citations.sh

check-ts-reader: ## the TypeScript reader reproduces Lean's reading of the printed corpus
	bash scripts/check-ts-eff-corpus.sh

check-truth: ## the printed programs exit and schedule as Effect rc.112 does
	bash scripts/check-truth.sh

check-target: ## the printed programs' types agree with the TypeScript compiler (T0)
	$(PY) scripts/check-target.py

check-schema-codec: ## Ty encodings agree with the runtime's schema codec
	bash scripts/check-schema-codec.sh

check-ocaml: ## the OCaml differentials over Lean-cut goldens, and the engine's own tests
	bash scripts/check-ocaml.sh dune-tests
	bash scripts/check-ocaml.sh engine-tests

check-ingest: ## the two foreign-TypeScript readers over the full constructed census (nightly)
	bash scripts/check-ingest.sh

check-ingest-smoke: ## the same readers over the printed corpus and a small foreign corpus (a minute)
	bash scripts/check-ingest.sh --smoke

check-host-protocol: ## the keyed session protocol replays recorded rc.112 runs
	$(PY) scripts/check-host-protocol.py

check-census: ## the behaviour census matches the vendored runtime source
	bash scripts/check-effect-runtime-census.sh

check-streams: ## the vendored stream documentation examples still hold
	bash scripts/check-streams.sh

check-schema-ts: ## Lean-emitted schema documents compile and revive on the host
	bash scripts/check-schema-typescript-generation.sh

# The compatibility snapshot: reflect the working tree in a checkout outside the
# repository and compare its constructor shapes with the promoted baseline. Joins
# `check` once the baseline is re-promoted at the freeze commit (the current one
# predates the removal of `choose`).
COMPAT_BASELINE ?= Test/fixtures/baseline/66ee4657-supplement-v1/snapshot.json
check-compat: ## the constructor shapes of every stored type against the baseline snapshot
	@work="$$(mktemp -d "$${TMPDIR:-/tmp}/effect4-compat.XXXXXX")/tree"; \
	  $(PY) scripts/check-compatibility.py prepare --work "$$work" --working-tree && \
	  $(PY) scripts/check-compatibility.py reflect --work "$$work" && \
	  $(PY) scripts/check-compatibility.py compare --baseline $(COMPAT_BASELINE) --candidate "$$work/snapshot.json"; \
	  status=$$?; rm -rf "$$(dirname "$$work")"; exit $$status

check-tools: ## the checkers' own self-tests (planted defects must be refused)
	bash scripts/test-trust-gate.sh
	bash scripts/test-internal-citations-gate.sh
	$(PY) scripts/test-source-citations.py
	$(PY) scripts/test-conform-report.py
	$(PY) scripts/test-generated-gate.py
	$(PY) scripts/test-truth-stamp.py
	$(PY) scripts/test-program-structure.py
	$(PY) scripts/test-compatibility.py

sweep: ## the previous serial sweep, kept until every check above has replaced it
	bash scripts/sweep.sh --keep-going

# ---------------------------------------------------------------------------- misc

.PHONY: help clean
help: ## this list
	@awk 'BEGIN {FS = ":.*## "} /^[a-zA-Z0-9_$$()%-]+:.*## / {printf "  %-22s %s\n", $$1, $$2}' $(MAKEFILE_LIST)

clean: ## lake clean (drops the build, the stamps and the generation markers)
	$(LAKE) clean
