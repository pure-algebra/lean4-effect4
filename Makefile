# The one entry point. `make help` lists the targets.
#
# Four kinds of target:
#   build*   Lake builds: `build` is the core and the law graph, `build-tools` the tool roots.
#   corpus   the printed corpus, a build artifact under .lake/corpus that three checks
#            read (the TypeScript reader, the ingest smoke, the OCaml engine differential).
#   gen-*    the generated files, one rule per group, in the dependency order the
#            producers need. A rule fires when its generator, its inputs, or the
#            compiled core it reads changed; its marker is .lake/gen/<group>.
#   check-*  the checks. What a landing owes (AGENTS.md, Working): `check` is the proofs
#            (the build), and `check-full` adds the behaviour gates, every run compared
#            with an outside implementation (the Effect runtime, the TypeScript compiler,
#            the OCaml engine). The batteries, the whole-tree axiom gate,
#            drift and document checks run through `check-sweep`; CI
#            runs the drift and the documents on every push.
#            A check that names its inputs is a marker rule too (.lake/check/<name>)
#            and is skipped while nothing it reads has changed; `make -B <target>`
#            forces it. `clean-check` forgets local markers but keeps shared passes. CI starts from a fresh clone, so it
#            has no markers and runs everything.
#
# Check markers depend on content keys. The keys include source closures, commands,
# package pins and runtime identities; file times never identify a successful check.
# Producers reached by check-full also key their source content and outputs.
# Drift of a committed generated file is `make check-gen`: regenerate the
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
# The native TypeScript compiler's synchronous client needs node (bun lacks the handle it reads).
NODE ?= node
PY ?= python3
OPAM_SWITCH ?= effect4
OCAML ?= opam exec --switch=$(OPAM_SWITCH) --
export LAKE BUN NODE PY OPAM_SWITCH OCAML
GEN := .lake/gen
CHK := .lake/check
export LEAN_NUM_THREADS ?= 3
.DEFAULT_GOAL := help
.NOTPARALLEL:

LEAN_SOURCES := $(shell find src Test -name '*.lean')
# The core's sources: the Effect4 root without the law graph. A gate whose tool reads the core
# depends on these, or on all the Lean sources, and builds exactly what its tool imports; no gate
# depends on `build`, which builds both library roots. The few that
# load the whole tree (the root elaboration, the trust harness, the architecture map) are the
# exceptions, named where they stand.
# The build's pins: a change to the toolchain, the Lake configuration or a package pin changes
# every compiled output, so every gate below depends on them too (Codex's BUILD-PINS, 2026-10-10).
BUILD_PINS := lean-toolchain lakefile.toml lake-manifest.json
CORE_SOURCES := $(filter-out src/Effect4/Laws.lean src/Effect4/Laws/%,$(filter src/Effect4.lean src/Effect4/%,$(LEAN_SOURCES))) $(BUILD_PINS)
LEAN_INPUTS := $(LEAN_SOURCES) $(BUILD_PINS)
# Build exactly the workspace modules that Lean files import, before `lake env lean` runs them
# (`lake env` builds nothing). An unreadable file stops the recipe; an empty list builds nothing,
# since a bare `lake build` is every default target (Codex's BUILD-IMPORTS, 2026-10-10).
build_imports = @modules="$$($(PY) scripts/lean-imports.py $(1))" && { [ -z "$$modules" ] || $(LAKE) build $$modules; }
# The `--load-dynlib` flags of the native libraries that Lake loads for the same modules
# (`native_flags`, `scripts/generate.py`): with them `lake env lean` runs the core as native code,
# not interpreted. A producer that runs the machine imports a module of `TestProgram` or
# `TestDogfood`, which load the native core, and takes them after `build_imports` (the codegen
# refactor's CR-2; the truth manifest took 63 s interpreted and 12 s native). The other
# producers' imports load no native library, and they stay interpreted, as the lakefile measured.
native_flags = $$($(PY) scripts/lean-imports.py --dynlibs $(1))
# Every folder that a lane of `ts/eff` reads (seat LANES, decisions row 295): the ingest's fidelity,
# census and fixture folders and the red twins of the tests stood outside this list.
TS_EFF_SOURCES := $(wildcard ts/eff/*.ts ts/eff/test/*.ts ts/eff/test/red/* ts/eff/ingest/*.ts ts/eff/ingest/test/*.ts \
  ts/eff/ingest/fidelity/*.ts ts/eff/ingest/census/* ts/eff/ingest/fixtures/* ts/eff/ingest/fixtures/*/* ts/eff/ingest/fixtures/*/*/*) \
  ts/eff/package.json ts/eff/bun.lock ts/eff/tsconfig.json ts/eff/test/type-projection.gen.json
VENDOR_SOURCES := $(wildcard vendor/effect-4.0.0-rc.112/src/*.ts vendor/effect-4.0.0-rc.112/src/internal/*.ts)

# ---------------------------------------------------------------------------- build

.PHONY: build build-tools
build: wire-roots ## lake build: the core and the law graph; connect orphan modules first
	@mkdir -p $(GEN)
	set -o pipefail; $(LAKE) build Effect4 Effect4Laws 2>&1 | tee $(GEN)/build.log

.PHONY: wire-roots
wire-roots:
	$(PY) scripts/wire-roots.py

.PHONY: build-profile
build-profile: ## where the last `make build` spent its time: the critical path and the slowest modules (.lake/gen/build-profile.md)
	@$(PY) scripts/build-profile.py $(GEN)/build.log

bank-census: ## every Effect4 aesop rule bank: its rules, simp lemmas and the clauses that name it (an instrument)
	$(LAKE) build Effect4Laws
	$(LAKE) env lean tools/BankCensusRun.lean

profile-module: ## FILE=<src/…/X.lean>: re-elaborate one built module with the profiler and aesop's statistics; summary here, raw logs in .lake/gen/profile/
	@test -n "$(FILE)" || { echo "usage: make profile-module FILE=src/Effect4/Laws/…/X.lean"; exit 2; }
	$(PY) scripts/profile-module.py $(FILE)

build-tools: build ## the generator and checker roots (Tools, OCaml5, Conform, Effect4Gen and its native guard)
	$(LAKE) build Tools OCaml5 Conform Effect4Gen Effect4GenNative

# ---------------------------------------------------------------------------- gen
#
# Each group's marker depends on the markers of the groups whose outputs its producer reads,
# and on no other. derived writes Lean modules the rest import, so every Lean producer waits
# on it; readme renders the TypeScript tables that ts cuts; truth reads the atoms' prelude
# (derived), the tables (ts) and the session protocol (host-protocol). A regenerated group
# re-cuts what reads it and nothing else (the codegen refactor's CR-2). Until then each marker
# depended on the one before it in GEN_GROUPS, so `make gen-schema-ts` re-cut the truth lane
# first, and the truth lane read a protocol that host-protocol wrote after it.
#
# lcnf sits between derived and eff -- it used to sit after readme, which made `make gen` a
# non-fixpoint: eff read the api_engine.ml of the previous run, so a changed row needed two
# passes and the nightly was the only thing that closed it (tooling plan 4.2, finding C1).

# The one assignment of wire tags. Every producer of canonical bytes reads it: the Lean
# codecs (derived), the OCaml codec and the golden bytes (eff), the wire manifest (wire) and
# the TypeScript writer (ts).
WIRE_TAGS := tools/Effect4Gen/wire-tags.json

# What every `scripts/generate.py` group reads besides its own sources: the orchestrator itself and
# the one header-and-layout module each Lean producer writes through (`Tools.GeneratedStamp`).
PRODUCER_COMMON := scripts/generate.py scripts/lib/derived_plan.py tools/Tools/GeneratedStamp.lean

# Declaration-site variance, read off the vendored rc.112 sources by a Lean `--run` driver
# (tooling plan 1.4a). It is an INPUT of `derived` -- the TyView group reads it -- so it is the
# first link of the chain, and `check-gen` holds it like any other generated file.
# `generate.py` reads the manifest's `VariancesFlags` for it, so the manifest is a source.
VARIANCES := tools/Effect4Gen/variances.json
VARIANCE_OUT := $(VARIANCES) src/Effect4/Program/TyVariance.lean
VARIANCE_SOURCES := tools/Tools/Variances.lean $(VENDOR_SOURCES) $(PRODUCER_COMMON) \
  tools/Effect4Gen/manifest.json \
  $(wildcard src/Effect4/Store/Carrier/*.lean) lakefile.toml lake-manifest.json lean-toolchain
VARIANCE_KEY = $(PY) scripts/gate-cache.py key gen-variances --runtime lean --inputs $(CHECK_CACHE_SOURCES) $(VARIANCE_SOURCES) --outputs $(VARIANCE_OUT)
$(CHK)/gen-variances.key: FORCE
	@$(VARIANCE_KEY)
$(GEN)/variances: $(CHK)/gen-variances.key
	$(PY) scripts/generate.py --only variances
	@$(VARIANCE_KEY)
	@mkdir -p $(GEN) && touch $@

DERIVED_SOURCES := $(wildcard tools/Effect4Gen/*.lean tools/Effect4Gen/guards/*.lean) tools/Effect4Gen/manifest.json tools/Effect4Gen/binders.json \
  $(wildcard $(VARIANCES)) $(WIRE_TAGS) tools/Tools/WireTags.lean $(PRODUCER_COMMON) lakefile.toml
# Bootstrap freshness cannot depend on compiled consumers of stale generated files, so the inputs
# are source files: every one in the import closure of the generators and of each manifest group's
# imports, read from the headers (`scripts/lean-imports.py --closure`). An edit outside it, to the
# LCNF route or a battery, cannot change a derived output and reruns no group (LC-4). A file added
# to the closure changes the file that imports it.
DERIVED_INPUTS := $(shell $(PY) scripts/lean-imports.py --closure --manifest tools/Effect4Gen/manifest.json \
  Effect4Gen.Exe Effect4Gen.CatalogueExe Tools.GeneratedStamp) lake-manifest.json lean-toolchain
DERIVED_OUT := src/Effect4/Program/TyEq.lean src/Effect4/Store/Domain/Derived/Json.lean src/Effect4/Store/Domain/Derived/Schema.lean \
  src/Effect4/Store/Domain/Derived/Program.lean src/Effect4/Store/Domain/PinDerived.lean src/Effect4/Api/Derived.lean \
  src/Effect4/Store/Domain/Derived/Value.lean src/Effect4/Api/RefusalsDerived.lean src/Effect4/Api/RunnerDerived.lean \
  src/Effect4/Machine/Fold.lean src/Effect4/Program/Fold.lean src/Effect4/Program/TyFoldExtras.lean src/Effect4/Laws/Program/TyView.lean src/Effect4/Store/Carrier/Fold.lean src/Effect4/Schema/Fold.lean src/Effect4/Program/LayerView.lean src/Effect4/Program/NodeLenses.lean src/Effect4/Program/Binders.lean src/Effect4/Program/Scoped.lean \
  src/Effect4/Program/Authoring/Lifts.lean src/Effect4/Laws/Program/Authoring/Lifts.lean \
  src/Effect4/Program/Authoring/Rows.lean src/Effect4/Laws/Program/Authoring/Rows.lean \
  src/Effect4/Program/Authoring/Atoms.lean src/Effect4/Laws/Program/Authoring/Atoms.lean \
  src/Effect4/Codegen/Authoring/Forms.lean src/Effect4/Laws/Program/Authoring/Forms.lean \
  src/Effect4/Program/AtomInventory.lean harness/truth/prelude-atoms.gen.ts src/Effect4/Codegen/TsFold.lean \
  src/OCaml5/Ml/Fold.lean

# A missing output must run its producer instead of becoming a missing prerequisite.
DERIVED_KEY = $(PY) scripts/gate-cache.py key gen-derived --runtime lean --inputs $(CHECK_CACHE_SOURCES) $(DERIVED_SOURCES) $(DERIVED_INPUTS) --outputs $(DERIVED_OUT)
$(CHK)/gen-derived.key: FORCE $(GEN)/variances
	@$(DERIVED_KEY)
$(GEN)/derived: $(CHK)/gen-derived.key
	$(PY) scripts/generate.py --only derived
	@$(DERIVED_KEY)
	@mkdir -p $(GEN) && touch $@

# The LCNF outputs (each header carries its own regenerating command). The group is
# NOT a link of the hermetic chain: it regenerates in place only (generate.py refuses
# `--output-dir` for it), so `check-gen` does not reach it. What the chain needs is the order,
# and `ocaml/engine/api_engine.ml` in EFF_SOURCES below: together they make the second pass
# unnecessary. `make gen-lcnf` is run by name, by `gen`, by the check-ocaml CI job, and by
# `$(CHK)/ocaml`, which depends on it, so the OCaml gate builds the current machine (LC-3).
# Its sources are the generator's: the driver, the route (`OCaml5.Lcnf`, `OCaml5.Ml`) and the
# Conform modules it reads (the mono index, the source evaluator's primitives), and the modules
# each artefact imports: `Effect4.Api`, the to-do host run that the todo lane lowers (LC-6), the
# constructor lane's functions (`Test.Codegen.ConstructorLane`) and the Modeled lane's codec
# (`Test.Codegen.ModeledLane`), none of which reaches a law module.
LCNF_SOURCES := src/OCaml5/Tools/LcnfGen.lean $(wildcard src/OCaml5/Lcnf/*.lean src/OCaml5/Ml/*.lean) \
  $(wildcard tools/Conform/Lcnf/*.lean tools/Conform/Core/*.lean tools/Conform/Source/*.lean) \
  ocaml/gen/roots.json ocaml/engine/externs.txt ocaml/engine/tools/api_engine_prelude.ml \
  scripts/lib/lcnf_interfaces.py $(wildcard ocaml/gen/interface/*.ml ocaml/gen/interface/*.mli) ocaml/gen/interface/dune $(PRODUCER_COMMON)
LCNF_OUT := ocaml/eff/eff_types.ml ocaml/eff/eff_types.mli ocaml/gen/api_gen.ml \
  ocaml/gen/api_gen.mli ocaml/gen/closure-api_gen.tsv ocaml/engine/api_engine.ml \
  ocaml/engine/api_engine.mli ocaml/gen/closure-api_engine.tsv ocaml/engine/test/todo/todo_gen.ml \
  ocaml/engine/test/todo/todo_gen.mli ocaml/gen/closure-todo_gen.tsv ocaml/engine/test/ctors/ctors_gen.ml \
  ocaml/engine/test/ctors/ctors_gen.mli ocaml/gen/closure-ctors_gen.tsv ocaml/engine/test/modeled/modeled_gen.ml \
  ocaml/engine/test/modeled/modeled_gen.mli ocaml/gen/closure-modeled_gen.tsv ocaml/engine/test/rocq/rocq_gen.ml \
  ocaml/engine/test/rocq/rocq_gen.mli ocaml/gen/closure-rocq_gen.tsv
LCNF_KEY = $(PY) scripts/gate-cache.py key gen-lcnf --runtime lean --inputs $(CHECK_CACHE_SOURCES) $(LCNF_SOURCES) --lean OCaml5.Tools.LcnfGen Effect4.Api Effect4.Run.Kit Effect4.Program.Check Effect4.Run.LiveRecord Test.Dogfood.Scenario.Todo.HostRun Test.Codegen.ConstructorLane Test.Codegen.ModeledLane Effect4.Laws.Run.Tree --outputs $(LCNF_OUT)
$(CHK)/gen-lcnf.key: FORCE $(GEN)/derived
	@$(LCNF_KEY)
$(GEN)/lcnf: $(CHK)/gen-lcnf.key
	$(PY) scripts/generate.py --only lcnf
	@$(LCNF_KEY)
	@mkdir -p $(GEN) && touch $@

EFF_SOURCES := src/OCaml5/Tools/EffGen.lean $(wildcard src/OCaml5/Eff/*.lean) $(WIRE_TAGS) \
  $(PRODUCER_COMMON)
$(GEN)/eff: $(GEN)/derived $(EFF_SOURCES) $(CORE_SOURCES)
	$(PY) scripts/generate.py --only eff
	@mkdir -p $(GEN) && touch $@

$(GEN)/wire: $(GEN)/derived src/OCaml5/Tools/EffWire.lean $(PRODUCER_COMMON) $(CORE_SOURCES)
	$(PY) scripts/generate.py --only wire
	@mkdir -p $(GEN) && touch $@

$(GEN)/cas: $(GEN)/derived src/OCaml5/Tools/CasDiskOracle.lean src/OCaml5/Tools/CasDiskCuts.lean src/OCaml5/Store/DiskOracle.lean src/OCaml5/Tools/CasGoldens.lean src/OCaml5/Tools/CasFacts.lean src/OCaml5/Store/Facts.lean scripts/lib/store_facts.py $(PRODUCER_COMMON) $(CORE_SOURCES)
	$(PY) scripts/generate.py --only cas
	@mkdir -p $(GEN) && touch $@

TS_SOURCES := $(wildcard tools/Tools/*.lean tools/Drivers/*.lean tools/TestSupport/*.lean) $(WIRE_TAGS) $(VARIANCES) src/Effect4/Codegen/Print.lean lakefile.toml \
  vendor/effect-4.0.0-rc.112/src/unstable/sql/SqlClient.ts vendor/effect-4.0.0-rc.112/src/unstable/sql/Statement.ts \
  vendor/effect-4.0.0-rc.112/src/unstable/persistence/KeyValueStore.ts scripts/generate.py
$(GEN)/ts: $(GEN)/derived $(TS_SOURCES) $(CORE_SOURCES)
	$(PY) scripts/generate.py --only ts
	@mkdir -p $(GEN) && touch $@

# The only host producer of the hermetic chain. Without the pinned install it does not fail
# with "install the dependencies": it resolves `effect` to whatever is above the worktree and
# dies inside a generated schema (`Schema.TaggedUnion is not a function`), which is what a
# fresh worktree saw here. Order-only, like every other consumer of the install.
$(GEN)/readme: $(GEN)/ts ts/eff/ingest/render-readme.ts ts/eff/profile.gen.ts ts/eff/forms.gen.ts ts/eff/taxonomy.gen.ts scripts/generate.py | ts/eff/node_modules
	$(PY) scripts/generate.py --only readme
	@mkdir -p $(GEN) && touch $@

# The truth harness: Lean writes the corpus from the committed tapes, then the real
# runtime prints the modules, re-records the tapes and writes the result. Both are
# deterministic given the pinned host; the comparison against a fresh run is check-truth.
# The prelude and the files it re-exports: a gate that reads printed modules depends on all five.
PRELUDE_SOURCES := harness/truth/prelude.ts harness/truth/control.ts harness/truth/records.ts harness/truth/tuples.ts harness/truth/prelude-atoms.gen.ts
TRUTH_SOURCES := harness/truth/Truth.lean Test/Codegen/TermRows.lean Test/Program/MaskContract.lean Test/Program/QueueScenarios.lean Test/Program/QueueMask.lean Test/Program/SemaphoreScenarios.lean Test/Program/PoolScenarios.lean Test/Program/PoolPublic.lean Test/Program/DefinitionsControls.lean Test/Program/QueueDefs.lean Test/Codegen/ServicesPrint.lean $(PRELUDE_SOURCES) harness/truth/run-truth.ts \
  $(wildcard harness/truth/tapes/*.jsonl) ts/eff/package.json ts/eff/bun.lock
$(GEN)/truth: $(GEN)/derived $(GEN)/ts $(GEN)/host-protocol $(TRUTH_SOURCES) $(LEAN_INPUTS)
	$(call build_imports,harness/truth/Truth.lean)
	$(LAKE) env lean -M4096 $(call native_flags,harness/truth/Truth.lean) --run harness/truth/Truth.lean harness/truth/corpus.json --tapes harness/truth/tapes
	$(BUN) run harness/truth/run-truth.ts --manifest harness/truth/corpus.json --out harness/truth --timeout 300 --tape-out harness/truth/tapes
	@mkdir -p $(GEN) && touch $@

$(GEN)/host-protocol: $(GEN)/derived tools/Tools/HostProtocol.lean $(CORE_SOURCES)
	$(LAKE) build Effect4.Api.HostSession
	$(call build_imports,tools/Tools/HostProtocol.lean)
	$(LAKE) env lean -M4096 --run tools/Tools/HostProtocol.lean harness/truth/session
	@mkdir -p $(GEN) && touch $@

SCHEMA_TS_DIR := harness/schema-generation
$(GEN)/schema-ts: $(GEN)/derived $(wildcard $(SCHEMA_TS_DIR)/Emit*.lean) $(LEAN_INPUTS)
	$(call build_imports,$(wildcard $(SCHEMA_TS_DIR)/Emit*.lean))
	$(LAKE) env lean -M4096 $(SCHEMA_TS_DIR)/EmitFixture.lean > $(SCHEMA_TS_DIR)/Person.generated.ts
	$(LAKE) env lean -M4096 $(SCHEMA_TS_DIR)/EmitCoverageFixture.lean > $(SCHEMA_TS_DIR)/AllRepresentations.generated.ts
	$(LAKE) env lean -M4096 $(SCHEMA_TS_DIR)/EmitMultiFixture.lean > $(SCHEMA_TS_DIR)/TwoRoots.generated.ts
	@mkdir -p $(GEN) && touch $@

# The runtime behaviour census is cut from the vendored rc.112 sources; its producer
# prints the table.
generated/effect-runtime-census.tsv: scripts/generate-effect-runtime-census.sh $(VENDOR_SOURCES)
	bash scripts/generate-effect-runtime-census.sh > $@
$(GEN)/census: generated/effect-runtime-census.tsv
	@mkdir -p $(GEN) && touch $@

# The semantics report (generated/semantics.md): the registry's claims checked against the
# loaded roots and rendered once. Pure Lean, no host; the JSON form is a build artifact under
# .lake/gen/semantics-report. It reads no other generation group, so it is a hermetic group of
# its own and `check-gen` holds its drift like any other committed generated file.
# The registry's Test roots are loaded beside Effect4.Laws (`registry.roots`): two program
# batteries, the five acceptance programs (decisions row 206) and the scenario modules that hold
# a placed claim (decisions row 254). The recipe builds exactly these roots and the report, and
# the group depends on the Lean sources, never on `build`: until 2026-10-09 it depended on the
# roots' traces, whose rule is `build`, so every run first built the whole battery and the axiom
# gate. The plan reads the ProofGraph modules. One tool module is a root too: the flow's checked
# reachability (`Tools.View.FlowReach`), which imports the summary law; it holds the pointers of
# the claims `dependency-summary-exact` and `view-reachability-summary-exact`.
SEMANTICS_TOOL_ROOTS := Tools.View.FlowReach
SEMANTICS_DOGFOOD_NAMES := P1HttpCache P2HandlerLayers P3WorkerQueue P4RateLimiter P5LedgerService \
  Bank
SEMANTICS_DOGFOOD := $(foreach m,$(SEMANTICS_DOGFOOD_NAMES),Test.Dogfood.$(subst /,.,$(m)))

# The engine's fixtures (decisions rows 254 and 255; the group `fixtures` of docs/GENERATED.md).
# A lane is a folder under ocaml/engine/test/ with a writer, write.lean: a Lean script that
# writes the lane's *.txt from the programs `Api.Author.build` admits. The engine's dune test
# reads the files, and a Lean battery binds each by `include_str`. Lake does not take such a
# file as an input, so a fixture that changed alone left the battery's evidence stale. Here the
# marker depends on the fixtures, writers and the writers' source closures. A fixture
# that changes alone is written again from Lean, and `check-gen` refuses a committed fixture
# that Lean does not write.
#
# The rule does not wait for `build`. When a program changes, the binding battery refuses the
# old fixture, so the default build is red until the fixture is written again. The producer
# builds the modules that a writer imports, and no other. Until 2026-10-06 the marker depended
# on those modules' traces, whose rule is `build`: the group could not repair the staleness that
# made the build fail.
ENGINE_FIXTURE_WRITERS := $(wildcard ocaml/engine/test/*/write.lean)

# The root Tools.View.FlowReach imports the view, graph and code planes: their files stale the
# report (a superset of the closure, so no edit is missed). The report writes its document as
# JSON; the site's shell, its rules and its other pages are the site's (the target `site`).
SEMANTICS_SOURCES := tools/Tools/Semantics.lean tools/Drivers/Semantics.lean \
  tools/Tools/SemanticsDocument.lean tools/Tools/Document.lean tools/Tools/Document/Json.lean \
  $(wildcard tools/Tools/View/*.lean tools/Tools/Graph/*.lean tools/Tools/Code/*.lean) \
  tools/Tools/SemanticsDisplay.lean tools/Tools/GeneratedStamp.lean src/Effect4/Laws/Auto/Semantics.lean \
  $(wildcard tools/ProofGraph/*.lean) \
  Test/Counterexamples/REGISTER.md docs/core/decisions.md lean-toolchain lakefile.toml
$(GEN)/semantics: $(SEMANTICS_SOURCES) $(LEAN_INPUTS)
	$(LAKE) build semantics-report Effect4.Laws Test.Program.TypedProgBindRed $(SEMANTICS_DOGFOOD) $(SEMANTICS_TOOL_ROOTS)
	rm -rf $(GEN)/semantics-report && mkdir -p $(GEN)/semantics-report
	$(LAKE) exe semantics-report $(GEN)/semantics-report
	cp $(GEN)/semantics-report/semantics.md generated/semantics.md
	@mkdir -p $(GEN) && touch $@

# The documentation site (decisions row 363): standard files only, every page checked by the HTML
# Standard's content model, each with its document as JSON. The site is one value
# (tools/Tools/Site.lean); tools/Drivers/Site.lean builds it from the semantics report's document,
# which the semantics group writes when its sources change, so an edit of the shell, the rules or
# a page of the site's own runs in seconds. The written copy (docs/site/) and the specimen pass the
# controlled-English check (decisions row 366, point 8); the report's pages, whose words come from
# the registry and the docstrings, are counted. A fresh folder replaces the old one whole.
# The site's written copy (docs/site/README.md): Markdown that a writer edits and every build reads.
SITE_COPY := $(shell find docs/site -name '*.md' 2>/dev/null | sort)
.PHONY: site
site: $(GEN)/semantics ## the documentation site into .lake/gen/site (Lean's pages, CSS files, the JSON contract)
	$(call build_imports,tools/Drivers/Site.lean)
	rm -rf $(GEN)/site-next && mkdir -p $(GEN)/site-next
	$(LAKE) env lean --run tools/Drivers/Site.lean $(GEN)/site-next $(GEN)/semantics-report
	$(PY) scripts/check-language.py --strict $(SITE_COPY) $(GEN)/site-next/specimen/index.md
	@echo "site: $$($(PY) scripts/check-language.py --show $$(find $(GEN)/site-next/semantics -name index.md) | grep -c '^$(GEN)') language findings in the report's pages, from the registry's words and the docstrings"
	rm -rf $(GEN)/site && mv $(GEN)/site-next $(GEN)/site
	@echo "site: $(GEN)/site"

# Publish the site from this Mac through wrangler's own sign-in (`wrangler login`, once): no API
# token and no repository secret. Cloudflare Pages project effect4-docs, production (decisions row 363).
.PHONY: deploy-site
deploy-site: site ## publish .lake/gen/site to Cloudflare Pages (effect4-docs) with wrangler's sign-in
	wrangler pages deploy $(GEN)/site --project-name=effect4-docs --branch=main \
	  --commit-hash=$$(git rev-parse HEAD) --commit-message="$$(git log -1 --format=%s)"

# The lanes' inventory: every fixture and every writer, by path. A wildcard prerequisite does
# not remember a path that left, so the list itself is a prerequisite. It changes when a fixture
# or a writer is added, removed or renamed (the pattern of $(CHK)/inventory), and the producer
# then refuses a fixture folder that has no writer.
$(GEN)/fixtures-inventory: FORCE
	@mkdir -p $(GEN); printf '%s\n' $(sort $(wildcard ocaml/engine/test/*/*.txt) $(ENGINE_FIXTURE_WRITERS)) > $@.new; \
	  if cmp -s $@.new $@; then rm -f $@.new; else mv $@.new $@; fi
# The writers' inputs are the sources of their import closure (`scripts/lean-imports.py --closure`):
# an edit outside it, to the LCNF route or the conformance tools, rewrites no fixture (LC-4).
FIXTURE_OUT := $(sort $(wildcard ocaml/engine/test/*/*.txt) $(filter %.txt,$(shell git ls-files -- ocaml/engine/test)))
FIXTURE_KEY = $(PY) scripts/gate-cache.py key gen-fixtures --runtime lean --inputs $(CHECK_CACHE_SOURCES) $(GEN)/fixtures-inventory scripts/generate.py scripts/lib/derived_plan.py --lean $(ENGINE_FIXTURE_WRITERS) --outputs $(FIXTURE_OUT)
$(CHK)/gen-fixtures.key: FORCE $(GEN)/fixtures-inventory
	@$(FIXTURE_KEY)
$(GEN)/fixtures: $(CHK)/gen-fixtures.key
	$(PY) scripts/generate.py --only fixtures
	@$(FIXTURE_KEY)
	@mkdir -p $(GEN) && touch $@

# The groups generate.py can regenerate into a temporary directory (no host runtime).
HERMETIC_GROUPS := variances derived eff wire cas ts readme semantics fixtures
# `gen`'s order, which is the producers' order above; lcnf is named here, between derived
# and eff, and nowhere in HERMETIC_GROUPS.
GEN_GROUPS := variances derived lcnf eff wire cas ts readme truth host-protocol schema-ts census semantics fixtures

.PHONY: gen gen-hermetic $(addprefix gen-,$(GEN_GROUPS)) clean-gen
gen: $(addprefix $(GEN)/,$(GEN_GROUPS)) ## regenerate every stale generated group, in order
gen-hermetic: $(addprefix $(GEN)/,$(HERMETIC_GROUPS)) ## the Lean-only groups (no host runtime)
# one group: make gen-eff, make gen-truth, ...
$(addprefix gen-,$(GEN_GROUPS)): gen-%: $(GEN)/%
clean-gen: ## forget the generation markers (the next `make gen` re-cuts everything)
	rm -rf $(GEN)

# Every committed path a generator writes. The drift check diffs exactly these.
GENERATED_PATHS := $(DERIVED_OUT) $(VARIANCES) src/Effect4/Program/TyVariance.lean \
  ocaml/eff ocaml/goldens/eff ocaml/engine/cas/goldens \
  $(LCNF_OUT) \
  ts/eff/eff.gen.ts ts/eff/json.gen.ts ts/eff/profile.gen.ts ts/eff/taxonomy.gen.ts ts/eff/names.gen.ts ts/eff/forms.gen.ts \
  ts/eff/wire.gen.ts ts/eff/packages.gen.ts ts/eff/templates.gen.ts ts/eff/test/type-projection.gen.json ts/eff/ingest/README.md \
  harness/truth/prelude-atoms.gen.ts \
  harness/truth/corpus.json harness/truth/generated harness/truth/result.json harness/truth/result.md \
  harness/truth/tapes harness/truth/session/protocol.gen.ts harness/truth/session/tape.schema.json \
  $(SCHEMA_TS_DIR)/Person.generated.ts $(SCHEMA_TS_DIR)/AllRepresentations.generated.ts $(SCHEMA_TS_DIR)/TwoRoots.generated.ts \
  generated/effect-runtime-census.tsv generated/corpus-index.tsv generated/row-types.tsv generated/assignability.tsv generated/row-citations.tsv \
  generated/semantics.md \
  ocaml/engine/test/*/*.txt

# ---------------------------------------------------------------------------- corpus
#
# The printed corpus: 400 programs of Lean's seeded generator (Test/Program/Gen.lean) and
# the wire corpus, printed by tools/Drivers/Corpus.lean as TypeScript beside the JSON and
# the canonical bytes of the program Lean's own reader kept, with Lean's typing verdict
# per program in index.tsv. Its content key follows the driver's source closure and outputs.
# The OCaml engine differential reads the directory through E4_LEAN_CORPUS.
# The index (one row per program: name, wellTyped, readable, chars) is also installed as
# generated/corpus-index.tsv, the committed expected file that names every program whose
# verdict a change moved (DI-60); check-gen holds it.

CORPUS := .lake/corpus
export E4_LEAN_CORPUS := $(abspath $(CORPUS))
export EFFECT4_CORPUS := $(abspath $(CORPUS))

CORPUS_KEY = $(PY) scripts/gate-cache.py key gen-corpus --runtime lean --inputs $(CHECK_CACHE_SOURCES) scripts/generate.py --lean Drivers.Corpus --outputs $(CORPUS) generated/corpus-index.tsv
$(CHK)/gen-corpus.key: FORCE
	@$(CORPUS_KEY)
$(CORPUS)/index.tsv: $(CHK)/gen-corpus.key
	$(LAKE) build Drivers.Corpus
	rm -rf $(CORPUS) && mkdir -p $(CORPUS)
	$(LAKE) env lean -DwarningAsError=true -M4096 $(call native_flags,tools/Drivers/Corpus.lean) --run tools/Drivers/Corpus.lean $(CORPUS) 400 4
	{ printf '# GENERATED by make corpus (tools/Drivers/Corpus.lean over Test/Program/Gen.lean and the wire corpus); do not edit\n# name\twellTyped\treadable\tchars\treason\tpath\tcodes\n'; cat $(CORPUS)/index.tsv; } > generated/corpus-index.tsv
	@$(CORPUS_KEY)
	@touch $@

.PHONY: corpus
corpus: $(CORPUS)/index.tsv ## the printed corpus under .lake/corpus (Lean's 400 programs and the wire corpus)

# The pinned install is a local producer. A content key prevents same-byte checkouts
# from reinstalling packages. Linked installs are validated and never changed here.
TS_INSTALLED_MANIFESTS = $(shell if test -d ts/eff/node_modules; then find -L ts/eff/node_modules -name package.json -type f; fi)
TS_INSTALL_KEY = $(PY) scripts/gate-cache.py key gen-ts-install --runtime none --environment BUN --inputs $(CHECK_CACHE_SOURCES) scripts/check-lock-install.py ts/eff/package.json ts/eff/bun.lock --outputs $(TS_INSTALL)
$(CHK)/gen-ts-install.key: FORCE
	@$(TS_INSTALL_KEY)
$(GEN)/ts-install: $(CHK)/gen-ts-install.key
	@if [ ! -L ts/eff/node_modules ]; then (cd ts/eff && $(BUN) install --frozen-lockfile); fi
	$(PY) scripts/check-lock-install.py .
	@$(TS_INSTALL_KEY)
	@mkdir -p $(GEN) && touch $@
ts/eff/node_modules: | $(GEN)/ts-install
	@test -d $@

# The truth harness and the schema codec resolve Effect and the compiler through
# harness/truth/node_modules, a link to that install (never a second install: the truth
# runner refuses a link that selects a different one).
harness/truth/node_modules: | ts/eff/node_modules
	ln -s ../../ts/eff/node_modules $@

# The to-do application (`apps/todo/`, decisions row 378 (15)) resolves Effect through its own link
# to that install, as the truth harness does.
apps/todo/node_modules: | ts/eff/node_modules
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
	@printf 'schema-host %s\n' "$$(test -d harness/schema-host/node_modules/effect && echo 'installed (typescript 7.0.2, tsgo)' || echo 'missing: npm ci --prefix harness/schema-host (check-schema-ts)')"

# ---------------------------------------------------------------------------- checks

CHECKS := roots native compiler ts-reader truth truth-release target schema-codec ocaml ingest-smoke \
  host-protocol service-identity census schema-ts schema-pins tools corpus tsgo tsdiag semantics docs language
.PHONY: check check-ts check-full check-sweep check-gen check-gen-full clean-check FORCE $(addprefix check-,$(CHECKS))
FORCE:

# The aggregates hold only the gates that test behaviour (owner, 2026-10-10): the proofs, and the
# runs compared with an outside implementation. The batteries, the axiom gate over the whole tree,
# the ratchets, the policies, the drift and the document checks stay callable by name, at a sweep.
check: build ## after a change: the core and the law graph; audit the landing's modules with `#axiom_audit`
.PHONY: batteries-touched
batteries-touched: ## the batteries a change against BASE (default HEAD) edits or names, read from Lean's .ilean references (build the edited modules first); the whole run is the sweep's
	@set -e; mods="$$($(PY) scripts/lean-imports.py --touched --base $(or $(BASE),HEAD))"; \
	if [ -z "$$mods" ]; then echo "batteries-touched: no battery reached"; \
	else echo "batteries-touched: $$(echo $$mods | wc -w | tr -d ' ') batteries"; $(LAKE) build $$mods; fi
check-ts: $(addprefix $(CHK)/,tsgo schema-codec schema-ts truth target ts-reader corpus tsdiag host-protocol ingest-smoke service-identity) ## every comparison with Effect and tsgo 7
check-ocaml: $(addprefix $(CHK)/,native compiler ocaml) ## every comparison on the OCaml route
check-full: check check-ts check-ocaml ## the build and every outside oracle
check-sweep: $(addprefix $(CHK)/,roots docs language semantics census schema-pins tools) check-gen $(if $(EFFECT4_RELEASE_NODE_MODULES),$(CHK)/truth-release) ## batteries, axioms, drift and documents

# Drift: regenerate the stale Lean-only groups, then refuse any change to a committed
# generated file. `check-gen-full` re-cuts every group, the host-cut ones included,
# without trusting file times.
define refuse_drift
	git diff --exit-code --stat -- $(GENERATED_PATHS)
	@untracked="$$(git status --porcelain -- $(GENERATED_PATHS) | grep '^??' || true)"; \
	  if [ -n "$$untracked" ]; then echo "FAIL check-gen: untracked generated files:"; echo "$$untracked"; exit 1; fi
endef

# The kernel rung, at a sweep only: every compiled Effect4 and Test declaration in the closure of the
# battery roots, replayed through the kernel into one environment of their dependencies
# (tools/Drivers/KernelReplay.lean). Never a bare `leanchecker`: it holds one environment per core.
check-kernel: ## (sweep) replay every compiled Effect4 and Test declaration through the kernel, after its self-test
	$(LAKE) build kernel-replay Test
	$(LAKE) exe kernel-replay --self-test
	$(LAKE) exe kernel-replay Test

check-gen: gen-hermetic $(CORPUS)/index.tsv ## regenerate the stale Lean-only groups and the corpus index; refuse a changed committed file
	$(refuse_drift)
	@echo 'PASS check-gen: every Lean-only generated file is what its generator emits'

check-gen-full:
	$(MAKE) -B gen
	$(refuse_drift)
	@echo 'PASS check-gen: every generated file is what its generator emits'

# one check: make check-roots, make check-truth, ...
$(addprefix check-,$(CHECKS)): check-%: $(CHK)/%
clean-check: ## forget local check markers and interrupted truth runs; retain shared passes
	@mkdir -p $(CHK)
	find $(CHK) -maxdepth 1 -type f ! -name 'gen-*' -delete
	rm -rf harness/truth/truth-check-*

# Make owns dependency order and commands. The cache hashes source closures, bytes,
# tool versions and these recipes. Old Lean traces never stand in for changed sources.
CHECK_CACHE_SOURCES := Makefile scripts/gate-cache.py scripts/lib/gate_cache.py scripts/lib/lean_imports.py
CHECK_ENVIRONMENT := LAKE BUN NODE PY OPAM_SWITCH OCAML OCAMLOPT TSGO_HOME E4_LEAN_CORPUS \
  EFFECT4_BUN EFFECT4_NODE EFFECT4_CORPUS EFFECT4_EFFECT_NODE_MODULES EFFECT4_RELEASE_NODE_MODULES \
  EFFECT4_GEN_TIMEOUT EFFECT4_OPAM_SWITCH EFFECT4_PROGRAM EFFECT4_TAPE \
  EFFECT4_RUNTIME_CENSUS_CANDIDATE EFFECT4_RUNTIME_CENSUS_ROWS EFFECT4_RUNTIME_CENSUS_SOURCE
export $(foreach v,$(CHECK_ENVIRONMENT),$(if $(filter undefined,$(origin $(v))),,$(v)))
TS_PINS := ts/eff/package.json ts/eff/bun.lock \
  $(if $(TSGO_HOME),$(TSGO_HOME)/package.json) \
  $(if $(EFFECT4_EFFECT_NODE_MODULES),$(wildcard $(addprefix $(EFFECT4_EFFECT_NODE_MODULES)/,effect/package.json @effect/sql-sqlite-bun/package.json @typescript/native-preview/package.json)))
TS_INSTALL = ts/eff/node_modules/effect/package.json ts/eff/node_modules/@typescript/native-preview/package.json $(TS_INSTALLED_MANIFESTS)
SCHEMA_INSTALL := $(addprefix $(or $(EFFECT4_EFFECT_NODE_MODULES),harness/schema-host/node_modules)/,effect/package.json typescript/package.json @effect/tsgo/package.json)

# Arguments: step, runtime, file inputs, Lean entries. Prerequisites that produce inputs
# are attached to the key below. Only a successful command publishes a shared pass.
define cached_check
$(CHK)/$(1).key: FORCE
	@$$(PY) scripts/gate-cache.py key $(1) --runtime $(2) --environment $$(CHECK_ENVIRONMENT) --inputs $$(CHECK_CACHE_SOURCES) $(3) --lean $(4)
$(CHK)/$(1): $(CHK)/$(1).key
	@$$(PY) scripts/gate-cache.py run $$(if $$(findstring B,$$(firstword $$(MAKEFLAGS))),--force,) $(1) -- $$(MAKE) --no-print-directory _run-$(1)
.PHONY: _run-$(1)
endef

# A fresh elaboration of Test/All.lean sees a new orphan source file even when Lake's
# roots are cached; the compiled import graph and the source inventory are AxiomGate's.
# The audit itself already runs inside `lake build` (Test.All re-elaborates whenever a
# module it imports changed), so the fresh elaboration is keyed on the source inventory:
# it re-runs when a file is added, removed or renamed, not on every edit.
$(CHK)/inventory: FORCE
	@mkdir -p $(CHK); printf '%s\n' $(sort $(LEAN_SOURCES)) > $@.new; \
	  if cmp -s $@.new $@; then rm -f $@.new; else mv $@.new $@; fi
$(eval $(call cached_check,roots,lean,$(CHK)/inventory lakefile.toml lean-toolchain,Test.All))
$(CHK)/roots.key: $(CHK)/inventory
_run-roots:
	$(LAKE) build Test
	$(LAKE) env lean -DwarningAsError=true Test/All.lean
	@echo 'PASS check-roots: the module-closure, library-root and axiom gates'

# One TypeScript compiler, tsgo 7 (AGENTS.md; decisions rows 57 and 168): no `typescript` package below
# 7 is installed under ts/, harness/ or tools/. The recipe is receipt J's line (step 7 (iii)); the
# marker reads the installed manifest inventory and the manifests and locks that fill it.
check-tsgo:
TSGO_INPUTS = $(shell find -L ts harness tools -path '*/node_modules/typescript/package.json' -print) \
  $(wildcard ts/*/package.json ts/*/bun.lock harness/*/package.json harness/*/package-lock.json harness/*/bun.lock tools/*/package.json)
$(eval $(call cached_check,tsgo,none,$(TSGO_INPUTS),))
_run-tsgo:
	@$(PY) -c 'import json,pathlib,sys; v=lambda p: json.loads(p.read_text())["version"]; bad=[p.as_posix()+": "+v(p) for r in ("ts","harness","tools") for p in sorted(pathlib.Path(r).rglob("node_modules/typescript/package.json")) if int(v(p).split(".")[0]) < 7]; print("\n".join(["FAIL check-tsgo: typescript below 7 (tsgo 7 is the one compiler):"]+bad) if bad else "PASS check-tsgo: no typescript below 7 under ts/, harness/ or tools/"); sys.exit(1 if bad else 0)'

# The authority documents (every tracked Markdown file that is not history) name paths, links,
# `git:<rev>:<path>` citations and make targets; each must resolve (scripts/lib/doc_refs.py). Keyed
# on the documents, the Makefile, the checker and the tracked-path inventory, so a deleted or moved
# file re-runs it the way a new Lean file re-runs the root audit.
DOCS := $(wildcard $(shell git ls-files -- '*.md' ':!docs/research' ':!vendor'))
$(CHK)/paths: FORCE
	@mkdir -p $(CHK); git ls-files > $@.new; \
	  if cmp -s $@.new $@; then rm -f $@.new; else mv $@.new $@; fi
$(eval $(call cached_check,docs,none,$(CHK)/paths $(DOCS) Makefile scripts/check-docs.py scripts/lib/doc_refs.py,))
$(CHK)/docs.key: $(CHK)/paths
.PHONY: repair-docs
repair-docs:
	$(PY) scripts/check-docs.py --fix
$(CHK)/docs.key: repair-docs
_run-docs:
	$(PY) scripts/check-docs.py

# The controlled English (docs/core/controlled-english.md): the checker's red and green controls,
# then strict mode on the specification and AGENTS.md. The other documents are reported, never
# refused, until a later slice normalizes them (`python3 scripts/check-language.py` prints the
# report). The rules and the dictionary are read from the specification itself. Keyed on the
# documents, the checker, the tracked-path inventory and the Lean sources the dictionary's anchors
# name, so a renamed declaration re-runs it. Not in `make check` yet.
LANGUAGE_SOURCES := scripts/check-language.py scripts/lib/language.py scripts/lib/doc_refs.py \
  $(LEAN_SOURCES) $(wildcard $(shell git ls-files --cached --others --exclude-standard -- 'tools/*.lean'))
$(eval $(call cached_check,language,none,$(CHK)/paths $(DOCS) $(LANGUAGE_SOURCES),))
$(CHK)/language.key: $(CHK)/paths
_run-language:
	$(PY) scripts/check-language.py --self-test
	$(PY) scripts/check-language.py --strict docs/core/controlled-english.md AGENTS.md

$(eval $(call cached_check,native,lean,scripts/check-conform.py scripts/lib/conform_report.py,tools/Conform/Effect4/NativeMain.lean))
_run-native:
	$(PY) scripts/check-conform.py native

$(eval $(call cached_check,compiler,ocaml,scripts/check-conform.py scripts/lib/conform_report.py,tools/Conform/Effect4/Normalization.lean))
_run-compiler:
	$(PY) scripts/check-conform.py compiler

# The TypeScript reader against Lean's reader: every `.ts` of the corpus and of the truth
# lane's exported modules must read back to the JSON Lean's own reader kept (`--oracle`),
# then the package's type check and its pinned cases.
TRUTH_GENERATED := harness/truth/corpus.json harness/truth/result.json harness/truth/result.md $(wildcard harness/truth/generated/*.ts)
$(eval $(call cached_check,ts-reader,ts,$(CORPUS) $(TS_EFF_SOURCES) $(TRUTH_GENERATED) $(PRELUDE_SOURCES) $(TS_PINS) $(TS_INSTALL),))
$(CHK)/ts-reader.key: $(CORPUS)/index.tsv | ts/eff/node_modules
_run-ts-reader:
	cd ts/eff && $(BUN) run check.ts $(abspath $(CORPUS)) $(abspath harness/truth/generated) --oracle $(abspath $(CORPUS))
	cd ts/eff && $(BUN) run typecheck
	cd ts/eff && $(BUN) test

# The host controls beside the lane: rc.112's `catchIf` clause, the prelude's cause queries,
# and the inventory guard (every generated atom has a prelude case that runs). Named one by
# one, as exact paths (`./`): a bare name is a filter, which also matches a copy under docs/research.
TRUTH_HOST_TESTS := harness/truth/records.test.ts harness/truth/catch-if.test.ts harness/truth/native-queries.test.ts harness/truth/prelude-inventory.test.ts harness/truth/if-case.test.ts
$(eval $(call cached_check,truth,ts,$(TRUTH_SOURCES) $(TRUTH_GENERATED) $(wildcard harness/truth/session/*.ts) scripts/check-truth.py scripts/lib/truth_host.py harness/truth/tsconfig.json harness/truth/records.typecheck.ts harness/truth/tuples.typecheck.ts harness/truth/tuples.ts harness/truth/folds.typecheck.ts harness/truth/term-rows.typecheck.ts harness/truth/literals.typecheck.ts harness/truth/queue-steps.typecheck.ts harness/truth/mask.typecheck.ts harness/truth/P2b.lean tools/target/checker.ts tools/target/oracle.ts $(TRUTH_HOST_TESTS) harness/truth/prelude-inventory.ts ts/eff/profile.gen.ts $(TS_PINS) $(TS_INSTALL),harness/truth/Truth.lean harness/truth/P2b.lean))
$(CHK)/truth.key:  | harness/truth/node_modules ts/eff/node_modules
_run-truth:
	$(call build_imports,harness/truth/Truth.lean harness/truth/P2b.lean)
	$(BUN) test $(addprefix ./,$(TRUTH_HOST_TESTS))
	$(PY) scripts/check-truth.py

# The release lane (decisions row 248; harness/truth/RELEASE-LANE.md): the truth harness's host phase
# on effect@4.0.1 beside the pinned run, judged by the build ledger (harness/truth/build-ledger.tsv:
# each program's expected agreement with each build; build-ledger.run.json: what those entries
# were measured on). It reads the committed manifest, result and tapes, which the pinned lane holds
# to a fresh run, so the pinned marker is its prerequisite; the rest is what it reads besides. The
# release install is selected by EFFECT4_RELEASE_NODE_MODULES only (no default, no download; bun
# runs with --no-install), and its manifests are prerequisites when the variable names one. Its
# controls run first, and the pinned lane's host tests run on both builds. `make gen-truth-ledger`
# promotes a fresh host run to the two committed files (the hand columns `reason` and `slice` are
# kept). Not in `check` and not in `check-full`: no tracked recipe installs the release.
TRUTH_RELEASE_LANE := scripts/check-truth-release.py scripts/lib/truth_ledger.py scripts/lib/truth_host.py \
  harness/truth/build-ledger.tsv harness/truth/build-ledger.run.json \
  harness/truth/select-controls.ts harness/truth/tuples.typecheck.ts harness/truth/tuples.ts \
  ts/eff/eff.gen.ts ts/eff/tsconfig.json \
  $(wildcard $(addprefix $(EFFECT4_RELEASE_NODE_MODULES)/,effect/package.json \
    @effect/sql-sqlite-bun/package.json @typescript/native-preview/package.json))
# Which install the variable names is an input too: the marker is stale when the name changes or goes.
$(CHK)/truth-release-install: FORCE
	@mkdir -p $(CHK); printf '%s\n' '$(EFFECT4_RELEASE_NODE_MODULES)' > $@.new; \
	  if cmp -s $@.new $@; then rm -f $@.new; else mv $@.new $@; fi
$(eval $(call cached_check,truth-release,ts,$(CHK)/truth $(TRUTH_RELEASE_LANE) $(CHK)/truth-release-install $(TS_PINS) $(TS_INSTALL),))
$(CHK)/truth-release.key: $(CHK)/truth $(CHK)/truth-release-install | ts/eff/node_modules
_run-truth-release:
	$(PY) scripts/check-truth-release.py --self-test
	$(PY) scripts/check-truth-release.py --host-tests $(TRUTH_HOST_TESTS)

.PHONY: gen-truth-ledger
gen-truth-ledger: $(CHK)/truth ## promote a fresh host run of both builds to harness/truth/build-ledger.tsv and build-ledger.run.json
	$(PY) scripts/check-truth-release.py --promote --host-tests $(TRUTH_HOST_TESTS)

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
$(eval $(call cached_check,corpus,ts,$(TRUTH_SOURCES) $(CORPUS_LANE) $(TS_PINS) $(TS_INSTALL),harness/truth/Truth.lean))
$(CHK)/corpus.key:  | harness/truth/node_modules ts/eff/node_modules
_run-corpus:
	$(call build_imports,harness/truth/Truth.lean)
	$(PY) scripts/check-corpus.py

.PHONY: gen-corpus-results
gen-corpus-results: | harness/truth/node_modules ## promote a fresh corpus run to harness/truth/corpus-results.tsv
	$(call build_imports,harness/truth/Truth.lean)
	$(PY) scripts/check-corpus.py --promote

# The architecture map (docs/GENERATED.md, group `architecture`): measured from the tree by a
# Lean driver that parses every import header, loads the roots for declaration counts and
# walks the estates; the role register tools/Tools/ArchitectureRoles.lean is its one hand
# input. Its proof graph is drawn from the semantics report's JSON, which gen-semantics writes.
# A report under .lake/gen, never committed and not in `check`. The view's input check runs first,
# on the report and on broken copies of it (scripts/check-proofgraph-input.mjs).
.PHONY: gen-architecture
# The Rocq workspace's generated inputs (rocq/README.md): the program types, rocq-of-ocaml over
# the components of ocaml/eff/eff_types.ml (rocq/tools/split_types.ml), and the call tree's
# skeleton, printed from Effect4.Run.Tree's base-phase LCNF (OCaml5.Lcnf.Gallina). It needs the
# opam switch `rocq`. No gate runs it; rocq/README.md gives the compile that checks the proofs.
ROCQ_TMP := $(GEN)/rocq-types
.PHONY: gen-rocq
gen-rocq: ## regenerate rocq/Eff_types.v, rocq/Skeleton.v and rocq/StoreCode.v (the opam switch rocq)
	$(LAKE) build Effect4.Run.Tree Effect4.Store.Domain.Word OCaml5.Lcnf.Gallina
	$(LAKE) env lean -M4096 --run src/OCaml5/Tools/GallinaGen.lean rocq/Skeleton.v rocq/StoreCode.v
	@rm -rf $(ROCQ_TMP) && mkdir -p $(ROCQ_TMP) && cp rocq/tools/split_types.ml $(ROCQ_TMP)/
	cd $(ROCQ_TMP) && opam exec --switch=rocq -- ocamlfind ocamlopt -package compiler-libs.common -linkpkg split_types.ml -o split_types
	$(ROCQ_TMP)/split_types ocaml/eff/eff_types.ml > $(ROCQ_TMP)/eff_types.ml
	cd $(ROCQ_TMP) && opam exec --switch=rocq -- ocamlfind ocamlc -bin-annot -c eff_types.ml && opam exec --switch=rocq -- rocq-of-ocaml -output Eff_types.v eff_types.ml
	{ printf '(* GENERATED by `make gen-rocq` (rocq-of-ocaml over rocq/tools/split_types.ml of ocaml/eff/eff_types.ml). Do not edit. *)\n\n'; cat $(ROCQ_TMP)/Eff_types.v; } > rocq/Eff_types.v

.PHONY: gen-store-rocq
gen-store-rocq: ## regenerate StoreCode and check unchanged Skeleton; keep Eff_types
	$(PY) scripts/generate.py --only store-rocq

gen-architecture: gen-semantics | build ## the architecture map, measured from the tree, into .lake/gen/architecture-map.html (a report)
	node scripts/check-proofgraph-input.mjs
	$(LAKE) build architecture-map
	@mkdir -p $(GEN)
	$(LAKE) exe architecture-map --out $(GEN)/architecture-map.html

# T0: the printed programs' answer, error and requirement types against the one compiler
# (tsgo, decisions row 57; tools/target). The oracle reads the truth modules and their
# prelude, the generated TypeScript tables, the package's compiler config, manifest and
# install, and the toolchain file; each is a prerequisite so a change to any of them re-runs
# it. The oracle's own compiler side runs under node (tools/target/checker.ts).
#
# Three steps before the report. The row lane's expected columns are Lean's own rendering
# (generated/row-types.tsv, tools/Tools/RowTypes.lean): the lane refuses a stale one rather
# than reading it, since a stale signature is a wrong expectation, not a missing one. Then
# the tool type-checks itself under the same compiler it drives — nothing did before, and
# `renderTy`, the hand copy of the printer it replaced, had fallen four constructors behind.
$(eval $(call cached_check,target,ts,$(TRUTH_GENERATED) $(PRELUDE_SOURCES) Test/fixtures/target/selection.json $(wildcard tools/target/*.ts tools/target/*.json) tools/Tools/RowTypes.lean tools/Tools/TypeSpelling.lean generated/row-types.tsv tools/Tools/TyVectors.lean generated/assignability.tsv ts/eff/profile.gen.ts ts/eff/eff.gen.ts ts/eff/packages.gen.ts ts/eff/tsconfig.json ts/eff/package.json lean-toolchain $(TS_PINS) $(TS_INSTALL),tools/Tools/RowTypes.lean tools/Tools/TyVectors.lean))
$(CHK)/target.key:  | ts/eff/node_modules
_run-target:
	$(call build_imports,tools/Tools/RowTypes.lean tools/Tools/TyVectors.lean)
	$(LAKE) env lean -M4096 --run tools/Tools/RowTypes.lean generated/row-types.tsv --check
	$(NODE) ts/eff/node_modules/@typescript/native-preview/bin/tsgo --noEmit -p tools/target/tsconfig.json
	$(BUN) test tools/target
	$(BUN) tools/target/cli.ts --repo .
	@mkdir -p .lake/target && $(LAKE) env lean -M4096 --run tools/Tools/TyVectors.lean .lake/target/ty-vectors.tsv
	$(BUN) tools/target/assignability.ts --repo . --vectors .lake/target/ty-vectors.tsv
	$(BUN) tools/target/rows.ts --repo .

.PHONY: gen-assignability
gen-assignability: ## promote a fresh assignability differential to generated/assignability.tsv
	$(call build_imports,tools/Tools/TyVectors.lean)
	@mkdir -p .lake/target && $(LAKE) env lean -M4096 --run tools/Tools/TyVectors.lean .lake/target/ty-vectors.tsv
	$(BUN) tools/target/assignability.ts --repo . --vectors .lake/target/ty-vectors.tsv --promote

.PHONY: gen-row-citations
gen-row-citations: ## promote a fresh rows/atoms report to generated/row-citations.tsv
	$(BUN) tools/target/rows.ts --repo . --promote

# The schema codec: Lean's `Ty.encode` results for the contract's cases, compared with
# rc.112's `Schema.toCodecJson` on the host, under each case's typed Schema as the code printer
# writes it (`Codegen.SchemaCode`); tsgo checks the generated Schemas and the checker together.
# The fresh module goes to the checker's work folder, which git ignores; nothing committed.
$(eval $(call cached_check,schema-codec,ts,$(wildcard harness/truth/schema-codec/*) $(TS_PINS) $(TS_INSTALL),harness/truth/schema-codec/Emit.lean))
$(CHK)/schema-codec.key:  | harness/truth/node_modules ts/eff/node_modules
_run-schema-codec:
	$(call build_imports,harness/truth/schema-codec/Emit.lean)
	$(LAKE) env lean -M4096 --run harness/truth/schema-codec/Emit.lean harness/truth/schema-codec/.work/values.ts
	$(NODE) harness/truth/node_modules/@typescript/native-preview/bin/tsgo --project harness/truth/schema-codec/tsconfig.json
	$(BUN) harness/truth/schema-codec/check.ts

# The OCaml lane (the effect4 opam switch; local only until the runner has one): the eff
# library's goldens and wire tests, the LCNF route's smoke, the engine's own tests and the
# three-engine differential (which reads the printed corpus), and the engine seam check. It
# depends on the LCNF group, so a change of the machine re-cuts the generated engine before
# the lane builds it (finding N10 of docs/research/2026-10-14-lowering-collation/README.md).
# The seam check also scans core sources for writes that remove fibers. Laws cannot enter the core.
# The lane reads no other core source: the key holds the scan's hits (`--c1-hits`), so an edit
# elsewhere in the core reruns the lane only through the corpus, the fixtures or the LCNF group.
OCAML_SOURCES := $(wildcard $(shell git ls-files --cached --others --exclude-standard -- ocaml)) \
  scripts/check-lcnf-interfaces.py scripts/check-lcnf-sealing.py scripts/lib/lcnf_interfaces.py
$(CHK)/fiber-writes: FORCE
	@mkdir -p $(CHK) && bash ocaml/engine/tools/gen-check.sh --c1-hits > $@.new && \
	  { if cmp -s $@.new $@; then rm -f $@.new; else mv $@.new $@; fi; }
$(eval $(call cached_check,ocaml,ocaml,$(CORPUS) $(OCAML_SOURCES) $(CHK)/fiber-writes $(BUILD_PINS),))
$(CHK)/ocaml.key: $(CORPUS)/index.tsv $(GEN)/fixtures $(GEN)/lcnf $(CHK)/fiber-writes
_run-ocaml:
	cd ocaml && $(OCAML) dune build && $(OCAML) dune test eff gen clock
	cd ocaml && $(OCAML) dune test engine
	$(PY) scripts/check-lcnf-interfaces.py
	$(PY) scripts/check-lcnf-sealing.py
	$(OCAML) bash ocaml/engine/tools/gen-check.sh

# The diagnostics lane (S0 of the printer/reader/positions redesign): every printed corpus
# program as a module under the pinned host configuration (Codegen/Diagnostics.lean writes
# .lake/corpus/tsconfig.json), one native tsgo run, and the agreement between this checker's
# located refusal (Api.explain) and TypeScript's diagnostics, one row per program in
# generated/tsdiag-agreement.tsv (committed; `make gen-tsdiag` promotes a fresh run). The lane
# fails on a program this checker types that TypeScript refuses, and on drift of the table.
$(eval $(call cached_check,tsdiag,ts,$(CORPUS) harness/tsdiag/run-tsdiag.mjs $(wildcard harness/truth/*.ts harness/truth/session/*.ts) ts/eff/profile.gen.ts ts/eff/eff.gen.ts generated/tsdiag-agreement.tsv $(TS_PINS) $(TS_INSTALL),))
$(CHK)/tsdiag.key: $(CORPUS)/index.tsv | ts/eff/node_modules
_run-tsdiag:
	$(NODE) harness/tsdiag/run-tsdiag.mjs $(abspath $(CORPUS)) $(abspath .lake/tsdiag)

.PHONY: check-tsdiag gen-tsdiag
check-tsdiag: $(CHK)/tsdiag
gen-tsdiag: $(CORPUS)/index.tsv | ts/eff/node_modules ## promote a fresh diagnostics run to generated/tsdiag-agreement.tsv
	$(NODE) harness/tsdiag/run-tsdiag.mjs $(abspath $(CORPUS)) $(abspath .lake/tsdiag) --promote

# The ingest smoke: the printed corpus through the foreign recognizer's printed contract.
$(eval $(call cached_check,ingest-smoke,ts,$(CORPUS) $(TS_EFF_SOURCES) $(TS_PINS) $(TS_INSTALL),))
$(CHK)/ingest-smoke.key: $(CORPUS)/index.tsv | ts/eff/node_modules
_run-ingest-smoke:
	$(BUN) ts/eff/ingest/check-corpus.ts printed $(abspath $(CORPUS))

# The keyed lane also performs the scenarios' scripts (decisions row 254), so the batteries that
# `harness/truth/session/Keyed.lean` imports are its inputs, by their sources. It performs the
# to-do's scripts on the to-do's emitted Effect service too (decisions row 378 (20), slice E4), so
# the service's runner and red controls, and the to-do application's writer of the service and its
# consumer (`apps/todo/`), are its inputs. It runs the to-do application on SQLite too (row 378
# (16), slice V4), so the application's front, repository and checker, and the checks they share
# with the keyed lane (`tools/Tools/RunChecks.lean`), are its inputs. The recipe builds what the
# five Lean files that the script runs import, since `lake env` builds nothing.
HOST_PROTOCOL_SERVICE := $(wildcard harness/truth/service/*.ts harness/truth/service/*.json harness/truth/service/red/* apps/todo/*.lean apps/todo/*.ts)
$(eval $(call cached_check,host-protocol,ts,$(wildcard harness/truth/session/*.ts harness/truth/session/*.lean harness/truth/session/*.json) $(HOST_PROTOCOL_SERVICE) $(PRELUDE_SOURCES) tools/Tools/HostProtocol.lean tools/Tools/RunChecks.lean tools/Tools/ProfileJson.lean scripts/check-host-protocol.py $(TS_PINS) $(TS_INSTALL),tools/Tools/HostProtocol.lean harness/truth/session/Keyed.lean harness/truth/session/Session.lean apps/todo/EmitTodo.lean apps/todo/Check.lean))
$(CHK)/host-protocol.key:  | harness/truth/node_modules apps/todo/node_modules ts/eff/node_modules
_run-host-protocol:
	$(call build_imports,tools/Tools/HostProtocol.lean harness/truth/session/Keyed.lean harness/truth/session/Session.lean apps/todo/EmitTodo.lean apps/todo/Check.lean)
	$(PY) scripts/check-host-protocol.py

$(eval $(call cached_check,service-identity,ts,scripts/check-service-identity.py $(PRELUDE_SOURCES) $(wildcard harness/truth/session/*.ts) ts/eff/profile.gen.ts ts/eff/eff.gen.ts ts/eff/packages.gen.ts $(TS_PINS) $(TS_INSTALL),tools/TestSupport/ServiceIdentity.lean))
$(CHK)/service-identity.key: | ts/eff/node_modules
_run-service-identity:
	$(call build_imports,tools/TestSupport/ServiceIdentity.lean)
	$(PY) scripts/check-service-identity.py

$(eval $(call cached_check,census,none,$(VENDOR_SOURCES) generated/effect-runtime-census.tsv Test/Audit/RuntimeCoverage.lean scripts/check-effect-runtime-census.sh scripts/generate-effect-runtime-census.sh,))
_run-census:
	bash scripts/check-effect-runtime-census.sh

# The semantics report's refusal controls: a registry naming an unloaded root, a stale witness or
# a malformed register row is refused with its reason. The report's own drift is `check-gen`'s.
$(eval $(call cached_check,semantics,lean,$(SEMANTICS_SOURCES) tools/Drivers/SemanticsControls.lean $(LEAN_INPUTS),Drivers.SemanticsControls Test.Audit.SemanticsCensus))
_run-semantics:
	$(LAKE) build semantics-controls Test.Audit.SemanticsCensus
	$(LAKE) exe semantics-controls

SCHEMA_SOURCES := $(shell find src/Effect4/Schema -name '*.lean') src/Effect4/Codegen/Schema.lean
# rc.112's own documents and the battery that reads them (slice A1); `include_str` files are not
# in a Lean closure, so the fixtures are named.
SCHEMA_DOCUMENTS := Test/Schema/DocumentJson.lean Test/fixtures/schema-documents/effect-rpc-rc112.json \
  Test/fixtures/schema-representation/observed/06-vectors.observed.json
$(eval $(call cached_check,schema-ts,ts,$(SCHEMA_SOURCES) $(wildcard $(SCHEMA_TS_DIR)/*) $(SCHEMA_DOCUMENTS) scripts/check-schema-typescript-generation.sh $(TS_PINS) $(TS_INSTALL) harness/schema-host/package.json harness/schema-host/package-lock.json $(SCHEMA_INSTALL),$(wildcard $(SCHEMA_TS_DIR)/Emit*.lean) Test/Schema/DocumentJson.lean))
$(CHK)/schema-ts.key:  | ts/eff/node_modules
_run-schema-ts:
	$(call build_imports,$(wildcard $(SCHEMA_TS_DIR)/Emit*.lean) Test/Schema/DocumentJson.lean)
	bash scripts/check-schema-typescript-generation.sh

# The rest of the Schema slice, on its inputs (ledger decision 3): the rc.112 tag pins
# are a textual extraction from the vendored SchemaRepresentation.ts. The retained
# generation gate uses the pinned host (EFFECT4_EFFECT_NODE_MODULES, harness/schema-host).
SCHEMA_PIN := vendor/effect-4.0.0-rc.112/src/SchemaRepresentation.ts
$(eval $(call cached_check,schema-pins,none,$(SCHEMA_PIN) src/Effect4/Schema/Representation.lean scripts/check-schema-census.sh,))
_run-schema-pins:
	bash scripts/check-schema-census.sh $(SCHEMA_PIN)

# The one tool harness: the exact `Classical.choice` admissions against compiled declarations.
SELFTEST_SOURCES := scripts/test-trust-boundaries.sh scripts/status.py scripts/lib/build_profile.py Test/Audit/AxiomGate.lean \
  $(shell find Test/fixtures/trust-gate -type f)
$(eval $(call cached_check,tools,lean,$(SELFTEST_SOURCES) scripts/test-lean-imports.py scripts/test-gate-cache.py scripts/test-wire-roots.py scripts/test-doc-repair.py scripts/wire-roots.py scripts/lib/doc_refs.py,Test.Audit.RuntimeCoverage Test.Program.ConfigContract Test.Audit.SemanticsCensus Conform.Cli.Audit tools/Drivers/ProgramStructureCheck.lean Effect4.Program.Native))
_run-tools:
	$(PY) scripts/test-lean-imports.py
	$(PY) scripts/test-gate-cache.py
	$(PY) scripts/test-wire-roots.py
	$(PY) scripts/test-doc-repair.py
	$(LAKE) build Test.Audit.RuntimeCoverage Test.Program.ConfigContract Test.Audit.SemanticsCensus Conform.Cli.Audit
	$(call build_imports,tools/Drivers/ProgramStructureCheck.lean)
	$(LAKE) env lean --run tools/Drivers/ProgramStructureCheck.lean
	bash scripts/test-trust-boundaries.sh

# ---------------------------------------------------------------------------- help

.PHONY: status
status: ## one screen, measured: HEAD and dirty paths, build and check freshness, generated drift, claims, ledger goals, registers, stale references
	@$(PY) scripts/status.py

.PHONY: help clean
help: ## this list
	@awk 'BEGIN {FS = ":.*## "} /^[a-zA-Z0-9_-]+:.*## / {printf "  %-18s %s\n", $$1, $$2}' $(MAKEFILE_LIST)
	@echo
	@echo '  gen-<group>        one generated group: derived, eff, wire, cas, ts, readme, lcnf,'
	@echo '                     truth, host-protocol, schema-ts, census, semantics'

clean: ## lake clean (drops the build, the generation and check markers)
	$(LAKE) clean
