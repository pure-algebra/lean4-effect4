# The one entry point. `make help` lists the targets.
#
# Four kinds of target:
#   build*   Lake builds; the axiom gate runs inside `lake build Test`.
#   corpus   the printed corpus, a build artifact under .lake/corpus that three checks
#            read (the TypeScript reader, the ingest smoke, the OCaml engine differential).
#   gen-*    the generated files, one rule per group, in the dependency order the
#            producers need. A rule fires when its generator, its inputs, or the
#            compiled core it reads changed; its marker is .lake/gen/<group>.
#   check-*  the checks. `check` is the tier that runs after every change: the build
#            (the axiom gate runs inside it), the fresh root elaboration and the
#            generated-file drift. `check-full` is everything else: the outside oracles
#            (the real Effect runtime, the TypeScript compiler, the OCaml engine), the
#            host groups and the tool harnesses.
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
# The native TypeScript compiler's synchronous client needs node (bun lacks the handle it reads).
NODE ?= node
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
TS_EFF_SOURCES := $(wildcard ts/eff/*.ts ts/eff/test/*.ts ts/eff/ingest/*.ts ts/eff/ingest/test/*.ts) ts/eff/package.json ts/eff/bun.lock ts/eff/tsconfig.json ts/eff/test/type-projection.gen.json
VENDOR_SOURCES := $(wildcard vendor/effect-4.0.0-rc.112/src/*.ts vendor/effect-4.0.0-rc.112/src/internal/*.ts)

# ---------------------------------------------------------------------------- build

.PHONY: build build-tools
build: ## lake build: the core, the proof graph, the batteries and the axiom gate; the log feeds `make build-profile`
	@mkdir -p $(GEN)
	set -o pipefail; $(LAKE) build 2>&1 | tee $(GEN)/build.log

.PHONY: build-profile
build-profile: ## where the last `make build` spent its time: the critical path and the slowest modules (.lake/gen/build-profile.md)
	@$(PY) scripts/build-profile.py $(GEN)/build.log

bank-census: ## every Effect4 aesop rule bank: its rules, simp lemmas and the clauses that name it (an instrument)
	$(LAKE) build Effect4Laws
	$(LAKE) env lean tools/BankCensusRun.lean

profile-module: ## FILE=<src/…/X.lean>: re-elaborate one built module with the profiler and aesop's statistics; summary here, raw logs in .lake/gen/profile/
	@test -n "$(FILE)" || { echo "usage: make profile-module FILE=src/Effect4/Laws/…/X.lean"; exit 2; }
	$(PY) scripts/profile-module.py $(FILE)

build-tools: build ## the generator and checker roots (Tools, OCaml5, Conform, Effect4Gen)
	$(LAKE) build Tools
	$(LAKE) build OCaml5
	$(LAKE) build Conform
	$(LAKE) build Effect4Gen

# ---------------------------------------------------------------------------- gen
#
# The order below is the producers' dependency order: derived writes Lean modules the
# rest import; lcnf cuts the engine face `ocaml/engine/api_engine.ml`; eff cuts the OCaml
# files and the engine structure mirror, which READS that face; ts cuts the TypeScript
# tables the ingest README renders. Each marker depends on the previous one, so a
# regenerated upstream group re-cuts everything downstream of it.
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
.PHONY: variance-output-missing
$(GEN)/variances: $(VARIANCE_SOURCES) $(wildcard $(VARIANCE_OUT)) $(if $(filter-out $(wildcard $(VARIANCE_OUT)),$(VARIANCE_OUT)),variance-output-missing)
	$(PY) scripts/generate.py --only variances
	@mkdir -p $(GEN) && touch $@

DERIVED_SOURCES := $(wildcard tools/Effect4Gen/*.lean tools/Effect4Gen/guards/*.lean) tools/Effect4Gen/manifest.json tools/Effect4Gen/binders.json \
  $(wildcard $(VARIANCES)) $(WIRE_TAGS) tools/Tools/WireTags.lean $(PRODUCER_COMMON) lakefile.toml
# Bootstrap freshness cannot depend on compiled consumers of stale generated files.
# Source files and directories also notice additions and deletions before Lake runs.
DERIVED_INPUTS := $(shell find src tools -type d -o -name '*.lean') lake-manifest.json lean-toolchain
DERIVED_OUT := src/Effect4/Program/TyEq.lean src/Effect4/Store/Domain/Derived/Json.lean src/Effect4/Store/Domain/Derived/Schema.lean \
  src/Effect4/Store/Domain/Derived/Program.lean src/Effect4/Store/Domain/PinDerived.lean src/Effect4/Api/Derived.lean \
  src/Effect4/Store/Domain/Derived/Value.lean src/Effect4/Api/RefusalsDerived.lean src/Effect4/Api/RunnerDerived.lean \
  src/Effect4/Program/Fold.lean src/Effect4/Program/TyFoldExtras.lean src/Effect4/Laws/Program/TyView.lean src/Effect4/Store/Carrier/Fold.lean src/Effect4/Schema/Fold.lean src/Effect4/Program/LayerView.lean src/Effect4/Program/NodeLenses.lean src/Effect4/Program/Binders.lean src/Effect4/Program/Scoped.lean \
  src/Effect4/Program/Authoring/Lifts.lean src/Effect4/Laws/Program/Authoring/Lifts.lean \
  src/Effect4/Program/Authoring/Rows.lean src/Effect4/Laws/Program/Authoring/Rows.lean \
  src/Effect4/Codegen/Authoring/Forms.lean src/Effect4/Laws/Program/Authoring/Forms.lean \
  src/Effect4/Program/AtomInventory.lean harness/truth/prelude-atoms.gen.ts

# A missing output must run its producer instead of becoming a missing prerequisite.
.PHONY: derived-output-missing
$(GEN)/derived: $(GEN)/variances $(DERIVED_SOURCES) $(DERIVED_INPUTS) $(wildcard $(DERIVED_OUT)) $(if $(filter-out $(wildcard $(DERIVED_OUT)),$(DERIVED_OUT)),derived-output-missing)
	$(PY) scripts/generate.py --only derived
	@mkdir -p $(GEN) && touch $@

# The four LCNF outputs (each header carries its own regenerating command). The group is
# NOT a link of the hermetic chain: it regenerates in place only (generate.py refuses
# `--output-dir` for it) and its slowest producer is the engine cut, measured at 14m38s, so
# `check-gen` -- which runs inside `make check`, on every core change -- must not reach it.
# What the chain needs is the order, and `ocaml/engine/api_engine.ml` in EFF_SOURCES below:
# together they make the second pass unnecessary. `make gen-lcnf` is run by name, by `gen`
# and by the check-ocaml CI job.
LCNF_SOURCES := src/OCaml5/Tools/LcnfGen.lean $(wildcard src/OCaml5/Lcnf/*.lean) \
  ocaml/gen/roots.json ocaml/engine/externs.txt ocaml/engine/tools/api_engine_prelude.ml $(PRODUCER_COMMON)
$(GEN)/lcnf: $(GEN)/derived $(LCNF_SOURCES) $(CORE)
	$(PY) scripts/generate.py --only lcnf
	@mkdir -p $(GEN) && touch $@

EFF_SOURCES := src/OCaml5/Tools/EffGen.lean $(wildcard src/OCaml5/Eff/*.lean) $(WIRE_TAGS) \
  scripts/generate-engine-structure.py scripts/lib/program_structure.py \
  ocaml/engine/layout-allowance.json ocaml/engine/api_engine.ml $(PRODUCER_COMMON)
$(GEN)/eff: $(GEN)/derived $(EFF_SOURCES) $(CORE)
	$(PY) scripts/generate.py --only eff
	@mkdir -p $(GEN) && touch $@

$(GEN)/wire: $(GEN)/eff src/OCaml5/Tools/EffWire.lean $(PRODUCER_COMMON) $(CORE)
	$(PY) scripts/generate.py --only wire
	@mkdir -p $(GEN) && touch $@

$(GEN)/cas: $(GEN)/wire src/OCaml5/Tools/CasGoldens.lean $(PRODUCER_COMMON) $(CORE)
	$(PY) scripts/generate.py --only cas
	@mkdir -p $(GEN) && touch $@

TS_SOURCES := $(wildcard tools/Tools/*.lean tools/Drivers/*.lean tools/TestSupport/*.lean) $(WIRE_TAGS) $(VARIANCES) src/Effect4/Codegen/Print.lean lakefile.toml \
  vendor/effect-4.0.0-rc.112/src/unstable/sql/SqlClient.ts vendor/effect-4.0.0-rc.112/src/unstable/sql/Statement.ts \
  vendor/effect-4.0.0-rc.112/src/unstable/persistence/KeyValueStore.ts scripts/generate.py
$(GEN)/ts: $(GEN)/cas $(TS_SOURCES) $(CORE)
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
TRUTH_SOURCES := harness/truth/Truth.lean harness/truth/records.ts harness/truth/prelude.ts harness/truth/prelude-atoms.gen.ts harness/truth/run-truth.ts \
  $(wildcard harness/truth/tapes/*.jsonl) ts/eff/package.json ts/eff/bun.lock
$(GEN)/truth: $(GEN)/readme $(TRUTH_SOURCES) $(CORE) $(LAWS)
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

# The semantics report (generated/semantics.md): the registry's claims checked against the
# loaded roots and rendered once. Pure Lean, no host; the JSON form is a build artifact under
# .lake/gen/semantics-report. It reads no other generation group, so it is a hermetic group of
# its own and `check-gen` holds its drift like any other committed generated file.
# The registry's Test roots are loaded beside Effect4.Laws (`registry.roots`), so their traces are
# inputs too: two program batteries and the five acceptance programs (decisions row 206). The
# plan reads the ProofGraph modules.
SEMANTICS_DOGFOOD := Test.Dogfood.P1HttpCache Test.Dogfood.P2HandlerLayers Test.Dogfood.P3WorkerQueue \
  Test.Dogfood.P4RateLimiter Test.Dogfood.P5LedgerService
SEMANTICS_ROOTS := .lake/build/lib/lean/Test/Program/TypedProgBindRed.trace \
  .lake/build/lib/lean/Test/Program/ProtocolPosts.trace \
  $(foreach m,P1HttpCache P2HandlerLayers P3WorkerQueue P4RateLimiter P5LedgerService,.lake/build/lib/lean/Test/Dogfood/$(m).trace)

# Lake rewrites these traces while `build` runs. Make reads a prerequisite that has no rule once,
# before any recipe, so a rule whose Lean sources changed saw the old time and stayed stale until
# a second run (seat T1, 2026-10-04). As targets of `build` with an empty recipe, they are read
# again after `build`: a rule reruns exactly when a trace moved.
$(CORE) $(LAWS) $(SEMANTICS_ROOTS) $(TRACE)/Api/HostSession.trace $(TRACE)/Codegen/Schema.trace \
  .lake/build/lib/lean/Test/Program/Gen.trace: build ;
SEMANTICS_SOURCES := tools/Tools/Semantics.lean tools/Drivers/Semantics.lean tools/Tools/SemanticsRegistry.lean \
  tools/Tools/SemanticsDisplay.lean tools/Tools/GeneratedStamp.lean src/Effect4/Laws/Auto/Semantics.lean \
  $(wildcard tools/ProofGraph/*.lean) \
  Test/Counterexamples/REGISTER.md docs/core/decisions.md lean-toolchain lakefile.toml
$(GEN)/semantics: $(SEMANTICS_SOURCES) $(LAWS) $(SEMANTICS_ROOTS) | build
	$(LAKE) build semantics-report Test.Program.TypedProgBindRed Test.Program.ProtocolPosts $(SEMANTICS_DOGFOOD)
	rm -rf $(GEN)/semantics-report && mkdir -p $(GEN)/semantics-report
	$(LAKE) exe semantics-report $(GEN)/semantics-report
	cp $(GEN)/semantics-report/semantics.md generated/semantics.md
	@mkdir -p $(GEN) && touch $@

# The groups generate.py can regenerate into a temporary directory (no host runtime).
HERMETIC_GROUPS := variances derived eff wire cas ts readme semantics
# `gen`'s order, which is the producers' order above; lcnf is named here, between derived
# and eff, and nowhere in HERMETIC_GROUPS.
GEN_GROUPS := variances derived lcnf eff wire cas ts readme truth host-protocol schema-ts census semantics

.PHONY: gen gen-hermetic $(addprefix gen-,$(GEN_GROUPS)) clean-gen
gen: $(addprefix $(GEN)/,$(GEN_GROUPS)) ## regenerate every stale generated group, in order
gen-hermetic: $(addprefix $(GEN)/,$(HERMETIC_GROUPS)) ## the Lean-only groups (no host runtime)
# one group: make gen-eff, make gen-truth, ...
$(addprefix gen-,$(GEN_GROUPS)): gen-%: $(GEN)/%
clean-gen: ## forget the generation markers (the next `make gen` re-cuts everything)
	rm -rf $(GEN)

# Every committed path a generator writes. The drift check diffs exactly these.
GENERATED_PATHS := $(DERIVED_OUT) $(VARIANCES) src/Effect4/Program/TyVariance.lean \
  ocaml/eff ocaml/goldens/eff ocaml/engine/cas/goldens ocaml/engine/e4_program_layout.ml \
  ocaml/engine/e4_program_layout.json \
  ocaml/gen/api_gen.ml ocaml/gen/fibers_gen.ml ocaml/gen/machine_gen.ml ocaml/engine/api_engine.ml \
  ocaml/gen/closure-api_gen.tsv ocaml/gen/closure-fibers_gen.tsv ocaml/gen/closure-machine_gen.tsv ocaml/gen/closure-api_engine.tsv \
  ts/eff/eff.gen.ts ts/eff/json.gen.ts ts/eff/profile.gen.ts ts/eff/taxonomy.gen.ts ts/eff/forms.gen.ts \
  ts/eff/wire.gen.ts ts/eff/packages.gen.ts ts/eff/templates.gen.ts ts/eff/test/type-projection.gen.json ts/eff/ingest/README.md \
  harness/truth/prelude-atoms.gen.ts \
  harness/truth/corpus.json harness/truth/generated harness/truth/result.json harness/truth/result.md \
  harness/truth/tapes harness/truth/session/protocol.gen.ts harness/truth/session/tape.schema.json \
  $(SCHEMA_TS_DIR)/Person.generated.ts $(SCHEMA_TS_DIR)/AllRepresentations.generated.ts $(SCHEMA_TS_DIR)/TwoRoots.generated.ts \
  generated/effect-runtime-census.tsv generated/corpus-index.tsv generated/row-types.tsv generated/assignability.tsv generated/row-citations.tsv \
  generated/semantics.md

# ---------------------------------------------------------------------------- corpus
#
# The printed corpus: 400 programs of Lean's seeded generator (Test/Program/Gen.lean) and
# the wire corpus, printed by tools/Drivers/Corpus.lean as TypeScript beside the JSON and
# the canonical bytes of the program Lean's own reader kept, with Lean's typing verdict
# per program in index.tsv. A build artifact, not committed. It is re-cut when Lake's
# trace of Drivers.Corpus changes, which Lake rewrites when the generator, the printer, the
# wire or the tool itself changes; the `lake build` that refreshes the trace is a no-op
# otherwise. The OCaml engine differential reads the directory through E4_LEAN_CORPUS.
# The index (one row per program: name, wellTyped, readable, chars) is also installed as
# generated/corpus-index.tsv, the committed expected file that names every program whose
# verdict a change moved (DI-60); check-gen holds it.

CORPUS := .lake/corpus
CORPUS_TRACE := .lake/build/lib/lean/Drivers/Corpus.trace
export E4_LEAN_CORPUS := $(abspath $(CORPUS))
export EFFECT4_CORPUS := $(abspath $(CORPUS))

$(CORPUS_TRACE): $(LEAN_SOURCES) $(wildcard tools/Tools/*.lean tools/Drivers/*.lean tools/TestSupport/*.lean) | build
	$(LAKE) build Drivers.Corpus

$(CORPUS)/index.tsv: $(CORPUS_TRACE)
	rm -rf $(CORPUS) && mkdir -p $(CORPUS)
	$(LAKE) env lean -DwarningAsError=true -M4096 --run tools/Drivers/Corpus.lean $(CORPUS) 400 4
	{ printf '# GENERATED by make corpus (tools/Drivers/Corpus.lean over Test/Program/Gen.lean and the wire corpus); do not edit\n# name\twellTyped\treadable\tchars\treason\tpath\tcodes\n'; cat $(CORPUS)/index.tsv; } > generated/corpus-index.tsv

.PHONY: corpus
corpus: $(CORPUS)/index.tsv ## the printed corpus under .lake/corpus (Lean's 400 programs and the wire corpus)

# The pinned TypeScript install the reader, the ingest and the truth harness run on.
ts/eff/node_modules: ts/eff/package.json ts/eff/bun.lock
	rm -rf ts/eff/node_modules
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
	@printf 'schema-host %s\n' "$$(test -d harness/schema-host/node_modules/effect && echo 'installed (typescript 7.0.2, tsgo)' || echo 'missing: npm ci --prefix harness/schema-host (check-schema-ts)')"

# ---------------------------------------------------------------------------- checks

CHECKS := roots proof-style cases native ts-reader truth target schema-codec ocaml ingest ingest-smoke \
  host-protocol census schema-ts schema-pins tools corpus tsgo semantics docs language
.PHONY: check check-full check-gen check-gen-full clean-check FORCE check-slow traversal-census $(addprefix check-,$(CHECKS))
FORCE:

check: build check-roots check-proof-style check-gen check-tsgo check-docs ## after every change: the build with its axiom gate, the fresh root elaboration, the proof-style ratchet, the generated-file drift, no TypeScript below 7, the authority documents' references
check-full: check check-slow check-cases check-native check-ts-reader check-corpus check-truth check-tsdiag check-target check-schema-codec check-ocaml check-ingest-smoke check-tools check-gen-full check-ingest check-host-protocol check-census check-schema-ts check-schema-pins check-semantics ## everything else: the outside oracles, the host groups and the tool harnesses

# Drift: regenerate the stale Lean-only groups, then refuse any change to a committed
# generated file. `check-gen-full` re-cuts every group, the host-cut ones included,
# without trusting file times.
define refuse_drift
	git diff --exit-code --stat -- $(GENERATED_PATHS)
	@untracked="$$(git status --porcelain -- $(GENERATED_PATHS) | grep '^??' || true)"; \
	  if [ -n "$$untracked" ]; then echo "FAIL check-gen: untracked generated files:"; echo "$$untracked"; exit 1; fi
endef

# The slow lane (owner, 2026-10-02): the batteries out of the default build, at a sweep.
check-slow: ## the slow batteries (`Test/Slow.lean`: long finite runs, the trace laws, the traversal census) and the axiom gate over them
	$(LAKE) build Test.Slow

# The kernel rung, at a sweep only: every compiled Effect4 and Test declaration in the closure of the
# battery roots, replayed through the kernel into one environment of their dependencies
# (tools/Drivers/KernelReplay.lean). Never a bare `leanchecker`: it holds one environment per core.
check-kernel: ## (sweep) replay every compiled Effect4 and Test declaration through the kernel, after its self-test
	$(LAKE) build kernel-replay Test Test.Slow
	$(LAKE) exe kernel-replay --self-test
	$(LAKE) exe kernel-replay Test Test.Slow

# The proof-style ratchet (AGENTS.md: no new simp_all, first, try or simp without only under src/):
# `make check` runs it as `check-proof-style`, and record-proof-style rewrites the baseline after a
# cleanup. The scan reads the sources and the baseline at elaboration, which Lake's trace of
# Test.Audit.ProofStyle does not cover: the marker's inputs do, so a baseline-only or a
# comment-only edit reruns it. The red fixtures and their baselines are inputs too, and the source
# inventory reruns it when a scanned source is added or deleted.
$(CHK)/proof-style: $(filter src/Effect4/%,$(LEAN_SOURCES)) Test/fixtures/proof-style/baseline.tsv \
  Test/fixtures/proof-style/red/Sample.lean Test/fixtures/proof-style/red-baseline.tsv \
  Test/fixtures/proof-style/red-stale.tsv $(CHK)/inventory \
  tools/ProofGraph/ProofStyle.lean Test/Audit/ProofStyle.lean | build
	$(LAKE) env lean -DwarningAsError=true Test/Audit/ProofStyle.lean
	@mkdir -p $(CHK) && touch $@

record-proof-style: ## rewrite Test/fixtures/proof-style/baseline.tsv from the tree (a reviewed diff)
	$(LAKE) build ProofGraph.ProofStyle Effect4 Effect4Laws
	$(LAKE) env lean tools/ProofStyleRecord.lean

traversal-census: ## print the traversal census (`docs/core/traversal-census.md`)
	$(LAKE) build Test.Audit.TraversalCensus

check-gen: gen-hermetic $(CORPUS)/index.tsv ## regenerate the stale Lean-only groups and the corpus index; refuse a changed committed file
	$(refuse_drift)
	@echo 'PASS check-gen: every Lean-only generated file is what its generator emits'

check-gen-full: ## regenerate every group from scratch (host runtime included) and refuse a changed committed file
	$(MAKE) -B gen
	$(refuse_drift)
	@echo 'PASS check-gen: every generated file is what its generator emits'

# one check: make check-roots, make check-truth, ...
$(addprefix check-,$(CHECKS)): check-%: $(CHK)/%
clean-check: ## forget the check markers (the next `make check` runs every check) and any interrupted truth run
	rm -rf $(CHK) harness/truth/truth-check-*

# A fresh elaboration of Test/All.lean sees a new orphan source file even when Lake's
# roots are cached; the compiled import graph and the source inventory are AxiomGate's.
# The audit itself already runs inside `lake build` (Test.All re-elaborates whenever a
# module it imports changed), so the fresh elaboration is keyed on the source inventory:
# it re-runs when a file is added, removed or renamed, not on every edit.
$(CHK)/inventory: FORCE
	@mkdir -p $(CHK); printf '%s\n' $(sort $(LEAN_SOURCES)) > $@.new; \
	  if cmp -s $@.new $@; then rm -f $@.new; else mv $@.new $@; fi
$(CHK)/roots: $(CHK)/inventory lakefile.toml lean-toolchain | build
	$(LAKE) env lean -DwarningAsError=true Test/All.lean
	@echo 'PASS check-roots: the module-closure, library-root and axiom gates'
	@mkdir -p $(CHK) && touch $@

# One TypeScript compiler, tsgo 7 (AGENTS.md; decisions rows 57 and 168): no `typescript` package below
# 7 is installed under ts/, harness/ or tools/. The recipe is receipt J's line (step 7 (iii)); the
# marker is keyed on what it reads, the install directories (a directory's time moves when a package
# is added to or removed from it) and the manifests and locks that fill them.
check-tsgo: ## no node_modules/typescript below 7 under ts/, harness/ or tools/ (tsgo 7 is the one compiler)
TSGO_INPUTS := $(wildcard ts/*/node_modules harness/*/node_modules tools/*/node_modules) \
  $(wildcard ts/*/package.json ts/*/bun.lock harness/*/package.json harness/*/package-lock.json harness/*/bun.lock tools/*/package.json)
$(CHK)/tsgo: $(TSGO_INPUTS)
	@$(PY) -c 'import json,pathlib,sys; v=lambda p: json.loads(p.read_text())["version"]; bad=[p.as_posix()+": "+v(p) for r in ("ts","harness","tools") for p in sorted(pathlib.Path(r).rglob("node_modules/typescript/package.json")) if int(v(p).split(".")[0]) < 7]; print("\n".join(["FAIL check-tsgo: typescript below 7 (tsgo 7 is the one compiler):"]+bad) if bad else "PASS check-tsgo: no typescript below 7 under ts/, harness/ or tools/"); sys.exit(1 if bad else 0)'
	@mkdir -p $(CHK) && touch $@

# The authority documents (every tracked Markdown file that is not history) name paths, links,
# `git:<rev>:<path>` citations and make targets; each must resolve (scripts/lib/doc_refs.py). Keyed
# on the documents, the Makefile, the checker and the tracked-path inventory, so a deleted or moved
# file re-runs it the way a new Lean file re-runs the root audit.
DOCS := $(shell git ls-files -- '*.md' ':!docs/research' ':!vendor')
$(CHK)/paths: FORCE
	@mkdir -p $(CHK); git ls-files > $@.new; \
	  if cmp -s $@.new $@; then rm -f $@.new; else mv $@.new $@; fi
$(CHK)/docs: $(CHK)/paths $(DOCS) Makefile scripts/check-docs.py scripts/lib/doc_refs.py
	$(PY) scripts/check-docs.py
	@mkdir -p $(CHK) && touch $@

# The controlled English (docs/core/controlled-english.md): the checker's red and green controls,
# then strict mode on the specification and AGENTS.md. The other documents are reported, never
# refused, until a later slice normalizes them (`python3 scripts/check-language.py` prints the
# report). The rules and the dictionary are read from the specification itself. Keyed on the
# documents, the checker, the tracked-path inventory and the Lean sources the dictionary's anchors
# name, so a renamed declaration re-runs it. Not in `make check` yet.
LANGUAGE_SOURCES := scripts/check-language.py scripts/lib/language.py scripts/lib/doc_refs.py \
  $(LEAN_SOURCES) $(shell git ls-files -- 'tools/*.lean')
$(CHK)/language: $(CHK)/paths $(DOCS) $(LANGUAGE_SOURCES)
	$(PY) scripts/check-language.py --self-test
	$(PY) scripts/check-language.py --strict docs/core/controlled-english.md AGENTS.md
	@mkdir -p $(CHK) && touch $@

CONFORM_SOURCES := $(shell find tools/Conform -name '*.lean' -o -name '*.json') scripts/check-conform.py scripts/lib/conform_report.py
$(CHK)/cases: $(CORE) $(CONFORM_SOURCES)
	$(PY) scripts/check-conform.py cases
	@mkdir -p $(CHK) && touch $@

$(CHK)/native: $(CORE) $(CONFORM_SOURCES)
	$(PY) scripts/check-conform.py native
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

# The host controls beside the lane: rc.112's `catchIf` clause, the prelude's cause queries,
# and the inventory guard (every generated atom has a prelude case that runs). Named one by
# one: `bun test harness/truth` would also pick up the lane's work directories.
TRUTH_HOST_TESTS := harness/truth/records.test.ts harness/truth/catch-if.test.ts harness/truth/native-queries.test.ts harness/truth/prelude-inventory.test.ts
$(CHK)/truth: $(CORE) $(LAWS) $(TRUTH_SOURCES) $(TRUTH_GENERATED) $(wildcard harness/truth/session/*.ts) scripts/check-truth.py scripts/lib/truth_host.py harness/truth/tsconfig.json harness/truth/records.typecheck.ts \
    $(TRUTH_HOST_TESTS) harness/truth/prelude-inventory.ts ts/eff/profile.gen.ts | harness/truth/node_modules
	$(BUN) test $(TRUTH_HOST_TESTS)
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

# The architecture map (docs/GENERATED.md, group `architecture`): measured from the tree by a
# Lean driver that parses every import header, loads the roots for declaration counts and
# walks the estates; the role register tools/Tools/ArchitectureRoles.lean is its one hand
# input. Its proof graph is drawn from the semantics report's JSON, which gen-semantics writes.
# A report under .lake/gen, never committed and not in `check`. The view's input check runs first,
# on the report and on broken copies of it (scripts/check-proofgraph-input.mjs).
.PHONY: gen-architecture
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
$(CHK)/target: $(CORE) $(LAWS) $(TRUTH_GENERATED) harness/truth/prelude.ts Test/fixtures/target/selection.json \
  $(wildcard tools/target/*.ts tools/target/*.json) tools/Tools/RowTypes.lean generated/row-types.tsv \
  tools/Tools/TyVectors.lean generated/assignability.tsv \
  ts/eff/profile.gen.ts ts/eff/eff.gen.ts ts/eff/packages.gen.ts ts/eff/tsconfig.json ts/eff/package.json ts/eff/node_modules lean-toolchain
	$(LAKE) env lean -M4096 --run tools/Tools/RowTypes.lean generated/row-types.tsv --check
	$(NODE) ts/eff/node_modules/@typescript/native-preview/bin/tsgo --noEmit -p tools/target/tsconfig.json
	$(BUN) test tools/target
	$(BUN) tools/target/cli.ts --repo .
	@mkdir -p .lake/target && $(LAKE) env lean -M4096 --run tools/Tools/TyVectors.lean .lake/target/ty-vectors.tsv
	$(BUN) tools/target/assignability.ts --repo . --vectors .lake/target/ty-vectors.tsv
	$(BUN) tools/target/rows.ts --repo .
	@mkdir -p $(CHK) && touch $@

.PHONY: gen-assignability
gen-assignability: | build ## promote a fresh assignability differential to generated/assignability.tsv
	@mkdir -p .lake/target && $(LAKE) env lean -M4096 --run tools/Tools/TyVectors.lean .lake/target/ty-vectors.tsv
	$(BUN) tools/target/assignability.ts --repo . --vectors .lake/target/ty-vectors.tsv --promote

.PHONY: gen-row-citations
gen-row-citations: | build ## promote a fresh rows/atoms report to generated/row-citations.tsv
	$(BUN) tools/target/rows.ts --repo . --promote

# The schema codec: Lean's `Ty.encode` results for the contract's cases, compared with
# rc.112's `Schema.toCodecJson` on the host; nothing committed.
$(CHK)/schema-codec: $(CORE) $(wildcard harness/truth/schema-codec/*) | build harness/truth/node_modules
	@tmp="$$(mktemp -d "$${TMPDIR:-/tmp}/effect4-schema-codec.XXXXXX")"; \
	  $(LAKE) env lean -M4096 --run harness/truth/schema-codec/Emit.lean "$$tmp/values.ts" && \
	  $(NODE) harness/truth/node_modules/@typescript/native-preview/bin/tsgo --project harness/truth/schema-codec/tsconfig.json && \
	  $(BUN) harness/truth/schema-codec/check.ts "$$tmp/values.ts"; \
	  status=$$?; rm -rf "$$tmp"; exit $$status
	@mkdir -p $(CHK) && touch $@

# The OCaml lane (the effect4 opam switch; local only until the runner has one): the eff
# library's goldens and wire tests, the LCNF route's smoke, the engine's own tests and the
# three-engine differential (which reads the printed corpus), and the engine seam check.
OCAML_SOURCES := $(shell find ocaml -type f -not -path '*/_build/*')
$(CHK)/ocaml: $(CORPUS)/index.tsv $(OCAML_SOURCES)
	cd ocaml && $(OCAML) dune build && $(OCAML) dune test eff gen clock
	cd ocaml && $(OCAML) dune test engine
	$(OCAML) bash ocaml/engine/tools/gen-check.sh
	@mkdir -p $(CHK) && touch $@

# The diagnostics lane (S0 of the printer/reader/positions redesign): every printed corpus
# program as a module under the pinned host configuration (Codegen/Diagnostics.lean writes
# .lake/corpus/tsconfig.json), one native tsgo run, and the agreement between this checker's
# located refusal (Api.explain) and TypeScript's diagnostics, one row per program in
# generated/tsdiag-agreement.tsv (committed; `make gen-tsdiag` promotes a fresh run). The lane
# fails on a program this checker types that TypeScript refuses, and on drift of the table.
$(CHK)/tsdiag: $(CORPUS)/index.tsv harness/tsdiag/run-tsdiag.mjs harness/truth/prelude.ts $(wildcard harness/truth/session/*.ts) generated/tsdiag-agreement.tsv | ts/eff/node_modules
	$(NODE) harness/tsdiag/run-tsdiag.mjs $(abspath $(CORPUS)) $(abspath .lake/tsdiag)
	@mkdir -p $(CHK) && touch $@

.PHONY: check-tsdiag gen-tsdiag
check-tsdiag: $(CHK)/tsdiag ## the corpus under the native TypeScript compiler against the checker's refusals
gen-tsdiag: $(CORPUS)/index.tsv | ts/eff/node_modules ## promote a fresh diagnostics run to generated/tsdiag-agreement.tsv
	$(NODE) harness/tsdiag/run-tsdiag.mjs $(abspath $(CORPUS)) $(abspath .lake/tsdiag) --promote

# The ingest smoke: the printed corpus through the foreign recognizer's printed contract.
# The census over the constructed foreign corpus is check-ingest (nightly).
$(CHK)/ingest-smoke: $(CORPUS)/index.tsv ts/eff/node_modules $(TS_EFF_SOURCES)
	$(BUN) ts/eff/ingest/check-corpus.ts printed $(abspath $(CORPUS))
	@mkdir -p $(CHK) && touch $@

# The fidelity step observes modules through harness/truth/run-truth.ts, which resolves `effect`
# through the truth link; a fresh worktree has none (order-only, like every other consumer).
$(CHK)/ingest: $(CORPUS)/index.tsv ts/eff/node_modules $(TS_EFF_SOURCES) tools/Drivers/ForeignCorpus.lean tools/Drivers/Styles.lean $(OCAML_SOURCES) scripts/check-ingest.sh | harness/truth/node_modules
	bash scripts/check-ingest.sh
	@mkdir -p $(CHK) && touch $@

$(CHK)/host-protocol: $(CORE) $(wildcard harness/truth/session/*.ts harness/truth/session/*.lean harness/truth/session/*.json) tools/Tools/HostProtocol.lean scripts/check-host-protocol.py | harness/truth/node_modules
	$(PY) scripts/check-host-protocol.py
	@mkdir -p $(CHK) && touch $@

$(CHK)/census: $(VENDOR_SOURCES) generated/effect-runtime-census.tsv Test/Audit/RuntimeCoverage.lean scripts/check-effect-runtime-census.sh scripts/generate-effect-runtime-census.sh
	bash scripts/check-effect-runtime-census.sh
	@mkdir -p $(CHK) && touch $@

# The semantics report's refusal controls: a registry naming an unloaded root, a stale witness or
# a malformed register row is refused with its reason. The report's own drift is `check-gen`'s.
$(CHK)/semantics: $(SEMANTICS_SOURCES) tools/Drivers/SemanticsControls.lean Test/Audit/SemanticsCensus.lean $(LAWS) | build
	$(LAKE) build semantics-controls Test.Audit.SemanticsCensus
	$(LAKE) exe semantics-controls
	@mkdir -p $(CHK) && touch $@

SCHEMA_SOURCES := $(shell find src/Effect4/Schema -name '*.lean') src/Effect4/Codegen/Schema.lean
$(CHK)/schema-ts: $(SCHEMA_SOURCES) $(wildcard $(SCHEMA_TS_DIR)/*) scripts/check-schema-typescript-generation.sh
	bash scripts/check-schema-typescript-generation.sh
	@mkdir -p $(CHK) && touch $@

# The rest of the Schema slice, on its inputs (ledger decision 3): the rc.112 tag pins
# are a textual extraction from the vendored SchemaRepresentation.ts. The retained
# generation gate uses the pinned host (EFFECT4_EFFECT_NODE_MODULES, harness/schema-host).
SCHEMA_PIN := vendor/effect-4.0.0-rc.112/src/SchemaRepresentation.ts
$(CHK)/schema-pins: $(SCHEMA_PIN) src/Effect4/Schema/Representation.lean scripts/check-schema-census.sh
	bash scripts/check-schema-census.sh $(SCHEMA_PIN)
	@mkdir -p $(CHK) && touch $@

# The one tool harness: the exact `Classical.choice` admissions against compiled declarations.
SELFTEST_SOURCES := scripts/test-trust-boundaries.sh Test/Audit/AxiomGate.lean \
  $(shell find Test/fixtures/trust-gate -type f)
$(CHK)/tools: $(SELFTEST_SOURCES) | build
	bash scripts/test-trust-boundaries.sh
	@mkdir -p $(CHK) && touch $@

# The conservativity check of an alphabet append (DI-47, decisions row 172; seat W2): goldens
# byte-identical unless the baseline policy names them, tags and manifests append-only, every
# verdict unchanged, every addition named, the generated diff recorded (C1-C5,
# scripts/lib/conservativity.py). It judges committed files, so an append's producers and
# `make corpus` run first. `make check-conservativity` runs its controls (ten mutations of HEAD and
# six unresolvable revisions); `make check-conservativity BASE=<rev>` also judges the working tree
# against BASE. Not `--strict` until the owner rules on promoting refOf, deferredOf, var and
# unknown in the baseline policy (row 172).
.PHONY: check-conservativity
check-conservativity: ## the alphabet-append check: its controls; BASE=<rev> also judges the tree
	bash scripts/check-conservativity.sh --self-test
	@if [ -n "$(BASE)" ]; then bash scripts/check-conservativity.sh $(BASE); fi

# The rule for the `Ty` append (decisions row 182; probe U §6.1; seat W2): no hand case analysis on
# `Ty` outside the generated folds and Laws/Program/Typed/Membership.lean, read from the census and
# the exhaustiveness gate, after the checker has established that it read a whole census (row 182
# amended: an empty, truncated or error-carrying log refuses with exit 2). `make check-ty-rule`
# runs its eighteen controls (seven log controls, eleven tree controls: the explicit producer
# inventory and every producer's exit status, seat ty-rule); `python3 scripts/check-ty-rule.py
# --tree` runs the census over the tree
# and prints the distance from the rule. The gate turns on with the append (seat W4): not in `check`.
.PHONY: check-ty-rule
check-ty-rule: ## the Ty append's rule checker: its controls (the gate is the append's)
	$(PY) scripts/check-ty-rule.py --self-test

# ---------------------------------------------------------------------------- help

.PHONY: status
status: ## one screen, measured: HEAD and dirty paths, build and check freshness, generated drift, claims, ledger goals, registers, stale references
	@$(PY) scripts/status.py

.PHONY: help clean
help: ## this list
	@awk 'BEGIN {FS = ":.*## "} /^[a-zA-Z0-9_-]+:.*## / {printf "  %-18s %s\n", $$1, $$2}' $(MAKEFILE_LIST)
	@echo
	@echo '  check-<name>       one check: roots, cases, native, ts-reader, truth, target, schema-codec,'
	@echo '                     ocaml, ingest, ingest-smoke, host-protocol, census, schema-ts, corpus,'
	@echo '                     schema-pins, tools, tsgo, semantics, docs, language'
	@echo '                     (each skipped while its inputs are unchanged; -B forces)'
	@echo '  gen-<group>        one generated group: derived, eff, wire, cas, ts, readme, lcnf,'
	@echo '                     truth, host-protocol, schema-ts, census, semantics'

clean: ## lake clean (drops the build, the generation and check markers)
	$(LAKE) clean
