#!/usr/bin/env bash
# Deterministic mechanism census of the pinned Effect v4 fiber runtime.
#
# The census keys are observed runtime BEHAVIOURS, never "function X exists".
# Each row names one behaviour, the pinned file and line span that establishes
# it, and a SHA-256 of exactly those bytes. A row is located by a literal
# ANCHOR that must occur exactly once in its file; the span is then
# anchor-line + offsets, so upstream edits ABOVE a span move the line numbers
# without disturbing the digest, while any edit INSIDE a span fails the run.
#
# Failure modes, all fatal:
#   * the pinned effect version is not 4.0.0-rc.112
#   * a pinned source file digest drifted from the expectation embedded below
#   * an anchor is absent, or occurs more than once
#   * a span digest drifted from the expectation embedded below
#   * a duplicate row id, an unknown kind, or a per-kind count drift
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
generator_rel="scripts/generate-effect-runtime-census.sh"

expected_effect_version="4.0.0-rc.112"
expected_upstream_commit="2600f62f4532026928454dcea8d1c48557b3f942"

# The census reads the VENDORED pin, so the gate is hermetic and runs in CI
# without a JavaScript toolchain or a node_modules tree. When
# EFFECT4_EFFECT_NODE_MODULES points at a real pinned install, the vendored
# bytes are additionally compared against it, which is what keeps the vendored
# copy honest.
pin_rel="vendor/effect-4.0.0-rc.112/src"
pin_src="$repo_root/$pin_rel"

if [[ $# -ne 0 ]]; then
  printf 'usage: generate-effect-runtime-census.sh\n' >&2
  exit 2
fi

for override_name in \
    EFFECT4_RUNTIME_CENSUS_SOURCE \
    EFFECT4_RUNTIME_CENSUS_ROWS \
    EFFECT4_RUNTIME_CENSUS_CANDIDATE; do
  if [[ -n "${!override_name-}" ]]; then
    printf 'FAIL runtime census generator rejects source override variable %s\n' \
      "$override_name" >&2
    exit 2
  fi
done

[[ -d "$pin_src" ]] || {
  printf 'FAIL runtime census: vendored Effect pin is absent: %s\n' "$pin_src" >&2
  exit 1
}

sha256_file() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  elif command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "$1" | awk '{print $1}'
  else
    printf 'FAIL neither sha256sum nor shasum is available\n' >&2
    return 1
  fi
}

sha256_stdin() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum | awk '{print $1}'
  else
    shasum -a 256 | awk '{print $1}'
  fi
}

# When the pinned install is reachable, confirm its declared version and that
# every vendored file is byte-identical to it. Read without node: this census
# is pure text extraction and must run where no JavaScript toolchain exists.
node_modules="${EFFECT4_EFFECT_NODE_MODULES:-$repo_root/../foldlab/library/effects/node_modules}"
installed_src="$node_modules/effect/src"
cross_check_install="no"
if [[ -d "$installed_src" ]]; then
  package_json="$node_modules/effect/package.json"
  [[ -f "$package_json" && ! -L "$package_json" ]] || {
    printf 'FAIL runtime census: %s is absent, not regular, or a symlink\n' "$package_json" >&2
    exit 1
  }
  actual_effect_version="$(awk -F'"' '/^[[:space:]]*"version"[[:space:]]*:/ { print $4; exit }' "$package_json")"
  [[ "$actual_effect_version" == "$expected_effect_version" ]] || {
    printf 'FAIL runtime census: reachable effect install is %s, expected %s\n' \
      "$actual_effect_version" "$expected_effect_version" >&2
    exit 1
  }
  cross_check_install="yes"
fi

# Whole-file digests. A file-level drift is reported before any span is read so
# the failure names the file rather than a scatter of span mismatches.
pinned_inputs() {
  cat <<'INPUTS'
internal/effect.ts|0e32b42fbc8901ae75419fbd2999bf5c96b40e4bb54cc42c4fc2ec778cc641f0
internal/core.ts|233b7a1fb3a53b9f49f63c01f810052cb174cc13742f52ea2e8bd482f302fd11
Scheduler.ts|e4c35925d7586a82f93975390f08a67bfff4261d35d8382db7c18c9acc349680
Scope.ts|d1f31095954a8348853620ac102ae665acb86afbac54189d99e57c37757ddf18
Exit.ts|f9e4baea6718bd6617069563028710cfaee3ba7b432826f87c405e0ca3513818
Cause.ts|4b39e7f578b9bceba6712fdf0f53410963006cb335a94f3c5bbd8c49cfe9962b
Array.ts|ccc7dfbb44f0a93d4911af0d1db187925cfe7e765804bb3b9bdff2b7e1fc3936
INPUTS
}

while IFS='|' read -r input_rel expected_sha; do
  [[ -n "$input_rel" ]] || continue
  input_file="$pin_src/$input_rel"
  [[ -f "$input_file" && ! -L "$input_file" ]] || {
    printf 'FAIL runtime census input is absent, not regular, or a symlink: %s\n' \
      "$input_file" >&2
    exit 1
  }
  actual_sha="$(sha256_file "$input_file")"
  [[ "$actual_sha" == "$expected_sha" ]] || {
    printf 'FAIL runtime census: vendored %s digest drifted: expected %s, found %s\n' \
      "$input_rel" "$expected_sha" "$actual_sha" >&2
    exit 1
  }
  if [[ "$cross_check_install" == "yes" ]]; then
    installed_file="$installed_src/$input_rel"
    [[ -f "$installed_file" ]] || {
      printf 'FAIL runtime census: pinned install is missing %s\n' "$input_rel" >&2
      exit 1
    }
    installed_sha="$(sha256_file "$installed_file")"
    [[ "$installed_sha" == "$expected_sha" ]] || {
      printf 'FAIL runtime census: vendored %s does not match the pinned install: vendor %s, install %s\n' \
        "$input_rel" "$expected_sha" "$installed_sha" >&2
      exit 1
    }
  fi
done < <(pinned_inputs)

# ---------------------------------------------------------------------------
# The frozen mechanism table.
#
#   kind|id|file|anchor|offset-start|offset-end|expected-span-sha256|summary
#
# `anchor` is a literal substring that must occur on exactly one line of
# `file`; the span runs from anchor-line + offset-start to anchor-line +
# offset-end inclusive. `|` never appears in an anchor or a summary.
# ---------------------------------------------------------------------------
census_rows() {
  cat <<'ROWS'
op|op.Success|internal/core.ts|op: "Success",|-2|6|2408a5c6160ec5874477cdc82f6dd67282ae731bd587804a6a9e5106cb1b15b7|Success pops a contA frame and calls it with the value; with an empty stack it yields itself as the Exit.
op|op.Failure|internal/core.ts|op: "Failure",|-2|17|754b34372a31319fe776e8644aa0bd0ba8ceb8bcf4574330f8759464e4e2cbfe|Failure annotates the cause with the current stack frame, pops contE frames skipping every one while the fiber is interrupted and interruptible, and yields the Exit when none answers.
op|op.WithFiber|internal/core.ts|op: "WithFiber",|-4|4|6f87566e5b53a1159357a69e9e274b837d59e3fca467ae91f972320c93a8a14c|WithFiber hands the raw FiberImpl to the argument function and returns the effect that function produces.
op|op.YieldableError|internal/core.ts|op: "YieldableError",|-7|11|fdf9b23907161b59b65c80c7cd806d709fe96bbdc1b4eba672c50e18e63f9ef3|A YieldableError is an Error subclass whose prototype carries an evaluate returning exitFail(this).
op|op.Sync|internal/effect.ts|op: "Sync",|-2|6|a62e87836af4e6aec7e595fcd9e3ff72055a35cb7bd64dfae18cb00e9d63f9d0|Sync runs the thunk, then behaves like Success with its result.
op|op.Suspend|internal/effect.ts|op: "Suspend",|-4|4|195140823d560317cae010f45b22ee8889c445399835295bb61ad8a34a0f1a13|Suspend returns the result of calling the thunk, with no stack interaction.
op|op.Yield|internal/effect.ts|op: "Yield",|-2|11|450965320ad5d66c74070577b04afbce29db772eedfddddf9cbb24e2b16d715d|Yield schedules a resume task on the fiber dispatcher at the requested priority and parks with a resume guard.
op|op.Async|internal/effect.ts|op: "Async",|-8|33|1c8b185ffdf24d997dcb0d922430c983c55712631bb0b0ae66930e8107fd3e54|Async calls register(resume, signal?); a synchronous resume short-circuits, otherwise the fiber parks and pushes an AsyncFinalizer when there is a cancel effect or a controller.
op|op.AsyncFinalizer|internal/effect.ts|op: "AsyncFinalizer",|-3|12|d12d2233a7e9fa0116790fef05d191a66c3464f6e7098423e4d4f9bc4d2c7874|AsyncFinalizer masks in contAll and, in contE, runs the cancel effect only when the cause carries an interrupt, then re-fails.
op|op.Iterator|internal/effect.ts|op: "Iterator",|-4|19|043ca6c586c288d1d0e91fb3f73bda43ab46ca868de60bb2a317188e226de8fe|Iterator drives the generator; an Exit yielded from it is folded inline and any other effect is pushed under this frame.
op|op.OnSuccess|internal/effect.ts|op: "OnSuccess",|-22|5|a531c44160c4f502f7728797e041890940d912fc3d3b9d611b853f9f061760fb|OnSuccess pushes itself and returns the inner effect; the contA arm is assigned per instance by flatMap, not by the prototype.
op|op.OnFailure|internal/effect.ts|op: "OnFailure",|-22|5|85a58897bd4c31170db46eafce829174d2988a138b4f476d67e7a083cd85fa5b|OnFailure pushes itself and returns the inner effect; the contE arm is assigned per instance by catchCause, not by the prototype.
op|op.OnSuccessAndFailure|internal/effect.ts|op: "OnSuccessAndFailure",|-34|5|54b2c0e19cf82b82cee6dc1134bd8e2305caa298ceef7248d476b1e3a051acdc|OnSuccessAndFailure pushes itself and returns the inner effect; both arms are assigned per instance by matchCauseEffect.
op|op.Exit|internal/effect.ts|op: "Exit",|-6|11|caddd92dee1d7c20e783b5c8cb56be3409a2c136a2847803ded3e52d68df66c2|Exit pushes itself; either arm resumes with the Exit value, reusing the exit argument the pop supplies when present.
op|op.OnExit|internal/effect.ts|op: "OnExit",|-6|22|3c7ba51542877af0b3f224b11fb6da3de0348238aafd72ba5bef97bf5fe009af|OnExit pushes itself; contAll masks the finalizer unless args[2] is true, and either arm runs the finalizer then restores the original exit.
op|op.SetInterruptible|internal/effect.ts|op: "SetInterruptible",|-1|9|4c002125d3b782f954a627646e5abed379adcc5b547d91d72f5f494cac806724|SetInterruptible defines contAll only: it restores the flag and, when the fiber becomes interruptible with a pending cause, replaces the continuation with failCause(cause).
op|op.While|internal/effect.ts|op: "While",|-6|16|7a40b8538d9301a024539885f6c7d4444e6cf76783631b902a1a0ef58f5c3d02|While tests, pushes itself and runs the body; contA steps and re-tests until the predicate is false.
frame-arm|frame-arm.OnSuccess|internal/effect.ts|const OnSuccessProto = makePrimitiveProto({|-6|6|20315a161f645b9ce2f3a5021cfd13acdd87bec3de411059e8e682827e8801dd|OnSuccess answers contA only; the prototype declares op and evaluate, and flatMap assigns contA on the instance.
frame-arm|frame-arm.OnFailure|internal/effect.ts|const OnFailureProto = makePrimitiveProto({|-6|6|bd5cd0bcf3869508b7623b561424fea844098dfed7d0e8cf2815042a5c4d7982|OnFailure answers contE only; catchCause assigns contE on the instance.
frame-arm|frame-arm.OnSuccessAndFailure|internal/effect.ts|const OnSuccessAndFailureProto = makePrimitiveProto({|-9|6|f2c5fd4378827b60bc917b78e07533e97942ae90dcd89270cb5a154f53301176|OnSuccessAndFailure answers contA and contE; matchCauseEffect assigns both on the instance.
frame-arm|frame-arm.Exit|internal/effect.ts|op: "Exit",|1|10|6438d4d17a076b5281007f8b7b2c4f615bb05bca3de6b7420b4a8446e3ff4cd8|The Exit frame declares contA and contE on the prototype and no contAll.
frame-arm|frame-arm.OnExit|internal/effect.ts|op: "OnExit",|6|21|650ee02b63e27bc85c9f3355809836212fcf702441c7c8772a4942ef0e7f131d|The OnExit frame declares all three arms; contAll pushes SetInterruptible(true) and clears interruptible so the finalizer runs masked.
frame-arm|frame-arm.SetInterruptible|internal/effect.ts|op: "SetInterruptible",|1|6|f5c96feb7f227c33c955bcb4ecfc87cfa7781690bfb7ee97d9b45452bd955e1c|The SetInterruptible frame declares contAll only and can return a replacement continuation used for either arm.
frame-arm|frame-arm.AsyncFinalizer|internal/effect.ts|op: "AsyncFinalizer",|1|11|3914198c54ed382ed4786ffd45cb35b24bab3f6cc4370f2f6943489ef4449e19|The AsyncFinalizer frame declares contAll and contE and no contA.
frame-arm|frame-arm.While|internal/effect.ts|op: "While",|1|15|f3d2b9ad8d9a6a3787732ce8c6a62b25b77a28ed5f66a82ee759f72801061146|The While frame declares contA only, alongside its evaluate.
frame-arm|frame-arm.Iterator|internal/effect.ts|op: "Iterator",|2|18|a1b667f9d214e2c7bd6164d9ab621277a1833781d46235a3397940c4a7a6f32b|The Iterator frame declares contA only, and its evaluate delegates to that same contA.
checkpoint|checkpoint.runloop-top|internal/effect.ts|        if (this._deferredInterrupt) {|-1|3|9f353715caa449b94f270c3887562efc633f5bd938e0792b4ab2d1c39372deeb|At the top of each runLoop iteration a deferred interrupt is cleared and the current primitive is replaced by failCause of the accumulated cause.
checkpoint|checkpoint.getcont-deferred|internal/effect.ts|      return deferredInterruptCont|-2|1|89b43a1943bf7a2ac1e7dd4c0f665b67b4f9707699efd737de3e0af64623d9d6|getCont answers a deferred interrupt before touching the stack, returning deferredInterruptCont whose both arms fail with the accumulated cause.
checkpoint|checkpoint.post-yield-cancel|internal/effect.ts|        if (current === Yield) {|0|12|b99254bc8eb34f32efa7c9ef431745f4e8750076f7c35a09a20e9e160ef950fc|After a Yield carrying a park thunk, a deferred interrupt fires the thunk as a cancel guard and the loop continues instead of parking.
checkpoint|checkpoint.exit-failcause-skip|internal/core.ts|    let cont = fiber.getCont(contE)|0|6|3c47308cf70c146066768437412b2413e40b146f3e3bf5bfb6712d9967b7231b|While the fiber is interruptible with a pending cause, exitFailCause keeps popping contE frames, so every user error handler is skipped.
checkpoint|checkpoint.set-fiber-interruptible|internal/effect.ts|const setFiberInterruptible = (fiber: FiberImpl)|0|4|c82c5f605a4a3ce65e11ee8d339147ca9ec51b16316da29b5f89bba416329d1b|setFiberInterruptible sets the flag, pushes the restoring frame, and returns an immediate failure when a cause is already pending.
checkpoint|checkpoint.set-interruptible-contall|internal/effect.ts|op: "SetInterruptible",|3|5|e91edec3b5b1d961153562ee09b3f03dcbbd28c12d52629dce9a042947b5c0b8|When a SetInterruptible frame is popped and leaves the fiber interruptible with a pending cause, it substitutes failCause(cause) for both arms.
interrupt|interrupt.unsafe-entry|internal/effect.ts|    let cause = causeInterrupt(fiberId)|-4|17|10b3609e5b557de0b003b94cd8f1200ba9df59e841384b6597419f6e1009fa49|interruptUnsafe is the single interruption entry: it no-ops after the Exit exists, always records the cause, and applies it now only when the fiber is interruptible and not inside runLoop.
interrupt|interrupt.accumulate|internal/effect.ts|    this._interruptedCause = this._interruptedCause|0|2|fac98b7069bfdc544edd5c1466a6caec8d39a5d9a96b448c7e61addc5d76e23a|Successive interruptors accumulate into one cause by causeCombine rather than replacing it.
fork|fork.unsafe|internal/effect.ts|export const forkUnsafe = <FA, FE, A, E, R>(|-1|20|6fe22e10c429beb31db41a5f79885b5d840970656e031f07e078971761310ef6|Every fork goes through forkUnsafe: it derives the child mask, constructs a FiberImpl over the parent context, starts it immediately or as a priority-0 dispatcher task, and registers it only when not a daemon.
fork|fork.child|internal/effect.ts|export const forkChild: {|-1|33|780ef2f435854200caafa277f787c7058046538e1f209b46f351001579eca972|forkChild installs the interruptChildren middleware and forks a non-daemon child, so the parent exit interrupts it.
fork|fork.detach|internal/effect.ts|export const forkDetach: {|-1|24|8a5546fcb8f589d7c454a29c50efbe9035381c77bb45b49035aa674999dc92b6|forkDetach forks a daemon: no registration, no middleware, and nothing interrupts it on the parent exit.
fork|fork.in|internal/effect.ts|export const forkIn: {|-1|42|7ae510972afb5bc0a08b7c3604cd29baca07a186b9653f23fddc91bf648d9cc5|forkIn forks a daemon and links it to a scope by a shared key: a scope finalizer interrupts it unless the interruptor is the child itself, the child observer removes the finalizer, and an already-Closed scope interrupts immediately.
fork|fork.scoped|internal/effect.ts|export const forkScoped: {|-1|24|3b9a27f7d169af398c4d2fe36ed367107128b365104e303e3c3fa6e4d4b931bb|forkScoped is forkIn applied to the ambient Scope service.
fork|fork.race-all|internal/effect.ts|export const raceAll = <Eff extends Effect.Effect<any, any, any>>(|-1|55|e1bfade75a179fe549bd6d2c2f8240e520afb9ec0cfaee109e3229314bc0627d|raceAll forks every entrant as an immediate daemon, resumes with the first success after interrupting the remaining fibers uninterruptibly, and concatenates every loser reason into one cause when all fail.
fork|fork.await-all-children|internal/effect.ts|export const awaitAllChildren = <A, E, R>(|-1|20|071aab49546add6f6f716a8648be7ecb76aecfa6c5766812423b651c48b6034d|awaitAllChildren snapshots the children before running and, on exit, awaits only those added during the run.
fork|fork.fiber-run-in|internal/effect.ts|export const fiberRunIn: {|-1|20|f3976f469e8e80190f8e96aff8913afaff75acd039ef08871e06d2133bdb8916|fiberRunIn binds an existing fiber to a scope with a keyed finalizer, interrupting immediately when the scope is already Closed.
fork|fork.join|internal/effect.ts|export const fiberJoin = <A, E>|-1|7|a6722115119e10cf39c7b2865fbebc2739492ed92c4b85864c4bb90796b7e6fa|join returns the stored Exit directly when the fiber is done and otherwise registers an observer; the Exit itself is the resumed effect.
fork|fork.await|internal/effect.ts|export const fiberAwait = <A, E>(|-1|9|a59be62d3aa7f49e0a458cfc7306e3afd05773ef575e4e43b95944dd64cb6795|await takes the same observer route as join but delivers the Exit as an ordinary value.
fork|fork.interrupt|internal/effect.ts|export const fiberInterrupt = <A, E>(|-1|28|eb5656d5a9fb1c91a26dad529c46ab678fd77dd992df837ada332722e6309ef7|interrupt records the interruptor id and stack annotations through interruptUnsafe and then awaits the target.
fork|fork.interrupt-all|internal/effect.ts|export const fiberInterruptAll = <A extends Iterable<Fiber.Fiber<any, any>>>(|-1|11|e61326781fa28916c357a56f57e3bbb1f7a715e281199caba7088e7761c3081a|interruptAll records an interrupt on every fiber first and only then awaits them all.
scope|scope.states|Scope.ts|export declare namespace State {|0|88|90b94bf3d9753538b3365c47169a92b7184dc0f06abd938585cc37dae59d480c|A scope state is Empty, Open with one inline finalizer or a keyed insertion-ordered map, or Closed carrying the closing Exit.
scope|scope.make|internal/effect.ts|export const scopeMakeUnsafe =|-1|7|e13bece248e12c84ceb28c3419fa01c2ef8101dc8685a90ba0a25d0f5665d4b0|A new scope starts at the shared constant Empty state with a sequential finalizer strategy by default.
scope|scope.add-finalizer|internal/effect.ts|export const scopeAddFinalizerUnsafe = (|-1|21|a8d5415bc35599b2801840be3d41d026d8bf783774193c2d55b097db9e751898|The first add stores an inline finalizer and its key; the second promotes both into a Map that preserves insertion order.
scope|scope.add-after-closed|internal/effect.ts|export const scopeAddFinalizerExit = (|-1|11|5c4034223fe93ffd6215481996194ef2d5f32f160ef705ab809826009137b12c|Adding a finalizer to a Closed scope runs it immediately with the stored closing Exit instead of registering it.
scope|scope.remove-finalizer|internal/effect.ts|export const scopeRemoveFinalizerUnsafe = (|-1|13|2b3ec0b907d06f7619282916b48fef624649bf1df9d979341964497baf1f080c|Removal clears the inline slot when the key matches and otherwise deletes from the map, leaving a non-Open scope untouched.
scope|scope.close-state-first|internal/effect.ts|export const scopeCloseUnsafe = <A, E>|-1|19|f241da8aab39a8c50d4b0ccf30df2dd4b8da83d140dd03891ac9d2ff95048941|Close is idempotent: it returns on an already-Closed scope and writes the Closed state before any finalizer runs.
scope|scope.close-lifo|internal/effect.ts|  const arr = Array.from(finalizers.values())|0|9|3a8ca4924ac01076efba31758e55946f2ff96776bc750e30d8cc9a8f2a0b9bd9|Many finalizers are materialised in insertion order and iterated backwards, so the last registered runs first.
scope|scope.close-sequential|internal/effect.ts|    if (self.strategy === "sequential") {|0|1|2d06212912eae7011f4c15d10ee343ded4c22d55dfc51fa841aa53d29d02cd94|The sequential strategy awaits each finalizer through exit(), capturing failures instead of throwing.
scope|scope.close-parallel|internal/effect.ts|      fibers.push(forkUnsafe(parent, finalizer(exit_), true, true, "inherit"))|-1|1|b059d1a6cb137f27ae675ac7212b39e00b07b50be7e76a0eb1c10d4bf48c52c7|The parallel strategy is immediate daemon forks that inherit the closing fiber mask, not a separate scheduler policy.
scope|scope.close-merge|internal/effect.ts|  if (fibers.length > 0) {|0|3|f3a1e6aa926e2170b82ee0a4783b5b54fbe125f7f957bedf21f6d360b64f7744|Parallel finalizer fibers are awaited together and every exit is merged by exitAsVoidAll.
scope|scope.exit-as-void-all|internal/effect.ts|export const exitAsVoidAll = <I extends Iterable<Exit.Exit<any, any>>>(|-1|13|8d2b0176e8d2fe2fcb6b00e0809255ddc1e55c27d579a6c8e40e69a7c66ef1c1|exitAsVoidAll concatenates the reasons of every failed exit into a single flat cause and is Void when none failed.
scope|scope.fork-linkage|internal/effect.ts|export const scopeForkUnsafe = (|-1|10|0bf6ca54deac3224b350ae50a73948c498806336c651d8f92d5233e7554c0d67|A child scope of a Closed parent is born Closed with the parent exit; otherwise one shared key links a parent finalizer closing the child to a child finalizer removing itself from the parent.
scope|scope.scoped|internal/effect.ts|export const scoped = <A, E, R>|-1|9|60d6c9b6e0bf5891d79fed44a065af07baaaec630150f28cde9dcbe92b72c91f|scoped installs a fresh scope in the fiber context and closes it with the fiber Exit through an OnExit frame, restoring the previous context first.
scope|scope.acquire-release|internal/effect.ts|export const acquireRelease = <A, E, R, R2>(|-1|16|355d596949a02871f9a6667a1dc6611855d1ffecbd63c1ac30f36753bbbd5764|acquireRelease runs under uninterruptibleMask, restores interruptibility for the acquire only when asked, and registers the release against the ambient scope with the captured context.
scheduler|scheduler.should-yield|Scheduler.ts|  shouldYield(fiber: Fiber.Fiber<unknown, unknown>) {|0|2|ed9e2590bf6b4e78de5f1854c702056afd80265956af504210d8ed3b978af4d4|The default scheduler asks a fiber to yield exactly when its current op count has reached its cached maxOpsBeforeYield.
scheduler|scheduler.priority-buckets|Scheduler.ts|class PriorityBuckets {|0|26|23dac26950791c38cd981a54bd6e6628dfc5d173135830a50a3f02e3899d3bdc|Tasks are held in priority buckets kept in ascending priority order, appended FIFO within a bucket, and drained by swapping the bucket array out.
scheduler|scheduler.dispatcher-arming|Scheduler.ts|  scheduleTask(task: () => void, priority: number) {|0|5|5eca3d76b73bd2ac9975097ab5f5ba13e7c0ce6a140477c620ca1288c6b2ab21|Only the first task of an idle dispatcher arms the host callback; later tasks join the already-armed batch.
scheduler|scheduler.run-tasks-drain-once|Scheduler.ts|  runTasks() {|0|8|c7ceb0694e56b02a06783c6c71e5ce96152d3921c796b83d7724424459f7c67c|runTasks drains the buckets once and runs that snapshot, so tasks enqueued during the run wait for the next host task.
scheduler|scheduler.flush|Scheduler.ts|  flush() {|0|8|d4125d178c11f8406627549c267c58df11fe1bd5cc9402a9dfc6fab7109390bc|flush cancels the armed callback and runs tasks synchronously in a loop until no bucket remains.
scheduler|scheduler.yield-now-resume-guard|internal/effect.ts|      fiber.evaluate(exitVoid as any)|-4|5|3bb3921adf4d7555a70d35b19b66811d3416f4d9b01a7861f078e3f0428e233c|yieldNow schedules its own resume at the given priority and parks behind a resume guard, so an interrupt while parked makes the queued task a no-op.
scheduler|scheduler.max-ops-default|Scheduler.ts|export const MaxOpsBeforeYield =|0|3|9cbc627ec93f0fc81630c8acce81905a619ad58f32035431f0bca6e6ceeb98ee|MaxOpsBeforeYield is a fiber-cached reference defaulting to 2048.
scheduler|scheduler.prevent-yield-default|Scheduler.ts|export const PreventSchedulerYield =|0|3|be4c0d8f8360c3c2ac4afe72153469b11351a61609be4b7fabc47f23e35d0952|PreventSchedulerYield is a fiber-cached reference defaulting to false.
scheduler|scheduler.host-loop|Scheduler.ts|const setImmediate = "setImmediate" in globalThis|0|20|9140d033ad60273d25af7777bfb6fa42c4d96dbb10e2e6012d623b324a028217|Async mode arms setImmediate where available and setTimeout 0 otherwise; sync mode arms a cancellable Promise microtask.
exit|exit.success-failure|Exit.ts|export interface Success<out A, out E = never> extends Exit.Proto<A, E> {|0|39|3704d8e5a8c9d324fbdd55318b77edf2de930913f9080f20446eab14d0397c80|An Exit is Success carrying a value or Failure carrying a Cause, and each is itself a primitive that can be stepped.
exit|exit.reason-alphabet|Cause.ts|export type Reason<E> = Fail<E>|0|0|7385a50926e2ab45f547b06fd8ba0b3f057bd24b3a37cada2c6611d18daa3802|The public reason alphabet is exactly Fail, Die and Interrupt with no further cases.
cause|cause.flat-reasons|internal/core.ts|export class CauseImpl<E> implements Cause.Cause<E> {|-1|38|96cf3cd46e9ee4e8a0fc6d70e4cd8e775dcbb089ff4e04c6744fda5f03e5ca4b|A Cause is a flat readonly array of reasons with no tree and no sequential or parallel distinction, and equality is pairwise over the ordered reasons.
cause|cause.reason-fail|internal/core.ts|export class Fail<E> extends ReasonBase<"Fail"> implements Cause.Fail<E> {|-1|41|f67e6322a0dcca6aef0fe37dc20e6f6e076adc658777ae20dea10ae8047e0105|A Fail reason carries the typed error and its annotations.
cause|cause.reason-die|internal/core.ts|export class Die extends ReasonBase<"Die"> implements Cause.Die {|-1|33|cf49585f403151aca03e742cdbdec16ff3e872df2eaf277e120f8c4d7d8b3c71|A Die reason carries an unknown defect and its annotations.
cause|cause.reason-interrupt|internal/effect.ts|export class Interrupt extends ReasonBase<"Interrupt"> implements Cause.Interrupt {|-1|38|0bda2e0222cb6da4e7f00abd86ab2457e0495d98265013fd8adb7397d7e9fa1e|An Interrupt reason carries an optional interruptor fiber id, and equality compares that id together with the annotations.
cause|cause.combine-union|internal/effect.ts|export const causeCombine: {|-1|16|05ba217ac1bb771788f8022bc9af3c35b50995b1504cbbeb8ac01ba13f79e062|causeCombine treats the empty cause as an identity and otherwise takes the set union of reasons, returning the original when the result is structurally equal.
cause|cause.finalizer-merge|internal/effect.ts|const combineFinalizerCause = <A, E, XE, XR>(|0|4|00d4eaf9f536a0c2e59834fed53e92a42eda28dcb8c26ea2e9b56aef235196a2|A finalizer failure under a failed exit is merged into the exit cause by causeCombine; under a successful exit the finalizer failure stands alone.
cause|cause.squash|internal/effect.ts|export const causeSquash = <E>(self: Cause.Cause<E>): unknown => {|-1|10|44b6f20bec8d07dcd34afa2cf3039c3259a99401467787308790cb327a14b4eb|causeSquash partitions the reasons and returns the first Fail error, else the first Die defect, else an Error naming interruption without error, else an Error naming the empty cause.
cause|cause.union-first-occurrence|Array.ts|      return isReadonlyArrayNonEmpty(b) ? dedupe(appendAll(a, b)) : a|-4|3|b8e9ec9f634bdc05b919de3bad0e810dba23b204860a7fccf7c6d881741a436b|b8e9ec9f634bdc05b919de3bad0e810dba23b204860a7fccf7c6d881741a436b|Arr.union returns the other operand when one side is empty and otherwise dedupes the concatenation self ++ that, so the union of two causes keeps first occurrences across both sides.
cause|cause.dedupe-first-occurrence|Array.ts|      const out: NonEmptyArray<A> = [headNonEmpty(input)]|-3|10|35c69cab2b77edcdb220cf1436e436ed0708c0f10bbecefab021a2378a7221a2|dedupeWith keeps the first element and then each later element not equivalent to any element already kept, so order is the order of first occurrence.
cause|cause.annotations|internal/core.ts|const annotationsMap = new WeakMap<object, ReadonlyMap<string, unknown>>()|0|61|b5fe124fb1f47310b5433917441d19602b0432ad9052607fbae0b26f9f019a89|Reason annotations are a per-reason string map, remembered per original error object in a WeakMap and merged on construction, and annotate never overwrites an existing key unless asked.
entry|entry.run-fork-with|internal/effect.ts|export const runForkWith = <R>(context: Context.Context<R>) =>|-1|25|804b61fdfcf77e47c1bcfc30044db62a81118dfdf089e5b32638330d1aa7bff9|runForkWith builds one FiberImpl over the caller context and evaluates it synchronously on the caller stack; there is no root scope and no root parent.
entry|entry.abort-signal|internal/effect.ts|  if (options?.signal) {|0|8|0b90364948b4274cbab6157407e0e6f92dd4bfe220afb391d96775f98ab90c77|An aborted signal interrupts with no interruptor id, and the listener is removed by an observer on the fiber exit.
entry|entry.run-callback-with|internal/effect.ts|export const runCallbackWith = <R>(context: Context.Context<R>) => {|-1|18|b175b6206fb34f8da12eb19f0fc62ae4131f3af268abe13465a7288c20e40131|runCallbackWith adds the onExit observer and returns an interruptor function that carries the caller supplied interruptor id.
entry|entry.run-promise-exit-with|internal/effect.ts|export const runPromiseExitWith = <R>(context: Context.Context<R>) => {|-1|11|3bfeb26b8da2b8e6468ecff3a82840c7e915406e888aa53887312a4cb5a62064|runPromiseExitWith resolves a promise from an observer, so the Exit is always delivered as a value.
entry|entry.run-promise-with|internal/effect.ts|export const runPromiseWith = <R>(context: Context.Context<R>) => {|-1|14|295b78dd2888fb96e87c0034aa057823126661655f843f07da9e126a58dd1a05|runPromiseWith rejects with causeSquash of the failure cause rather than with the Exit.
entry|entry.run-sync-exit-with|internal/effect.ts|export const runSyncExitWith = <R>(context: Context.Context<R>) => {|-1|9|47b882216f0bff876ec8995fce9354cb879041a3f305b9f44f931f8a24b802d2|runSyncExitWith returns an Exit argument unchanged, otherwise runs on a sync MixedScheduler, flushes the dispatcher, and dies with AsyncFiberError when the fiber is still parked.
entry|entry.async-fiber-error|internal/effect.ts|export class AsyncFiberError extends TaggedError("AsyncFiberError")<{|-1|11|9a635c1d40a42bff894750cea4f814be19b6ea69e7d576c2185dd4d92aa8e4cc|AsyncFiberError is the defect used when a fiber survives the runSync flush, and it carries the fiber itself.
entry|entry.with-error-reporting|internal/effect.ts|export const withErrorReporting: <|-1|25|0c5df5f7541f1f54a3e6fb4ed16c3e92e39c47b606054349583a340c8e8268c5|withErrorReporting is opt-in: it fans the cause to the current error reporters, which are empty by default.
rule|rule.frames-are-primitives|internal/effect.ts|      const op = this._stack.pop()|-1|8|eaf09fd168b9869aabc4ab98913e5d7226c8ee09bd6d14fd16ee6445502c53dd|A frame is selected by which of contA, contE and contAll it defines, and contAll runs on every frame passed during a pop, not only on the frame that answers.
rule|rule.interrupt-bypasses-handlers|internal/core.ts|    let cont = fiber.getCont(contE)|0|3|5bff8644b3def42e4449c4157b5395c0ad023a60163fc21c637adf53ccb38c0d|Once interrupted and interruptible, Failure skips every contE frame until a mask frame flips the flag or the stack empties, so catchCause never sees an interrupt outside an uninterruptible region.
rule|rule.yield-is-overloaded|internal/effect.ts|        if (current === Yield) {|0|12|b99254bc8eb34f32efa7c9ef431745f4e8750076f7c35a09a20e9e160ef950fc|Yield means finished when _yielded is an Exit and parked when it is a thunk.
rule|rule.only-fork-child-tracks|internal/effect.ts|  if (!daemon && !child._exit) {|0|3|3395dc20cf31ee311ffc50cfb0ae35ac36ba144a8887d45fa5076902363a7021|Only a non-daemon fork joins the parent children set; forkIn, forkScoped, forkDetach and the races all fork daemons.
rule|rule.children-interrupted-after-exit|internal/effect.ts|    // the interruptChildren middleware is added in Effect.forkChild|0|6|aa9aab060f785d19064f1f969475f010c8eb45a4026dd9d600db7a8e0477fa02|Children are interrupted after the Exit exists, between runLoop returning and observers firing, and only when the middleware was ever installed.
rule|rule.scope-close-lifo-state-first|internal/effect.ts|  if (self.state._tag === "Closed") return|0|7|cb37874dcd3a73b661ccaf1cf3a40df0f112ec4dbe186adef26d8b095434f80c|Scope close flips the state to Closed before running anything, and only then runs finalizers in reverse registration order.
rule|rule.cause-has-no-structure|internal/effect.ts|      Arr.union(self.reasons, that.reasons)|-7|3|60138d8dec137deb98b7579a00dd9809ab5a54cc5a796e080607d15c7756663a|causeCombine is a set union of reasons; there is no sequential or parallel cause node.
rule|rule.start-is-asymmetric|internal/effect.ts|  if (immediate) {|0|4|86f92b1b29d548b215db77854e7642192b15fd31fcf53da3a02a9f0fdbb778f0|The root fiber runs synchronously on the caller stack while children default to a deferred start on the parent dispatcher at priority 0.
rule|rule.record-and-apply-separate|internal/effect.ts|    this._interruptedCause = this._interruptedCause|0|9|5191cbe40554457dad6f760048e7abcb08a98db8971b4e1f05852bbf7fdf46d3|Recording an interrupt and applying it are separate: the cause is always stored and becomes the outcome at the first checkpoint where the fiber is interruptible.
rule|rule.budget-per-runloop-entry|internal/effect.ts|    let yielding = false|0|18|ac6955bbd3e14d4c2954911134ecf257384f445cfc7cd2f636c37a7b1d771fb9|The op counter resets on every runLoop entry and at most one scheduler yield is injected per entry.
ROWS
}

expected_kind_counts() {
  cat <<'COUNTS'
op|17
frame-arm|9
checkpoint|6
interrupt|2
fork|12
scope|14
scheduler|9
exit|2
cause|10
entry|8
rule|10
COUNTS
}

expected_row_total=99

tmp_parent="${TMPDIR:-/tmp}"
tmp_parent="${tmp_parent%/}"
tmp_root="$(mktemp -d "$tmp_parent/effect4-runtime-census.XXXXXX")"

cleanup() {
  local cleanup_rc=$?
  set +e
  case "$tmp_root" in
    "$tmp_parent"/effect4-runtime-census.*) rm -rf -- "$tmp_root" ;;
    *)
      printf 'FAIL refusing to remove unexpected path: %s\n' "$tmp_root" >&2
      cleanup_rc=1
      ;;
  esac
  exit "$cleanup_rc"
}
trap cleanup EXIT

data_rows="$tmp_root/data.tsv"
: >"$data_rows"

row_count=0
while IFS='|' read -r kind id file anchor offset_start offset_end expected_span_sha summary; do
  [[ -n "$kind" ]] || continue
  row_count=$((row_count + 1))

  source_file="$pin_src/$file"
  matches="$(grep -Fc -- "$anchor" "$source_file" || true)"
  [[ "$matches" == 1 ]] || {
    printf 'FAIL runtime census row %s: anchor occurs %s times in %s; expected once\n   anchor: %s\n' \
      "$id" "$matches" "$file" "$anchor" >&2
    exit 1
  }
  anchor_line="$(grep -Fn -- "$anchor" "$source_file" | cut -d: -f1)"
  start=$((anchor_line + offset_start))
  end=$((anchor_line + offset_end))
  [[ "$start" -ge 1 && "$end" -ge "$start" ]] || {
    printf 'FAIL runtime census row %s: degenerate span %s-%s in %s\n' \
      "$id" "$start" "$end" "$file" >&2
    exit 1
  }
  span_sha="$(sed -n "${start},${end}p" "$source_file" | sha256_stdin)"
  [[ "$span_sha" == "$expected_span_sha" ]] || {
    printf 'FAIL runtime census row %s: span %s:%s-%s digest drifted: expected %s, found %s\n' \
      "$id" "$file" "$start" "$end" "$expected_span_sha" "$span_sha" >&2
    exit 1
  }
  printf 'mechanism\t%s\t%s\t%s\t%s-%s\tsha256=%s\t%s\n' \
    "$kind" "$id" "$file" "$start" "$end" "$span_sha" "$summary" >>"$data_rows"
done < <(census_rows)

[[ "$row_count" == "$expected_row_total" ]] || {
  printf 'FAIL runtime census emitted %s rows; expected %s\n' \
    "$row_count" "$expected_row_total" >&2
  exit 1
}

duplicate_id="$(awk -F '\t' '{ seen[$3]++ } END { for (id in seen) if (seen[id] > 1) print id }' "$data_rows")"
[[ -z "$duplicate_id" ]] || {
  printf 'FAIL runtime census duplicate row id: %s\n' "$duplicate_id" >&2
  exit 1
}

while IFS='|' read -r kind expected_count; do
  [[ -n "$kind" ]] || continue
  actual_count="$(awk -F '\t' -v kind="$kind" '$2 == kind { n++ } END { print n + 0 }' "$data_rows")"
  [[ "$actual_count" == "$expected_count" ]] || {
    printf 'FAIL runtime census kind %s has %s rows; expected %s\n' \
      "$kind" "$actual_count" "$expected_count" >&2
    exit 1
  }
done < <(expected_kind_counts)

unknown_kind="$(awk -F '\t' '
  BEGIN {
    split("op frame-arm checkpoint interrupt fork scope scheduler exit cause entry rule", ks, " ")
    for (i in ks) known[ks[i]] = 1
  }
  !($2 in known) { print $2 }
' "$data_rows" | sort -u)"
[[ -z "$unknown_kind" ]] || {
  printf 'FAIL runtime census unknown kind: %s\n' "$unknown_kind" >&2
  exit 1
}

printf 'format\teffect4-effect-runtime-census-v1\n'
printf 'generator\t%s\tsha256=%s\n' "$generator_rel" "$(sha256_file "${BASH_SOURCE[0]}")"
printf 'regenerate\t./scripts/generate-effect-runtime-census.sh > generated/effect-runtime-census.tsv\n'
printf 'pin\teffect\t%s\tupstream=%s\n' "$expected_effect_version" "$expected_upstream_commit"
while IFS='|' read -r input_rel expected_sha; do
  [[ -n "$input_rel" ]] || continue
  printf 'input\t%s/%s\tsha256=%s\n' "$pin_rel" "$input_rel" "$expected_sha"
done < <(pinned_inputs)
printf 'columns\tmechanism\tkind\tid\tfile\tlines\tspan-sha256\tsummary\n'
cat "$data_rows"
