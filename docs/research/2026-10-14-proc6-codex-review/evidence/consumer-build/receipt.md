# PROC-6 consumer lifetime finite host probes

Reviewed HEAD: 9ccb94e2b8349f72dae884328e84cf25582c95c4.
Runtime: Bun 1.4.2. Effect 4.0.0-rc.112, imported from apps/todo/node_modules/effect/src/index.ts.
No repository edits. No lake or dune invocation.

Commands:

    bun /tmp/proc6-review-20261014/consumer-build/lifetime.ts
    bun /tmp/proc6-review-20261014/consumer-build/captured-context.ts

Both commands exit 0. Their standard output is preserved in lifetime.log and captured-context.log.

lifetime.ts tests one Ref-owning layer. Separate provide(layer) runs answer [1,1]. One startup build followed by provide(context) runs answers [1,2]. Three layer acquisitions occur.

captured-context.ts imports the exact emitted TodoAppLayer and real KeyedRecorder, tableRows and provideRows. It builds TodoAppLayer under recorded repository adapter A. It runs the emitted list method twice, under request adapters A and B. The first run succeeds and its record closes. Both repository dispatch attempts select A. The second run fails with `a live call after the request's record`. Thus later request provision does not override the repository context captured by TodoAppContext and restored by TodoApp_list.

Source explanation: internal/effect.ts provideContext calls updateContext(self, Context.merge(context)); the supplied captured context wins duplicate keys. Emitted TodoApp_list provides its captured state context inside the surrounding request provision.

These are finite host tests of lifetime and captured context routing. They establish no Lean theorem and no general source/target simulation. The emitted service is uncached. No claim about cached HTTP behavior follows.

## Current checkout update

The owner externally changed HEAD during review to 7c9bb76172400d2f885cf461f2f09db334d2495a. At that commit EmitTodo selects Cached.cached. The ignored .work/todo.gen.ts remains the old uncached file (SHA256 f7bc47f4b23081244a066ebf2cfe99ab405fc59e1854283d1809f19a92731113). Thus the initial uncached finding describes initial HEAD and stale local bytes, not the current producer.

Current EmitTodo source SHA256: 54f7e3720d4ce94da23f5a84d545ac6ff83dda6457fbe4544199be51f1d4c02d.
Fresh cached output SHA256: 2116bb8d490a772c79431fe5df03bf5a9f359b673706da5af952a0cb8ceef409.
Fresh table SHA256: 218086712100650e76020b10fd2994a6085b69159445ba8b5f4354fae0bca91a.

The initial narrow build fails only because sandbox disallows writes to the toolchain artifact cache. current-build.log retains it. Redirecting the supported LAKE_CACHE_DIR to /tmp succeeds; current-build-retry.log retains success. Commands:

    LAKE_CACHE_DIR=/tmp/proc6-review-20261014/consumer-build/lake-cache LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.Todo.Cached Effect4.Program.Authoring.ApplicationService Effect4.Codegen.RowServices Tools.Code.Module Tools.ProfileJson
    LAKE_CACHE_DIR=/tmp/proc6-review-20261014/consumer-build/lake-cache LEAN_NUM_THREADS=3 lake env lean --run apps/todo/EmitTodo.lean /tmp/proc6-review-20261014/consumer-build/emitted-current /Users/pooks/Dev/lean4-effect4/harness/truth/prelude.ts

Both corrected commands exit 0. The emitted file imports the existing prelude by absolute path; its node_modules symlink points to the application's existing dependencies. No install or repository source edit occurs.

    bun /tmp/proc6-review-20261014/consumer-build/captured-context-current.ts
    bun /tmp/proc6-review-20261014/consumer-build/cache-current.ts

Both exit 0. The captured-context-current probe lists through A, closes request A, then adds through B. Attempts are A:all and A:insert. First request succeeds; second fails with `a live call after the request's record`. A second list would hit the cache and not expose the captured-repository error.

The cache-current probe builds the fresh cached service once under a simple repository. First list calls all. Second list calls no host method. Add calls insert and invalidates the cache. List after add calls all again and returns the new todo. Thus the pasted claim that GET after POST is a cache hit is false for this emitted cached service: it is a miss because add invalidates. This is a finite runtime observation, not a universal proof.
