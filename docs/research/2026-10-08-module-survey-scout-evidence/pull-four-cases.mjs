import * as Cause from '/Users/pooks/.codex/worktrees/module-semaphore/lean4-effect4/vendor/effect-4.0.1/src/Cause.ts';
import * as Pull from '/Users/pooks/.codex/worktrees/module-semaphore/lean4-effect4/vendor/effect-4.0.1/src/Pull.ts';
const done=Cause.makeFailReason(Cause.Done('tail'));
const fail=Cause.makeFailReason('ordinary');
const interrupt=Cause.makeInterruptReason(7);
for (const [name,reasons] of Object.entries({done:[done],doneInterrupt:[done,interrupt],doneFail:[done,fail],noDone:[fail]})) {
 const cause=Cause.fromReasons(reasons);
 const filtered=Pull.filterDone(cause), exit=Pull.doneExitFromCause(cause);
 console.log(JSON.stringify({name,isDone:Pull.isDoneCause(cause),resultTag:filtered._tag,exitTag:exit._tag,leftover:filtered.success?.value,retained:filtered.failure?.reasons.map(r=>r._tag==='Fail'?r.error:r._tag)}));
}
