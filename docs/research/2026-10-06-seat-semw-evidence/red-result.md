effect 4.0.0-rc.112, bun 1.4.2, deadline 300 ms
| program | Lean exit | rc.112 exit | agree | schedule agree | runSyncExit agree | entry | notes |
|---|---|---|---|---|---|---|---|
| pSemaphoreProtected | success [[2,2,[2,1],[0,1]],[2,1,[1],[1]],[22]] | success [[2,2,[2,1],[0,1]],[0,2,[2,1],[0,1]],[]] | NO | yes | yes | runSyncExit | same kind, values differ; runSyncExit and runFork exits differ: success [[2,2,[2,1],[0,1]],[2,1,[1],[1]],[22]] |
| pSemaphoreBodies | success [[2,2,[2,1],[0,1]],[0,0,[],[]],[22,31]] | success [[2,2,[2,1],[0,1]],[0,2,[2,1],[0,1]],[]] | NO | yes | yes | runSyncExit | same kind, values differ; runSyncExit and runFork exits differ: success [[2,2,[2,1],[0,1]],[0,0,[],[]],[22,31]] |
FAIL: 2 of 61 programs disagree with rc.112 (pSemaphoreProtected, pSemaphoreBodies)
