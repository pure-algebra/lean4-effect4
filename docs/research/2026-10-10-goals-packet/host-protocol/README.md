# The host-protocol family: probe and plan (draft, written as the probe runs)

Status: a research note (history, not authority). It rules nothing. Base `5b40699ae`
(`refactor/phase1-phase3`), branch `probe/goals-host-protocol`.

## Running log

- `retries_declared` is false as stated. The script
  `parked ++ [.cancel ⟨3⟩, .receive http (ok body1), .apply http, .tick 2000, .tick 100, .flush, .hold http]`
  is all plain moves. Its observation has `calls = [answered "body-1", live]` and two attempts, so
  `retriesDeclared` is false (reproduced: `scratch/Explore1.lean`, a finite evaluation).
- The kernel checks that run in 1.28 s (`decide +kernel`, `scratch/KernelCost.lean`), and the
  build of `fetch` in 0.38 s. So a closed run of the Lean machine is cheap for the kernel.
- A bounded search (`scratch/Search1.lean`) plays every word of length 3 or less over 41 moves
  from `parked`, then a fixed tail. The moves: fire, evaluate, a yield verdict and an
  interruption at each of the fibers 0 to 8, three clock steps, the reply's receipt and its
  application. 70644 words; 6 fail. Each failing word delays the race's view of the finished
  attempt: a yield verdict at fiber 1 or 3, or an interruption of fiber 3. The yield verdict
  needs no interruption at all, so restricting the host's cancels does not repair the claim.
- `request` (routing) is in `StraightRows` and `LoopedRows` (reproduced, `scratch/Explore2.lean`).
  Admission takes only the canonical record frame at the configuration's column, and no
  negative integer at a `nat` column (reproduced).
