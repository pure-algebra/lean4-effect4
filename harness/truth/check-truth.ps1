<#
.SYNOPSIS
  The rc.112 truth check: Lean's manifest, then the rc.112 runner, compared.

.DESCRIPTION
  1. Runs `lake env lean -M4096 --run harness/truth/Truth.lean harness/truth/corpus.json`
     (one lean process, memory-capped, the whole process tree killed on timeout — the
     2026-09-04 rule), unless -SkipLean reuses the manifest on disk.
  2. Makes sure `harness/truth/node_modules` is a junction to the pinned installation's
     `node_modules` (`C:\Users\kokok\Dev\effect4-host`, effect@4.0.0-rc.112), so `effect`
     resolves from inside the repo; verifies the pinned version.
  3. Runs `bun run <abs>/harness/truth/run-truth.ts` from the pinned installation's directory.
     The runner writes `result.json` / `result.md` and prints the table.
  Exit code: the runner's (0 = every exit and schedule agrees; 1 = a disagreement;
  2 = the harness itself failed), or 3 when the Lean tool fails.

  Never starts `lake build`. Never commits.

.PARAMETER SkipLean
  Reuse harness/truth/corpus.json instead of regenerating it.
.PARAMETER TimeoutMs
  The rc.112 deadline for a parked program (default 300).
.PARAMETER LeanTimeoutSec
  How long the Lean tool may run before its process tree is killed (default 540).
#>
param(
  [switch]$SkipLean,
  [int]$TimeoutMs = 300,
  [int]$LeanTimeoutSec = 540
)
$ErrorActionPreference = "Stop"
$repo = (Resolve-Path (Join-Path $PSScriptRoot "..\..")).Path
$truth = Join-Path $repo "harness\truth"
$host_ = "C:\Users\kokok\Dev\effect4-host"
$manifest = Join-Path $truth "corpus.json"

# --- 1. the Lean face -------------------------------------------------------------------
if (-not $SkipLean) {
  $out = Join-Path $truth "lean.out.log"; $err = Join-Path $truth "lean.err.log"
  Write-Host "== Lean: harness/truth/Truth.lean -> harness/truth/corpus.json"
  $p = Start-Process -FilePath "lake" -WorkingDirectory $repo -NoNewWindow -PassThru `
    -ArgumentList @("env", "lean", "-M4096", "--run", "harness/truth/Truth.lean", "harness/truth/corpus.json") `
    -RedirectStandardOutput $out -RedirectStandardError $err
  # Touch the handle now: under Windows PowerShell 5.1 a -PassThru process whose handle was
  # never read reports a null ExitCode after WaitForExit, which read as "failed" here once.
  $null = $p.Handle
  if (-not $p.WaitForExit($LeanTimeoutSec * 1000)) {
    Write-Host "Lean tool timed out after $LeanTimeoutSec s; killing process tree $($p.Id)"
    taskkill /PID $p.Id /T /F | Out-Null
    exit 3
  }
  Get-Content $out | Write-Host
  if ((Get-Item $err).Length -gt 0) { Get-Content $err | Write-Host }
  if ($p.ExitCode -ne 0) { Write-Host "Lean tool failed with exit code $($p.ExitCode)"; exit 3 }
}
if (-not (Test-Path $manifest)) { Write-Host "no manifest at $manifest"; exit 3 }

# --- 2. the pinned installation ---------------------------------------------------------
$link = Join-Path $truth "node_modules"
$target = Join-Path $host_ "node_modules"
if (-not (Test-Path $target)) { Write-Host "pinned installation missing: $target"; exit 2 }
if (-not (Test-Path $link)) {
  New-Item -ItemType Junction -Path $link -Target $target | Out-Null
  Write-Host "created junction $link -> $target"
}
$version = (Get-Content (Join-Path $target "effect\package.json") | ConvertFrom-Json).version
if ($version -ne "4.0.0-rc.112") { Write-Host "effect is $version, not 4.0.0-rc.112"; exit 2 }

# --- 3. the rc.112 face -----------------------------------------------------------------
Write-Host "== rc.112: bun run harness/truth/run-truth.ts (effect $version)"
Push-Location $host_
try {
  & bun run (Join-Path $truth "run-truth.ts") --manifest $manifest --out $truth --timeout $TimeoutMs
  $code = $LASTEXITCODE
} finally {
  Pop-Location
}
exit $code
