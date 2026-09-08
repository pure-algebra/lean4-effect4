<#
.SYNOPSIS
  Regenerate every derived `Canonical` group in the tree and report what changed.

.DESCRIPTION
  The manifest is `tools\Effect4Gen\manifest.json`, the one of
  docs\research\2026-09-04-cas-trait-plan.md §4 at its landing paths: one group per emitted
  file, its imports, its carriers in dependency order, the `--kind` requests (a `Content`
  instance right after that carrier's `Canonical` one), and the acceptance guards appended
  verbatim after the generated declarations. It used to be written inside this script, which
  made Windows the only machine that could regenerate; it is now data, and
  `tools\Effect4Gen\Driver.lean` is the portable driver that reads the same file:

      lake env lean --run tools/Effect4Gen/Driver.lean [--group NAME] [--check] [--verify]

  Adding a group is an entry in the manifest and no code change in either driver.

  This script stays the entry point on the PC because of `Invoke-Lean` below: a ten-minute
  per-invocation timeout and a `lean.exe` process-tree kill, which the Lean driver has no
  portable way to provide and which this machine has needed (one `lean.exe` reached 54 GB on
  2026-09-04). Everything else the two drivers do is the same argument list.

  The script runs `lake env lean -M 4096 --run tools\Effect4Gen\Main.lean` once per group; it
  never runs `lake build`, `lake clean`, `lake update` or `lake exe` (the one lake is the
  coordinator's), so the modules a group imports must already be built. Each invocation gets a
  ten-minute timeout, after which its process tree is killed.

  It hashes every generated file before and after and prints one line per group saying whether
  the file changed. `-Verify` turns a change into a non-zero exit and also runs
  `git diff --exit-code` over the derived files, so a regenerated file that differs from the
  committed one refuses. `-Check` additionally type-checks each generated file with
  `lake env lean -M 4096`, counts its receipts, refuses any `sorryAx`/`Classical.choice`, and
  runs the projection guard `tools\Effect4Gen\Check.lean` over all of them.

.EXAMPLE
  pwsh -File scripts\generate-derived.ps1
  pwsh -File scripts\generate-derived.ps1 -Group Program -Check
  pwsh -File scripts\generate-derived.ps1 -Verify -Check
#>
[CmdletBinding()]
param(
  # Fail if any generated file changed, or differs from the committed one.
  [switch] $Verify,
  # Also type-check every generated file and run the projection guard.
  [switch] $Check,
  # Only this group (Json, Schema, Program, Pin).
  [string] $Group = "",
  # Per-invocation timeout in milliseconds.
  [int] $TimeoutMs = 600000
)

Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'

$repo = Resolve-Path (Join-Path $PSScriptRoot '..')
Set-Location $repo

$tool = 'tools\Effect4Gen\Main.lean'
$guard = 'tools\Effect4Gen\Check.lean'

# The manifest is data: tools\Effect4Gen\manifest.json, read here and by
# tools\Effect4Gen\Driver.lean. One group per emitted file -> imports, output, guards, kinds,
# carriers in dependency order. An applied type is one word with `@` for the space, so the
# shell never splits it. Adding a group is an entry there and no change here.
$manifestPath = Join-Path $repo 'tools\Effect4Gen\manifest.json'
$manifest = (Get-Content -Raw -Encoding UTF8 $manifestPath | ConvertFrom-Json).groups

function Invoke-Lean {
  param([string[]] $LeanArgs, [string] $Label)
  $stdout = [IO.Path]::GetTempFileName()
  $stderr = [IO.Path]::GetTempFileName()
  $proc = Start-Process -FilePath 'lake' -ArgumentList $LeanArgs -NoNewWindow -PassThru `
    -RedirectStandardOutput $stdout -RedirectStandardError $stderr
  if (-not $proc.WaitForExit($TimeoutMs)) {
    Write-Host "TIMEOUT $Label after $TimeoutMs ms; killing the process tree" -ForegroundColor Red
    try { Stop-Process -Id $proc.Id -Force } catch {}
    try {
      Get-CimInstance Win32_Process -Filter "name='lean.exe'" |
        ForEach-Object { Stop-Process -Id $_.ProcessId -Force }
    } catch {}
    return [pscustomobject]@{ Code = 124; Out = ''; Err = 'timeout' }
  }
  $o = (Get-Content $stdout -Raw -ErrorAction SilentlyContinue)
  $e = (Get-Content $stderr -Raw -ErrorAction SilentlyContinue)
  Remove-Item $stdout, $stderr -Force -ErrorAction SilentlyContinue
  return [pscustomobject]@{ Code = $proc.ExitCode; Out = $o; Err = $e }
}

function Get-FileHashOrEmpty {
  param([string] $Path)
  if (Test-Path $Path) { return (Get-FileHash -Algorithm SHA256 $Path).Hash } else { return '' }
}

$changed = @()
$failed = @()
$files = @()

foreach ($g in $manifest) {
  if ($Group -ne '' -and $g.Name -ne $Group) { continue }
  $file = $g.Out
  $files += $file
  $dir = Split-Path $file -Parent
  if (-not (Test-Path $dir)) { New-Item -ItemType Directory -Force -Path $dir | Out-Null }
  $before = Get-FileHashOrEmpty $file
  $a = @('env', 'lean', '-M', '4096', '--run', $tool,
         '--group', $g.Name, '--imports', $g.Imports, '--out', $file)
  if ($g.Guards -ne '' -and (Test-Path $g.Guards)) { $a += @('--append', $g.Guards) }
  foreach ($k in $g.Kinds) { $a += @('--kind', $k) }
  $a += $g.Types
  $r = Invoke-Lean -LeanArgs $a -Label ("generate " + $g.Name)
  if ($r.Code -ne 0) {
    Write-Host ("FAILED  {0}: the generator exited {1}" -f $g.Name, $r.Code) -ForegroundColor Red
    if ($r.Out) { Write-Host $r.Out }
    if ($r.Err) { Write-Host $r.Err }
    $failed += $g.Name
    continue
  }
  $after = Get-FileHashOrEmpty $file
  if ($before -eq '') {
    Write-Host ("new     {0} -> {1}" -f $g.Name, $file) -ForegroundColor Yellow
    $changed += $g.Name
  } elseif ($before -ne $after) {
    Write-Host ("CHANGED {0} -> {1}" -f $g.Name, $file) -ForegroundColor Yellow
    $changed += $g.Name
  } else {
    Write-Host ("same    {0} -> {1}" -f $g.Name, $file)
  }
}

if ($Check) {
  foreach ($file in $files) {
    if (-not (Test-Path $file)) { continue }
    $r = Invoke-Lean -LeanArgs @('env', 'lean', '-M', '4096', $file) -Label ("check " + $file)
    $receipts = 0
    if ($r.Out) {
      $receipts = ([regex]::Matches($r.Out, 'depends on axioms|does not depend on any axioms')).Count
      $bad = [regex]::Matches($r.Out, 'sorryAx|Classical\.choice').Count
      if ($bad -gt 0) {
        Write-Host ("FAILED  {0}: {1} receipts reach sorryAx or Classical.choice" -f $file, $bad) `
          -ForegroundColor Red
        $failed += $file
      }
    }
    if ($r.Code -ne 0) {
      Write-Host ("FAILED  {0}: lean exited {1}" -f $file, $r.Code) -ForegroundColor Red
      if ($r.Out) { Write-Host $r.Out }
      if ($r.Err) { Write-Host $r.Err }
      $failed += $file
    } else {
      Write-Host ("green   {0} ({1} receipts)" -f $file, $receipts)
    }
  }
  $present = @($files | Where-Object { Test-Path $_ })
  if ($present.Count -gt 0) {
    $r = Invoke-Lean -LeanArgs (@('env', 'lean', '-M', '4096', '--run', $guard) + $present) `
      -Label 'projection guard'
    if ($r.Code -ne 0) {
      Write-Host 'FAILED  the projection guard refused' -ForegroundColor Red
      if ($r.Out) { Write-Host $r.Out }
      if ($r.Err) { Write-Host $r.Err }
      $failed += 'projection guard'
    } else {
      $ok = ([regex]::Matches(($r.Out ?? ''), '(?m)^ok ')).Count
      Write-Host ("green   the projection guard agrees ({0} shapes)" -f $ok)
    }
  }
}

Write-Host ''
Write-Host ("changed: {0}" -f $(if ($changed.Count -eq 0) { 'nothing' } else { $changed -join ', ' }))
if ($failed.Count -gt 0) {
  Write-Host ("failed:  {0}" -f ($failed -join ', ')) -ForegroundColor Red
  exit 1
}
if ($Verify) {
  if ($changed.Count -gt 0) {
    Write-Host 'refusing: a generated file changed; commit the regenerated files' -ForegroundColor Red
    exit 1
  }
  $present = @($files | Where-Object { Test-Path $_ })
  if ($present.Count -gt 0) {
    & git diff --exit-code --quiet -- @present
    if ($LASTEXITCODE -ne 0) {
      Write-Host 'refusing: a derived file differs from the committed one' -ForegroundColor Red
      exit 1
    }
  }
}
exit 0
