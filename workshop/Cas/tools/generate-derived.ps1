<#
.SYNOPSIS
  Regenerate every `Canonical` group into workshop\Cas\Gen-out\ and report what changed.

.DESCRIPTION
  The manifest below is the one the plan's §4 tables: one group per emitted file, its imports,
  its carriers in dependency order, and the acceptance guards appended verbatim after the
  generated declarations.

  The script runs `lake env lean -M 4096 --run workshop\Cas\gen\Main.lean` once per group; it
  never runs `lake build`, `lake clean`, `lake update` or `lake exe`, because lane S2 owns the
  machine's one build. Each invocation gets a ten-minute timeout, after which its process tree
  is killed.

  It hashes every generated file before and after and prints one line per group saying whether
  the file changed. `-Verify` turns a change into a non-zero exit — the landing's
  `git diff --exit-code`, before the files are tracked. `-Check` additionally type-checks each
  generated file with `lake env lean -M 4096` and runs the projection guard
  `workshop\Cas\gen\Check.lean` over all of them.

.EXAMPLE
  pwsh -File workshop\Cas\tools\generate-derived.ps1
  pwsh -File workshop\Cas\tools\generate-derived.ps1 -Check
  pwsh -File workshop\Cas\tools\generate-derived.ps1 -Verify
#>
[CmdletBinding()]
param(
  # Fail if any generated file changed.
  [switch] $Verify,
  # Also type-check every generated file and run the projection guard.
  [switch] $Check,
  # Only this group (Json, Program, Schema).
  [string] $Group = "",
  # Per-invocation timeout in milliseconds.
  [int] $TimeoutMs = 600000
)

Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'

$repo = Resolve-Path (Join-Path $PSScriptRoot '..\..\..')
Set-Location $repo

$outDir = 'workshop\Cas\Gen-out'
$tool = 'workshop\Cas\gen\Main.lean'
$guard = 'workshop\Cas\gen\Check.lean'
if (-not (Test-Path $outDir)) { New-Item -ItemType Directory -Force -Path $outDir | Out-Null }

# The manifest: group -> imports, guards, carriers in dependency order. An applied type is one
# word with `@` for the space, so the shell never splits it.
$manifest = @(
  [pscustomobject]@{
    Name    = 'Json'
    Imports = 'Cas.Templates'
    Guards  = 'workshop\Cas\gen\guards-json.lean'
    Types   = @('Effect4.Float64', 'Effect4.Json')
  },
  [pscustomobject]@{
    Name    = 'Program'
    Imports = 'Cas.Program'
    Guards  = 'workshop\Cas\gen\guards-program.lean'
    Types   = @(
      'Effect4.Program.Lit', 'Effect4.Machine.FnName', 'Effect4.FinalizerStrategy',
      'Effect4.Supervision.MaskMode', 'Effect4.Supervision.ObserverMode',
      'Effect4.Program.NativeOp', 'Effect4.Supervision.ForkOptions', 'Effect4.Program.Term',
      'Effect4.Program.CauseTerm', 'Effect4.Program.Eff@Effect4.Program.NativeOp')
  },
  [pscustomobject]@{
    Name    = 'Schema'
    Imports = 'Cas.Templates'
    Guards  = 'workshop\Cas\gen\guards-schema.lean'
    Types   = @(
      'Effect4.ReferenceKey', 'Effect4.GlobalSymbolKey', 'Effect4.AnnotationEntry',
      'Effect4.LiteralValue', 'Effect4.EnumValue', 'Effect4.EnumEntry', 'Effect4.PropertyKey',
      'Effect4.RepresentationAnnotation', 'Effect4.UnionMode', 'Effect4.Representation',
      'Effect4.ReferenceEntry', 'Effect4.Document', 'Effect4.MultiDocument')
  }
)

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
  $file = Join-Path $outDir ($g.Name + '.lean')
  $files += $file
  $before = Get-FileHashOrEmpty $file
  $a = @('env', 'lean', '-M', '4096', '--run', $tool,
         '--group', $g.Name, '--imports', $g.Imports, '--out', $file)
  if ($g.Guards -ne '' -and (Test-Path $g.Guards)) { $a += @('--append', $g.Guards) }
  $a += $g.Types
  $r = Invoke-Lean -LeanArgs $a -Label ("generate " + $g.Name)
  if ($r.Code -ne 0) {
    Write-Host ("FAILED  {0}: the generator exited {1}" -f $g.Name, $r.Code) -ForegroundColor Red
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
if ($Verify -and $changed.Count -gt 0) {
  Write-Host 'refusing: a generated file changed; commit the regenerated files' -ForegroundColor Red
  exit 1
}
exit 0
