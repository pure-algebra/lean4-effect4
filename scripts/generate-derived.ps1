<#
.SYNOPSIS
  Regenerate every derived `Canonical` group in the tree and report what changed.

.DESCRIPTION
  The manifest below is the one of docs\research\2026-09-04-cas-trait-plan.md §4 at its landing
  paths: one group per emitted file, its imports, its carriers in dependency order, the
  `--kind` requests (a `Content` instance right after that carrier's `Canonical` one), and the
  acceptance guards appended verbatim after the generated declarations.

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

# The manifest: group -> imports, output, guards, kinds, carriers in dependency order. An applied
# type is one word with `@` for the space, so the shell never splits it.
$manifest = @(
  [pscustomobject]@{
    Name    = 'Json'
    Imports = 'Effect4.Store.Canonical'
    Out     = 'src\Effect4\Store\Derived\Json.lean'
    Guards  = 'tools\Effect4Gen\guards\json.lean'
    Kinds   = @()
    Types   = @('Effect4.Float64', 'Effect4.Json')
  },
  [pscustomobject]@{
    # The Schema carriers hold `Json` and `Float64` fields, whose instances are the Json group's.
    Name    = 'Schema'
    Imports = 'Effect4.Store.Derived.Json'
    Out     = 'src\Effect4\Store\Derived\Schema.lean'
    Guards  = 'tools\Effect4Gen\guards\schema.lean'
    Kinds   = @()
    Types   = @(
      'Effect4.ReferenceKey', 'Effect4.GlobalSymbolKey', 'Effect4.AnnotationEntry',
      'Effect4.LiteralValue', 'Effect4.EnumValue', 'Effect4.EnumEntry', 'Effect4.PropertyKey',
      'Effect4.RepresentationAnnotation', 'Effect4.UnionMode', 'Effect4.Representation',
      'Effect4.ReferenceEntry', 'Effect4.Document', 'Effect4.MultiDocument')
  },
  [pscustomobject]@{
    Name    = 'Program'
    Imports = 'Effect4.Program.Native,Effect4.Store.Canonical'
    Out     = 'src\Effect4\Program\Derived.lean'
    Guards  = 'tools\Effect4Gen\guards\program.lean'
    Kinds   = @()
    Types   = @(
      'Effect4.Program.Lit', 'Effect4.Machine.FnName', 'Effect4.FinalizerStrategy',
      'Effect4.Supervision.MaskMode', 'Effect4.Supervision.ObserverMode',
      'Effect4.Program.NativeOp', 'Effect4.Supervision.ForkOptions', 'Effect4.Program.Term',
      'Effect4.Program.CauseTerm', 'Effect4.Program.Eff@Effect4.Program.NativeOp')
  },
  [pscustomobject]@{
    # `Tree` is the store's own carrier (a name space as content, `Store/Node.lean`); its
    # instance is emitted here beside `Pin`'s so no area above the store supplies a store type's
    # instance (coordinator, 2026-09-05, after lane C's note).
    Name    = 'Pin'
    Imports = 'Effect4.Store.Pin,Effect4.Store.Node'
    Out     = 'src\Effect4\Store\PinDerived.lean'
    Guards  = 'tools\Effect4Gen\guards\pin.lean'
    Kinds   = @('Effect4.Store.Pin=source', 'Effect4.Store.Tree=tree')
    Types   = @('Effect4.Store.PinRole', 'Effect4.Store.Pin', 'Effect4.Store.Tree')
  },
  [pscustomobject]@{
    # The census (lane C): sources first, because `Entry.source : Ref Source` needs the kind.
    # No appended guards: `Links.lean` and `Rc112.lean` exercise the laws over the real census.
    Name    = 'StdLib'
    Imports = 'Effect4.Evidence.StdLib.Entry'
    Out     = 'src\Effect4\Evidence\StdLib\Derived.lean'
    Guards  = ''
    Kinds   = @('Effect4.StdLib.Source=source', 'Effect4.StdLib.Entry=export')
    Types   = @('Effect4.StdLib.ExportKind', 'Effect4.StdLib.Source', 'Effect4.StdLib.Entry')
  },
  [pscustomobject]@{
    # The Char room (lane X). `Implementation`, `Receipt` and `Label` are hand instances in the
    # room (ordering: they sit below `Char/Evidence.lean`); `Evidence` joins this group once the
    # non-recursive sum reader is fixed (see NOTES-X.md, open item 1). The acceptance guards are
    # `#guard`s in the room, not an appended fragment.
    Name    = 'Char'
    Imports = 'Effect4.Evidence.Char.Conformance.Surface'
    Out     = 'src\Effect4\Evidence\Char\Derived.lean'
    Guards  = ''
    Kinds   = @('Effect4.Char.Evidence=annotation', 'Effect4.Char.Claim=annotation',
                'Effect4.Char.Manifest=component', 'Effect4.Char.Target=annotation',
                'Effect4.Char.Characterized=annotation')
    Types   = @(
      'Effect4.Char.Rung', 'Effect4.Char.ClaimKind', 'Effect4.Char.Evidence', 'Effect4.Char.Claim',
      'Effect4.Char.Entry', 'Effect4.Char.Grade', 'Effect4.Char.Verb', 'Effect4.Char.GradeRow',
      'Effect4.Char.Manifest', 'Effect4.Char.Failure@String', 'Effect4.Char.Target',
      'Effect4.Char.ClaimRung', 'Effect4.Char.Characterized')
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
