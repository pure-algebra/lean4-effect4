# The 158-program corpus on the wasm host, under the Windows node (node is not on the WSL
# PATH). The wasm twin of `ocaml/avatar/tools/run-corpus-jsoo.ps1`, line for line: same
# program list, same environment variables, same "\n"-joined write, so the faces are
# byte-comparable with the WSL ones.
#
#   pwsh ocaml/wasm/tools/run-corpus-wasm.ps1 [mode] [outdir]
#
# Writes <outdir>/wasm-<mode>/<program>.tsv (default outdir: ocaml/wasm/out/corpus).
# Build first:  wsl -e bash ocaml/wasm/tools/build-wasm.sh <mode>
param([string]$Mode = 'cps', [string]$OutDir = '')
$here = Split-Path -Parent $MyInvocation.MyCommand.Path
$wasmDir = Split-Path -Parent $here                       # <repo>/ocaml/wasm
$repo = Split-Path -Parent (Split-Path -Parent $wasmDir)  # <repo>
if (-not $OutDir) { $OutDir = Join-Path $wasmDir 'out\corpus' }

$js = wsl -e wslpath -w "/home/kokok/Dev/e4-wasm/avatar-$Mode/_build/default/avatar_main.bc.wasm.js"
if (-not (Test-Path $js)) { throw "no avatar_main.bc.wasm.js for mode '$Mode': run build-wasm.sh $Mode" }
Write-Output "binary: $js"

$progs = (Select-String -Path (Join-Path $repo 'ocaml\avatar\corpus\programs.txt') -Pattern '^prog (\S+)').Matches |
  ForEach-Object { $_.Groups[1].Value }
$dest = Join-Path $OutDir "wasm-$Mode"
New-Item -ItemType Directory -Force $dest | Out-Null
$ok = 0; $bad = 0
$sw = [System.Diagnostics.Stopwatch]::StartNew()
foreach ($p in $progs) {
  $env:EFFECT4_FAMILY = 'corpus'; $env:EFFECT4_PROGRAM = $p
  $target = Join-Path $dest "$p.tsv"
  $text = & node $js 2>$null
  if ($LASTEXITCODE -eq 0) { $ok++ } else { $bad++; Write-Output "WASM-FAIL $p" }
  # `node` prints with "\n"; join the lines back with "\n" so the file is byte-comparable
  # with the WSL faces.
  [System.IO.File]::WriteAllText($target, (($text -join "`n") + "`n"))
}
$sw.Stop()
Remove-Item Env:EFFECT4_FAMILY, Env:EFFECT4_PROGRAM -ErrorAction SilentlyContinue
Write-Output "wasm-$Mode ok=$ok bad=$bad wall=$([math]::Round($sw.Elapsed.TotalSeconds,1))s -> $dest"
