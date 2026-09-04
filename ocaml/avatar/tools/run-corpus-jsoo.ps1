# The corpus on the js_of_ocaml face, run under the Windows `node` (node is not on the WSL
# PATH). Companion of `run-corpus-wsl.sh`.
#
#   pwsh tools/run-corpus-jsoo.ps1 <outdir>
#
# Writes <outdir>/jsoo/<program>.tsv, one per `prog` line of `corpus/programs.txt`.
#
# The binary: the workspace build (`dune build avatar` from `ocaml/`, into
# `ocaml/_build/default/avatar/`) is preferred; the project-local `--root .` build
# (`avatar/_build/default/`) is the fallback.
param([Parameter(Mandatory = $true)][string]$OutDir)
$here = Split-Path -Parent (Split-Path -Parent $MyInvocation.MyCommand.Path)
$js = Join-Path (Split-Path -Parent $here) '_build\default\avatar\avatar_main.bc.js'
if (-not (Test-Path $js)) { $js = Join-Path $here '_build\default\avatar_main.bc.js' }
if (-not (Test-Path $js)) { throw "no avatar_main.bc.js: build with 'dune build avatar' from ocaml/" }
Write-Output "binary: $js"
$progs = (Select-String -Path (Join-Path $here 'corpus\programs.txt') -Pattern '^prog (\S+)').Matches |
  ForEach-Object { $_.Groups[1].Value }
New-Item -ItemType Directory -Force (Join-Path $OutDir 'jsoo') | Out-Null
$ok = 0; $bad = 0
foreach ($p in $progs) {
  $env:EFFECT4_FAMILY = 'corpus'; $env:EFFECT4_PROGRAM = $p
  $target = Join-Path $OutDir "jsoo\$p.tsv"
  $text = & node $js 2>$null
  if ($LASTEXITCODE -eq 0) { $ok++ } else { $bad++; Write-Output "JSOO-FAIL $p" }
  # `node` prints with "\n"; join the lines back with "\n" so the file is byte-comparable
  # with the WSL faces.
  [System.IO.File]::WriteAllText($target, (($text -join "`n") + "`n"))
}
Remove-Item Env:EFFECT4_FAMILY, Env:EFFECT4_PROGRAM -ErrorAction SilentlyContinue
Write-Output "jsoo ok=$ok bad=$bad"
