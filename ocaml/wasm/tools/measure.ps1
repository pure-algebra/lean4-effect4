# The spike's numbers, each one a command. Writes ocaml/wasm/out/measurements.tsv.
#
#   pwsh ocaml/wasm/tools/measure.ps1 [-Runs 3] [-SkipCorpus]
#
# Hosts: native and bytecode in WSL (the pinned `effect4` switch), jsoo and wasm under the
# Windows node. The jsoo/native/bytecode binaries are the workspace build
# (`cd ocaml && dune build avatar`); the wasm ones are `build-wasm.sh cps`'s.
# Best of N for the witness report; one timed pass for the corpus (158 programs).
param([int]$Runs = 3, [switch]$SkipCorpus)
$here = Split-Path -Parent $MyInvocation.MyCommand.Path
$wasmDir = Split-Path -Parent $here
$repo = Split-Path -Parent (Split-Path -Parent $wasmDir)
$out = Join-Path $wasmDir 'out'
New-Item -ItemType Directory -Force $out | Out-Null
$rows = New-Object System.Collections.ArrayList
function Row($what, $host_, $cmd, $value) {
  [void]$rows.Add(("{0}`t{1}`t{2}`t{3}" -f $what, $host_, $cmd, $value))
  Write-Output ("{0,-22} {1,-12} {2}" -f $what, $host_, $value)
}

$wb = '/home/kokok/Dev/e4-wasm/avatar-cps/_build/default'
$ab = "$repo\ocaml\_build\default\avatar"          # the workspace build, Windows path
$abWsl = (wsl -e wslpath -u $ab.Replace('\', '/')) # ... and the same as WSL sees it
$repoWsl = (wsl -e wslpath -u $repo.Replace('\', '/'))
$wWit = wsl -e wslpath -w "$wb/avatar_witnesses.bc.wasm.js"
$wMain = wsl -e wslpath -w "$wb/avatar_main.bc.wasm.js"

# ---- sizes -------------------------------------------------------------------------------
$jsooWit = (Get-Item "$ab\avatar_witnesses.bc.js").Length
$jsooMain = (Get-Item "$ab\avatar_main.bc.js").Length
Row 'size witnesses' 'jsoo' 'avatar_witnesses.bc.js' "$jsooWit B"
Row 'size witnesses' 'native' 'avatar_witnesses.exe' "$((Get-Item "$ab\avatar_witnesses.exe").Length) B"
Row 'size witnesses' 'bytecode' 'avatar_witnesses.bc' "$((Get-Item "$ab\avatar_witnesses.bc").Length) B"
foreach ($t in @(@('witnesses', 'avatar_witnesses'), @('main', 'avatar_main'))) {
  $loader = [int](wsl -e bash -c "stat -c %s $wb/$($t[1]).bc.wasm.js")
  $assets = [int](wsl -e bash -c "du -sb $wb/$($t[1]).bc.wasm.assets | cut -f1")
  $wasmOnly = [int](wsl -e bash -c "cat $wb/$($t[1]).bc.wasm.assets/*.wasm | wc -c")
  Row "size $($t[0])" 'wasm-cps' "$($t[1]).bc.wasm.js + .assets" "$loader B loader + $assets B assets ($wasmOnly B of .wasm)"
}
Row 'size main' 'jsoo' 'avatar_main.bc.js' "$jsooMain B"

# ---- witness report, best of $Runs -------------------------------------------------------
function Best($n, $sb) {
  $best = [double]::MaxValue
  for ($i = 0; $i -lt $n; $i++) {
    $sw = [System.Diagnostics.Stopwatch]::StartNew(); & $sb | Out-Null; $sw.Stop()
    if ($sw.Elapsed.TotalMilliseconds -lt $best) { $best = $sw.Elapsed.TotalMilliseconds }
  }
  [math]::Round($best)
}
Row "witnesses best-of-$Runs" 'native' 'avatar_witnesses.exe (in WSL)' `
  "$(Best $Runs { wsl -e bash -c "$abWsl/avatar_witnesses.exe" }) ms"
Row "witnesses best-of-$Runs" 'wasm-cps' 'node avatar_witnesses.bc.wasm.js' `
  "$(Best $Runs { & node $wWit }) ms"
Row "witnesses best-of-$Runs" 'jsoo' 'node avatar_witnesses.bc.js' `
  "$(Best $Runs { & node "$ab\avatar_witnesses.bc.js" }) ms"

# ---- corpus, 158 programs ----------------------------------------------------------------
if (-not $SkipCorpus) {
  $progs = (Select-String -Path "$repo\ocaml\avatar\corpus\programs.txt" -Pattern '^prog (\S+)').Matches |
    ForEach-Object { $_.Groups[1].Value }
  function CorpusTime($sb) {
    $sw = [System.Diagnostics.Stopwatch]::StartNew()
    foreach ($p in $progs) { $env:EFFECT4_FAMILY = 'corpus'; $env:EFFECT4_PROGRAM = $p; & $sb | Out-Null }
    $sw.Stop(); Remove-Item Env:EFFECT4_FAMILY, Env:EFFECT4_PROGRAM -ErrorAction SilentlyContinue
    [math]::Round($sw.Elapsed.TotalSeconds, 1)
  }
  Row 'corpus 158' 'wasm-cps' 'node avatar_main.bc.wasm.js x158' "$(CorpusTime { & node $wMain 2>$null }) s"
  Row 'corpus 158' 'jsoo' 'node avatar_main.bc.js x158' "$(CorpusTime { & node "$ab\avatar_main.bc.js" 2>$null }) s"
  # native: one WSL process per program, as run-corpus-wsl.sh does.
  $sw = [System.Diagnostics.Stopwatch]::StartNew()
  wsl -e bash -c "cd $abWsl && for p in `$(grep '^prog ' $repoWsl/ocaml/avatar/corpus/programs.txt | awk '{print `$2}' | tr -d '\r'); do EFFECT4_FAMILY=corpus EFFECT4_PROGRAM=`$p ./avatar_main.exe > /dev/null; done" 2>$null | Out-Null
  $sw.Stop()
  Row 'corpus 158' 'native' 'avatar_main.exe x158 (in WSL)' "$([math]::Round($sw.Elapsed.TotalSeconds,1)) s"
}

$rows | Set-Content -Encoding utf8 (Join-Path $out 'measurements.tsv')
Write-Output "-> $(Join-Path $out 'measurements.tsv')"
