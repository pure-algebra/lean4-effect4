# The avatar's witness and clause report on the wasm host, under the Windows node (node is
# not on the WSL PATH), compared byte for byte with the committed baseline.
#
#   pwsh ocaml/wasm/tools/run-witnesses-wasm.ps1 [mode]        # mode: cps (default) | jspi
#
# Writes ocaml/wasm/out/witnesses-wasm-<mode>.txt and `cmp`s it against
# ocaml/avatar/tools/witnesses-after.txt (identical to ocaml/avatar/out/witnesses.report.tsv,
# the native/bytecode/jsoo baseline: 429 HOLDS, 0 FAILS). Build first:
#   wsl -e bash ocaml/wasm/tools/build-wasm.sh <mode>
#
# `node` prints "\n"; the file is written with "\n" so it compares directly with the
# LF-terminated baseline, exactly as run-corpus-jsoo.ps1 does for the js face.
param([string]$Mode = 'cps')
$here = Split-Path -Parent $MyInvocation.MyCommand.Path
$wasmDir = Split-Path -Parent $here                       # <repo>/ocaml/wasm
$repo = Split-Path -Parent (Split-Path -Parent $wasmDir)  # <repo>
$out = Join-Path $wasmDir 'out'
New-Item -ItemType Directory -Force $out | Out-Null

$js = wsl -e wslpath -w "/home/kokok/Dev/e4-wasm/avatar-$Mode/_build/default/avatar_witnesses.bc.wasm.js"
if (-not (Test-Path $js)) { throw "no avatar_witnesses.bc.wasm.js for mode '$Mode': run build-wasm.sh $Mode" }
Write-Output "binary: $js"

$target = Join-Path $out "witnesses-wasm-$Mode.txt"
$errf = Join-Path $out "witnesses-wasm-$Mode.err"
$sw = [System.Diagnostics.Stopwatch]::StartNew()
$text = & node $js 2>$errf
$sw.Stop()
$code = $LASTEXITCODE
[System.IO.File]::WriteAllText($target, (($text -join "`n") + "`n"))
Write-Output "wasm-$Mode exit=$code wall=$($sw.ElapsedMilliseconds)ms lines=$($text.Count)"
$e = Get-Content $errf -Raw -ErrorAction SilentlyContinue
if ($e) { Write-Output "stderr: $($e.Trim())" }

$baseline = Join-Path $repo 'ocaml\avatar\tools\witnesses-after.txt'
$hb = (Get-FileHash $baseline -Algorithm SHA256).Hash
$hw = (Get-FileHash $target -Algorithm SHA256).Hash
Write-Output "baseline (native = bytecode = jsoo): $baseline"
Write-Output "  sha256 baseline = $hb"
Write-Output "  sha256 wasm     = $hw"
if ($hb -eq $hw) {
  Write-Output "WITNESSES AGREE: wasm-$Mode is byte-identical to the three-host baseline"
} else {
  Write-Output "WITNESSES DISAGREE: first differing lines"
  $a = Get-Content $baseline; $b = Get-Content $target; $shown = 0
  for ($i = 0; $i -lt [Math]::Max($a.Count, $b.Count); $i++) {
    if ($a[$i] -ne $b[$i]) {
      Write-Output ("line {0}`n  baseline: {1}`n  wasm    : {2}" -f ($i + 1), $a[$i], $b[$i])
      if (++$shown -ge 5) { break }
    }
  }
}
# The report's verdict column is tab-prefixed; "HOLDS" also occurs in prose, so count the
# column, not the word. The three-host baseline is 429 HOLDS / 0 FAILS (avatar README §6).
$t = [System.IO.File]::ReadAllText($target)
$holds = ([regex]::Matches($t, "`tHOLDS")).Count
$fails = ([regex]::Matches($t, "`tFAILS")).Count
Write-Output "wasm-$Mode : $holds HOLDS / $fails FAILS"
Select-String -Path $target -Pattern '^(clauses|witnesses|run-clauses|park-guard)' |
  ForEach-Object { $_.Line }
