# The value probe on every host, under the Windows node (node is not on the WSL PATH).
#
#   pwsh ocaml/wasm/tools/run-probes.ps1
#
# Writes ocaml/wasm/out/probe.<host>.tsv for native, byte, jsoo, wasm-cps and wasm-jspi
# (the last two with and without `--experimental-wasm-jspi`), and prints a comparison.
# Build first:  wsl -e bash ocaml/wasm/tools/build-probe.sh cps
#               wsl -e bash ocaml/wasm/tools/build-probe.sh jspi wasm-only
$ErrorActionPreference = 'Continue'
$here = Split-Path -Parent $MyInvocation.MyCommand.Path
$out = Join-Path (Split-Path -Parent $here) 'out'
New-Item -ItemType Directory -Force $out | Out-Null
$B = '/home/kokok/Dev/e4-wasm/probe'

function Run-Node([string]$wslPath, [string]$tag, [string[]]$nodeArgs) {
  $w = wsl -e wslpath -w $wslPath
  $target = Join-Path $out "probe.$tag.tsv"
  $err = Join-Path $out "probe.$tag.err"
  $all = & node @nodeArgs $w 2>$err
  $code = $LASTEXITCODE
  [System.IO.File]::WriteAllText($target, (($all -join "`n") + "`n"))
  $e = (Get-Content $err -Raw -ErrorAction SilentlyContinue)
  Write-Output "$tag exit=$code stderr=$(if ($e) { $e.Trim() } else { '<none>' })"
}

# native and bytecode, inside WSL
wsl -e bash -c "$B/jsoo/_build/default/probe.exe" |
  Set-Content -Encoding utf8 (Join-Path $out 'probe.native.tsv')
wsl -e bash -lc "eval `$(opam env --switch=effect4 --set-switch) && ocamlrun $B/jsoo/_build/default/probe.bc" |
  Set-Content -Encoding utf8 (Join-Path $out 'probe.byte.tsv')

Run-Node "$B/jsoo/_build/default/probe.bc.js"      'jsoo'          @()
Run-Node "$B/wasm-cps/_build/default/probe.bc.wasm.js"  'wasm-cps'  @()
Run-Node "$B/wasm-jspi/_build/default/probe.bc.wasm.js" 'wasm-jspi' @()
Run-Node "$B/wasm-jspi/_build/default/probe.bc.wasm.js" 'wasm-jspi-flag' @('--experimental-wasm-jspi')

Write-Output ''
Write-Output 'key                  native               jsoo                 wasm-cps'
$n = @{}; $j = @{}; $w = @{}
foreach ($pair in @(@('probe.native.tsv', $n), @('probe.jsoo.tsv', $j), @('probe.wasm-cps.tsv', $w))) {
  Get-Content (Join-Path $out $pair[0]) | ForEach-Object {
    $f = $_ -split "`t"; if ($f.Count -ge 2) { $pair[1][$f[0]] = $f[1] } }
}
foreach ($k in $n.Keys) {
  $mark = if ($n[$k] -ne $w[$k] -or $j[$k] -ne $w[$k]) { ' *' } else { '' }
  '{0,-20} {1,-20} {2,-20} {3}{4}' -f $k, $n[$k], $j[$k], $w[$k], $mark | Write-Output
}
# This is a reporter: a host that refuses (wasm-jspi on node < 25) is a printed row above,
# not a failure of the script. Exit 0 so a caller sees the report, not the last node's code.
exit 0
