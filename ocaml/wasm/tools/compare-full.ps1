# Full-byte comparison of two corpus face directories — headers included.
#
#   pwsh ocaml/wasm/tools/compare-full.ps1 <dirA> <dirB>
#
# `compare-wasm.sh` (and the avatar's `compare-faces.sh`) compare the event rows only,
# because a face's header rows carry that run's own digests and pin. Two runs made by the
# same runner with the same environment have the same headers too, so wasm-cps against a
# freshly-run jsoo face can be compared whole — a strictly stronger claim. Use this only
# between two faces produced in the same pass; against the committed `out/corpus/*.ocaml.tsv`
# use `compare-wasm.sh`.
param([Parameter(Mandatory = $true)][string]$A, [Parameter(Mandatory = $true)][string]$B)
$same = 0; $diff = 0; $missing = 0; $firstDiff = $null
foreach ($f in Get-ChildItem $A -Filter *.tsv) {
  $g = Join-Path $B $f.Name
  if (-not (Test-Path $g)) { $missing++; Write-Output "MISSING $($f.Name)"; continue }
  if ((Get-FileHash $f.FullName -Algorithm SHA256).Hash -eq (Get-FileHash $g -Algorithm SHA256).Hash) {
    $same++
  } else {
    $diff++; Write-Output "DIFFER $($f.Name)"
    if (-not $firstDiff) { $firstDiff = $f.Name }
  }
}
Write-Output "full-byte: identical=$same differing=$diff missing=$missing"
if ($firstDiff) {
  Write-Output "--- first differing rows of $firstDiff ---"
  Compare-Object (Get-Content (Join-Path $A $firstDiff)) (Get-Content (Join-Path $B $firstDiff)) |
    Select-Object -First 6 | Format-Table -AutoSize
}
