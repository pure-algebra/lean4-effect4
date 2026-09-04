# The rc.112 face of the corpus (`corpus_rc112.mjs`) under the Windows `node`, over the
# vendored effect package at `C:\Users\kokok\Dev\effect4-host\node_modules`. Companion of
# `run-corpus-wsl.sh`; the classification is `run-corpus.sh`'s ("no rc.112 surface" is a
# skip, any other failure is "did not terminate").
#
#   pwsh tools/run-corpus-rc112.ps1 <outdir>
#
# Writes <outdir>/rc112/<program>.tsv and <outdir>/rc112-skips.txt.
param([Parameter(Mandatory = $true)][string]$OutDir)
$here = Split-Path -Parent (Split-Path -Parent $MyInvocation.MyCommand.Path)
$progs = (Select-String -Path (Join-Path $here 'corpus\programs.txt') -Pattern '^prog (\S+)').Matches |
  ForEach-Object { $_.Groups[1].Value }
$rc = Join-Path $OutDir 'rc112'
New-Item -ItemType Directory -Force $rc | Out-Null
$skips = Join-Path $OutDir 'rc112-skips.txt'
Set-Content -Path $skips -Value ''
$ok = 0; $skip = 0; $bad = 0
Push-Location $here
try {
  foreach ($p in $progs) {
    # a `file://` URL: `corpus_rc112.mjs` does `import(`${nm}/effect/dist/index.js`)`, and
    # node's ESM loader rejects a bare Windows drive path
    $env:EFFECT4_NODE_MODULES = 'file:///C:/Users/kokok/Dev/effect4-host/node_modules'
    $env:EFFECT4_CORPUS = 'corpus/programs.txt'
    $env:EFFECT4_PROGRAM = $p
    $outFile = Join-Path $rc "$p.tsv"
    $errFile = Join-Path $rc "$p.err"
    $proc = Start-Process -FilePath 'node' -ArgumentList 'corpus_rc112.mjs' -NoNewWindow -PassThru `
      -RedirectStandardOutput $outFile -RedirectStandardError $errFile
    if (-not $proc.WaitForExit(8000)) { try { $proc.Kill() } catch {}; $code = -1 } else { $code = $proc.ExitCode }
    if ($code -eq 0) { $ok++ }
    elseif ((Get-Content $errFile -Raw) -match 'no rc\.112 surface') {
      $skip++; Remove-Item $outFile -ErrorAction SilentlyContinue
      Add-Content $skips "$p`tno-rc112-surface`t$((Get-Content $errFile -TotalCount 1))"
    }
    else {
      $bad++; Remove-Item $outFile -ErrorAction SilentlyContinue
      Add-Content $skips "$p`trc112-did-not-terminate`t$((Get-Content $errFile -TotalCount 1))"
    }
  }
}
finally { Pop-Location }
Remove-Item Env:EFFECT4_NODE_MODULES, Env:EFFECT4_CORPUS, Env:EFFECT4_PROGRAM -ErrorAction SilentlyContinue
Write-Output "rc112 ok=$ok skipped=$skip nonterminating=$bad"
