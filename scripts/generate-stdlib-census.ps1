# Deterministic export census of the pinned Effect v4 standard library.
#
# One row per `export` declaration of each listed public module of the pinned
# install, with the file's SHA-256 and the declaration's line. The census is
# what `src/Effect4/Evidence/StdLib/Rc112.lean` (generated here, do not edit) carries as
# data: a `Source` per file and an `Entry` per export, each entry pointing at
# its file's node through `source : Ref Source`.
#
# The file keeps names only. Digests cross as hexadecimal literals read by
# `StdLib.digestOfHex` (guarded row by row below), and the entries' source
# references are computed from the sources at elaboration through the
# `sourceAddresses` table, so no address literal is ever written: an address is
# a function of the value under version byte 0 and would go stale silently.
#
# The pinned install is read, never vendored: the digest of each file is the
# pin, and a run against a different install fails on the package version.
#
# Usage: pwsh scripts/generate-stdlib-census.ps1 [-Install <node_modules/effect>]
param(
  [string]$Install = 'C:\Users\kokok\Dev\effect4-host\node_modules\effect',
  [string[]]$Modules = @('Effect', 'Ref', 'Deferred', 'Scope', 'Layer', 'Context', 'Fiber',
    'Exit', 'Cause', 'Option', 'Result', 'Schema', 'Queue', 'PubSub', 'Stream', 'Sink',
    'Channel', 'Schedule', 'Duration', 'Runtime', 'Scheduler')
)
$ErrorActionPreference = 'Stop'
$repo = Split-Path -Parent $PSScriptRoot
$expectedVersion = '4.0.0-rc.112'
$pkg = Get-Content (Join-Path $Install 'package.json') -Raw | ConvertFrom-Json
if ($pkg.version -ne $expectedVersion) { throw "pinned install is $($pkg.version), expected $expectedVersion" }

$kindOf = @{ 'const' = 'const'; 'function' = 'function'; 'class' = 'class'; 'abstract class' = 'class';
  'interface' = 'interface'; 'type' = 'type'; 'namespace' = 'namespace' }
$pattern = '^export (?:declare )?(const|function|abstract class|class|interface|type|namespace) ([A-Za-z_$][A-Za-z0-9_$]*)'

$files = @(); $rows = @()
foreach ($m in $Modules) {
  $file = Join-Path $Install "src/$m.ts"
  if (-not (Test-Path $file)) { throw "module $m has no source at $file" }
  $sha = (Get-FileHash -Algorithm SHA256 $file).Hash.ToLower()
  $files += [pscustomobject]@{ module = $m; file = "src/$m.ts"; sha256 = $sha }
  $lines = @(Get-Content $file)
  # Local declarations by name, for the aliased exports below: a reserved word
  # is exported as `export { await_ as await }`, and its kind and line are the
  # local declaration's.
  $locals = @{}
  $n = 0
  foreach ($line in $lines) {
    $n++
    $local = [regex]::Match($line, '^(?:export )?(?:declare )?(const|function|abstract class|class|interface|type|namespace) ([A-Za-z_$][A-Za-z0-9_$]*)')
    if ($local.Success -and -not $locals.ContainsKey($local.Groups[2].Value)) {
      $locals[$local.Groups[2].Value] = @{ kind = $kindOf[$local.Groups[1].Value]; line = $n }
    }
  }
  $n = 0; $inBlock = $false
  foreach ($line in $lines) {
    $n++
    $match = [regex]::Match($line, $pattern)
    if ($match.Success) {
      $rows += [pscustomobject]@{ module = $m; name = $match.Groups[2].Value; kind = $kindOf[$match.Groups[1].Value]; line = $n; sha256 = $sha }
      continue
    }
    # `export { a as b, c }` blocks: one row per exported name, at the local
    # declaration's kind and line when it is declared in this file.
    if ($line -match '^export \{\s*$') { $inBlock = $true; continue }
    if ($inBlock) {
      if ($line -match '^\}') { $inBlock = $false; continue }
      $alias = [regex]::Match($line, '^\s*([A-Za-z_$][A-Za-z0-9_$]*)(?:\s+as\s+([A-Za-z_$][A-Za-z0-9_$]*))?\s*,?\s*$')
      if ($alias.Success) {
        $local = $alias.Groups[1].Value
        $exported = if ($alias.Groups[2].Success) { $alias.Groups[2].Value } else { $local }
        if ($locals.ContainsKey($local)) {
          $rows += [pscustomobject]@{ module = $m; name = $exported; kind = $locals[$local].kind; line = $locals[$local].line; sha256 = $sha }
        } else {
          $rows += [pscustomobject]@{ module = $m; name = $exported; kind = 'const'; line = $n; sha256 = $sha }
        }
      }
    }
  }
}

# The TSV: the record every other face is checked against.
$tsv = @("format`teffect4-stdlib-census-v1", "pin`teffect`t$expectedVersion", "generator`tscripts/generate-stdlib-census.ps1")
foreach ($f in $files) { $tsv += "input`t$($f.file)`tsha256=$($f.sha256)" }
$tsv += "columns`tmodule`tname`tkind`tline"
foreach ($r in $rows) { $tsv += "row`t$($r.module)`t$($r.name)`t$($r.kind)`t$($r.line)" }
$enc = New-Object System.Text.UTF8Encoding $false
[IO.File]::WriteAllText((Join-Path $repo 'generated/stdlib-census.tsv'), ($tsv -join "`n") + "`n", $enc)

# The Lean data module: chunks of two hundred so no list literal is unwieldy.
function LeanStr($s) { '"' + ($s -replace '\\', '\\\\' -replace '"', '\"') + '"' }
$lean = @()
$lean += 'import Effect4.Evidence.StdLib.Derived'
$lean += ''
$lean += '/-!'
$lean += '# StdLib.Rc112'
$lean += ''
$lean += 'Generated by `scripts/generate-stdlib-census.ps1` from the pinned `effect@4.0.0-rc.112`'
$lean += 'install: one `Source` per file read, with its SHA-256, and one `Entry` per `export`'
$lean += 'declaration of each listed public module, with the declaration''s line. The census TSV is'
$lean += '`generated/stdlib-census.tsv`.'
$lean += ''
$lean += 'The file carries names only. A digest is a hexadecimal literal read by `digestOfHex`, and the'
$lean += 'guards below refuse the module if any literal is not thirty-two bytes of hexadecimal.'
$lean += 'An entry''s `source` is not a literal either: `entries` fills it from `sourceAddresses`, the'
$lean += 'twenty-one-row table of the pinned files'' addresses, so a change to any carrier''s shape'
$lean += 'moves every reference at once instead of leaving a stale address behind.'
$lean += ''
$lean += 'Do not edit.'
$lean += '-/'
$lean += ''
$lean += 'set_option autoImplicit false'
$lean += ''
$lean += 'namespace Effect4.StdLib.Rc112'
$lean += ''
$lean += 'open Effect4.Store'
$lean += ''
$lean += '/-- The pinned files as the instrument read them: module, path, SHA-256 in hexadecimal. -/'
$lean += 'def rawSources : List (String × String × String) :='
$lean += '  [ ' + (($files | ForEach-Object { "($(LeanStr $_.module), $(LeanStr $_.file), $(LeanStr $_.sha256))" }) -join "`n  , ")
$lean += '  ]'
$lean += ''
$lean += '/-- The pinned files, by module. -/'
$lean += 'def sources : List Source :='
$lean += '  rawSources.map fun row => ⟨row.1, row.2.1, digestOfHex row.2.2⟩'
$lean += ''
$lean += '/-- The address of each pinned file''s node, by module: the table `entries` reads so that no'
$lean += 'address literal is ever written. -/'
$lean += 'def sourceAddresses : List (String × Ref Source) :='
$lean += '  sources.map fun source => (source.module, address source)'
$lean += ''
$chunks = [Math]::Ceiling($rows.Count / 200)
for ($c = 0; $c -lt $chunks; $c++) {
  $slice = $rows | Select-Object -Skip ($c * 200) -First 200
  $lean += "private def rawChunk$c : List (String × String × ExportKind × Nat) :="
  $lean += '  [ ' + (($slice | ForEach-Object { "($(LeanStr $_.module), $(LeanStr $_.name), .$($_.kind -replace '^class$','class_' -replace '^namespace$','namespace_'), $($_.line))" }) -join "`n  , ")
  $lean += '  ]'
  $lean += ''
}
$lean += '/-- Every export of the listed modules, in file order: module, name, kind, line. -/'
$lean += 'def rawEntries : List (String × String × ExportKind × Nat) :='
$lean += '  ' + ((0..($chunks - 1) | ForEach-Object { "rawChunk$_" }) -join ' ++ ')
$lean += ''
$lean += '/-- Every export as store content, its `source` filled from the address table. The table is'
$lean += 'read once per traversal: the twenty-one addresses are twenty-one hashes, not one per row. -/'
$lean += 'def entries : List Entry :='
$lean += '  let table := sourceAddresses'
$lean += '  rawEntries.map fun row =>'
$lean += '    ⟨row.1, row.2.1, row.2.2.1, row.2.2.2,'
$lean += '      ((table.find? fun binding => binding.1 == row.1).map Prod.snd).getD ⟨zeroDigest⟩⟩'
$lean += ''
$lean += "/-- The row count the census wrote. -/"
$lean += "def count : Nat := $($rows.Count)"
$lean += ''
$lean += '/-! ## Anti-vacuity: the shape of the data, without an address in sight -/'
$lean += ''
$lean += "#guard rawSources.length = $($files.Count)"
$lean += "#guard rawEntries.length = count"
$lean += '#guard rawSources.all fun row => (Digest.ofHex? row.2.2).isSome'
$lean += '-- Every module a row was written for has a pinned file, so no entry falls back on the'
$lean += '-- zero digest for its source reference.'
$lean += '#guard (rawEntries.map (·.1)).eraseDups.all fun m => rawSources.any fun row => row.1 == m'
$lean += '#guard sources.all fun source => source.sha256 ≠ zeroDigest'
$lean += ''
$lean += '/-! ## Receipts -/'
$lean += ''
$lean += '#print axioms rawSources'
$lean += '#print axioms sources'
$lean += '#print axioms sourceAddresses'
$lean += '#print axioms rawEntries'
$lean += '#print axioms entries'
$lean += ''
$lean += 'end Effect4.StdLib.Rc112'
[IO.File]::WriteAllText((Join-Path $repo 'src/Effect4/Evidence/StdLib/Rc112.lean'), ($lean -join "`n") + "`n", $enc)
"modules: $($files.Count); rows: $($rows.Count)"
$rows | Group-Object module | ForEach-Object { "  {0,-10} {1,5}" -f $_.Name, $_.Count }
