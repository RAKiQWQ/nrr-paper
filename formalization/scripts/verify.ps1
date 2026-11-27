param(
    [string]$LeanBin = '',
    [ValidateRange(1, 64)][int]$LeanThreads = 2
)

$ErrorActionPreference = 'Stop'
$projectRoot = Split-Path -Parent $PSScriptRoot
$previousPath = $env:PATH
$previousThreads = $env:LEAN_NUM_THREADS

Push-Location -LiteralPath $projectRoot
try {
    if ($LeanBin) {
        if (-not (Test-Path -LiteralPath (Join-Path $LeanBin 'lake.exe'))) {
            throw "lake.exe was not found in $LeanBin"
        }
        $env:PATH = $LeanBin + [IO.Path]::PathSeparator + $env:PATH
    }
    $env:LEAN_NUM_THREADS = [string]$LeanThreads

    # Every project source must be reachable from the default import root.
    # Otherwise a successful lake build could silently omit unfinished files.
    $reachable = [Collections.Generic.HashSet[string]]::new([StringComparer]::OrdinalIgnoreCase)
    $pending = [Collections.Generic.Stack[string]]::new()
    $pending.Push((Join-Path $projectRoot 'NRR.lean'))
    while ($pending.Count -gt 0) {
        $sourcePath = $pending.Pop()
        if (-not $reachable.Add($sourcePath)) { continue }
        foreach ($line in Get-Content -LiteralPath $sourcePath -Encoding utf8) {
            if ($line -match '^import\s+(NRR(?:\.[A-Za-z_][A-Za-z0-9_]*)*)\s*$') {
                $modulePath = $Matches[1].Replace('.', [IO.Path]::DirectorySeparatorChar) + '.lean'
                $dependencyPath = Join-Path $projectRoot $modulePath
                if (-not (Test-Path -LiteralPath $dependencyPath)) {
                    throw "Missing project import: $modulePath"
                }
                $pending.Push($dependencyPath)
            }
        }
    }
    $omitted = @(Get-ChildItem -LiteralPath (Join-Path $projectRoot 'NRR') -Filter '*.lean' -File -Recurse |
        Where-Object { -not $reachable.Contains($_.FullName) })
    if ($omitted.Count -gt 0) {
        throw ('Default build omits project sources: ' + (($omitted | ForEach-Object Name) -join ', '))
    }
    Write-Output "Default import closure covers $($reachable.Count) project source files."

    & lake build
    if ($LASTEXITCODE -ne 0) { throw 'Lean project build failed.' }

    & lake env lean ProofAudit.lean
    if ($LASTEXITCODE -ne 0) { throw 'Transitive axiom audit failed.' }

    & python ../scripts/verify.py
    if ($LASTEXITCODE -ne 0) { throw 'Exact arithmetic checks failed.' }
}
finally {
    Pop-Location
    $env:PATH = $previousPath
    $env:LEAN_NUM_THREADS = $previousThreads
}
