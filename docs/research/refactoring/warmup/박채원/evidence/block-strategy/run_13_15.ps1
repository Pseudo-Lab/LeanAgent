# Re-run rules 1-7 for warm-up rows 13-15 with the benchmark header (`import Mathlib`),
# Lean v4.26.0 + Mathlib v4.26.0 pinned in project/lake-manifest.json.
# Usage (PowerShell, in this folder):
#   Set-ExecutionPolicy -Scope Process Bypass -Force
#   .\run_13_15.ps1 -Jsonl <benchmark_data_warmup.jsonl>        # add -SkipCache after the first run
param([string]$Jsonl, [string[]]$Rows = @("13", "14", "15"), [switch]$SkipCache)

$ErrorActionPreference = "Stop"
$Rows  = @($Rows | ForEach-Object { $_ -split "," } | Where-Object { $_ } | ForEach-Object { [int]$_ })
$Root  = Split-Path -Parent $MyInvocation.MyCommand.Path
$Proj  = Join-Path $Root "project"
$Res   = Join-Path $Root "results"
if (-not $Jsonl) { throw "give -Jsonl <path to benchmark_data_warmup.jsonl>" }
$Jsonl = (Resolve-Path $Jsonl).Path
$env:PYTHONUTF8 = "1"
function Check($what) { if ($LASTEXITCODE -ne 0) { throw "FAILED: $what (exit $LASTEXITCODE)" } }

if (Get-Command py -ErrorAction SilentlyContinue)         { $Py = "py";     $PyArgs = @("-3", "-X", "utf8") }
elseif (Get-Command python -ErrorAction SilentlyContinue) { $Py = "python"; $PyArgs = @("-X", "utf8") }
else { throw "Python 3 not found." }

Push-Location $Proj
try {
    if (-not $SkipCache) { lake exe cache get; Check "lake exe cache get" }
    lake env lean Smoke.lean; Check "import Mathlib smoke test"
} finally { Pop-Location }

foreach ($k in $Rows) {
    & $Py @PyArgs (Join-Path $Root "prune_unused.py") --jsonl $Jsonl --row $k --project $Proj `
        --out (Join-Path $Res "prune$k"); Check "prune_unused row $k"
    & $Py @PyArgs (Join-Path $Root "block_dp.py") --jsonl $Jsonl --row $k --project $Proj `
        --prune (Join-Path $Res "prune$k") --out (Join-Path $Res "dp$k"); Check "block_dp row $k"
}
$files = @($Rows | ForEach-Object { Join-Path $Res "dp$_\result.json" })
& $Py @PyArgs (Join-Path $Root "reduction_ci.py") @files --md (Join-Path $Res "ci.md") `
    --json (Join-Path $Res "ci.json"); Check "reduction_ci"
