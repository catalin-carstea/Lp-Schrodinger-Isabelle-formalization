[CmdletBinding()]
param(
    [switch]$SkipBuild,
    [string]$IsabelleHome,
    [string]$AfpThys,
    [string]$IsabelleUser
)
$ErrorActionPreference = 'Stop'
# Windows PowerShell 5.1 and PowerShell 7 share the same Python checker.
$python = $null
$prefix = @()
foreach ($name in @('py', 'python3', 'python')) {
    $candidate = Get-Command $name -CommandType Application -ErrorAction SilentlyContinue | Select-Object -First 1
    if (-not $candidate) { continue }
    $probeArgs = @()
    if ($name -eq 'py') { $probeArgs += '-3' }
    $probeArgs += @('-c', 'import sys; sys.exit(0 if sys.version_info >= (3, 10) else 1)')
    & $candidate.Source @probeArgs 2>$null
    if ($LASTEXITCODE -eq 0) {
        $python = $candidate.Source
        if ($name -eq 'py') { $prefix = @('-3') }
        break
    }
}
if (-not $python) { throw 'Install Python 3.10 or newer, then reopen your terminal.' }
$arguments = @($prefix) + @('-B', (Join-Path $PSScriptRoot 'check.py'))
if ($SkipBuild) { $arguments += '--skip-build' }
if ($IsabelleHome) { $arguments += @('--isabelle-home', $IsabelleHome) }
if ($AfpThys) { $arguments += @('--afp-thys', $AfpThys) }
if ($IsabelleUser) { $arguments += @('--isabelle-user', $IsabelleUser) }
& $python @arguments
exit $LASTEXITCODE
