param(
    [ValidateRange(1, 65535)]
    [int]$Port = 8010,
    [switch]$SkipBuild
)

$ErrorActionPreference = 'Stop'
Push-Location -LiteralPath $PSScriptRoot
try {
    if (-not $SkipBuild) {
        & lake exe textbook
        if ($LASTEXITCODE -ne 0) { throw '교재 생성에 실패했다.' }
    }
    $pythonPath = $null
    foreach ($name in @('python', 'python3', 'py')) {
        $candidate = Get-Command $name -ErrorAction SilentlyContinue
        if ($candidate -and $candidate.Source -notlike '*WindowsApps*') {
            $pythonPath = $candidate.Source
            break
        }
    }
    if (-not $pythonPath) {
        $bundled = Join-Path $env:USERPROFILE '.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe'
        if (Test-Path -LiteralPath $bundled) { $pythonPath = $bundled }
    }
    if (-not $pythonPath) { throw 'Python 3를 찾을 수 없다. Python 3를 설치한 뒤 다시 실행하라.' }
    if (Test-Path -LiteralPath 'web/wasm-runtime.local.json') {
        & $pythonPath scripts/prepare_pages.py --runtime-config web/wasm-runtime.local.json
    } else {
        & $pythonPath scripts/prepare_pages.py
    }
    if ($LASTEXITCODE -ne 0) { throw 'WASM 미리보기 준비에 실패했다.' }
    & $pythonPath -u web/serve.py --port $Port
    if ($LASTEXITCODE -ne 0) { throw '상호작용 미리보기를 시작할 수 없다. 위의 오류를 확인하라.' }
}
finally { Pop-Location }
