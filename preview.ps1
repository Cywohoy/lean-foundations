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
        if ($LASTEXITCODE -ne 0) {
            throw '교재 생성에 실패했다. 위의 Lean 오류를 확인하라.'
        }
        $exampleFiles = Get-ChildItem -LiteralPath '_out/example-code' -Filter '*.lean' -Recurse -File
        foreach ($exampleFile in $exampleFiles) {
            & lake env lean $exampleFile.FullName
            if ($LASTEXITCODE -ne 0) {
                throw ('추출한 예제 코드의 검사에 실패했다: ' + $exampleFile.Name)
            }
        }
    }
    & ./interactive-preview.ps1 -Port $Port -SkipBuild
    if ($LASTEXITCODE -ne 0) {
        throw '미리보기를 시작할 수 없다. 실행 중인 서버나 포트를 확인하라.'
    }
}
finally {
    Pop-Location
}
