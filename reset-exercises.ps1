[CmdletBinding()]
param(
    [string[]]$Section = @('All')
)

Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'

$templateRoot = Join-Path $PSScriptRoot 'ExerciseTemplates'
$workingRoot = Join-Path $PSScriptRoot 'Exercises'
$backupRoot = Join-Path $PSScriptRoot 'exercise-backups'

if (-not (Test-Path -LiteralPath $templateRoot -PathType Container)) {
    throw '연습문제 원본 폴더 ExerciseTemplates를 찾을 수 없다.'
}

$templates = @(Get-ChildItem -LiteralPath $templateRoot -Filter '*.lean' -File |
    Sort-Object Name)
if ($templates.Count -eq 0) {
    throw '초기화할 연습문제 원본이 없다.'
}

if ($Section -contains 'All') {
    if ($Section.Count -ne 1) {
        throw 'All과 개별 절 이름은 함께 지정할 수 없다.'
    }
    $selectedTemplates = $templates
}
else {
    $selectedTemplates = @(
        foreach ($sectionName in $Section) {
            $matched = @($templates | Where-Object {
                $_.BaseName -eq $sectionName -or $_.Name -eq $sectionName
            })
            if ($matched.Count -eq 0) {
                $available = ($templates.BaseName -join ', ')
                throw "절을 찾을 수 없다: $sectionName. 사용할 수 있는 이름: $available"
            }
            $matched[0]
        }
    )
    $selectedTemplates = @($selectedTemplates | Sort-Object Name -Unique)
}

if ($selectedTemplates.Count -eq 0) {
    throw '초기화할 절을 지정하라.'
}
if ((Test-Path -LiteralPath $workingRoot) -and
    -not (Test-Path -LiteralPath $workingRoot -PathType Container)) {
    throw 'Exercises 경로가 폴더가 아니다.'
}

# 모든 백업을 마친 뒤에 원본을 복사한다.
$backupName = (Get-Date -Format 'yyyyMMdd-HHmmss-fff') + '-' +
    ([guid]::NewGuid().ToString('N').Substring(0, 8))
$backupRunRoot = Join-Path $backupRoot $backupName
New-Item -ItemType Directory -Path $backupRunRoot -Force | Out-Null

foreach ($template in $selectedTemplates) {
    $workingPath = Join-Path $workingRoot $template.Name
    if (Test-Path -LiteralPath $workingPath) {
        if (-not (Test-Path -LiteralPath $workingPath -PathType Leaf)) {
            throw ('풀이 파일 경로가 파일이 아니다: ' + $workingPath)
        }
        $backupPath = Join-Path $backupRunRoot $template.Name
        Copy-Item -LiteralPath $workingPath -Destination $backupPath
    }
}

New-Item -ItemType Directory -Path $workingRoot -Force | Out-Null
foreach ($template in $selectedTemplates) {
    $resetTargetPath = Join-Path $workingRoot $template.Name
    Copy-Item -LiteralPath $template.FullName -Destination $resetTargetPath -Force
    Write-Host ('초기화: ' + $template.Name)
}
Write-Host ('기존 풀이 백업: ' + $backupRunRoot)
