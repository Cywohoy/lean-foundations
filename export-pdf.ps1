param(
    [switch]$SkipBuild
)

$ErrorActionPreference = 'Stop'
Push-Location -LiteralPath $PSScriptRoot
try {
    foreach ($toolName in @('lake', 'latexmk', 'lualatex')) {
        if (-not (Get-Command $toolName -ErrorAction SilentlyContinue)) {
            throw ('실행 도구를 찾을 수 없다: ' + $toolName + '. README.md의 PDF 출력 항목을 확인하라.')
        }
    }

    if (-not $SkipBuild) {
        Write-Host '[1/3] 교재와 예제 코드 검사'
        & lake exe textbook --with-tex
        if ($LASTEXITCODE -ne 0) {
            throw '교재 생성에 실패했다. 위의 Lean 오류를 확인하라.'
        }
        $exampleFiles = Get-ChildItem -LiteralPath '_out/example-code' -Filter '*.lean' -Recurse -File
        foreach ($exampleFile in $exampleFiles) {
            & lake env lean $exampleFile.FullName
            if ($LASTEXITCODE -ne 0) {
                throw ('예제 코드의 검사에 실패했다: ' + $exampleFile.Name)
            }
        }
    }

    Write-Host '[2/3] 한국어 글꼴과 PDF 설정 적용'
    $texDirectory = Join-Path $PSScriptRoot '_out/tex'
    $texPath = Join-Path $texDirectory 'main.tex'
    if (-not (Test-Path -LiteralPath $texPath -PathType Leaf)) {
        throw 'LaTeX 원고가 없다. SkipBuild 옵션 없이 다시 실행하라.'
    }
    Copy-Item -LiteralPath 'assets/pdf/book-style.tex' -Destination $texDirectory -Force
    $fontDirectory = Join-Path $texDirectory 'fonts'
    New-Item -ItemType Directory -Path $fontDirectory -Force | Out-Null
    foreach ($fontFile in (Get-ChildItem -LiteralPath 'assets/fonts/pdf' -File)) {
        Copy-Item -LiteralPath $fontFile.FullName -Destination $fontDirectory -Force
    }

    # Replace only the generated preamble; the book and checked code stay intact.
    $texSource = [System.IO.File]::ReadAllText($texPath)
    # Verso ends code blocks with an empty row. Keep the delimiter on its
    # own line, but remove empty rows that enlarge the bottom of the frame.
    $texSource = [regex]::Replace(
        $texSource,
        '(?:\r?\n[ \t]*){2,}(?=\\end\{LeanVerbatim\})',
        "`n"
    )
    # Verso's unwrapped columns can push the symbol reference past the page.
    $texSource = [regex]::Replace(
        $texSource,
        '(?s)\\begin\{tabular\}\{llll\}(\s*처음 등장하는 절&기호&뜻&입력.*?)\\end\{tabular\}',
        '\begin{BookSymbolTable}$1\end{BookSymbolTable}'
    )
    $texSource = [regex]::Replace($texSource, '\\documentclass\[[^\]]*\]\{memoir\}', '\documentclass[a4paper,11pt,oneside]{memoir}')
    $texSource = $texSource.Replace('\usepackage{sourcecodepro}', '\usepackage{fontspec}')
    $texSource = $texSource.Replace('\usepackage{sourcesanspro}', '')
    $texSource = $texSource.Replace('\usepackage{sourceserifpro}', '')
    $texSource = $texSource.Replace('\setmonofont{DejaVu Sans Mono}', '\input{book-style.tex}')
    if (-not $texSource.Contains('\markboth{이 교재에 대하여}{이 교재에 대하여}')) {
        $texSource = $texSource.Replace("\cleardoublepage`n", "\cleardoublepage`n\markboth{이 교재에 대하여}{이 교재에 대하여}`n")
    }
    if (-not $texSource.Contains('\input{book-style.tex}')) {
        throw 'Verso의 LaTeX 기본 설정이 바뀌었다. PDF 설정을 연결하는 부분을 확인하라.'
    }
    [System.IO.File]::WriteAllText($texPath, $texSource, [System.Text.UTF8Encoding]::new($false))

    Write-Host '[3/3] 전체 문서 PDF 생성'
    Push-Location -LiteralPath $texDirectory
    try {
        $buildLog = Join-Path $texDirectory 'pdf-build.log'
        # Native tools may write routine progress to stderr.
        $ErrorActionPreference = 'Continue'
        & latexmk -lualatex -interaction=nonstopmode -halt-on-error -file-line-error main.tex *> $buildLog
        $pdfExitCode = $LASTEXITCODE
        $ErrorActionPreference = 'Stop'
        if ($pdfExitCode -ne 0) {
            Get-Content -LiteralPath $buildLog -Tail 35
            throw ('PDF 생성에 실패했다. 자세한 기록: ' + $buildLog)
        }
        if (Select-String -LiteralPath 'main.log' -Pattern 'Missing character:' -Quiet) {
            throw 'PDF에 표시하지 못한 글자가 있다. _out/tex/main.log에서 글꼴 경고를 확인하라.'
        }
    }
    finally {
        $ErrorActionPreference = 'Stop'
        Pop-Location
    }

    $outputDirectory = Join-Path $PSScriptRoot 'output/pdf'
    New-Item -ItemType Directory -Path $outputDirectory -Force | Out-Null
    $outputPath = Join-Path $outputDirectory 'lean-foundations-ko.pdf'
    Copy-Item -LiteralPath (Join-Path $texDirectory 'main.pdf') -Destination $outputPath -Force
    Copy-Item -LiteralPath $outputPath -Destination '_out/html-multi/lean-foundations-ko.pdf' -Force
    Write-Host ('PDF 저장 완료: ' + $outputPath)
}
finally {
    Pop-Location
}
