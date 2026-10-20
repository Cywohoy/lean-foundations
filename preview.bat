@echo off
setlocal EnableExtensions DisableDelayedExpansion
chcp 65001 >nul
title Lean Algebra - Preview

pushd "%~dp0"
if errorlevel 1 (
    echo 프로젝트 폴더를 열 수 없다.
    pause
    exit /b 1
)

where lake.exe >nul 2>nul
if errorlevel 1 set "PATH=%USERPROFILE%\.elan\bin;%PATH%"
where lake.exe >nul 2>nul
if errorlevel 1 (
    echo Lean 실행 도구를 찾을 수 없다. README.md의 준비 항목을 확인하라.
    goto failed
)

echo [1/3] 교재 생성
lake.exe exe textbook
if errorlevel 1 goto failed

echo.
echo [2/3] 예제 코드 검사
for /r "_out\example-code" %%F in (*.lean) do (
    lake.exe env lean "%%F"
    if errorlevel 1 goto failed
)

echo.
echo [3/3] 미리보기 서버 시작
echo 교재 주소: http://127.0.0.1:8000/
echo 이 창을 열어 두면 서버가 계속 실행된다.
echo 서버 종료: Ctrl+C 또는 이 창 닫기
echo.
powershell.exe -NoProfile -ExecutionPolicy Bypass -File "%~dp0interactive-preview.ps1" -Port 8000 -SkipBuild
if errorlevel 1 goto failed

popd
endlocal
exit /b 0

:failed
echo.
echo 미리보기를 실행할 수 없다. 위의 오류 메시지를 확인하라.
echo 서버가 이미 실행 중이면 기존 창을 사용하라.
pause
popd
endlocal
exit /b 1
