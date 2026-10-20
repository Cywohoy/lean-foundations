@echo off
setlocal EnableExtensions DisableDelayedExpansion
chcp 65001 >nul
title Lean Algebra - Reset Exercises

pushd "%~dp0"
if errorlevel 1 (
    echo 프로젝트 폴더를 열 수 없다.
    pause
    exit /b 1
)

if "%~1"=="" (
    powershell.exe -NoProfile -ExecutionPolicy Bypass -File "%~dp0reset-exercises.ps1"
) else (
    powershell.exe -NoProfile -ExecutionPolicy Bypass -File "%~dp0reset-exercises.ps1" -Section "%~1"
)
if errorlevel 1 goto failed

echo.
echo 연습문제 초기화를 마쳤다. 기존 풀이는 위의 백업 폴더에 보관했다.
pause
popd
endlocal
exit /b 0

:failed
echo.
echo 초기화에 실패했다. 위의 오류 메시지를 확인하라.
pause
popd
endlocal
exit /b 1
