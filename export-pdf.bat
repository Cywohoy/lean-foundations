@echo off
setlocal EnableExtensions DisableDelayedExpansion
chcp 65001 >nul
title Lean Algebra - PDF

pushd "%~dp0"
if errorlevel 1 exit /b 1
where lake.exe >nul 2>nul
if errorlevel 1 set "PATH=%USERPROFILE%\.elan\bin;%PATH%"

powershell.exe -NoProfile -ExecutionPolicy Bypass -File "%~dp0export-pdf.ps1"
if errorlevel 1 goto failed

echo.
echo PDF: output\pdf\lean-algebra-ko.pdf
pause
popd
endlocal
exit /b 0

:failed
echo.
echo PDF를 생성할 수 없다. 위의 오류 메시지를 확인하라.
pause
popd
endlocal
exit /b 1
