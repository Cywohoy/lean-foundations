@echo off
setlocal EnableExtensions DisableDelayedExpansion
chcp 65001 >nul
title Lean Algebra - Interactive Preview
pushd "%~dp0"
if errorlevel 1 exit /b 1
where lake.exe >nul 2>nul
if errorlevel 1 set "PATH=%USERPROFILE%\.elan\bin;%PATH%"
powershell.exe -NoProfile -ExecutionPolicy Bypass -File "%~dp0interactive-preview.ps1" %*
if errorlevel 1 pause
popd
endlocal
