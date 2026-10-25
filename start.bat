@echo off
rem Double-click to start monitoring. Press Ctrl+C to stop.
cd /d "%~dp0"
where py >nul 2>nul
if %errorlevel%==0 (py -3 main.py %*) else (python main.py %*)
echo.
pause
