@echo off
rem Put this folder on PATH to run "wsc" from anywhere.
rem Uses the py launcher when present, otherwise python.
rem Comments stay ASCII: cmd reads this file in the console code page, not UTF-8.
where py >nul 2>nul
if %errorlevel%==0 (
    py -3 "%~dp0wsc.py" %*
) else (
    python "%~dp0wsc.py" %*
)
exit /b %errorlevel%
