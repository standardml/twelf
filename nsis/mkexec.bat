rem
rem
rem Twelf Batch File Creator
rem
rem Arguments:
rem $1 = SMLNJ runtime
rem $2 = Twelf root directory
rem $3 = Type of executable (e.g. twelf-server, twelf-sml)
rem
echo @echo off > %2\bin\%3.bat
echo %1 @SMLload=%2\bin\.heap\%3>> %2\bin\%3.bat
pause
