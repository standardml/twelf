echo @echo off > %1\%2.bat
echo %1\run.x86-win32.exe @SMLload=%1\.heap\%2 \>> %1\%2.bat
echo      @SMLdebug=/dev/null >> %1\%2.bat