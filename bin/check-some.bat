@echo off
rem checks a list of files; prints to omdoc if -omdoc DIR is supplied
SET SML=sml
SET BIN=%~dp0

if %1==-omdoc (
  SET OMDOC=%2
  shift
  shift
) else (
  SET OMDOC=
)

:loop
if "%1"=="" goto end

SET COMMAND=
if "%OMDOC%" == "" goto twelf

SET FILE=%1
rem delete : in FILE
SET FILE2=%FILE::=%
if %FILE%==%FILE2% (
   rem %1 contains no :, i.e., is relative, remove ".elf" (anywhere in the string)
   SET TARGET=%OMDOC%\%FILE:.elf=%
) else (
   rem %1 contains :, i.e., is absolute, remove ".elf" (anywhere in the string)
   SET TARGET=%FILE:.elf=%
)
SET COMMAND=Print.OMDoc.toFile %TARGET%.omdoc

:twelf
(
   echo loadFile %1
   if not "%COMMAND%"=="" echo %COMMAND%
)  | %SML% @SMLload="%BIN%.heap\twelf-server"
shift
goto loop

:end
rem 