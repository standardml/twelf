@echo off
SET SML=sml
echo loadFile %1 | %SML% @SMLload="%~dp0\.heap\twelf-server"
