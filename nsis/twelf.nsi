Name "Twelf 1.3"
Icon twelf.ico
OutFile ..\twelf-1-3.exe
CRCCheck on
UninstallIcon uninst.ico
UninstallExeName uninst.exe

LicenseText "Information:"
LicenseData LICENSE

ComponentText "This will install Twelf 1.3 on your computer."
InstType Standard
InstType Full
InstType Minimal
EnabledBitmap enabled.bmp
DisabledBitmap disabled.bmp

DirText "Please select a location to install Twelf 1.3 (or use the default)."

InstallDir $PROGRAMFILES\Twelf
InstallDirRegKey HKEY_LOCAL_MACHINE SOFTWARE\Twelf ""

Section "Twelf Server (required)"
SectionIn 1,2,3
SetOutPath $INSTDIR
File README.txt
SetOutPath $INSTDIR\bin
File mkexec.exe
File run.x86-win32.exe
File twelf.ico
SetOutPath $INSTDIR\bin\.heap
File ..\bin\.heap\twelf-server.x86-win32
SetOutPath $INSTDIR\emacs
File ..\emacs\README
File ..\emacs\*.el
File twelf-init.el
SetOutPath $STARTMENU\Programs\Twelf
CreateShortCut "$STARTMENU\Programs\Twelf\Twelf Server.lnk" $INSTDIR\bin\twelf-server.bat "" $INSTDIR\bin\twelf.ico 0

Section "Twelf SML"
SectionIn 2
SetOutPath $INSTDIR\bin\.heap
File ..\bin\.heap\twelf-sml.x86-win32
SetOutPath $STARTMENU\Programs\Twelf
CreateShortCut "$STARTMENU\Programs\Twelf\Twelf SML.lnk" $INSTDIR\bin\twelf-sml.bat "" $INSTDIR\bin\twelf.ico 0
Section "Documentation"
SectionIn 1,2
SetOutPath $INSTDIR\doc\dvi
File ..\doc\dvi\twelf.dvi
SetOutPath $INSTDIR\doc\html
File ..\doc\html\*.html
SetOutPath $INSTDIR\doc\info
File ..\doc\info\*.*
SetOutPath $INSTDIR\doc\pdf
File ..\doc\pdf\twelf.pdf
SetOutPath $INSTDIR\doc\ps
File ..\doc\ps\twelf.ps
SetOutPath $STARTMENU\Programs\Twelf
CreateShortCut "$STARTMENU\Programs\Twelf\Twelf User's Guide (HTML).lnk" $INSTDIR\doc\html\index.html "" "" 0
CreateShortCut "$STARTMENU\Programs\Twelf\Twelf User's Guide (PDF).lnk" $INSTDIR\doc\pdf\twelf.pdf "" "" 0

Section "Examples"
SectionIn 1,2
SetOutPath $INSTDIR\examples
File ..\examples\*.*
SetOutPath $INSTDIR\examples\arith
File ..\examples\arith\*.*
SetOutPath $INSTDIR\examples\ccc
File ..\examples\ccc\*.*
SetOutPath $INSTDIR\examples\church-rosser
File ..\examples\church-rosser\*.*
SetOutPath $INSTDIR\examples\compile
File ..\examples\compile\*.*
SetOutPath $INSTDIR\examples\compile\cls
File ..\examples\compile\cls\*.*
SetOutPath $INSTDIR\examples\compile\cpm
File ..\examples\compile\cpm\*.*
SetOutPath $INSTDIR\examples\compile\cps
File ..\examples\compile\cps\*.*
SetOutPath $INSTDIR\examples\compile\cxm
File ..\examples\compile\cxm\*.*
SetOutPath $INSTDIR\examples\compile\debruijn
File ..\examples\compile\debruijn\*.*
SetOutPath $INSTDIR\examples\compile\debruijn1
File ..\examples\compile\debruijn1\*.*
SetOutPath $INSTDIR\examples\cpsocc
File ..\examples\cpsocc\*.*
SetOutPath $INSTDIR\examples\cut-elim
File ..\examples\cut-elim\*.*
SetOutPath $INSTDIR\examples\fol
File ..\examples\fol\*.*
SetOutPath $INSTDIR\examples\guide
File ..\examples\guide\*.*
SetOutPath $INSTDIR\examples\handbook
File ..\examples\handbook\*.*
SetOutPath $INSTDIR\examples\incll
File ..\examples\incll\*.*
SetOutPath $INSTDIR\examples\kolm
File ..\examples\kolm\*.*
SetOutPath $INSTDIR\examples\lp
File ..\examples\lp\*.*
SetOutPath $INSTDIR\examples\lp-horn
File ..\examples\lp-horn\*.*
SetOutPath $INSTDIR\examples\mini-ml
File ..\examples\mini-ml\*.*
SetOutPath $INSTDIR\examples\polylam
File ..\examples\polylam\*.*
SetOutPath $INSTDIR\examples\prop-calc
File ..\examples\prop-calc\*.*

Section "CLP Examples"
SectionIn 1,2
SetOutPath $INSTDIR\examples-clp
File ..\examples-clp\*.*
SetOutPath $INSTDIR\examples-clp\arith
File ..\examples-clp\arith\*.*
SetOutPath $INSTDIR\examples-clp\base
File ..\examples-clp\base\*.*
SetOutPath $INSTDIR\examples-clp\crypt
File ..\examples-clp\crypt\*.*
SetOutPath $INSTDIR\examples-clp\integers
File ..\examples-clp\integers\*.*
SetOutPath $INSTDIR\examples-clp\laplace
File ..\examples-clp\laplace\*.*
SetOutPath $INSTDIR\examples-clp\lists
File ..\examples-clp\lists\*.*
SetOutPath $INSTDIR\examples-clp\mortgage
File ..\examples-clp\mortgage\*.*
SetOutPath $INSTDIR\examples-clp\pelletier
File ..\examples-clp\pelletier\*.*
SetOutPath $INSTDIR\examples-clp\sieve
File ..\examples-clp\sieve\*.*

Section "TeX Output"
SectionIn 1,2
SetOutPath $INSTDIR\tex
File ..\tex\*.*

Section "Source Code"
SectionIn 2
SetOutPath $INSTDIR
File ..\*.sml
File ..\*.cm
File Makefile
SetOutPath $INSTDIR\src
File ..\src\*.*
SetOutPath $INSTDIR\src\domains
File ..\src\domains\*.*
SetOutPath $INSTDIR\src\formatter
File ..\src\formatter\*.*
SetOutPath $INSTDIR\src\frontend
File ..\src\frontend\*.*
SetOutPath $INSTDIR\src\global
File ..\src\global\*.*
SetOutPath $INSTDIR\src\heuristic
File ..\src\heuristic\*.*
SetOutPath $INSTDIR\src\index
File ..\src\index\*.*
SetOutPath $INSTDIR\src\int-inf
File ..\src\int-inf\*.*
SetOutPath $INSTDIR\src\lambda
File ..\src\lambda\*.*
SetOutPath $INSTDIR\src\m2
File ..\src\m2\*.*
SetOutPath $INSTDIR\src\meta
File ..\src\meta\*.*
SetOutPath $INSTDIR\src\modes
File ..\src\modes\*.*
SetOutPath $INSTDIR\src\names
File ..\src\names\*.*
SetOutPath $INSTDIR\src\opsem
File ..\src\opsem\*.*
SetOutPath $INSTDIR\src\order
File ..\src\order\*.*
SetOutPath $INSTDIR\src\paths
File ..\src\paths\*.*
SetOutPath $INSTDIR\src\print
File ..\src\print\*.*
SetOutPath $INSTDIR\src\server
File ..\src\server\*.*
SetOutPath $INSTDIR\src\solvers
File ..\src\solvers\*.*
SetOutPath $INSTDIR\src\stream
File ..\src\stream\*.*
SetOutPath $INSTDIR\src\subordinate
File ..\src\subordinate\*.*
SetOutPath $INSTDIR\src\table
File ..\src\table\*.*
SetOutPath $INSTDIR\src\terminate
File ..\src\terminate\*.*
SetOutPath $INSTDIR\src\thm
File ..\src\thm\*.*
SetOutPath $INSTDIR\src\timing
File ..\src\timing\*.*
SetOutPath $INSTDIR\src\trail
File ..\src\trail\*.*
SetOutPath $INSTDIR\src\typecheck
File ..\src\typecheck\*.*

Section -post
WriteRegStr HKEY_LOCAL_MACHINE SOFTWARE\Twelf "" $INSTDIR
WriteRegStr HKEY_LOCAL_MACHINE "Software\Microsoft\Windows\CurrentVersion\Uninstall\Twelf" "DisplayName" "Twelf 1.3"
WriteRegStr HKEY_LOCAL_MACHINE "Software\Microsoft\Windows\CurrentVersion\Uninstall\Twelf" "UninstallString" '"$INSTDIR\uninst.exe"'
SetOutPath $STARTMENU\Programs\Twelf
CreateShortCut "$STARTMENU\Programs\Twelf\Twelf 1.3 README.lnk" $INSTDIR\Readme.txt "" "" 0
CreateShortCut "$STARTMENU\Programs\Twelf\Uninstall Twelf.lnk" $INSTDIR\uninst.exe "" "" 0
Exec '"$INSTDIR\bin\mkexec" "$INSTDIR\bin\run.x86-win32.exe" "$INSTDIR" twelf-server'
Exec '"$INSTDIR\bin\mkexec" "$INSTDIR\bin\run.x86-win32.exe" "$INSTDIR" twelf-sml'
MessageBox MB_OK "Twelf 1.3 was installed successfully. Please modify your _emacs file as described in the README file."
Exec '"write" "$INSTDIR\README.txt"'
Exec '"explorer" "$STARTMENU\Programs\Twelf"'

Section Uninstall
DeleteRegKey HKEY_LOCAL_MACHINE "Software\Microsoft\Windows\CurrentVersion\Uninstall\Twelf"
DeleteRegKey HKEY_LOCAL_MACHINE SOFTWARE\Twelf
# remove Programs/Twelf
Delete $STARTMENU\Programs\Twelf\*.*
RMDir $STARTMENU\Programs\Twelf
# remove sources
Delete $INSTDIR\src\domains\*.*
RMDir $INSTDIR\src\domains
Delete $INSTDIR\src\formatter\*.*
RMDir $INSTDIR\src\formatter
Delete $INSTDIR\src\frontend\*.*
RMDir $INSTDIR\src\frontend
Delete $INSTDIR\src\global\*.*
RMDir $INSTDIR\src\global
Delete $INSTDIR\src\heuristic\*.*
RMDir $INSTDIR\src\heuristic
Delete $INSTDIR\src\index\*.*
RMDir $INSTDIR\src\index
Delete $INSTDIR\src\int-inf\*.*
RMDir $INSTDIR\src\int-inf
Delete $INSTDIR\src\lambda\*.*
RMDir $INSTDIR\src\lambda
Delete $INSTDIR\src\m2\*.*
RMDir $INSTDIR\src\m2
Delete $INSTDIR\src\meta\*.*
RMDir $INSTDIR\src\meta
Delete $INSTDIR\src\modes\*.*
RMDir $INSTDIR\src\modes
Delete $INSTDIR\src\names\*.*
RMDir $INSTDIR\src\names
Delete $INSTDIR\src\opsem\*.*
RMDir $INSTDIR\src\opsem
Delete $INSTDIR\src\order\*.*
RMDir $INSTDIR\src\order
Delete $INSTDIR\src\paths\*.*
RMDir $INSTDIR\src\paths
Delete $INSTDIR\src\print\*.*
RMDir $INSTDIR\src\print
Delete $INSTDIR\src\server\*.*
RMDir $INSTDIR\src\server
Delete $INSTDIR\src\solvers\*.*
RMDir $INSTDIR\src\solvers
Delete $INSTDIR\src\stream\*.*
RMDir $INSTDIR\src\stream
Delete $INSTDIR\src\subordinate\*.*
RMDir $INSTDIR\src\subordinate
Delete $INSTDIR\src\table\*.*
RMDir $INSTDIR\src\table
Delete $INSTDIR\src\terminate\*.*
RMDir $INSTDIR\src\terminate
Delete $INSTDIR\src\thm\*.*
RMDir $INSTDIR\src\thm
Delete $INSTDIR\src\timing\*.*
RMDir $INSTDIR\src\timing
Delete $INSTDIR\src\trail\*.*
RMDir $INSTDIR\src\trail
Delete $INSTDIR\src\typecheck\*.*
RMDir $INSTDIR\src\typecheck
Delete $INSTDIR\src\*.*
RMDir $INSTDIR\src
# remove TeX output
Delete $INSTDIR\tex\*.*
RMDir $INSTDIR\tex
# remove CLP examples
Delete $INSTDIR\examples-clp\arith\*.*
RMDir $INSTDIR\examples-clp\arith
Delete $INSTDIR\examples-clp\base\*.*
RMDir $INSTDIR\examples-clp\base
Delete $INSTDIR\examples-clp\crypt\*.*
RMDir $INSTDIR\examples-clp\crypt
Delete $INSTDIR\examples-clp\integers\*.*
RMDir $INSTDIR\examples-clp\integers
Delete $INSTDIR\examples-clp\laplace\*.*
RMDir $INSTDIR\examples-clp\laplace
Delete $INSTDIR\examples-clp\lists\*.*
RMDir $INSTDIR\examples-clp\lists
Delete $INSTDIR\examples-clp\mortgage\*.*
RMDir $INSTDIR\examples-clp\mortgage
Delete $INSTDIR\examples-clp\pelletier\*.*
RMDir $INSTDIR\examples-clp\pelletier
Delete $INSTDIR\examples-clp\sieve\*.*
RMDir $INSTDIR\examples-clp\sieve
Delete $INSTDIR\examples-clp\*.*
RMDir $INSTDIR\examples-clp
# remove examples
Delete $INSTDIR\examples\arith\*.*
RMDir $INSTDIR\examples\arith
Delete $INSTDIR\examples\ccc\*.*
RMDir $INSTDIR\examples\ccc
Delete $INSTDIR\examples\church-rosser\*.*
RMDir $INSTDIR\examples\church-rosser
Delete $INSTDIR\examples/compile\cls\*.*
RMDir $INSTDIR\examples/compile\cls
Delete $INSTDIR\examples/compile\cpm\*.*
RMDir $INSTDIR\examples/compile\cpm
Delete $INSTDIR\examples/compile\cps\*.*
RMDir $INSTDIR\examples/compile\cps
Delete $INSTDIR\examples/compile\cxm\*.*
RMDir $INSTDIR\examples/compile\cxm
Delete $INSTDIR\examples/compile\debruijn\*.*
RMDir $INSTDIR\examples/compile\debruijn
Delete $INSTDIR\examples/compile\debruijn1\*.*
RMDir $INSTDIR\examples/compile\debruijn1
Delete $INSTDIR\examples\compile\*.*
RMDir $INSTDIR\examples\compile
Delete $INSTDIR\examples\cpsocc\*.*
RMDir $INSTDIR\examples\cpsocc
Delete $INSTDIR\examples\cut-elim\*.*
RMDir $INSTDIR\examples\cut-elim
Delete $INSTDIR\examples\fol\*.*
RMDir $INSTDIR\examples\fol
Delete $INSTDIR\examples\guide\*.*
RMDir $INSTDIR\examples\guide
Delete $INSTDIR\examples\handbook\*.*
RMDir $INSTDIR\examples\handbook
Delete $INSTDIR\examples\incll\*.*
RMDir $INSTDIR\examples\incll
Delete $INSTDIR\examples\kolm\*.*
RMDir $INSTDIR\examples\kolm
Delete $INSTDIR\examples\lp\*.*
RMDir $INSTDIR\examples\lp
Delete $INSTDIR\examples\lp-horn\*.*
RMDir $INSTDIR\examples\lp-horn
Delete $INSTDIR\examples\mini-ml\*.*
RMDir $INSTDIR\examples\mini-ml
Delete $INSTDIR\examples\polylam\*.*
RMDir $INSTDIR\examples\polylam
Delete $INSTDIR\examples\prop-calc\*.*
RMDir $INSTDIR\examples\prop-calc
Delete $INSTDIR\examples\*.*
RMDir $INSTDIR\examples
# remove docs
Delete $INSTDIR\doc\dvi\*.*
RMDir $INSTDIR\doc\dvi
Delete $INSTDIR\doc\html\*.*
RMDir $INSTDIR\doc\html
Delete $INSTDIR\doc\info\*.*
RMDir $INSTDIR\doc\info
Delete $INSTDIR\doc\pdf\*.*
RMDir $INSTDIR\doc\pdf
Delete $INSTDIR\doc\ps\*.*
RMDir $INSTDIR\doc\ps
Delete $INSTDIR\doc\*.*
RMDir $INSTDIR\doc
# remove main files
Delete $INSTDIR\emacs\*.*
RMDir $INSTDIR\emacs
Delete $INSTDIR\bin\.heap\*.*
RMDir $INSTDIR\bin\.heap
Delete $INSTDIR\bin\*.*
RMDir $INSTDIR\bin
Delete $INSTDIR\*.*
RMDir $INSTDIR
