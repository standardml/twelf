(* Twelf Server in Poly/ML *)
(* This is currently not a stand-alone program *)
(* Interrupts do not work properly in Poly/ML *)
(* Load this into "poly bin/twelf_dbase" *)
use "src/server/sigint.sig";
use "src/server/sigint-polyml.sml";
use "src/server/server.sml";
PolyML.onEntry (fn () => OS.Process.exit (Server.server ("twelf-server", [])));
PolyML.commit ();
PolyML.exit (0);
