(* comment out first line if undefined in your version of SMLofNJ *)
(* call sml-cm with @SMLdebug=/dev/null instead *)
(* This is for SML/NJ version >= 110.20 (using the new interface to CM) *)
SMLofNJ.Internals.GC.messages false;
CM.make "server.cm";
SMLofNJ.exportFn ("bin/.heap/twelf-server", Server.server);
