(* comment out first line if undefined in your version of SMLofNJ *)
(* call sml-cm with @SMLdebug=/dev/null instead *)
SMLofNJ.Internals.GC.messages false;
CM.make' ("sources.cm");
if SMLofNJ.exportML ("bin/.heap/twelf-sml")
then (print (Twelf.version ^ "\n"); Timing.init ()) else ();

