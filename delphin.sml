(* comment out first line if undefined in your version of SMLofNJ *)
(* call sml-cm with @SMLdebug=/dev/null instead *)
SMLofNJ.Internals.GC.messages false;
CM.make' ("delphin.cm");
if SMLofNJ.exportML ("bin/.heap/delphin")
then (print (Delphin.version ^ "\n"); Delphin.top ()) else ();

