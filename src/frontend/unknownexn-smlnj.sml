(* Print exception trace in unknownExn.  Both SML/NJ and MLton have
   SMLofNJ.exnHistory.
*)

structure UnknownExn =
  UnknownExn (val exnHistory = SMLofNJ.exnHistory);
