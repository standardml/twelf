(* A do-nothing stub for SML implementations without an SML/NJ-like
   exnHistory function.
*)

structure UnknownExn =
  UnknownExn (val exnHistory = fn exn => nil);
