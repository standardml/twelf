
signature TYPECHECK =
sig

  (** 
     Given a list of const, dec pairs, check_signat typechecks
     the dec against the decs it's seen so far and installs them
     in the global signature.
   *)
  val check_signat : (Syntax.const * Syntax.dec) list -> unit
  val check_signat_clear : (Syntax.const * Syntax.dec) list -> unit

end
