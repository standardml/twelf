
signature TRANSLATE =
sig

  (** Translate a Twelf declaration to a Flewt declaration. *)
  val translate_condec : IntSyn.cid * IntSyn.ConDec -> Syntax.dec

  (** Translate the currently loaded Twelf signature to Flewt *)
  val translate_signat : unit -> (Syntax.const * Syntax.dec) list

end

