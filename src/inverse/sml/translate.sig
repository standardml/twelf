
signature TRANSLATE =
sig

  (* -------------------------------------------------------------------------- *)
  (*  Exceptions                                                                *)
  (* -------------------------------------------------------------------------- *)

  exception Fail_const_condec of string * S.const * I.ConDec
  exception Fail_exp of string * I.Exp

  (** Translate a Twelf declaration to a Flewt declaration. *)
  val translate_condec : Intsyn.cid * Intsyn.ConDec -> Syntax.dec

  (** True if our typechecker understands the dec. *)
  val can_translate : IntSyn.ConDec -> bool

end

