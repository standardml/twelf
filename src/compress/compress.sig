(* `Compressed' terms with omitted redundant arguments *)

signature COMPRESS =
sig
  (*  type ConDec*)
	 
    val sgnReset     : unit -> unit 
			       
    val sgnLookup    : IntSyn.cid -> Sgn.sigent
(*    val sgnApp       : (IntSyn.cid -> unit) -> unit *)

    val sgnResetUpTo  : int -> unit 
    val sgnCompressUpTo  : int -> unit 

    val check : Syntax.tp list * Syntax.term * Syntax.tp -> bool
    val set_modes : int * Syntax.mode list -> unit
end
