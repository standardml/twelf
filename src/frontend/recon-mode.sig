(* External Syntax of Mode Declarations *)
(* Author: Carsten Schuermann *)

signature EXTMODES =
sig
  structure ExtSyn : EXTSYN 
  (*! structure Paths : PATHS  !*)

  type mode

  val plus  : Paths.region -> mode
  val star  : Paths.region -> mode
  val minus : Paths.region -> mode
  val minus1 : Paths.region -> mode

  type modedec 

  structure Short :
  sig
    type mterm
    type mspine

    val mnil  : Paths.region -> mspine
    val mapp  : (mode * string option) * mspine -> mspine 
    val mroot : string list * string * Paths.region * mspine -> mterm

    val toModedec : mterm -> modedec
  end

  structure Full :
  sig
    type mterm

    val mroot : ExtSyn.term * Paths.region -> mterm
    val mpi : mode * ExtSyn.dec * mterm -> mterm

    val toModedec : mterm -> modedec
  end

end;  (* signature EXTMODES *)


signature RECON_MODE =
sig
  (*! structure ModeSyn : MODESYN !*)
  include EXTMODES

  exception Error of string
  val modeToMode : modedec -> (IntSyn.cid * ModeSyn.ModeSpine) * Paths.region
end;  (* signature RECON_MODE *)
