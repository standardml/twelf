(* External Syntax of Mode Declarations *)
(* Author: Carsten Schuermann *)

signature EXTMODES =
sig
  structure ExtSyn : EXTSYN 
  structure Paths : PATHS 

  type mode

  val plus  : Paths.region -> mode
  val star  : Paths.region -> mode
  val minus : Paths.region -> mode

  type modedec 

  structure Short :
  sig
    type mterm
    type mspine

    val mnil  : Paths.region -> mspine
    val mapp  : (mode * ExtSyn.name option) * mspine -> mspine 
    val mroot : ExtSyn.name * Paths.region * mspine -> mterm

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


signature MODE_RECON =
sig
  structure ModeSyn : MODESYN
  include EXTMODES

  exception Error of string
  val modeToMode : modedec -> (ModeSyn.IntSyn.cid * ModeSyn.ModeSpine) * Paths.region
end;  (* signature MODE_RECON *)
