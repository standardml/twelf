(* Strategy *)
(* Author: Carsten Schuermann *)

signature STRATEGY = 
sig
  structure MetaSyn : METASYN

  val run : MetaSyn.State list -> MetaSyn.State list * MetaSyn.State list 
              (* open cases -> remaining cases * solved cases *)

end;  (* signature STRATEGY *)
