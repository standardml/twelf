(* Basic search engine *)
(* Author: Carsten Schuermann *)

signature OLDSEARCH = 
sig
  structure MetaSyn : METASYN

  exception Error of string

  val searchEx : 
      IntSyn.dctx * IntSyn.Exp list
      * (IntSyn.Exp * IntSyn.Sub)
      * (unit -> unit)
      -> MetaSyn.State list
    
  val searchAll : 
      IntSyn.dctx * IntSyn.Exp list
      * (IntSyn.Exp * IntSyn.Sub)
      * (MetaSyn.State list -> MetaSyn.State list)
      -> MetaSyn.State list
end;  (* signature SEARCH *)
