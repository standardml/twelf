(* Basic search engine *)
(* Author: Carsten Schuermann *)

signature SEARCH = 
sig
  structure MetaSyn : METASYN

  exception Error of string

  val searchEx : 
      MetaSyn.IntSyn.dctx * (MetaSyn.IntSyn.dctx * MetaSyn.IntSyn.Exp) list
      * (MetaSyn.IntSyn.Exp * MetaSyn.IntSyn.Sub)
      * (unit -> MetaSyn.State)
      -> MetaSyn.State list
    
  val searchAll : 
      MetaSyn.IntSyn.dctx * (MetaSyn.IntSyn.dctx * MetaSyn.IntSyn.Exp) list
      * (MetaSyn.IntSyn.Exp * MetaSyn.IntSyn.Sub)
      * (unit -> MetaSyn.State)
      -> MetaSyn.State list
end;  (* signature SEARCH *)
