(* The Parser *)
(* Author: Richard Fontana *)

signature PARSE =
sig
  
  structure DextSyn  : DEXTSYN
    
  val fparse : string -> unit
  val gparse : string -> DextSyn.Ast
  val sparse : unit -> DextSyn.Ast

end  (* signature PARSE *)
