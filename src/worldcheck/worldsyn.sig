(* World Checking *) 
(* Author: Carsten Schuermann *)


signature WORLDSYN = 
sig

  exception Error of string 


  val reset : unit -> unit
  val install : IntSyn.cid * Tomega.Worlds -> unit
  val lookup : IntSyn.cid -> Tomega.Worlds      (* raises Error if undeclared *)
  val uninstall : IntSyn.cid -> bool	(* true if declared *)

  val worldcheck : Tomega.Worlds -> IntSyn.cid -> unit
  val ctxToList  : IntSyn.Dec IntSyn.Ctx -> IntSyn.Dec list
  val isSubsumed : Tomega.Worlds -> IntSyn.cid -> unit
  val getWorlds  : IntSyn.cid -> Tomega.Worlds
end; (* signature WORLDSYN *)
