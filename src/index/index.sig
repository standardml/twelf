(* Indexing *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning *)

signature INDEX =
sig

  (*! structure IntSyn : INTSYN !*)
    
  val reset : unit -> unit
  val resetFrom : IntSyn.cid -> unit

  val install : IntSyn.ConDecForm -> IntSyn.Head -> unit

  (* lookup a = [c1,...,cn] *)
  (* c1,...,cn are all constants with target family a *)
  (* in order of declaration, defined constants are omitted *)
  val lookup : IntSyn.cid -> IntSyn.Head list

end;  (* signature INDEX *)
