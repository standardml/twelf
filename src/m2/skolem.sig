(* Skolem administration *)
(* Author: Carsten Schuermann *)

signature SKOLEM =
sig
  (*! structure IntSyn : INTSYN !*)

  val install: IntSyn.cid list -> unit
end;  (* signature SKOLEM *)
