(* Rings (aka cyclic lists) *)
(* Author: Carsten Schuermann *)

signature RING =
sig
  exception Empty 
  type 'a ring

  val init : 'a list -> 'a ring
  val empty : 'a ring -> bool
  val insert: 'a ring * 'a -> 'a ring
  val delete: 'a ring -> 'a ring
  val current: 'a ring -> 'a 
  val next : 'a ring -> 'a ring
  val previous : 'a ring -> 'a ring
  val foldr : ('a * 'b -> 'b) -> 'b -> 'a ring -> 'b
  val map : ('a -> 'b) -> 'a ring -> 'b ring (* does not necessarily map f in order *)
end;  (* signature RING *)
