(* Sets *)
(* Author: Brigitte Pientka *)

(* This provides a common interface to ordered sets *)
(* based on red/black trees *)

signature RBSET =

sig
  type key = int (* parameter *)
  type 'a entry = key * 'a

  exception Error of string

  type 'a ordSet
  val new : unit -> 'a ordSet		
  val copy : 'a ordSet -> 'a ordSet		

  val insert : 'a ordSet -> 'a entry -> unit
  val insertList : 'a ordSet -> ('a entry) list -> unit
  val insertShadow : 'a ordSet -> 'a entry -> unit

  val insertLast : 'a ordSet -> 'a -> unit

(*  val delete : 'a ordSet -> key -> unit*)

  val lookup : 'a ordSet -> key -> 'a option  

  val isEmpty : 'a ordSet -> bool
  val last : 'a ordSet -> 'a entry

  val clear : 'a ordSet -> unit

  (* Applies f:'a -> unit to all entries in the set
     pre-order traversal *)
  val app : 'a ordSet -> ('a -> unit) -> unit
  val update : 'a ordSet -> ('a -> 'a) -> 'a ordSet

  (* Applies f:'a entry -> unit to all entries in the set
     pre-order traversal *)
  val forall : 'a ordSet -> ('a entry -> unit) -> unit
(*  val exists : 'a ordSet -> ('a entry -> 'b option) -> ('a entry (* key * 'a *) * 'b) option *)
  val exists : 'a ordSet -> ('a entry -> bool) -> bool
  val existsOpt : 'a ordSet -> ('a -> bool) -> int option

  val size : 'a ordSet -> int
  val union: 'a ordSet -> 'a ordSet -> 'a ordSet
  val difference: 'a ordSet -> 'a ordSet -> 'a ordSet
  val difference2: 'a ordSet -> 'a ordSet -> ('a ordSet * 'a ordSet)
  val differenceModulo: 'a ordSet -> 'b ordSet -> ('a -> 'b -> unit) -> ('a ordSet * 'b ordSet)
  (* splits two sets into S1, S2, S3 *)
  val splitSets: 'a ordSet -> 'a ordSet -> ('a -> 'a -> 'a option) -> ('a ordSet * 'a ordSet * 'a ordSet)
  val intersection: 'a ordSet -> 'a ordSet -> 'a ordSet

end;  (* signature RBSET *)
