(* Hash Tables *)
(* Author: Frank Pfenning *)
(* Modified: Roberto Virga *)

(* This provides a common interface to hash tables *)
(* red/black trees and similar data structures *)

signature TABLE =
sig
  type key (* parameter *)
  type 'a entry = key * 'a

  type 'a Table
  val new : int -> 'a Table		(* size hint for some implementations *)

  val insert : 'a Table -> 'a entry -> unit
  (* insert entry, return shadowed entry if there is one *)
  val insertShadow : 'a Table -> 'a entry -> ('a entry) option
  val lookup : 'a Table -> key -> 'a option
  val delete : 'a Table -> key -> unit
  val clear : 'a Table -> unit

  (* Apply function to all entries in unpredictable order *)
  val app : ('a entry -> unit) -> 'a Table -> unit

end;  (* signature TABLE *)
