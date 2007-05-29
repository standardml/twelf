
(** 
 A tabular data structure.
 *) 
signature TABLE =
sig

  type key
  type 'a table

  (** Give the expected size of the eventual table. 
      Some implementations may grow outside that initial
      bound if necessary.  Others may raise an exception.
   *)
  val empty : int -> 'a table

  (** Insert a key/value pair into the table.  
      Raise Fail if key is already present. *)
  val insert : 'a table -> key * 'a -> 'a table

  (** Lookup a key in the table. Raise Fail if key not present *)
  val lookup : 'a table -> key -> 'a
       
  (** number of key/value pairs *)
  val size : 'a table -> int

  val app : ('a -> unit) -> 'a table -> unit
(*   val foldl : ('a * 'b -> 'b) -> 'b -> 'a table -> 'b *)
(*   val foldr : ('a * 'b -> 'b) -> 'b -> 'a table -> 'b *)

end
