
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
  val table : int -> 'a table

  (** Insert a key/value pair into the table.  
      Raise Fail if key is already present. *)
  val insert : 'a table -> key * 'a -> 'a table

  (** Lookup a key in the table. Raise Fail if key not present *)
  val lookup : 'a table -> key -> 'a
       
  (** number of key/value pairs *)
  val size : 'a table -> int

  (** Iterate a procedure over the table. *)
  val app : ('a -> unit) -> 'a table -> unit

  (** Iterate a procedure over the table. *)
  val appi : (int * 'a -> unit) -> 'a table -> unit

  (** Clear the table. *)
  val clear : 'a table -> unit

end
