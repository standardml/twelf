
(** Imperative arrays that automatically grow to
    accomodate new data. The array can have 'holes'
    where no data are stored, though these are not
    treated efficiently. *)
signature GROWARRAY =
sig

  type 'a growarray
    
  val growarray : int -> 'a -> 'a growarray

  val empty : unit -> 'a growarray

  (** return actual length *)
  val length : 'a growarray -> int

  (** can raise Subscript when out of bounds *)
  val sub : 'a growarray -> int -> 'a

  (** only raises subscript if index is negative. *)
  val update : 'a growarray -> int -> 'a -> unit

  (** stick an element at the end *)
  val append : 'a growarray -> 'a -> unit

  (** true if a position has been set *)
  val used : 'a growarray -> int -> bool

  (** 
     after calling this, don't use the growarray
     any longer, since it may share data with the returned
     array. 

     @exception Subscript if the array has holes.
*)
  val finalize : 'a growarray -> 'a Array.array

end
